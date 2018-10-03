/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   Copyright 2015, 2016 Google Inc. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.

 */

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

using namespace llvm;

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}


char AFLCoverage::ID = 0;


bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Instrument all the things! */

  int inst_blocks = 0;

  // Return value instrumentation. 
  for (auto &F : M) 
    for (auto &BB : F) {
      for (auto &I : BB) {
        if (ReturnInst *R = dyn_cast<ReturnInst>(&I)) {
          if (Value *RV = R->getReturnValue()) {
            
            if (AFL_R(100) >= inst_ratio) continue;

            // We want to insert instrumentation before the return value.
            IRBuilder<> IRB(R); 

            unsigned int cur_loc = AFL_R(MAP_SIZE);

            ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

            LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
            PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
            Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

            LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
            MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
            Value *MapPtrIdx =
              IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

            // Is the return value a pointer, or not? 
            if (RV->getType()->isFloatTy() || 
                (RV->getType()->isIntegerTy() && !(RV->getType()->getScalarSizeInBits() > 1)) ||
                RV->getType()->isStructTy() || 
                RV->getType()->isVectorTy())
            {
              // If it's one of these cases, then skip it. 
              continue;
            } else if (RV->getType()->isPointerTy()) {
              // Add instrumentation that checks whether or not the value is 
              // NULL, and ANDs it into the current map idx.
             
              // First, get the counter value. 
              LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
              Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      
              // Then, compute the value we want to OR in, by using cmp and select.
              Value *RTBC = IRB.CreateBitCast(RV, IRB.getInt64Ty());
              Value *NV = ConstantInt::get(IRB.getInt64Ty(), 0);
              Value *IsNull = IRB.CreateICmpEQ(RTBC, NV);
              Value *IsNullV = ConstantInt::get(IRB.getInt8Ty(), 1);
              Value *IsNonNullV = ConstantInt::get(IRB.getInt8Ty(), 2);
              Value *SelectedV = IRB.CreateSelect(IsNull, IsNullV, IsNonNullV);
              Value *ORedV = IRB.CreateOr(Counter, SelectedV);

              // Write that value back into the map.
              IRB.CreateStore(ORedV, MapPtrIdx)
                ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
            } else {
              // First, get the counter value. 
              LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
              Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
 
              // Add instrumentation that records the signed-ness of the value,
              // and ORit into the current map idx. 
              Value *Z = ConstantInt::get(RV->getType(), 0); 
              Value *ReqZ = IRB.CreateICmpEQ(RV, Z);
              Value *RltZ = IRB.CreateICmpSLT(RV, Z);
              Value *RgtZ = IRB.CreateICmpSGT(RV, Z);

              Value *IsREqZ = ConstantInt::get(IRB.getInt8Ty(), 1);
              Value *IsNotREqZ = ConstantInt::get(IRB.getInt8Ty(), 2);
              Value *IsRltZ = ConstantInt::get(IRB.getInt8Ty(), 3);
              Value *IsNotRltZ = ConstantInt::get(IRB.getInt8Ty(), 4);
              Value *IsRgtZ = ConstantInt::get(IRB.getInt8Ty(), 5);
              Value *IsNotRgtZ = ConstantInt::get(IRB.getInt8Ty(), 6);

              Value *S1v = IRB.CreateSelect(ReqZ, IsREqZ, IsNotREqZ);
              Value *S2v = IRB.CreateSelect(RltZ, IsRltZ, IsNotRltZ);
              Value *S3v = IRB.CreateSelect(RgtZ, IsRgtZ, IsNotRgtZ);
              Value *t1 = IRB.CreateOr(S1v, S2v);
              Value *t2 = IRB.CreateOr(S3v, t1);
              Value *ORedV = IRB.CreateOr(Counter, t2);

              // Write that value back into the map.
              IRB.CreateStore(ORedV, MapPtrIdx)
                ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
            }

            StoreInst *Store =
                IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
            Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

            inst_blocks++;
          }
        }
      }
    }

  // Parameter instrumentation.
  for (auto &F : M) {
    if (F.isVarArg())
      continue;

    if (F.size() == 0)
      continue;

    BasicBlock &BB = F.getEntryBlock();

    BasicBlock::iterator IP = BB.getFirstInsertionPt();
    IRBuilder<> IRB(&(*IP));

    std::vector<Value *> intParms;
    std::vector<Value *> ptrParms;
    // Get the parameter list for this function and make two sets: the 
    // integer type parameters and the pointer type parameters.
    for (auto &V : F.args()) {
      uint64_t tw = M.getDataLayout().getTypeAllocSizeInBits(V.getType());
      if (V.getType()->isPointerTy())
        ptrParms.push_back(&V);
      else if(V.getType()->isIntegerTy() && tw > 1)
        intParms.push_back(&V);
    }

    // If there is more than one of either, add comparisons between them.
    std::vector<std::pair<Value *, Value *>> instrumentPairs;
    if (intParms.size() > 1) 
      for( unsigned i = 0 ; i < intParms.size() - 1; i++) 
        for (unsigned j = i; j < intParms.size(); j++) 
          instrumentPairs.push_back(std::make_pair(intParms[i], intParms[j]));

    if (ptrParms.size() > 1) 
      for( unsigned i = 0 ; i < ptrParms.size() - 1; i++) 
        for (unsigned j = i; j < ptrParms.size(); j++) 
          instrumentPairs.push_back(std::make_pair(ptrParms[i], ptrParms[j]));

    for (auto &P : instrumentPairs) {
      // Each P is its own instrument point. 
      Value *RHS = P.first; 
      Value *LHS = P.second;

      unsigned int cur_loc = AFL_R(MAP_SIZE);

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
        IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));
 
      if (RHS->getType()->isPointerTy()) {
        LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
        Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      
        Value *RTBC = IRB.CreateBitCast(RHS, IRB.getInt64Ty());
        Value *LTBC = IRB.CreateBitCast(LHS, IRB.getInt64Ty());
        Value *IsNull = IRB.CreateICmpEQ(RTBC, LTBC);
        Value *IsNullV = ConstantInt::get(IRB.getInt8Ty(), 1);
        Value *IsNonNullV = ConstantInt::get(IRB.getInt8Ty(), 2);
        Value *SelectedV = IRB.CreateSelect(IsNull, IsNullV, IsNonNullV);
        Value *ORedV = IRB.CreateOr(Counter, SelectedV);

        IRB.CreateStore(ORedV, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      } else {
        LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
        Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
 
        //Value *Z = ConstantInt::get(RV->getType(), 0); 
        Value *LHSi = IRB.CreateSExt(LHS, IRB.getInt64Ty());
        Value *RHSi = IRB.CreateSExt(RHS, IRB.getInt64Ty());
        Value *LeqR = IRB.CreateICmpEQ(LHSi, RHSi);
        Value *LltR = IRB.CreateICmpSLT(LHSi, RHSi);
        Value *LgtR = IRB.CreateICmpSGT(LHSi, RHSi);

        Value *IsLEqR = ConstantInt::get(IRB.getInt8Ty(), 1);
        Value *IsNotLEqR = ConstantInt::get(IRB.getInt8Ty(), 2);
        Value *IsLltR = ConstantInt::get(IRB.getInt8Ty(), 3);
        Value *IsNotLltR = ConstantInt::get(IRB.getInt8Ty(), 4);
        Value *IsLgtR = ConstantInt::get(IRB.getInt8Ty(), 5);
        Value *IsNotLgtR = ConstantInt::get(IRB.getInt8Ty(), 6);

        Value *S1v = IRB.CreateSelect(LeqR, IsLEqR, IsNotLEqR);
        Value *S2v = IRB.CreateSelect(LltR, IsLltR, IsNotLltR);
        Value *S3v = IRB.CreateSelect(LgtR, IsLgtR, IsNotLgtR);
        Value *t1 = IRB.CreateOr(S1v, S2v);
        Value *t2 = IRB.CreateOr(S3v, t1);
        Value *ORedV = IRB.CreateOr(Counter, t2);

        IRB.CreateStore(ORedV, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      }

      StoreInst *Store =
        IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;
    }
  }

  // Edge instrumentation. 
  for (auto &F : M)
    for (auto &BB : F) {

      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio) continue;

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE);

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

      /* Load prev_loc */

      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;

    }

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_OptimizerLast, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
