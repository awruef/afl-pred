#include <clang/AST/ASTConsumer.h>
#include <clang/AST/RecursiveASTVisitor.h>
#include <clang/Frontend/CompilerInstance.h>
#include <clang/Frontend/FrontendAction.h>
#include <clang/Rewrite/Core/Rewriter.h>
#include <clang/Tooling/CommonOptionsParser.h>
#include <clang/Tooling/Tooling.h>
#include <clang/Analysis/CFG.h>
#include <clang/Analysis/Analyses/PostOrderCFGView.h>
#include <llvm/ADT/STLExtras.h>
#include <llvm/ADT/StringSwitch.h>
#include <llvm/Option/OptTable.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/Signals.h>
#include <llvm/Support/TargetSelect.h>

using namespace std;
using namespace clang::driver;
using namespace clang::tooling;
using namespace clang;
using namespace llvm;

static cl::OptionCategory Cat("skeleton options");
cl::opt<bool> Verbose("verbose",
                      cl::desc("Print verbose information"),
                      cl::init(false),
                      cl::cat(Cat));

template <typename T>
class GenericAction : public ASTFrontendAction {
public:
  GenericAction() {}

  virtual unique_ptr<ASTConsumer>
  CreateASTConsumer(CompilerInstance &Compiler, StringRef InFile) {
    return unique_ptr<ASTConsumer>(new T(InFile, &Compiler.getASTContext()));
  }
};

class TransformConsumer : public ASTConsumer {
public:
  explicit TransformConsumer(StringRef File, ASTContext *C) : Ctx(C), File(File) {}

  virtual void HandleTranslationUnit(ASTContext &);

private:
  ASTContext *Ctx;
  string  File;
};

class SkeletonVisitor : public RecursiveASTVisitor<SkeletonVisitor> {
  ASTContext *Ctx;
public:
  explicit SkeletonVisitor(ASTContext *C) : Ctx(C) {}

  bool VisitBinAssign(BinaryOperator *);
};

bool SkeletonVisitor::VisitBinAssign(BinaryOperator *O) {

  return true;
}

void TransformConsumer::HandleTranslationUnit(ASTContext &C) {
  SkeletonVisitor S(&C);

  for (const auto &D : C.getTranslationUnitDecl()->decls())
    S.TraverseDecl(D);

  return;
}

typedef GenericAction<TransformConsumer> TransformAction;

int main(int argc, const char **argv) {
  sys::PrintStackTraceOnErrorSignal(argv[0]);

  // Initialize targets for clang module support.
  InitializeAllTargets();
  InitializeAllTargetMCs();
  InitializeAllAsmPrinters();
  InitializeAllAsmParsers();

  CommonOptionsParser OptionsParser(argc, argv, Cat);
  tooling::CommandLineArguments args = OptionsParser.getSourcePathList();
  ClangTool Tool(OptionsParser.getCompilations(), args);

  unique_ptr<ToolAction>  Action = newFrontendActionFactory<TransformAction>();

  if (Action)
    Tool.run(Action.get());
  else
    llvm_unreachable("No action!");

  return 0;
}
