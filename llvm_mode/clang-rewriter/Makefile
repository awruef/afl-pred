
CONFIG ?= llvm-config

CXXFLAGS = $(shell $(CONFIG) --cxxflags) -g -ggdb
LDFLAGS = $(shell $(CONFIG) --ldflags) 
LLVM_LIBS = $(shell $(CONFIG) --libs)
SYSLIBS = $(shell $(CONFIG) --system-libs)
LIBS = -lclangTooling -lclangFrontend -lclangRewrite -lclangRewriteFrontend -lclangDriver -lclangSerialization -lclangParse -lclangSema -lclangAnalysis -lclangAST -lclangEdit -lclangLex -lclangCodeGen -lclangBasic 

all: skeleton 

skeleton: skeleton.cpp 
	$(CXX) -o skeleton skeleton.cpp $(CXXFLAGS) $(LDFLAGS) $(LIBS) $(LLVM_LIBS) $(SYSLIBS)

clean:
	rm skeleton
