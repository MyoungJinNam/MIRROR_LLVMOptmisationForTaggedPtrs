//===-----  FuncInfoAbstract.h - Transformation pass        -----===//
//===-----  Copyright © March 2022 by Myoung Jin Nam        -----===//
//===-----  myoungjin.nam@gmail.com, mjn31@cantab.ac.uk     -----===//

#ifndef LLVM_TRANSFORMS_FUNC_INFO_ABSTRACT_MIUPASS_H
#define LLVM_TRANSFORMS_FUNC_INFO_ABSTRACT_MIUPASS_H

#include "llvm/IR/PassManager.h"
#include <llvm/Pass.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Support/Casting.h>
#include <llvm/IR/Dominators.h>
#include <llvm/ADT/DepthFirstIterator.h>
#include <llvm/ADT/SmallSet.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/IR/MDBuilder.h>
#include <llvm/IR/Metadata.h>
#include <llvm/Analysis/MemoryBuiltins.h>
#include <llvm/Analysis/TargetLibraryInfo.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/ScalarEvolutionExpressions.h>
#include <llvm/Analysis/AssumptionCache.h>
#include <llvm/Analysis/LoopAccessAnalysis.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/Analysis/LoopIterator.h>
#include <llvm/Analysis/LoopPass.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/Transforms/Utils/Local.h>

#include <iostream>
#include <map>
#include <set>
#include <utility>
#include <tr1/memory>
#include <tr1/tuple>
#include <assert.h>
#include <unordered_set>

using namespace llvm;

namespace SelfContainedMiuProject {

    class FuncInfoAbstract {
      
      protected:
        
        Function* F = nullptr;
        TargetLibraryInfoWrapperPass *TLIWP = nullptr;
 
      public:
        
        FuncInfoAbstract(Function* F) {
            this->F = F;
        }
        virtual ~FuncInfoAbstract() = 0;
        
        void setTLIWP (TargetLibraryInfoWrapperPass *TLIWP_M)
        {
            this->TLIWP = TLIWP_M; 
        }
        TargetLibraryInfo * getTLI(const Function & F)
        {
            return &this->TLIWP->getTLI(F);
        }
    };
    
    FuncInfoAbstract::~FuncInfoAbstract() {}
} // namespace SelfContainedMiuProject 

#endif //LLVM_TRANSFORMS_FUNC_INFO_MIU_MIUPASS_H
