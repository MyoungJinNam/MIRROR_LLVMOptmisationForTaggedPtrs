//===-----  RemoveRTChks/ModInfoAbstract.h - Transformation pass    -----===//
//===-----  Copyright © March 2022 by Myoung Jin Nam                -----===//
//===-----  myoungjin.nam@gmail.com, mjn31@cantab.ac.uk             -----===//

#ifndef LLVM_TRANSFORMS_MOD_INFO_ABSTRACT_MIUPASS_H
#define LLVM_TRANSFORMS_MOD_INFO_ABSTRACT_MIUPASS_H

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
//#include <tr1/memory>
//#include <tr1/tuple>
#include <assert.h>
#include <unordered_set>

using namespace llvm;

namespace SelfContainedMiuProject {

    template < typename T>
    static bool has_elem_o (std::unordered_set<T> & OST, T elem)
    {
        auto it= OST.find(elem);
        if (it != OST.end()) {
            return true;       
        }
        return false;
    }

    class ModInfoAbstract {
      
      protected:
        
      public:
        
        Module* M = nullptr;
        LLVMContext * CXT = nullptr;
        const DataLayout *DL;
        //ScalarEvolution* SE = nullptr;
        
        TargetLibraryInfo* TLI = nullptr;
        function_ref<const TargetLibraryInfo &(Function &)> GetTLI;
        
        ModInfoAbstract(Module* M) {
            this->M = M;
            this->CXT = &(M->getContext());
            this->DL = &(M->getDataLayout());
        }
        virtual ~ModInfoAbstract() = 0;
        
        /*
        virtual void resetMainPrologueHook (StringRef & Fname)
        {
            this->MainPrologueName= Fname; 
        }
        void setScalarEvolution(ScalarEvolution* SE) {
            this->SE = SE;
        }
        */
        
        void setLLVMContext(LLVMContext * CXT) {
            this->CXT = CXT;
        }
        void setDL(const DataLayout *DL) {
            this->DL = DL;
        }
        void setTLI(function_ref<const TargetLibraryInfo &(Function &)> GetTLI)
        {
            this->GetTLI= GetTLI; 
        }

        const TargetLibraryInfo * getFuncTLI (Function * FN) 
        {
            return &GetTLI(const_cast<Function &>(*FN));
        }
    
        void initialiseModInfo (function_ref<const TargetLibraryInfo &(Function &)> GetTLI) 
        {
            //this->SE = M->SE;
            this->CXT = &(M->getContext());
            this->DL = &(M->getDataLayout());
            this->GetTLI= GetTLI; 
            //this->MainPrologueName = "MIU_main_prologue_base";
        }
        /*
        virtual void initialiseModInfo ()
        {
            //this->SE = M->SE;
            this->CXT = &(M->getContext());
            this->DL = &(M->getDataLayout());
            //this->MainPrologueName = "MIU_main_prologue_base";
        }
        
        virtual bool isHookFunc (Function * Func)
        {
            assert(!(this->Prefix.empty()));
            if (Func->getName().startswith(this->Prefix)) {
                return true;
            }
            return false;
        }
        virtual bool isCallHook (Value * Val)
        {
            if (!isa<CallInst>(Val)) return false;
            
            CallInst * CI = cast<CallInst>(Val); 
            if (!CI->getCalledFunction()) return false; 
            
            Function * Callee = CI->getCalledFunction();
            if (isHookFunc (Callee)) {
                return true;
            }
            return false;
        } 
        */

        virtual bool instrGep(GetElementPtrInst* Gep) {return false;} 
        virtual bool instrumentLoadOrStore(Instruction * I) {return false;} 
        virtual bool instrLoad (LoadInst * Ins) {return false;} 
        virtual bool instrStore (StoreInst * Ins) {return false;} 
        virtual bool getHookProto (FunctionCallee & Hook, StringRef & HookName) {return false;}
        
        virtual bool instrMainFunction () {return false;}
        virtual bool instrMainFunction (StringRef & FName) {
            return false;
        }
        
        virtual bool instrAllocaInst(AllocaInst * Ins) {return false;}
        virtual bool instrCallBase(CallBase * Ins) {return false;}
        virtual bool instrCallInst(CallInst * Ins) {return false;}

        virtual Function * getOrInsertHook (Instruction * Ins) {return nullptr;}
        virtual void setIgnoreUserFunctions () {}
        //virtual bool isIgnoreFunction (Function * Caller) {return false;}                    
        virtual bool visitGlobals() { return false; }
        /* pure virtual functions */
        virtual bool visitFunc (Function* F) = 0; 
    };
    
    ModInfoAbstract::~ModInfoAbstract() {}

} // namespace SelfContainedMiuProject 

#endif //LLVM_TRANSFORMS_MOD_INFO_MIU_MIUPASS_H
