//
//===-- HookInfoAbstract.h -------------------*- C++ -*-===//
//===-- Copyright © March 2022 by Myoung Jin Nam  -------------===//
//===-- myoungjin.nam@gmail.com, mjn31@cantab.ac.uk  ----------===//


#ifndef LLVM_TRANSFORMS_MIUPROJECT_HOOK_INFO_ABSTRACT_MIUPASS_H
#define LLVM_TRANSFORMS_MIUPROJECT_HOOK_INFO_ABSTRACT_MIUPASS_H

#include "llvm/IR/PassManager.h"

using namespace llvm;
using namespace SelfContainedMiuProject;

namespace SelfContainedMiuProject {
// TODO: disable namespace later

    class HookInfoAbstract {
      
      protected:
        
        StringRef Prefix = "";
        Module * M = nullptr;
        
        LLVMContext * CXT = nullptr;
        //const DataLayout *DL;                
      
      public:
        
        //- Constructor, Destructor -//
        HookInfoAbstract(StringRef & prefix, Module * mod) 
        {        
            assert(!prefix.empty());
            this->Prefix = prefix;
            this->M = mod;
            this->CXT = &M->getContext();
        }
        virtual ~HookInfoAbstract() {}
       
        virtual bool isHookFunc (Function * Func)
        {
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
    };

} // namespace SelfContainedMiuProject 

#endif // LLVM_TRANSFORMS_MIUPROJECT_HOOK_INFO_ABSTRACT_MIUPASS_H
