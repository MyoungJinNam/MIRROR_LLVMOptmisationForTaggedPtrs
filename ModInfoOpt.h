//===-----  RemoveRTChks/ModInfoOpt.h - Transformation pass  -----===//
//===-----  Copyright © March 2022 by Myoung Jin Nam        -----===//
//===-----  myoungjin.nam@gmail.com, mjn31@cantab.ac.uk     -----===//

#ifndef LLVM_TRANSFORMS_MOD_INFO_OPT_MIUPASS_H
#define LLVM_TRANSFORMS_MOD_INFO_OPT_MIUPASS_H

#include "llvm/IR/PassManager.h"
#include "./ModInfoAbstract.h"

using namespace llvm;
using namespace SelfContainedMiuProject;

namespace SelfContainedMiuProject {

    class ModInfoOpt : public ModInfoAbstract {
      
      protected:
        
        StringRef Prefix = "";
        unsigned NumRemovedHooks = 0;
        std::unordered_set <Value*> Untracked;
        std::unordered_set <Function*> IgnoreFunctions;
      
      public:
        
        ModInfoOpt(Module * M, StringRef & prefix) : ModInfoAbstract (M)
        {        
            this->M = M;
            this->CXT = &(M->getContext());
            this->DL = &(M->getDataLayout());
            this->Prefix = prefix;
            errs()<<"ModInfoOpt_constructor_called\n";
        }
        virtual ~ModInfoOpt() {}
        
        virtual Value * getInstrumentedPtr (CallInst * CI)
        {
            assert(CI);
            // TODO: Fill it  
        }
        /* Instrment direct function calls to heap alloc (malloc, new etc) */ 
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

        virtual bool isIgnoreFunction (Function * Caller) 
        {
            bool Ignore = false;

            if (Caller->isDeclaration()) {
                Ignore |= true; 
            }
            if (isHookFunc (Caller)) {
                //errs()<<"(IS_HOOKFUNC) ";
                Ignore |= true; 
            }
            if (has_elem_o (this->IgnoreFunctions, Caller)) {
                //errs()<<"(IgnoreFunctions) ";
                Ignore |= true; 
            } 

            return Ignore;    
        }
        
        void insertToUntracked(Value * Val) 
        {
            // TODO. skip dups
            this->Untracked.insert(Val);
        }
        
        bool findUntracked (Value * Elem)
        {
            if (has_elem_o(this->Untracked, Elem)) {
                return true;
            }
            return false;
        }
        
        virtual Instruction * replaceCallHook (CallInst * CI, Function * Rep) 
        {
            //TODO: fill this
            return nullptr;
        }
        
        virtual Instruction * stripCallHook (CallInst * CI) 
        {
            //TODO: fill this
            return nullptr;
        }
         
        virtual bool visitFunc(Function* F) {return false;}
        
    };

} // namespace SelfContainedMiuProject 

#endif //LLVM_TRANSFORMS_MOD_INFO_OPT_MIUPASS_H
