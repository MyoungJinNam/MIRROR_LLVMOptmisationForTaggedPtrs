//
//===-- ModInfoOpt.h              -------------------*- C++ -*-===//
//===-- Copyright © March 2022 by Myoung Jin Nam  -------------===//

#ifndef LLVM_TRANSFORMS_MOD_INFO_OPT_MIUPASS_H
#define LLVM_TRANSFORMS_MOD_INFO_OPT_MIUPASS_H

#include "llvm/IR/PassManager.h"
//#include "./ModInfoAbstract.h"

using namespace llvm;
//using namespace MiuProject;

namespace MiuProject {
    template < typename T>
    static bool has_elem_o (unordered_set<T> & OST, T elem)
        {
            auto it= OST.find(elem);
            if (it != OST.end()) {
                return true;       
            }
            return false;
        }    
    /* 
    class ModInfoOpt {
      
      protected:
        
      public:
        
        Module* M = nullptr;
        TargetLibraryInfo* TLI = nullptr;
        ScalarEvolution* SE = nullptr;
        LLVMContext * CXT = nullptr;
        const DataLayout *DL;
        function_ref<const TargetLibraryInfo &(Function &)> GetTLI;
        
        ModInfoOpt(Module* M) {
            this->M = M;
        }
        virtual ~ModInfoOpt() {};
        
        ModInfoAbstract(Module* M) {
            this->M = M;
        }
        virtual ~ModInfoAbstract() = 0;
        // TODO: remove modinfoabstract

        void setScalarEvolution(ScalarEvolution* SE) {
            this->SE = SE;
        }
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
        */
        
        /*
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
        virtual void initialiseModInfo ()
        {
            //this->SE = M->SE;
            this->CXT = &(M->getContext());
            this->DL = &(M->getDataLayout());
            //this->MainPrologueName = "MIU_main_prologue_base";
        }
        */
        
        /*
        // Next two funcs are moved to modinfoopt class.

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

        /*
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
        
        virtual bool isIgnoreFunction (Function * Caller) {return false;}                    
        virtual bool visitGlobals() { return false; }
        //- pure virtual functions -//
        virtual bool visitFunc (Function* F) = 0; 
    };
    */
    
    //ModInfoAbstract::~ModInfoAbstract() {}
    
    //- class ModInfoOpt -//

    //class ModInfoOpt : public ModInfoAbstract {
    
    class ModInfoOpt {
      
      protected:

        StringRef Prefix = "";
 
        std::unordered_set <Function*> IgnoreFunctions;
        unsigned NumRemovedHooks = 0;
        std::unordered_set <Value*> Untracked;
       
        // Moved from abstract class. TODO: remove comments later 
        Module* M = nullptr;
        TargetLibraryInfo* TLI = nullptr;
        ScalarEvolution* SE = nullptr;
        LLVMContext * CXT = nullptr;
        const DataLayout *DL;
        function_ref<const TargetLibraryInfo &(Function &)> GetTLI;
     
      public:

        //ModInfoOpt(Module * M, StringRef & prefix) : ModInfoAbstract (M)
        ModInfoOpt(Module * M, StringRef & prefix) 
        {        
            this->M = M;
            this->CXT = &(M->getContext());
            this->DL = &(M->getDataLayout());
            this->Prefix = prefix;
        }
        virtual ~ModInfoOpt() {}
       
        /* 
        virtual Value * getInstrumentedPtr (CallInst * CI)
        {
            assert(CI);
            // TODO: Fill it  
        }
        */

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
        /* 
        not used?

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
        */
        
    };

} // namespace MiuProject 

#endif //LLVM_TRANSFORMS_MOD_INFO_OPT_MIUPASS_H
