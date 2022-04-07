//===----- Optimisation - Transformation pass -----===//
#define DEBUG_TYPE "remove_rtchks"

////
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Pass.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include <llvm/Pass.h>
#include "llvm/Passes/PassPlugin.h"
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

/* MiuProject-related */
// TODO: make it self-contained under the branch

#include "../../ModInfoOpt.h"
#include "../../FuncInfoAbstract.h"
#include "../../HookInfoAbstract.h"

#include <iostream>
#include <map>
#include <set>
#include <utility>
#include <tr1/memory>
#include <tr1/tuple>
#include <assert.h>

#define MIU_PRINT_DEBUG
#ifdef MIU_PRINT_DEBUG
#  define dbg(x) x
#else
#  define dbg(x) 
#endif

using namespace llvm;
using namespace MiuProject;
    
namespace {
    
    class HookInfoMiu : public MiuProject::HookInfoAbstract {
      
      protected: 
        
        StringRef ChkBoundHookName = "";
        StringRef UpdatePtrHookName = "";
        StringRef UntagHookName = "";
        StringRef AllocHookName = "";

      public: 
        //- constructor, destructor -//
        HookInfoMiu (StringRef & str) : MiuProject::HookInfoAbstract (str) 
        {
            this->Prefix = str;
            errs()<<" ------> HookInfoMiu_constructor_called\n";
             
        } 
        virtual ~HookInfoMiu() {}    
        
        virtual void setChkBoundHookName (StringRef & Str) 
        {
            this->ChkBoundHookName = Str;
        }
        
        virtual void setUpdatePtrHookName (StringRef & Str) 
        {
            this->UpdatePtrHookName = Str;
        }
        
        virtual void setUntagHookName (StringRef & Str) 
        {
            this->UntagHookName = Str;
        }

        virtual void setAllocHookName (StringRef & Str) 
        {
            this->AllocHookName = Str;
        }
        virtual StringRef getUntagHookName ()
        {
            return this->UntagHookName;
        }
        
        //- check hook funcs -//
        virtual bool isCheckBoundHookName (StringRef & Str) 
        {
            if (Str.equals(this->ChkBoundHookName)) return true;
            return false;
        }
         
        virtual bool isUpdatePtrHookName (StringRef & Str) 
        {
            if (Str.equals(this->UpdatePtrHookName)) return true;
            return false;
        }
        
        virtual bool isUntagHookName (StringRef & Str) 
        {
            if (Str.equals(this->UntagHookName)) return true;
            return false;
        }

        virtual bool isAllocHookName (StringRef & Str) 
        {
            if (Str.equals(this->AllocHookName)) return true;
            return false;
        }
        
        //- check if it is call hook -// 
        virtual bool isCheckBoundCallHook (Instruction * Ins)
        {
            if (!isCallHook(Ins)) { return false; }
            StringRef HookName = cast<CallInst>(Ins)->getCalledFunction()->getName();
            if (isCheckBoundHookName(HookName)) { return true; }
            return false; 
        }
        virtual bool isUntagCallHook (Instruction * Ins)
        {
            if (!isCallHook(Ins)) { return false; }
            StringRef HookName = cast<CallInst>(Ins)->getCalledFunction()->getName();
            if (isUntagHookName(HookName)) { return true; }
            return false; 
        }
        
        virtual bool isUpdatePtrCallHook (Instruction * Ins)
        {
            if (!isCallHook(Ins)) { return false; }
            StringRef HookName = cast<CallInst>(Ins)->getCalledFunction()->getName();
            if (isUpdatePtrHookName(HookName)) { return true; }
            return false; 
        }
        
        virtual bool isUntracked (Value * Val)
        {
            auto search = Untracked.find(Val);
            if (search != Untracked.end()) {
                return true;
            }
            return false;
        }
        
        //- modified: __isSafeAccess in Framer.h.   -// 
        //- Consider spacemiu repo.                 -//
       /* virtual bool isInboundPtr (Value * Ptr) 
        {
            CallInst * ci= __isAllocation(gep->getPointerOperand(), M, gep); 
            //ci is hook_alloca,hook_gv, or malloc call
            if (ci==nullptr) {
                return NOTSAFESTATICALLY; 
            }
            if (gep->hasAllZeroIndices()) { // base addr of alloca/gv
                return SAFESTATICALLY; 
            }
            // ***** malloc s ***   
            if (ci->getCalledFunction()->getName().equals("malloc")) {
                return handleMallocStaticBounds(gep, ci, isMemAccess, M); 
            }
            // ***** malloc e ***

            if (!isa<ConstantInt>(gep->getOperand(1)->stripPointerCasts())){
                return NOTSAFESTATICALLY; // issafeaccess==0. 
            }
            if (!((cast<ConstantInt>(gep->getOperand(1)->stripPointerCasts()))->equalsInt(0))) {
                return NOTSAFESTATICALLY; 
            }
            if (!gep->hasAllConstantIndices()) {
                if (gep->getNumIndices()<=2) {
                    return COMPAREIDXATRUNTIME; // issafeaccess==2. requiring runtime check 
                } 
                else {
                    return NOTSAFESTATICALLY;
                } 
            }
            // offset= base~ptr (two args. 2nd is gep's ptr.assignment)
            unsigned offset= getStaticOffset(gep, &M.getDataLayout()); 
            unsigned totalsize= getmysize(ci);
            unsigned sizeToAccess= FramerGetBitwidth(cast<PointerType>(gep->getType())->getElementType(), &M.getDataLayout())/8;

            return isStaticInBound(offset, 
                    sizeToAccess,
                    totalsize,
                    isMemAccess);  

        } 
    };

    class FuncInfoRemRTChks : public MiuProject::FuncInfoAbstract {

      protected:
        std::unordered_set <Value*> GlobalAllocs;
        std::unordered_set <Value*> Locals;
        std::unordered_set <Value*> HeapAllocs;
        
        //- merging into one 
        
        std::unordered_set <Value*> FNUntracked;
        std::unordered_set <Value*> FNSafePtrs;
        
        std::vector<Instruction*> RedundantChks;
      
      public:
        
        //- constructor, destructor -//
        FuncInfoRemRTChks (Function * F) : MiuProject::FuncInfoAbstract (F) 
        {
            this->F = F;
            //errs()<<"FuncInfoRemRTChks_instance_created\n";
        } 
        virtual ~FuncInfoRemRTChks() {}    
        
        virtual Function * getFunction () 
        {
            return this->F;
        }
        
        // Accumulate FNSafePtrs. Or delete this func..
        virtual bool isSafePtr (Value * Ptr)
        {
            Value * RawPtr = Ptr->stripPointerCasts();
            return has_elem_o (FNSafePtrs, RawPtr);
        }
        /*
        virtual bool isSafeAccess (Value * Ptr)
        {
            Value * op = Ptr->stripPointerCasts();

            //if (isHookedAllocaOrGV(op, paddedGVs)) {
            if () {
                return SAFESTATICALLY;
            }
            Value * mallocop= ismalloc(Ptr);
            if (mallocop!=nullptr) {

                return SAFESTATICALLY;
            }
            if (GEPOperator * gep=dyn_cast<GEPOperator>(op)) {  
                dbg("skip. safe gep\n";)
                    return __isSafeAccess(gep, M, isMemAccess); 
            }
            else {

                /// commented since I am doubtful if this will /////////
                /// make a big difference for performance.      /////////
                /// can try later                               /////////
                //        if (checkSafeWithDomTree(op, dt)) { 
                //            errs()<<"Read todo\n"; //TODO. bring case splitting (if load stuff) to here.
                //            return true;
                //        }
            } 
            return 0; 
        }
        */

        void stripHook (CallInst * CI, Value * Ptr = nullptr)
        { 
            std::vector<User*> Users(CI->user_begin(), CI->user_end());
            assert(Ptr && "stripHook: do_something");

            for (auto User : Users){
                Instruction * iUser = dyn_cast<Instruction>(User); 
                //- iUser is BCI or CI's User -//
                assert(iUser);

                if (isa<CastInst>(iUser)) {
                    CastInst * BCI = cast<CastInst>(iUser);

                    for (auto UserOfBCI = BCI->user_begin(); UserOfBCI!=BCI->user_end(); UserOfBCI++) { 
                        Instruction * iUserOfBCI = dyn_cast<Instruction>(*UserOfBCI);
                        int OpIdx = getOpIdx(iUserOfBCI, BCI);  
                        if (OpIdx < 0) continue;

                        //assert(iUserOfBCI->getOperand(OpIdx)->getType()==Ptr->getType()); 
                        Value * newOp = Ptr;
                        if (iUserOfBCI->getOperand(OpIdx)->getType()!=Ptr->getType()) {
                            IRBuilder<> B(iUserOfBCI); 
                            Value * newBCI = B.CreatePointerCast(Ptr, iUserOfBCI->getOperand(OpIdx)->getType()); 
                            errs()<<"newBCI: "<<*newBCI<<"\n";
                            newOp = newBCI;
                        }
                        iUserOfBCI->setOperand(OpIdx, newOp); 
                        dbg(errs()<<"- BCI's newUser:  "<<*iUserOfBCI<<"\n";);
                        //insert_tovec(RedundantChks, (Instruction*)BCI); //TODO remove dups. MiuUtils
                        this->addRedundantChks((Instruction*)BCI); //TODO remove dups. MiuUtils
                    }
                }
                else {
                    int OpIdx = getOpIdx(iUser, CI);  
                    dbg(errs()<<"- Else OldUser:  "<<*iUser<<"\n";);
                    assert(iUser->getOperand(OpIdx)->getType()==Ptr->getType()); 

                    iUser->setOperand(OpIdx, Ptr);
                    dbg(errs()<<"- Else newUser:  "<<*iUser<<"\n";);
                }

                //insert_tovec(RedundantChks, (Instruction*)CI);
                this->addRedundantChks((Instruction*)CI); 

            } // end of for loop
        }
        
        void replaceHook (CallInst * CI, FunctionCallee & Callee, int OpIdx=0)
        {
            // TODO. replace hook with newone. (checkbound with tag-cleaning) 
            Value * Ptr = CI->getOperand(OpIdx)->stripPointerCasts();

            IRBuilder<> B(CI);

            CallInst* newCI = B.CreateCall(Callee, CI->getOperand(OpIdx));
            std::vector<User*> Users(CI->user_begin(), CI->user_end());
            
            dbg(errs()<<"replace_newCI: "<<*newCI<<"\n");            
            for (auto User : Users){
                Instruction * iUser = dyn_cast<Instruction>(User); 
                //- iUser is BCI or CI's User -//
                assert(iUser);

                if (isa<CastInst>(iUser)) {

                    CastInst * BCI = cast<CastInst>(iUser); 
                    dbg(errs()<<"Orig_BCI: "<<Users.size()<<"\n";);
                    dbg(errs()<<"  #users: "<<Users.size()<<"\n";);

                    BCI->setOperand(0, newCI);
                    dbg(errs()<<"new_BCI : "<<Users.size()<<"\n";);
                    dbg(errs()<<"  #users: "<<Users.size()<<"\n";);
                    // change BCI's op

                    for (auto UserOfBCI = BCI->user_begin(); UserOfBCI!=BCI->user_end(); UserOfBCI++) { 
                        Instruction * iUserOfBCI = dyn_cast<Instruction>(*UserOfBCI);

                        int OpIdx = getOpIdx(iUserOfBCI, BCI);  
                        if (OpIdx < 0) continue;

                        // todo: change BCI's ptr operand to new hook
                        assert(iUserOfBCI->getOperand(OpIdx)->getType()==Ptr->getType()); 

                        // TODO: is this correct??? ************

                        // Replaced hook call, not setoperand.
                        //iUserOfBCI->setOperand(OpIdx, Ptr); 

                        dbg(errs()<<"- BCI's newUser:  "<<*iUserOfBCI<<"\n";)
                    }
                }
                else {
                    int OpIdx = getOpIdx(iUser, CI);  
                    dbg(errs()<<"- Else OldUser:  "<<*iUser<<"\n";)
                    assert(iUser->getOperand(OpIdx)->getType()==Ptr->getType()); 
                    
                    iUser->setOperand(OpIdx, CI);
                    dbg(errs()<<"- Else newUser:  "<<*iUser<<"\n";)
                }

                //insert_tovec(RedundantChks, (Instruction*)CI);
            } // end of for loop
        }

        bool hasZeroRedundantChks()
        {
            return RedundantChks.empty();
        }
        void eraseRedundantChks() 
        { 
            errs()<<"ERASE_size: "<<this->RedundantChks.size()<<"\n";
            for (unsigned i=0; i<this->RedundantChks.size(); i++) {
                Instruction * Redun = this->RedundantChks.at(i);
                dbg(errs()<<i<<"_ERASE: "<< *Redun <<"\n";); 
                Redun->eraseFromParent(); 
            }
            errs()<<"------ERASE_done\n";
        }
        
        void clearRedChks()
        {
            this->RedundantChks.clear();
        }

        virtual void collectAllocations ()
        {
            errs()<<"collectAllocations ---\n";
            
            //- globals -//
            Module * mod = F->getParent(); 
            for (auto GV = mod->global_begin(); GV!=mod->global_end(); GV++) {
                GlobalAllocs.insert(&*GV);
                errs()<<"GV: "<<*GV<<"\n";
            }
            for (auto & Ins : instructions(F)) {
                //- locals -//
                if (isa<AllocaInst>(&Ins)) {
                    Locals.insert(&Ins);  
                    errs()<<"Local: "<<Ins<<"\n";
                }
                //- heap -//
                //- TODO: this is for Miu. Add pm_alloc for spp -//
                else if (isa<CallInst>(&Ins)) { 
                    CallInst * CI = cast<CallInst>(&Ins);
                    Function * CalleeF = CI->getCalledFunction();
                    if (!CalleeF) continue;
                     
                    //- Heap -// 
                    if (isAllocationFn(CI, &TLIWP->getTLI(*CalleeF))) {
                        HeapAllocs.insert(&Ins);
                        errs()<<"Heap: "<<Ins<<"\n";
                    }
                }
            } 
        }
        
        virtual void derivePerRegion(std::unordered_set<Value*> & Ptrs) 
        {
            for (auto Ptr : Ptrs) {
              dbg(errs()<<"* Ptr: "<<*Ptr<<"\n");
              for (auto User = Ptr->user_begin(); User!=Ptr->user_end(); ++User) {
                // TODO: Just to check if replacement is correct. 
                // Refine later.
                // if the ptr operand (operand(0)) is untracked
                dbg(errs()<<"  -user: "<<*User<<"\n");
                if (isa<GetElementPtrInst>(*User)) {
                  dbg(errs()<<"   -> add_to_FNUntraked\n");
                  FNUntracked.insert(*User); 
                }
              }
            }
        }

        virtual void deriveUntrackedPtrs ()
        {
            errs()<<"\n--deriveUntrackedPtrs----\n";
            //- TODO: disable some of them for Miu
            derivePerRegion(Locals);
            derivePerRegion(GlobalAllocs);
            derivePerRegion(HeapAllocs);
        }
        
        virtual void deriveSafePtrs ()
        {
            // insert all allocs
            for (auto Ptr : FNUntracked) {
                FNSafePtrs.insert(Ptr);
            }
            // TODO: fill this. derive.
        }
        
        void addFNUntracked (Value * Ptr)
        {
            FNUntracked.insert((Ptr));
        }
        
        void addRedundantChks (Instruction * Ins)
        {
            errs()<<RedundantChks.size()<<"_AddRedundant: "<<*Ins<<"\n";
            insert_tovec(RedundantChks, Ins);
        }
        
        virtual bool isFNUntracked (Value * Ptr) 
        {
            if (has_elem_o (FNUntracked, Ptr)) {
                return true;
            }
            return false; 
        }

    }; 
    
    class ModInfoOptRMChks : public MiuProject::ModInfoOpt {
      
      protected:
       
        //FuncInfoRemRTChks * CurFuncInfo; 
        /*
        StringRef ChkBoundHookName = "";
        StringRef UpdatePtrHookName = "";
        StringRef UntagHookName = "";
        StringRef AllocHookName = "";
        */
        HookInfo * hookinfo = nullptr;

      public:  
        
        ModInfoOptRMChks (Module * M, StringRef & prefix) : MiuProject::ModInfoOpt (M, prefix) {} 
        virtual ~ModInfoOptRMChks() {}    
        
        virtual setHookInfo (StringRef & prefix)
        {
            HookInfo =  
        }

        //- Set hook funcs -//
        /*
        virtual void setChkBoundHookName (StringRef & Str) 
        {
            this->ChkBoundHookName = Str;
        }
        
        virtual void setUpdatePtrHookName (StringRef & Str) 
        {
            this->UpdatePtrHookName = Str;
        }
        
        virtual void setUntagHookName (StringRef & Str) 
        {
            this->UntagHookName = Str;
        }

        virtual void setAllocHookName (StringRef & Str) 
        {
            this->AllocHookName = Str;
        }
        virtual StringRef getUntagHookName ()
        {
            return this->UntagHookName;
        }
        
        //- check hook funcs -//
        virtual bool isCheckBoundHookName (StringRef & Str) 
        {
            if (Str.equals(this->ChkBoundHookName)) return true;
            return false;
        }
         
        virtual bool isUpdatePtrHookName (StringRef & Str) 
        {
            if (Str.equals(this->UpdatePtrHookName)) return true;
            return false;
        }
        
        virtual bool isUntagHookName (StringRef & Str) 
        {
            if (Str.equals(this->UntagHookName)) return true;
            return false;
        }

        virtual bool isAllocHookName (StringRef & Str) 
        {
            if (Str.equals(this->AllocHookName)) return true;
            return false;
        }
        
        //- check if it is call hook -// 
        virtual bool isCheckBoundCallHook (Instruction * Ins)
        {
            if (!isCallHook(Ins)) { return false; }
            StringRef HookName = cast<CallInst>(Ins)->getCalledFunction()->getName();
            if (isCheckBoundHookName(HookName)) { return true; }
            return false; 
        }
        virtual bool isUntagCallHook (Instruction * Ins)
        {
            if (!isCallHook(Ins)) { return false; }
            StringRef HookName = cast<CallInst>(Ins)->getCalledFunction()->getName();
            if (isUntagHookName(HookName)) { return true; }
            return false; 
        }
        
        virtual bool isUpdatePtrCallHook (Instruction * Ins)
        {
            if (!isCallHook(Ins)) { return false; }
            StringRef HookName = cast<CallInst>(Ins)->getCalledFunction()->getName();
            if (isUpdatePtrHookName(HookName)) { return true; }
            return false; 
        }
        */
        
        virtual bool isUntracked (Value * Val)
        {
            auto search = Untracked.find(Val);
            if (search != Untracked.end()) {
                return true;
            }
            return false;
        }


        //- modified: __isSafeAccess in Framer.h.   -// 
        //- Consider spacemiu repo.                 -//
       /* virtual bool isInboundPtr (Value * Ptr) 
        {
            CallInst * ci= __isAllocation(gep->getPointerOperand(), M, gep); 
            //ci is hook_alloca,hook_gv, or malloc call
            if (ci==nullptr) {
                return NOTSAFESTATICALLY; 
            }
            if (gep->hasAllZeroIndices()) { // base addr of alloca/gv
                return SAFESTATICALLY; 
            }
            // ***** malloc s ***   
            if (ci->getCalledFunction()->getName().equals("malloc")) {
                return handleMallocStaticBounds(gep, ci, isMemAccess, M); 
            }
            // ***** malloc e ***

            if (!isa<ConstantInt>(gep->getOperand(1)->stripPointerCasts())){
                return NOTSAFESTATICALLY; // issafeaccess==0. 
            }
            if (!((cast<ConstantInt>(gep->getOperand(1)->stripPointerCasts()))->equalsInt(0))) {
                return NOTSAFESTATICALLY; 
            }
            if (!gep->hasAllConstantIndices()) {
                if (gep->getNumIndices()<=2) {
                    return COMPAREIDXATRUNTIME; // issafeaccess==2. requiring runtime check 
                } 
                else {
                    return NOTSAFESTATICALLY;
                } 
            }
            // offset= base~ptr (two args. 2nd is gep's ptr.assignment)
            unsigned offset= getStaticOffset(gep, &M.getDataLayout()); 
            unsigned totalsize= getmysize(ci);
            unsigned sizeToAccess= FramerGetBitwidth(cast<PointerType>(gep->getType())->getElementType(), &M.getDataLayout())/8;

            return isStaticInBound(offset, 
                    sizeToAccess,
                    totalsize,
                    isMemAccess);  

        }
        */

        virtual bool optGEPHooks (FuncInfoRemRTChks * FI) 
        {
            bool changed = false;
            Function * F = FI->getFunction();

            for (auto & Ins : instructions(F)) {

                if (!isUpdatePtrCallHook (&Ins)) {  continue; } 

                CallInst * CI = cast<CallInst>(&Ins);

                dbg(errs()<<"\nUpdateTagHook: "<<*CI<<"\n";);

                unsigned PtrIdx = 0; 
                Value * Op = CI->getOperand (PtrIdx);
                Value * Ptr = Op->stripPointerCasts();
                dbg(errs()<<"Stripped_Ptr:  "<<*Ptr<<"\n";);

                // TODO: this is SPP-specific.
                if (!Ptr) {
                    FI->addFNUntracked(Ptr);
                }
                // if the pointer operand is tag-free. 
                if (isUntracked(Ptr) || FI->isFNUntracked (Ptr)) {
                    
                    dbg(errs()<<"-> Strip: Untracked or Locals.\n";);
                    FI->stripHook(CI, Ptr);
                } 
                else {;}

            } // end of for

            if (!FI->hasZeroRedundantChks()) {
                changed |= true;
                FI->eraseRedundantChks(); 
            }
            
            FI->clearRedChks();

            return changed;
        }
        
        // MemAccess Opt. Pre-LTO  
        virtual bool optMemAccessHooks (FuncInfoRemRTChks * FI)
        {
            assert(FI->hasZeroRedundantChks());
            Function * F = FI->getFunction();
            
            bool changed = false;

            for (auto & Ins : instructions(F)) {

                if (!isCheckBoundCallHook(&Ins)) { continue; }
                CallInst * CI = cast<CallInst>(&Ins);

                dbg(errs()<<"\n-- isCheckBoundCallHook_ins: "<<*CI<<" -------- \n";);
                unsigned PtrIdx = 0; 
                Value * Op = CI->getOperand (PtrIdx);
                Value * Ptr = dyn_cast<Instruction>(Op->stripPointerCasts());
                
                dbg(errs()<<"bound_Ptr:  "<<*Ptr<<"\n";);
                
                // TODO: perform this during initializing vector
                // TODO: Important!: this is only for SPP
                if (!Ptr) {      
                    FI->addFNUntracked(Ptr);
                }
                dbg(errs()<<"   -> not_inst(spp_only!) "<<*Ptr<<"\n";);
                 
                if (isUntracked(Ptr) || FI->isFNUntracked(Ptr)) {

                    dbg(errs()<<"-> Untracked_ptr. Strip.\n";);
                    FI->stripHook(CI, Ptr);

                }   
                //else if (isSafePtr(Ptr) || isSafeAccess(Ptr)) {
                else if (isSafePtr(Ptr)) {
                    dbg(errs()<<"-> safe_ptr. Replace.\n";);
                    FunctionCallee Rep;
                    StringRef TmpName= getUntagHookName(); 
                    dbg(errs()<<"Hook_name: "<<TmpName<<"\n");
                    bool GotProto= getHookProto(Rep, TmpName);
                    assert(GotProto);
                    FI->replaceHook(CI, Rep, PtrIdx);
                }
                else {;}
            } // end of for loop
            
            // TODO: check if hook calls are folded (combined).
            if (!FI->hasZeroRedundantChks()) { 
                changed |= true;
                FI->eraseRedundantChks(); 
            }
            return changed;
        }

        virtual bool optExtCallHooks (FuncInfoRemRTChks * FI)
        {
            assert(FI->hasZeroRedundantChks());
            Function * F = FI->getFunction();
            
            bool changed = false;

            for (auto & Ins : instructions(F)) {
                
                if (!isUntagCallHook(&Ins)) { continue; }

                CallInst * CI = cast<CallInst>(&Ins);
                dbg(errs()<<"\nUntagHook: "<<*CI<<"\n";);

                unsigned PtrIdx = 0; 

                Value * Op = CI->getOperand (PtrIdx);
                Value * Ptr = dyn_cast<Instruction>(Op->stripPointerCasts());
                
                dbg(errs()<<"Ptr:  "<<*Ptr<<"\n";);

                if (!Ptr) {
                    FI->addFNUntracked(Ptr);
                }
                if (isUntracked(Ptr) || FI->isFNUntracked(Ptr)) {
                    // strip 
                    dbg(errs()<<"-> Strip:: Untracked or Locals\n";);
                    std::vector<User*> Users(CI->user_begin(), CI->user_end());

                    for (auto User : Users){
                        Instruction * iUser = dyn_cast<Instruction>(User); 
                        //- iUser is BCI or CI's User -//
                        if (isa<CastInst>(iUser)) {
                            CastInst * BCI = cast<CastInst>(iUser);
                            assert(BCI->hasOneUser()); //- Miu-specific implementation
                            Instruction * UserOfBCI = dyn_cast<Instruction>(*(BCI->user_begin()));
                            int OpIdx = getOpIdx(UserOfBCI, BCI);  
                            if (OpIdx < 0) { continue; }

                            if (UserOfBCI->getOperand(OpIdx)->getType() != Ptr->getType()) {
                                IRBuilder<> B(UserOfBCI);
                                Value * newBCI= B.CreateBitCast(Ptr, UserOfBCI->getOperand(OpIdx)->getType()); 
                                UserOfBCI->setOperand(OpIdx, newBCI);; 
                            }
                            else {
                                UserOfBCI->setOperand(OpIdx, Ptr);; 
                            }
                            FI->addRedundantChks((Instruction*)BCI); 
                        }
                        else {
                            int OpIdx = getOpIdx(iUser, CI);  
                            assert(iUser->getOperand(OpIdx)->getType()==Ptr->getType()); 
                            iUser->setOperand(OpIdx, Ptr);
                        }
                        FI->addRedundantChks((Instruction*)CI);
                    } // end of for loop
                }   // end of if
            } // end of for loop
            
            // TODO: check if hook calls are folded (combined).
            if (!FI->hasZeroRedundantChks()) { 
                changed |= true;
                FI->eraseRedundantChks(); 
            }
            return changed;
        }
    }; // end of class
    
    /* 
    void ModInfoOptRMChks::initialiseUntracked ()
    {
        // for SPP, untrack Locals
        // for SPP, untrack Globals 
        //std::vector<GlobalVariable*> GVs(M->global_begin(), M->global_end());
        for (auto & GV : M->globals()) {
           Untracked.insert(&GV); 
        }
    }
    */

    class Remove_RTChks : public ModulePass {

      public:
        static char ID;

        Remove_RTChks() : ModulePass(ID) {}
        
        void getAnalysisUsage(AnalysisUsage &AU) const override{

            AU.addRequired<DominatorTreeWrapperPass>();
            AU.addRequired<AAResultsWrapperPass>(); 
            AU.addRequired<CallGraphWrapperPass>(); 
            AU.addRequired<TargetLibraryInfoWrapperPass>();
        }

        virtual bool runOnModule(Module& M) {
            
            StringRef ModName = M.getModuleIdentifier(); 
            StringRef SrcFileName = ModName.substr(ModName.rfind('/')); 

            errs() <<"\n-----------------------------------------\n";
            errs() <<">> RemoveCHKS_BB:: " << SrcFileName <<"\n";
            
            bool Changed = false;
            
            //-  ModInfoType instance creating -//
            
            StringRef HookPrefix= "MIU_";
            
            // TODO: Separate HookInfo from ModInfo 
            ModInfoOptRMChks MiuMod(&M, HookPrefix);
            
            //-  TLI setting   -//
            // TODO: redundant? Trim initialising 
            auto GetTLI = [this](Function &F) -> TargetLibraryInfo & {
                return this->getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(F);
            };
            TargetLibraryInfoWrapperPass *TLIWP 
                = &getAnalysis<TargetLibraryInfoWrapperPass>();

            MiuMod.setTLI(GetTLI);
            
            ModInfoOptRMChks MiuMod(&M, HookPrefix);
            
            //TODO: Clean the code (replace above with following_
            MiuMod.initialiseModInfo(GetTLI);
            
            //-  Set hook names  -//
            StringRef ChkBoundHookName = "MIU_checkbound";
            StringRef UpdatePtrHookName = "MIU_updatetag";
            StringRef UntagHookName = "MIU_cleantag";
            StringRef AllocHookName = "MIU_instr_heap_alloc";

            MiuMod.setChkBoundHookName(ChkBoundHookName);
            MiuMod.setUpdatePtrHookName(UpdatePtrHookName);
            MiuMod.setUntagHookName(UntagHookName);
            MiuMod.setAllocHookName(AllocHookName);
            
            // TODO: 
            //MiuMod.initialiseUntracked ();
    
            //Track the external functions first &
            //Track the pointers derived from pmemobj_direct_inline
            
            //- Running on Function -//  
            for (auto F = M.begin(); F != M.end(); ++F) {
                
                errs() << "\n> FN :: "<<F->getName()<<".............\n"; 
                if (MiuMod.isIgnoreFunction(&*F)) { 
                    dbg(errs()<<"skip\n";)
                    continue;
                }
                 
                FuncInfoRemRTChks * FInfo = new FuncInfoRemRTChks(&*F);
                
                FInfo->setTLIWP(TLIWP);
                
                // TODO: Modify collectAllocations for spp
                FInfo->collectAllocations(); 
                
                // TODO: Modify deriveUntrackedPtrs for spp
                FInfo->deriveUntrackedPtrs();
                
                FInfo->deriveSafePtrs();
                 
                Changed |= MiuMod.optGEPHooks (FInfo);
                
                errs() << "optGEPHooks_done\n"; 

                Changed |= MiuMod.optMemAccessHooks (FInfo);              
                errs()<<"optMemAccess_done\n"; 
                
                delete FInfo;

                // TODO: update mod-level opt information (#removed_checks)
            }
           
            // TODO: if this runs as a non-LTO, creating RT TypeTables is necessary?
            // TODO: MAKE SURE that following Miupass does NOT intrument these GVs.  
            
            // TODO!! modify test src (put more structure types) 

            //- Main function instrumentation (prologue etc)  -// 
            dbg(errs()<<"\n";)

            //Changed |= MiuMod.instrMainFunction();
            errs() << "> Exiting RemoveCHKS_BB_Pass .......\n";
            
            return Changed;
        }
        
    };  // end of Remove_RTChks class

    char Remove_RTChks::ID = 0;
    
    static RegisterPass<Remove_RTChks> X("remove_rtchks", "Remove_RTChks Pass 1", false, false);

    static void registerPass(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
        PM.add(new Remove_RTChks());
    }
    //apply the module pass at this phase because EarlyAsPossible can cause UB
    static RegisterStandardPasses
    //RegisterMyPass(PassManagerBuilder::EP_ModuleOptimizerEarly,
    RegisterMyPass(PassManagerBuilder::EP_ScalarOptimizerLate,
                   registerPass);

    //to keep the pass available even in -O0
    static RegisterStandardPasses
    RegisterMyPass_non_opt(PassManagerBuilder::EP_EnabledOnOptLevel0,
                   registerPass);

} // endof anonymous namespace



