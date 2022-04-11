//===-----  RemoveRTChks/RemoveRTChks.cpp - Transformation pass -----===//
//===-----  Copyright © March 2022 by Myoung Jin Nam            -----===//
//===-----  myoungjin.nam@gmail.com, mjn31@cantab.ac.uk         -----===//

#define DEBUG_TYPE "remove_rtchks"

/* MiuProject-related */
// TODO: make it self-contained under the branch
#include "./ModInfoOpt.h"
#include "./FuncInfoAbstract.h"
#include "./HookInfoAbstract.h"

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
using namespace SelfContainedMiuProject;
    
namespace {
    
    template < typename T>
    static bool has_elem_o (unordered_set<T> & OST, T elem)
    {
        auto it= OST.find(elem);
        if (it != OST.end()) {
            return true;       
        }
        return false;
    }

    class HookInfoMiu : public SelfContainedMiuProject::HookInfoAbstract {
      
      protected: 
        
        StringRef ChkBoundHookName = "";
        StringRef UpdatePtrHookName = "";
        StringRef UntagHookName = "";
        StringRef AllocHookName = "";
        //- spp-specific. -//
        StringRef PMAllocFuncName = "";

      public: 
        //- constructor, destructor -//
        HookInfoMiu (StringRef & prefix, Module * mod) : SelfContainedMiuProject::HookInfoAbstract (prefix, mod) 
        {
            this->ChkBoundHookName = "MIU_checkbound";
            this->UpdatePtrHookName = "MIU_updatetag";
            this->UntagHookName = "MIU_cleantag";
            this->AllocHookName = "MIU_instr_heap_alloc";
            //- TODO: Handle name mangling. Should I move this to modinfo? 
            this->PMAllocFuncName = "pmemobj_direct_inline";
            
            //assert(ChkBoundHookName.startswith(Prefix));
            //assert(UpdatePtrHookName.startswith(Prefix));
            //assert(UntagHookName.startswith(Prefix));
            //assert(AllocHookName.startswith(Prefix));
        } 
        
        virtual ~HookInfoMiu() {
            errs()<<">> free_HookInfoMiu\n";
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
        
        virtual bool isAllocHookFunc (Function * Fn) 
        {
            StringRef Fname = Fn->getName();
            if (isAllocHookName(Fname)) return true;
            return false;
        }
        
        virtual bool isAllocCallHook (Instruction * Ins)
        {
            if (!isCallHook(Ins)) { return false; }
            StringRef HookName = cast<CallInst>(Ins)->getCalledFunction()->getName();
            if (isCheckBoundHookName(HookName)) { return true; }
            return false; 
        }
        
        bool isPMAllocFuncName (StringRef & Str) 
        {
            //- TODO: name mangling -//
            if (Str.equals(this->PMAllocFuncName)) return true;
            return false;
        }
        
        bool isPMAllocFunc (Function * Fn) 
        {
            StringRef Fname = Fn->getName();
            if (isPMAllocFuncName(Fname)) return true;
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
        
        virtual bool getHookProto_Untag (FunctionCallee & Hook)
        {
            Type* VoidPTy= Type::getInt8PtrTy(*CXT);
            std::vector <Type*> ParamTypes = {VoidPTy};
            FunctionType * FTY= FunctionType::get(VoidPTy, ParamTypes, false);
            Hook = M->getOrInsertFunction(this->UntagHookName, FTY); 
            
            return true; 
        }
        //- modified: __isSafeAccess in Framer.h.   -// 
        //- Consider spacemiu repo.                 -//
    
    };

    class FuncInfoRemRTChks : public SelfContainedMiuProject::FuncInfoAbstract {

      protected:
        
        //- merging into one 
        
        std::unordered_set <Value*> TagFreePtrs;
        std::unordered_set <Value*> SafePtrs;
        
        std::queue <Vallue*> PtrQ;
        
        std::vector<Instruction*> RedundantChks;
      
      public:
        
        //- constructor, destructor -//
        FuncInfoRemRTChks (Function * F) : SelfContainedMiuProject::FuncInfoAbstract (F) 
        {
            this->F = F;
        } 
        virtual ~FuncInfoRemRTChks() {}    
        
        virtual Function * getFunction () 
        {
            return this->F;
        }

        // TODO: Make these set to protected and create member funcs to manipulate.  
        std::unordered_set <Value*> GlobalAllocs;
        std::unordered_set <Value*> Locals;
        std::unordered_set <Value*> HeapAllocs;
        
        // Accumulate SafePtrs. Or delete this func..
        virtual bool isSafePtr (Value * Ptr)
        {
            Value * RawPtr = Ptr->stripPointerCasts();
            return has_elem_o (SafePtrs, RawPtr);
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
                        //assert(iUserOfBCI->getOperand(OpIdx)->getType()==Ptr->getType()); 

                        // TODO: is this correct??? ************
                        // Replaced hook call, not setoperand.
                        iUserOfBCI->setOperand(OpIdx, newCI); 

                        dbg(errs()<<"- BCI's newiUser:  "<<*iUserOfBCI<<"\n";)
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

        virtual bool initTagFreePtrs ()
        {
            //- TODO: disable some of them for Miu
            
            //- Locals are tag-free: spp-specific -// 
            for (auto Ptr : Locals) {
                PtrQ.push(Ptr); 
            }
            //- volatile heap allocs are tag-free: spp-specific -// 
            for (auto Ptr : HeapAllocs) {
                PtrQ.push(Ptr); 
            }
            //- GVs are tag-free: spp-specific -// 
            for (auto Ptr : GlobalAllocs) {
                PtrQ.push(Ptr); 
            } 
              
            return !(PtrQ.empty()); 
        }

        virtual void deriveTagFreePtrs ()
        {
            //- while iterating on queue, add to tagfreeptrs set. -//

            while (!PtrQ.empty()) {
                
                Value * Ptr = PtrQ.front(); 
                PtrQ.pop();
                TagFreePtrs.insert(Ptr);
                
                errs()<<"\nTagFreePtr: "<<*Ptr<<"  ----- \n";
                // TODO: confusing. should strip or not?
                // Value * Ptr = Elem->stripPointerCasts(); 

                for (auto User = Ptr->user_begin(); User!=Ptr->user_end(); ++User) {
                    dbg(errs()<<"  Usr: "<<**User<<"\n");
                    // TODO: Just to check if replacement is correct. 
                    // Refine later.
                    if (isa<UnaryInstruction>(*User)){
                        errs()<<"  --> 1. UnaryInstruction\n"; 
                        //TagFreePtrs.insert(*User);
                        PtrQ.push(*User);
                    }
                    else if (isa<GEPOperator>(*User)) {
                        Value * GepOpPtrVal = cast<GEPOperator>(*User)->getPointerOperand();
                        //- if the ptr operand (operand(0)) is TagFree -// 
                        if (Ptr == GepOpPtrVal->stripPointerCasts()) { 
                            errs()<<"  --> 2. ptr_is_GEP's ptrval\n";
                            //TagFreePtrs.insert(*User);
                            PtrQ.push(*User);
                        }
                    }
                    else {
                        errs()<<"  --> 3. else\n";
                    }
                }
            } 
            /*
            for (auto Elem : TagFreePtrs) {
                
                Value * Ptr = Elem->stripPointerCasts();
                 
                errs()<<"\nTagFreePtr: "<<*Ptr<<"  ----- \n";
                for (auto User = Ptr->user_begin(); User!=Ptr->user_end(); ++User) {
                    dbg(errs()<<"  Usr: "<<**User<<"\n");
                    // TODO: Just to check if replacement is correct. 
                    // Refine later.
                    if (isa<UnaryInstruction>(*User)){
                        errs()<<"    -> 1. UnaryInstruction\n"; 
                        TagFreePtrs.insert(*User);
                    }
                    else if (isa<GEPOperator>(*User)) {
                        Value * GepOpPtrVal = cast<GEPOperator>(*User)->getPointerOperand();
                        //- if the ptr operand (operand(0)) is TagFree -// 
                        if (Ptr == GepOpPtrVal->stripPointerCasts()) { 
                            errs()<<"    -> 2. ptr_is_GEP's ptrval\n";
                            TagFreePtrs.insert(*User);
                        }
                    }
                    else {
                        errs()<<"    -> 3_else\n";
                    }
                }
            } 
            */
            // TODO: DT
            // TODO: points-to  
        }
        
        virtual void deriveSafePtrs ()
        {
            // insert all allocs
            for (auto Ptr : TagFreePtrs) {
                SafePtrs.insert(Ptr);
            }
            // TODO: fill this. derive.
        }
        
        void addTagFreePtr (Value * Ptr)
        {
            TagFreePtrs.insert((Ptr));
        }
        
        void addRedundantChks (Instruction * Ins)
        {
            errs()<<RedundantChks.size()<<"_AddRedundant: "<<*Ins<<"\n";
            insert_tovec(RedundantChks, Ins);
        }
        
        virtual bool isTagFreePtr (Value * Ptr) 
        {
            if (has_elem_o (TagFreePtrs, Ptr)) {
                return true;
            }
            return false; 
        }

    }; 
    
    class ModInfoOptRMChks : public SelfContainedMiuProject::ModInfoOpt {
      
      protected:
        
        HookInfoMiu * hookinfo = nullptr;
       
      public:  
        
        ModInfoOptRMChks (Module * M, StringRef & prefix, HookInfoMiu * Hookinfo) : SelfContainedMiuProject::ModInfoOpt (M, prefix) 
        {
            this->M = M;
            this->CXT = &(M->getContext());
            this->DL = &(M->getDataLayout());
            this->Prefix = prefix;
            this->hookinfo = Hookinfo;  
            assert(!this->Prefix.empty());    
            assert(this->M);    
        } 
        virtual ~ModInfoOptRMChks() {}    
        
        HookInfoMiu * getHookInfo()
        {
            return this->hookinfo; 
        }
        
        virtual bool isUntracked (Value * Val)
        {
            auto search = Untracked.find(Val);
            if (search != Untracked.end()) {
                return true;
            }
            return false;
        }
        
        virtual void collectAllocations (FuncInfoRemRTChks * FInfo)
        {
            errs()<<"collectAllocations ---\n";
            Function * Fn = FInfo->getFunction();

            //- globals -//
            for (auto GV = M->global_begin(); GV!=M->global_end(); GV++) {
                FInfo->GlobalAllocs.insert(&*GV);
                errs()<<"GV: "<<*GV<<"\n";
            }
            for (auto & Ins : instructions(Fn)) {
                //- locals -//
                if (isa<AllocaInst>(&Ins)) {
                    FInfo->Locals.insert(&Ins);  
                    errs()<<"Local: "<<Ins<<"\n";
                }
                //- heap -//
                //- TODO: this is for Miu. Add pm_alloc for spp -//
                else if (isa<CallInst>(&Ins)) { 
                    CallInst * CI = cast<CallInst>(&Ins);
                    Function * CalleeF = CI->getCalledFunction();
                    if (!CalleeF) continue;
                     
                    //- Volatile Heap -// 
                    if (isAllocationFn(CI, FInfo->getTLI(*CalleeF))) {
                        FInfo->HeapAllocs.insert(&Ins);
                        errs()<<"Heap: "<<Ins<<"\n";
                    }
                    //- spp-specific -//
                    else if (getHookInfo()->isPMAllocFunc(CalleeF)) {
                        FInfo->HeapAllocs.insert(&Ins);
                        errs()<<"Heap: "<<Ins<<"\n";
                    }
                    else {;}
                }
            } 
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

            for (auto & Ins : instructions(FI->getFunction())) {

                if (!getHookInfo()->isUpdatePtrCallHook (&Ins)) {  continue; } 

                CallInst * CI = cast<CallInst>(&Ins);

                dbg(errs()<<"\nUpdateTagHook: "<<*CI<<"\n";);

                unsigned PtrIdx = 0; 
                Value * Op = CI->getOperand (PtrIdx);
                Value * Ptr = Op->stripPointerCasts();
                dbg(errs()<<"Stripped_Ptr:  "<<*Ptr<<"\n";);

                // TODO: this is SPP-specific.
                if (!Ptr) {
                    FI->addTagFreePtr(Ptr);
                }
                // if the pointer operand is tag-free. 
                if (FI->isTagFreePtr (Ptr)) {
                    
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
            bool changed = false;

            for (auto & Ins : instructions(FI->getFunction())) {

                if (!getHookInfo()->isCheckBoundCallHook(&Ins)) { continue; }
                CallInst * CI = cast<CallInst>(&Ins);

                dbg(errs()<<"\n-- isCheckBoundCallHook_ins: "<<*CI<<" -------- \n";);
                unsigned PtrIdx = 0; 
                Value * Op = CI->getOperand (PtrIdx);
                Value * Ptr = dyn_cast<Instruction>(Op->stripPointerCasts());
                
                dbg(errs()<<"bound_Ptr:  "<<*Ptr<<"\n";);
                
                // TODO: perform this during initializing vector
                // TODO: Important!: this is only for SPP
                if (!Ptr) {      
                    FI->addTagFreePtr(Ptr);
                    dbg(errs()<<"   -> not_inst. Addto_Un_tracked. (spp_only!) "<<*Ptr<<"\n";);
                }
                if (isUntracked(Ptr) || FI->isTagFreePtr(Ptr)) {
                    dbg(errs()<<"-> Untracked_ptr. Strip.\n";);
                    FI->stripHook(CI, Ptr);
                }   
                //else if (isSafePtr(Ptr) || isSafeAccess(Ptr)) {
                else if (isSafePtr(Ptr)) {
                    dbg(errs()<<"-> safe_ptr. Replace.\n";);
                    FunctionCallee Rep;
                    StringRef TmpName= getHookInfo()->getUntagHookName(); 
                    dbg(errs()<<"new_Hook: "<<TmpName<<"\n");
                    bool GotProto= getHookInfo()->getHookProto_Untag(Rep);
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
            
            bool changed = false;

            for (auto & Ins : instructions(FI->getFunction())) {
                
                if (!getHookInfo()->isUntagCallHook(&Ins)) { continue; }

                CallInst * CI = cast<CallInst>(&Ins);
                dbg(errs()<<"\nUntagHook: "<<*CI<<"\n";);

                unsigned PtrIdx = 0; 

                Value * Op = CI->getOperand (PtrIdx);
                Value * Ptr = dyn_cast<Instruction>(Op->stripPointerCasts());
                
                dbg(errs()<<"Ptr:  "<<*Ptr<<"\n";);

                if (!Ptr) {
                    FI->addTagFreePtr(Ptr);
                }
                if (isUntracked(Ptr) || FI->isTagFreePtr(Ptr)) {
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
            
            bool Changed = false;
            
            StringRef ModName = M.getModuleIdentifier(); 
            StringRef SrcFileName = ModName.substr(ModName.rfind('/')); 

            errs() <<"\n-----------------------------------------\n";
            errs() <<">> RemoveCHKS_BB:: " << SrcFileName <<"\n";
            
            //- "Hook"InfoMiu creation-// 
            StringRef HookPrefix= "MIU_";
            HookInfoMiu hookinfo(HookPrefix, &M);  
            
            //-  "Mod"Info instance creatiion -//
            ModInfoOptRMChks MiuMod (&M, HookPrefix, &hookinfo);

            //-  TLI setting   -//
            // TODO: redundant? Trim initialising 
            /*auto GetTLI = [this](Function &F) -> TargetLibraryInfo & {
                return this->getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(F);
            };
            MiuMod.setTLI(GetTLI);
            //TODO: Clean the code (replace above with following_
            //MiuMod.initialiseModInfo(GetTLI);
            */

            TargetLibraryInfoWrapperPass *TLIWP 
                = &getAnalysis<TargetLibraryInfoWrapperPass>();

            // TODO: !!! DO! 
            //MiuMod.initialiseUntracked ();
    
            //Track the external functions first &
            //Track the pointers derived from pmemobj_direct_inline
            
            //- Running on Function -//  
            for (auto F = M.begin(); F != M.end(); ++F) {
                // TODO: No setting for IgnoreFunctions. Do something?
                // e.g. spp branch: pmem-specific functions

                errs() << "\n> FN :: "<<F->getName()<<".............\n"; 
                // TODO: make isIgnoreFunction a modulepass' member func.
                if (MiuMod.isIgnoreFunction(&*F)) { 
                    dbg(errs()<<"skip\n";)
                    continue;
                }
                
                //- FuncInto instance creation -//
                FuncInfoRemRTChks FInfo (&*F);
                FInfo.setTLIWP(TLIWP);
                
                // TODO: Modify collectAllocations for spp
                MiuMod.collectAllocations(&FInfo); 
                
                //- Change this func for SPP -// 
                // TODO: Modify deriveTagFreePtrs for spp
                bool hasTagFreePtrs = FInfo.initTagFreePtrs ();
                if (hasTagFreePtrs) { 
                    FInfo.deriveTagFreePtrs(); 
                }
                else { 
                    errs() <<"Warning: No_tag_free_ptrs\n"; 
                }
                
                // TODO: Modify deriveTagFreePtrs for spp
                FInfo.deriveSafePtrs();
                 
                Changed |= MiuMod.optGEPHooks (&FInfo);
                Changed |= MiuMod.optMemAccessHooks (&FInfo);              
                
                // TODO: update mod-level opt information (#removed_checks)
            }
           
            dbg(errs()<<"\n";)
            errs() << "\n> Exiting_RemoveCHKS_Pass .......\n";
            
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



