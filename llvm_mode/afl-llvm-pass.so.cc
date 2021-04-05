/*
   american fuzzy lop++ - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   Copyright 2015, 2016 Google Inc. All rights reserved.
   Copyright 2019-2020 AFLplusplus Project. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.

 */

#define AFL_LLVM_PASS

#include "config.h"
#include "debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <list>
#include <string>
#include <fstream>
#include <sys/time.h>

#include "llvm/Config/llvm-config.h"
#if LLVM_VERSION_MAJOR == 3 && LLVM_VERSION_MINOR < 5
typedef long double max_align_t;
#endif

#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#if LLVM_VERSION_MAJOR > 3 || \
    (LLVM_VERSION_MAJOR == 3 && LLVM_VERSION_MINOR > 4)
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/CFG.h"
#else
#include "llvm/DebugInfo.h"
#include "llvm/Support/CFG.h"
#endif

using namespace llvm;

namespace {

class AFLCoverage : public ModulePass {

 public:
  static char ID;
  AFLCoverage() : ModulePass(ID) {

    char *instWhiteListFilename = getenv("AFL_LLVM_WHITELIST");
    if (instWhiteListFilename) {

      std::string   line;
      std::ifstream fileStream;
      fileStream.open(instWhiteListFilename);
      if (!fileStream) report_fatal_error("Unable to open AFL_LLVM_WHITELIST");
      getline(fileStream, line);
      while (fileStream) {

        myWhitelist.push_back(line);
        getline(fileStream, line);

      }

    }

  }

  // ripped from aflgo
  static bool isBlacklisted(const Function *F) {

    static const char *Blacklist[] = {

        "asan.",
        "llvm.",
        "sancov.",
        "__ubsan_handle_",

    };

    for (auto const &BlacklistFunc : Blacklist) {

      if (F->getName().startswith(BlacklistFunc)) { return true; }

    }

    return false;

  }

  bool runOnModule(Module &M) override;

  // StringRef getPassName() const override {

  //  return "American Fuzzy Lop Instrumentation";
  // }

 protected:
  std::list<std::string> myWhitelist;

};

}  // namespace

char AFLCoverage::ID = 0;

bool AFLCoverage::runOnModule(Module &M) {
  LLVMContext &C = M.getContext();

  IntegerType *   Int8Ty = IntegerType::getInt8Ty(C);
  IntegerType *   Int32Ty = IntegerType::getInt32Ty(C);
  struct timeval  tv;
  struct timezone tz;
  u32             rand_seed;

  /* Setup random() so we get Actually Random(TM) outputs from AFL_R() */
  gettimeofday(&tv, &tz);
  rand_seed = tv.tv_sec ^ tv.tv_usec ^ getpid();
  AFL_SR(rand_seed);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass" VERSION cRST " by <lszekeres@google.com>\n");

  } else if (getenv("AFL_QUIET"))

    be_quiet = 1;

  /* Decide instrumentation ratio */

  char *       inst_ratio_str = getenv("AFL_INST_RATIO");
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

  GlobalVariable *AFLIdxPtr =
        new GlobalVariable(M, PointerType::get(Int32Ty, 0), false,
                           GlobalValue::ExternalLinkage, 0, "__afl_idx_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc", 0,
      GlobalVariable::GeneralDynamicTLSModel, 0, false);

  //ConstantInt *zero8 = ConstantInt::get(Int8Ty, 0);
  //ConstantInt *one8 = ConstantInt::get(Int8Ty, 1);
  //ConstantInt *one32 = ConstantInt::get(Int32Ty, 1);
  //ConstantInt *minusOne = ConstantInt::get(Int32Ty, -1);

  /* Instrument all the things! */

  int inst_blocks = 0;

  for (auto &F : M){
  		std::vector<BasicBlock::iterator> ips;
  		for(auto &bb : F){
  			ips.push_back(bb.getFirstInsertionPt());
  		}

  		for (auto &IP : ips) {

  			//BasicBlock::iterator IP = BB.getFirstInsertionPt();
  			//Instruction * firstInstOrig = &(*IP);
  			IRBuilder<> IRB(&(*IP));

  			if (AFL_R(100) >= inst_ratio)
  				continue;

  			/* Make up cur_loc */

  			unsigned int cur_loc = AFL_R(MAP_SIZE);
  			while((cur_loc ^ (cur_loc >> 1)) == 0){
  				cur_loc = AFL_R(MAP_SIZE);
  			}

  			ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

  			/* Load prev_loc */
  			LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
  			PrevLoc->setMetadata(M.getMDKindID("nosanitize"),
  					MDNode::get(C, None));
  			Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

  			/*load idx*/
  			LoadInst *IdxPtr = IRB.CreateLoad(AFLIdxPtr);
  			IdxPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
  			Value *idxAddr = IRB.CreateGEP(Int32Ty, IdxPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

  			//load index value
  			LoadInst* idxVal = IRB.CreateLoad(idxAddr);
  			idxVal->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

  			//check if index value is -1
  			Value* cond = IRB.CreateICmpEQ(ConstantInt::get(Int32Ty, -1), idxVal);

  			//create then block
  			Instruction* then = SplitBlockAndInsertIfThen(cond, &(*IP), false, MDBuilder(C).createBranchWeights(1, 100000));
  			assert(dyn_cast<BranchInst>(then)->isUnconditional());

  			//instrument then block
  			IRB.SetInsertPoint(then);
  			LoadInst* cntVal = IRB.CreateLoad(IdxPtr);
  			cntVal->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
  			IRB.CreateStore(cntVal, idxAddr)->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
  			IRB.CreateStore(IRB.CreateAdd(cntVal, ConstantInt::get(Int32Ty, 1)), IdxPtr)->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));


  			//instrument tail
  			IRB.SetInsertPoint(&(*IP));
  			PHINode* idx = IRB.CreatePHI(Int32Ty, 2);
  			idx->addIncoming(idxVal, idxVal->getParent());
  			idx->addIncoming(cntVal, cntVal->getParent());

  			LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
  			MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
  			Value *mapAddr = IRB.CreateGEP(Int8Ty, MapPtr, idx);

  			LoadInst *mapVal = IRB.CreateLoad(mapAddr);
  			mapVal->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
  			IRB.CreateStore(IRB.CreateAdd(mapVal, ConstantInt::get(Int8Ty, 1)), mapAddr)->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

  			/* Set prev_loc to cur_loc >> 1 */
  			IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc)->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

  			inst_blocks++;

  		}
  	}

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks)
      WARNF("No instrumentation targets found.");
    else
      OKF("Instrumented %u locations (%s mode, ratio %u%%).", inst_blocks,
          getenv("AFL_HARDEN")
              ? "hardened"
              : ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN"))
                     ? "ASAN/MSAN"
                     : "non-hardened"),
          inst_ratio);

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

