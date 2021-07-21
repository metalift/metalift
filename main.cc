#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorOr.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IRReader/IRReader.h"

#include "ir.h"

using namespace llvm;
using namespace metalift;

static cl::opt<std::string> FileName(cl::Positional, cl::desc("Bitcode file"), cl::Required);

struct Context
{
  std::map<const std::string, Expr *> memory;

};


void computeVC (const BasicBlock &bb) 
{
  outs() << "Basic block (name=" << bb.getName() << ") has " << bb.size() << " instructions.\n";

const Instruction * qq = NULL;  
  for (const Instruction &inst : bb) 
  {
    outs() << "instr: " << inst <<"\n";
    
    if (const AllocaInst * i = dyn_cast<AllocaInst>(&inst)) 
    {
      outs() << "name: " << i->getName() << "\n";
      if (qq == NULL)
      {
        qq = i;
        outs() << "assign\n";
      }
    } 
    else if (const StoreInst * i = dyn_cast<StoreInst>(&inst)) {
      outs() << "val: " << *(i->getPointerOperand()) << "\n";
      if (qq) {
        outs() << "1: " << *(i->getPointerOperand()) << " 2: " << *qq << "\n";
        outs() << "same? " << (i->getPointerOperand() == qq) << "\n";
      }
    }
    
    
  }

  Lit * l1 = new Lit(1);
  Expr * a = new Ite(new Leq(new Var("a"), l1), l1, l1);
  std::cout << "it is: " << *a << "\n";
}




//void computeVC (const Instruction *i) {}

int main(int argc, char** argv) 
{
  cl::ParseCommandLineOptions(argc, argv, "LLVM parser\n");
  LLVMContext context;

/*
  ErrorOr<std::unique_ptr<MemoryBuffer>> mb =
  MemoryBuffer::getFile(FileName);
  if (std::error_code ec = mb.getError()) {
      errs() << ec.message();
      return -1;
  }
  Expected<std::unique_ptr<Module>>  m = parseBitcodeFile(mb->get()->getMemBufferRef(), context);
  if (Error ec = m.takeError()) { 
  //if (std::error_code ec = m.getError()) {
      //errs() << "Error reading bitcode: " << ec.message() << "\n";
      errs() << "Error reading bitcode: " << ec << "\n";
      return -1;
  }
  */
  SMDiagnostic Err;
  std::unique_ptr<Module> m2(parseIRFile(FileName, Err, context));
  if (!m2) {
    Err.print(argv[0], errs());
    return 1;
  }


  //for (Module::const_iterator i = m.get()->getFunctionList().begin(), 
  for (Module::const_iterator i = m2.get()->getFunctionList().begin(), 
      e = m2.get()->getFunctionList().end(); i != e; ++i) {
      if (!i->isDeclaration()) {
          const Function &fn = *i;
          for (const BasicBlock &bb : fn) {
              computeVC(bb);
          }
          //outs() << i->getName() << " has " << i->size()
          //       << " basic blocks.\n";
      }
  }

  return 0;
}


/*

#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Pass.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

int main(int argc, char **argv) {
  if (argc < 2) {
    errs() << "Usage: " << argv[0] << " <IR file>\n";
    return 1;
  }

  // Parse the input LLVM IR file into a module.
  SMDiagnostic Err;
  LLVMContext Context;
  std::unique_ptr<Module> Mod(parseIRFile(argv[1], Err, Context));
  if (!Mod) {
    Err.print(argv[0], errs());
    return 1;
  }

  // Go over all named mdnodes in the module
  for (Module::const_named_metadata_iterator I = Mod->named_metadata_begin(),
                                             E = Mod->named_metadata_end();
       I != E; ++I) {
    outs() << "Found MDNode:\n";
    // These dumps only work with LLVM built with a special cmake flag enabling
    // dumps.
    // I->dump();

    for (unsigned i = 0, e = I->getNumOperands(); i != e; ++i) {
      Metadata *Op = I->getOperand(i);
      if (auto *N = dyn_cast<MDNode>(Op)) {
        outs() << "  Has MDNode operand:\n  ";
        // N->dump();
        outs() << "  " << N->getNumOperands() << " operands\n";
      }
    }
  }

  return 0;
}
*/