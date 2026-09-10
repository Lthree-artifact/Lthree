import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def scev_samesign_exitvalue_correct_src :=
  [llvm()| {
  llvm.func @scev_samesign_exitvalue_correct_src(%unused : i8) -> i8 {
  ^entry(%unused : i8):
    %e_a = llvm.mlir.constant 1 : i8
    %e_b = llvm.mlir.constant 0 : i8
    %e_xor = llvm.xor %e_a, %e_b : i8
    %e_lim = llvm.mlir.constant 100 : i8
    %e_guard = llvm.icmp "ult" %e_xor, %e_lim : i8
    %e_zero = llvm.mlir.constant 0 : i8
    llvm.cond_br %e_guard : i1, ^loop(%e_zero : i8), ^out(%e_zero : i8)
  ^loop(%f : i8):
    %l_one = llvm.mlir.constant 1 : i8
    %cmp = llvm.icmp "slt" %f, %l_one : i8
    %l_zero = llvm.mlir.constant 0 : i8
    llvm.cond_br %cmp : i1, ^loop(%l_one : i8), ^out(%l_zero : i8)
  ^out(%res : i8):
    llvm.return %res : i8
  }
  }]

def scev_samesign_exitvalue_correct_tgt :=
  [llvm()| {
  llvm.func @scev_samesign_exitvalue_correct_tgt(%unused : i8) -> i8 {
  ^entry(%unused : i8):
    %r = llvm.mlir.constant 0 : i8
    llvm.return %r : i8
  }
  }]

end TestLoop
end InstCombine
