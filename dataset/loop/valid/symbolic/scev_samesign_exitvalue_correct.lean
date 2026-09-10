import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def scev_samesign_exitvalue_correct_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @scev_samesign_exitvalue_correct_src(%unused : _) -> _ {
  ^entry(%unused : _):
    %e_a = llvm.mlir.constant 1 : _
    %e_b = llvm.mlir.constant 0 : _
    %e_xor = llvm.xor %e_a, %e_b : _
    %e_lim = llvm.mlir.constant 100 : _
    %e_guard = llvm.icmp "ult" %e_xor, %e_lim : _
    %e_zero = llvm.mlir.constant 0 : _
    llvm.cond_br %e_guard : i1, ^loop(%e_zero : _), ^out(%e_zero : _)
  ^loop(%f : _):
    %l_one = llvm.mlir.constant 1 : _
    %cmp = llvm.icmp "slt" %f, %l_one : _
    %l_zero = llvm.mlir.constant 0 : _
    llvm.cond_br %cmp : i1, ^loop(%l_one : _), ^out(%l_zero : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

def scev_samesign_exitvalue_correct_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @scev_samesign_exitvalue_correct_tgt(%unused : _) -> _ {
  ^entry(%unused : _):
    %r = llvm.mlir.constant 0 : _
    llvm.return %r : _
  }
  }]

end TestLoop
end InstCombine
