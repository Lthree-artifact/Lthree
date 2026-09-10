import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def licm_exitvalue_mul_nuw_kept_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @licm_exitvalue_mul_nuw_kept_src(%a : _) -> _ {
  ^entry(%a : _):
    %e_zero = llvm.mlir.constant 0 : _
    llvm.br ^loop(%e_zero : _, %e_zero : _)
  ^loop(%k : _, %val : _):
    %o = llvm.or %val, %a : _
    %l_65536 = llvm.mlir.constant 65536 : _
    %m1 = llvm.mul %o, %l_65536 overflow<nuw> : _
    %l_m9 = llvm.mlir.constant -9 : _
    %sext = llvm.mul %m1, %l_m9 overflow<nsw> : _
    %l_one = llvm.mlir.constant 1 : _
    %k1 = llvm.add %k, %l_one : _
    %l_two = llvm.mlir.constant 2 : _
    %cond = llvm.icmp "eq" %k1, %l_two : _
    llvm.cond_br %cond : i1, ^out(%sext : _), ^loop(%k1 : _, %l_one : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

def licm_exitvalue_mul_nuw_kept_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @licm_exitvalue_mul_nuw_kept_tgt(%a : _) -> _ {
  ^entry(%a : _):
    %e_one = llvm.mlir.constant 1 : _
    %o = llvm.or %e_one, %a : _
    %l_c = llvm.mlir.constant -589824 : _
    %r = llvm.mul %o, %l_c overflow<nuw> : _
    llvm.return %r : _
  }
  }]

end TestLoop
end InstCombine
