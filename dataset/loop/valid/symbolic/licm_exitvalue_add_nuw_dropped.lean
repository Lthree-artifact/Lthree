import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def licm_exitvalue_add_nuw_dropped_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @licm_exitvalue_add_nuw_dropped_src(%c1 : _, %c2 : _) -> _ {
  ^entry(%c1 : _, %c2 : _):
    %e_zero = llvm.mlir.constant 0 : _
    %e_start = llvm.mlir.constant 0 : _
    llvm.br ^loop(%e_zero : _, %e_start : _)
  ^loop(%k : _, %index : _):
    %step_add = llvm.add %index, %c1 : _
    %index_next = llvm.add %step_add, %c2 overflow<nuw> : _
    %l_one = llvm.mlir.constant 1 : _
    %k1 = llvm.add %k, %l_one : _
    %l_three = llvm.mlir.constant 3 : _
    %cond = llvm.icmp "eq" %k1, %l_three : _
    llvm.cond_br %cond : i1, ^out(%index_next : _), ^loop(%k1 : _, %index_next : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

def licm_exitvalue_add_nuw_dropped_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @licm_exitvalue_add_nuw_dropped_tgt(%c1 : _, %c2 : _) -> _ {
  ^entry(%c1 : _, %c2 : _):
    %invariant_op = llvm.add %c1, %c2 : _
    %s2 = llvm.add %invariant_op, %invariant_op : _
    %s3 = llvm.add %s2, %invariant_op : _
    llvm.return %s3 : _
  }
  }]

end TestLoop
end InstCombine
