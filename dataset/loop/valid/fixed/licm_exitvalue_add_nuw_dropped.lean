import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def licm_exitvalue_add_nuw_dropped_src :=
  [llvm()| {
  llvm.func @licm_exitvalue_add_nuw_dropped_src(%c1 : i64, %c2 : i64) -> i64 {
  ^entry(%c1 : i64, %c2 : i64):
    %e_zero = llvm.mlir.constant 0 : i64
    %e_start = llvm.mlir.constant 0 : i64
    llvm.br ^loop(%e_zero : i64, %e_start : i64)
  ^loop(%k : i64, %index : i64):
    %step_add = llvm.add %index, %c1 : i64
    %index_next = llvm.add %step_add, %c2 overflow<nuw> : i64
    %l_one = llvm.mlir.constant 1 : i64
    %k1 = llvm.add %k, %l_one : i64
    %l_three = llvm.mlir.constant 3 : i64
    %cond = llvm.icmp "eq" %k1, %l_three : i64
    llvm.cond_br %cond : i1, ^out(%index_next : i64), ^loop(%k1 : i64, %index_next : i64)
  ^out(%res : i64):
    llvm.return %res : i64
  }
  }]

def licm_exitvalue_add_nuw_dropped_tgt :=
  [llvm()| {
  llvm.func @licm_exitvalue_add_nuw_dropped_tgt(%c1 : i64, %c2 : i64) -> i64 {
  ^entry(%c1 : i64, %c2 : i64):
    %invariant_op = llvm.add %c1, %c2 : i64
    %s2 = llvm.add %invariant_op, %invariant_op : i64
    %s3 = llvm.add %s2, %invariant_op : i64
    llvm.return %s3 : i64
  }
  }]

end TestLoop
end InstCombine
