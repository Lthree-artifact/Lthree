import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def licm_exitvalue_mul_nuw_kept_src :=
  [llvm()| {
  llvm.func @licm_exitvalue_mul_nuw_kept_src(%a : i32) -> i32 {
  ^entry(%a : i32):
    %e_zero = llvm.mlir.constant 0 : i32
    llvm.br ^loop(%e_zero : i32, %e_zero : i32)
  ^loop(%k : i32, %val : i32):
    %o = llvm.or %val, %a : i32
    %l_65536 = llvm.mlir.constant 65536 : i32
    %m1 = llvm.mul %o, %l_65536 overflow<nuw> : i32
    %l_m9 = llvm.mlir.constant -9 : i32
    %sext = llvm.mul %m1, %l_m9 overflow<nsw> : i32
    %l_one = llvm.mlir.constant 1 : i32
    %k1 = llvm.add %k, %l_one : i32
    %l_two = llvm.mlir.constant 2 : i32
    %cond = llvm.icmp "eq" %k1, %l_two : i32
    llvm.cond_br %cond : i1, ^out(%sext : i32), ^loop(%k1 : i32, %l_one : i32)
  ^out(%res : i32):
    llvm.return %res : i32
  }
  }]

def licm_exitvalue_mul_nuw_kept_tgt :=
  [llvm()| {
  llvm.func @licm_exitvalue_mul_nuw_kept_tgt(%a : i32) -> i32 {
  ^entry(%a : i32):
    %e_one = llvm.mlir.constant 1 : i32
    %o = llvm.or %e_one, %a : i32
    %l_c = llvm.mlir.constant -589824 : i32
    %r = llvm.mul %o, %l_c overflow<nuw> : i32
    llvm.return %r : i32
  }
  }]

end TestLoop
end InstCombine
