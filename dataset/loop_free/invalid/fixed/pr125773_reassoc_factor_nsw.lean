import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr125773_reassoc_factor_nsw_src :=
  [llvm()| {
  llvm.func @pr125773_reassoc_factor_nsw_src(%X1 : i64, %X2 : i64, %g0 : i64, %g1 : i64) -> i64 {
  ^bb0(%X1 : i64, %X2 : i64, %g0 : i64, %g1 : i64):
    %A = llvm.add %X1, %g0 overflow<nsw> : i64
    %B = llvm.mul %X2, %g1 overflow<nsw> : i64
    %C = llvm.mul %X2, %A overflow<nsw> : i64
    %D = llvm.add %B, %C overflow<nsw> : i64
    llvm.return %D : i64
  }
  }]

def pr125773_reassoc_factor_nsw_tgt :=
  [llvm()| {
  llvm.func @pr125773_reassoc_factor_nsw_tgt(%X1 : i64, %X2 : i64, %g0 : i64, %g1 : i64) -> i64 {
  ^bb0(%X1 : i64, %X2 : i64, %g0 : i64, %g1 : i64):
    %c_i64_67 = llvm.mlir.constant(67 : i64) : i64
    %reass_add = llvm.add %X1, %c_i64_67 : i64
    %reass_mul = llvm.mul %reass_add, %X2 overflow<nsw> : i64
    llvm.return %reass_mul : i64
  }
  }]
