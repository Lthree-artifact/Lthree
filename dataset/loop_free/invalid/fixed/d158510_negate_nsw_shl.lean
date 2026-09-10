import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def d158510_negate_nsw_shl_src :=
  [llvm()| {
  llvm.func @d158510_negate_nsw_shl_src(%a : i64, %shamt : i64) -> i64 {
  ^bb0(%a : i64, %shamt : i64):
    %c_i64_1 = llvm.mlir.constant(1 : i64) : i64
    %pow2 = llvm.shl %c_i64_1, %shamt : i64
    %c_i64_0 = llvm.mlir.constant(0 : i64) : i64
    %neg_pow2 = llvm.sub %c_i64_0, %pow2 : i64
    %mul = llvm.mul %a, %neg_pow2 overflow<nsw> : i64
    llvm.return %mul : i64
  }
  }]

def d158510_negate_nsw_shl_tgt :=
  [llvm()| {
  llvm.func @d158510_negate_nsw_shl_tgt(%a : i64, %shamt : i64) -> i64 {
  ^bb0(%a : i64, %shamt : i64):
    %c_i64_1 = llvm.mlir.constant(1 : i64) : i64
    %pow2 = llvm.shl %c_i64_1, %shamt : i64
    %c_i64_0 = llvm.mlir.constant(0 : i64) : i64
    %a_neg = llvm.sub %c_i64_0, %a overflow<nsw> : i64
    %mul = llvm.mul %a_neg, %pow2 overflow<nsw> : i64
    llvm.return %mul : i64
  }
  }]
