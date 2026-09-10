import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr71768_sdiv_neg_prod_src :=
  [llvm()| {
  llvm.func @pr71768_sdiv_neg_prod_src(%a : i64, %b : i64) -> i64 {
  ^bb0(%a : i64, %b : i64):
    %mul = llvm.mul %a, %b : i64
    %c_i64_0 = llvm.mlir.constant(0 : i64) : i64
    %neg = llvm.sub %c_i64_0, %mul : i64
    %div = llvm.sdiv %neg, %mul : i64
    llvm.return %div : i64
  }
  }]

def pr71768_sdiv_neg_prod_tgt :=
  [llvm()| {
  llvm.func @pr71768_sdiv_neg_prod_tgt(%a : i64, %b : i64) -> i64 {
  ^bb0(%a : i64, %b : i64):
    %c_i64_m1 = llvm.mlir.constant(-1 : i64) : i64
    llvm.return %c_i64_m1 : i64
  }
  }]
