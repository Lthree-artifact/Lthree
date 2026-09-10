import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def d102864_udivmul_srem_to_zero_src :=
  [llvm()| {
  llvm.func @d102864_udivmul_srem_to_zero_src(%a : i64, %y : i64) -> i64 {
  ^bb0(%a : i64, %y : i64):
    %x = llvm.udiv %a, %y : i64
    %mul = llvm.mul %x, %y : i64
    %mod = llvm.srem %mul, %y : i64
    llvm.return %mod : i64
  }
  }]

def d102864_udivmul_srem_to_zero_tgt :=
  [llvm()| {
  llvm.func @d102864_udivmul_srem_to_zero_tgt(%a : i64, %y : i64) -> i64 {
  ^bb0(%a : i64, %y : i64):
    %c_i64_0 = llvm.mlir.constant(0 : i64) : i64
    llvm.return %c_i64_0 : i64
  }
  }]
