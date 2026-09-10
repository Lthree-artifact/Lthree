import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr121633_srem_mul_mul_assume_src :=
  [llvm()| {
  llvm.func @pr121633_srem_mul_mul_assume_src(%x : i64, %y : i64, %z : i64) -> i64 {
  ^bb0(%x : i64, %y : i64, %z : i64):
    %remc = llvm.srem %y, %z : i64
    %cond = llvm.icmp "eq" %remc, %y : i64
    llvm.assume %cond : i1
    %mul1 = llvm.mul %x, %y : i64
    %mul2 = llvm.mul %x, %z : i64
    %rem = llvm.srem %mul1, %mul2 : i64
    llvm.return %rem : i64
  }
  }]

def pr121633_srem_mul_mul_assume_tgt :=
  [llvm()| {
  llvm.func @pr121633_srem_mul_mul_assume_tgt(%x : i64, %y : i64, %z : i64) -> i64 {
  ^bb0(%x : i64, %y : i64, %z : i64):
    %mul = llvm.mul %x, %y : i64
    llvm.return %mul : i64
  }
  }]
