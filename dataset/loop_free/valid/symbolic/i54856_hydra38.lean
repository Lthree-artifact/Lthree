import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def hydra38_54856_src (w1 : Nat) (_h1 : 0 < w1) :=
[llvm(w1)| {
llvm.func @hydra38_54856_src(%x : w1, %C1 : w1, %C2 : w1) -> i1 {
^bb0(%x : w1, %C1 : w1, %C2 : w1):
  %is_pow2 = llvm.isPowerOf2 %C1 : w1
  llvm.assume %is_pow2 : i1
  %one = llvm.mlir.constant(1 : w1) : w1
  %diff = llvm.sub %C1, %C2 : w1
  %is_diff_one = llvm.icmp "eq" %diff, %one : w1
  llvm.assume %is_diff_one : i1
  %c2_and_x = llvm.and %C2, %x : w1
  %c2_ne_and = llvm.icmp "ne" %C2, %c2_and_x : w1
  %x_ult_c1 = llvm.icmp "ult" %x, %C1 : w1
  %result = llvm.and %c2_ne_and, %x_ult_c1 : i1
  llvm.return %result : i1
}
}]

def hydra38_54856_tgt (w1 : Nat) (_h1 : 0 < w1) :=
[llvm(w1)| {
llvm.func @hydra38_54856_tgt(%x : w1, %C1 : w1, %C2 : w1) -> i1 {
^bb0(%x : w1, %C1 : w1, %C2 : w1):
  %is_pow2 = llvm.isPowerOf2 %C1 : w1
  llvm.assume %is_pow2 : i1
  %one = llvm.mlir.constant(1 : w1) : w1
  %diff = llvm.sub %C1, %C2 : w1
  %is_diff_one = llvm.icmp "eq" %diff, %one : w1
  llvm.assume %is_diff_one : i1
  %result = llvm.icmp "ult" %x, %C2 : w1
  llvm.return %result : i1
}
}]
