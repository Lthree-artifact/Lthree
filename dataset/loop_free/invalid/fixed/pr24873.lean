import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr24873_src :=
  [llvm()| {
  llvm.func @pr24873_src(%V : i64) -> i1 {
  ^bb0(%V : i64):
    %c_i64_m4611686018427387904 = llvm.mlir.constant(-4611686018427387904 : i64) : i64
    %ashr = llvm.ashr %c_i64_m4611686018427387904, %V : i64
    %c_i64_m1 = llvm.mlir.constant(-1 : i64) : i64
    %icmp = llvm.icmp "eq" %ashr, %c_i64_m1 : i64
    llvm.return %icmp : i1
  }
  }]

def pr24873_tgt :=
  [llvm()| {
  llvm.func @pr24873_tgt(%V : i64) -> i1 {
  ^bb0(%V : i64):
    %c_i64_62 = llvm.mlir.constant(62 : i64) : i64
    %icmp = llvm.icmp "eq" %V, %c_i64_62 : i64
    llvm.return %icmp : i1
  }
  }]
