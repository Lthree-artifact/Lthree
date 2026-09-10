import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i163084_src :=
  [llvm()| {
  llvm.func @i163084_src(%arg0 : i64) -> i1 {
  ^bb0(%arg0 : i64):
    %c_64_12 = llvm.mlir.constant(12 : i64) : i64
    %v0 = llvm.sdiv exact %arg0, %c_64_12 : i64
    %v1 = llvm.icmp "ugt" %v0, %c_64_12 : i64
    llvm.return %v1 : i1
  }
  }]

def i163084_tgt :=
  [llvm()| {
  llvm.func @i163084_tgt(%arg0 : i64) -> i1 {
  ^bb0(%arg0 : i64):
    %c_64_144 = llvm.mlir.constant(144 : i64) : i64
    %v0 = llvm.icmp "ugt" %arg0, %c_64_144 : i64
    llvm.return %v0 : i1
  }
  }]
