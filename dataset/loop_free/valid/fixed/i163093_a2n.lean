import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i163093_a2n_src :=
  [llvm()| {
  llvm.func @i163093_a2n_src(%arg0 : i64, %load_v1 : i64, %load_v3 : i64) -> i1 {
  ^bb0(%arg0 : i64, %load_v1 : i64, %load_v3 : i64):
    %v4 = llvm.sub %load_v1, %load_v3 : i64
    %c_64_0 = llvm.mlir.constant(0 : i64) : i64
    %v5 = llvm.icmp "slt" %load_v1, %c_64_0 : i64
    %v6 = llvm.select %v5, %c_64_0, %v4 : i64
    %v7 = llvm.sub %load_v3, %arg0 : i64
    %v8 = llvm.add %v7, %v6 : i64
    %v9 = llvm.icmp "eq" %v8, %c_64_0 : i64
    llvm.return %v9 : i1
  }
  }]

def i163093_a2n_tgt :=
  [llvm()| {
  llvm.func @i163093_a2n_tgt(%arg0 : i64, %load_v1 : i64, %load_v3 : i64) -> i1 {
  ^bb0(%arg0 : i64, %load_v1 : i64, %load_v3 : i64):
    %c_64_0 = llvm.mlir.constant(0 : i64) : i64
    %v4 = llvm.icmp "slt" %load_v1, %c_64_0 : i64
    %v5 = llvm.select %v4, %load_v3, %load_v1 : i64
    %v6 = llvm.sub %v5, %arg0 : i64
    %v7 = llvm.icmp "eq" %v6, %c_64_0 : i64
    llvm.return %v7 : i1
  }
  }]
