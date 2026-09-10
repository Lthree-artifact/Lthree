import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i154025_src :=
  [llvm()| {
  llvm.func @i154025_src(%arg0 : i32, %arg1 : i32, %arg2 : i32, %arg3 : i32) -> i32 {
  ^bb0(%arg0 : i32, %arg1 : i32, %arg2 : i32, %arg3 : i32):
    %v0 = llvm.or %arg3, %arg2 : i32
    %c_32_0 = llvm.mlir.constant(0 : i32) : i32
    %v1 = llvm.icmp "ne" %arg1, %c_32_0 : i32
    %v2 = llvm.or %v0, %arg0 : i32
    %v3 = llvm.icmp "ne" %v2, %c_32_0 : i32
    %c_1_true = llvm.mlir.constant(true) : i1
    %v4 = llvm.select %v3, %c_1_true, %v1 : i1
    %v5 = llvm.select %v4, %arg0, %c_32_0 : i32
    llvm.return %v5 : i32
  }
  }]

def i154025_tgt :=
  [llvm()| {
  llvm.func @i154025_tgt(%arg0 : i32, %arg1 : i32, %arg2 : i32, %arg3 : i32) -> i32 {
  ^bb0(%arg0 : i32, %arg1 : i32, %arg2 : i32, %arg3 : i32):
    llvm.return %arg0 : i32
  }
  }]
