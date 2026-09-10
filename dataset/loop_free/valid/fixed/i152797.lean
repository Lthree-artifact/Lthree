import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i152797_src :=
  [llvm()| {
  llvm.func @i152797_src(%load_v1 : i32, %ptr_v0 : i64) -> i1 {
  ^bb0(%load_v1 : i32, %ptr_v0 : i64):
    %c_64_3 = llvm.mlir.constant(3 : i64) : i64
    %c_64_0 = llvm.mlir.constant(0 : i64) : i64
    %ptr_v0_low = llvm.and %ptr_v0, %c_64_3 : i64
    %ptr_v0_aligned = llvm.icmp "eq" %ptr_v0_low, %c_64_0 : i64
    llvm.assume %ptr_v0_aligned : i1
    %v2 = llvm.zext %load_v1 : i32 to i64
    %v4 = llvm.add %v2, %ptr_v0 : i64
    %c_64_2 = llvm.mlir.constant(2 : i64) : i64
    %v5 = llvm.and %v4, %c_64_2 : i64
    %v6 = llvm.icmp "eq" %v5, %c_64_0 : i64
    llvm.return %v6 : i1
  }
  }]

def i152797_tgt :=
  [llvm()| {
  llvm.func @i152797_tgt(%load_v1 : i32, %ptr_v0 : i64) -> i1 {
  ^bb0(%load_v1 : i32, %ptr_v0 : i64):
    %c_64_3 = llvm.mlir.constant(3 : i64) : i64
    %c_64_0 = llvm.mlir.constant(0 : i64) : i64
    %ptr_v0_low = llvm.and %ptr_v0, %c_64_3 : i64
    %ptr_v0_aligned = llvm.icmp "eq" %ptr_v0_low, %c_64_0 : i64
    llvm.assume %ptr_v0_aligned : i1
    %c_32_2 = llvm.mlir.constant(2 : i32) : i32
    %v2 = llvm.and %load_v1, %c_32_2 : i32
    %c_32_0 = llvm.mlir.constant(0 : i32) : i32
    %v3 = llvm.icmp "eq" %v2, %c_32_0 : i32
    llvm.return %v3 : i1
  }
  }]
