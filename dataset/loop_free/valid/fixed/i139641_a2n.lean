import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i139641_a2n_src :=
  [llvm()| {
  llvm.func @i139641_a2n_src(%arg0 : i32) -> i64 {
  ^bb0(%arg0 : i32):
    %c_32_0 = llvm.mlir.constant(0 : i32) : i32
    %1 = llvm.sub %c_32_0, %arg0 : i32
    %c_32_63 = llvm.mlir.constant(63 : i32) : i32
    %2 = llvm.and %1, %c_32_63 : i32
    %3 = llvm.zext nneg %2 : i32 to i64
    %c_64_0 = llvm.mlir.constant(0 : i64) : i64
    %4 = llvm.sub %c_64_0, %3 overflow<nsw> : i64
    %c_64_8 = llvm.mlir.constant(8 : i64) : i64
    %5 = llvm.lshr %4, %c_64_8 : i64
    %6 = llvm.or %5, %4 : i64
    llvm.return %6 : i64
  }
  }]

def i139641_a2n_tgt :=
  [llvm()| {
  llvm.func @i139641_a2n_tgt(%arg0 : i32) -> i64 {
  ^bb0(%arg0 : i32):
    %c_32_63 = llvm.mlir.constant(63 : i32) : i32
    %1 = llvm.and %arg0, %c_32_63 : i32
    %c_32_0 = llvm.mlir.constant(0 : i32) : i32
    %2 = llvm.icmp "ne" %1, %c_32_0 : i32
    %3 = llvm.sext %2 : i1 to i64
    llvm.return %3 : i64
  }
  }]
