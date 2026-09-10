import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i143957_src :=
  [llvm()| {
  llvm.func @i143957_src(%arg0 : i64) -> i1 {
  ^bb0(%arg0 : i64):
    %c_64_32 = llvm.mlir.constant(32 : i64) : i64
    %1 = llvm.lshr %arg0, %c_64_32 : i64
    %2 = llvm.trunc %1 overflow<nuw> : i64 to i32
    %c_32_55296 = llvm.mlir.constant(55296 : i32) : i32
    %3 = llvm.xor %2, %c_32_55296 : i32
    %c_32_m1114112 = llvm.mlir.constant(-1114112 : i32) : i32
    %4 = llvm.add %3, %c_32_m1114112 : i32
    %c_32_m1112064 = llvm.mlir.constant(-1112064 : i32) : i32
    %5 = llvm.icmp "ult" %4, %c_32_m1112064 : i32
    %c_64_1114112 = llvm.mlir.constant(1114112 : i64) : i64
    %6 = llvm.icmp "eq" %1, %c_64_1114112 : i64
    %7 = llvm.or %6, %5 : i1
    llvm.return %7 : i1
  }
  }]

def i143957_tgt :=
  [llvm()| {
  llvm.func @i143957_tgt(%arg0 : i64) -> i1 {
  ^bb0(%arg0 : i64):
    %c_64_32 = llvm.mlir.constant(32 : i64) : i64
    %1 = llvm.lshr %arg0, %c_64_32 : i64
    %2 = llvm.trunc %1 overflow<nuw> : i64 to i32
    %c_32_55296 = llvm.mlir.constant(55296 : i32) : i32
    %3 = llvm.xor %2, %c_32_55296 : i32
    %c_32_m1114112 = llvm.mlir.constant(-1114112 : i32) : i32
    %4 = llvm.add %3, %c_32_m1114112 : i32
    %c_32_m1112064 = llvm.mlir.constant(-1112064 : i32) : i32
    %5 = llvm.icmp "ult" %4, %c_32_m1112064 : i32
    llvm.return %5 : i1
  }
  }]
