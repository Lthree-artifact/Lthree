import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i154258_src :=
  [llvm()| {
  llvm.func @i154258_src(%v3 : i32, %v4 : i32) -> i1 {
  ^bb0(%v3 : i32, %v4 : i32):
    %v5 = llvm.shl %v3, %v4 : i32
    %v6 = llvm.sext %v5 : i32 to i64
    %c_32_32768 = llvm.mlir.constant(32768 : i32) : i32
    %v7 = llvm.add %v5, %c_32_32768 : i32
    %c_64_2147516416 = llvm.mlir.constant(2147516416 : i64) : i64
    %v8 = llvm.add %v6, %c_64_2147516416 overflow<nsw> : i64
    %c_64_4294967296 = llvm.mlir.constant(4294967296 : i64) : i64
    %c_64_0 = llvm.mlir.constant(0 : i64) : i64
    %v9_lhs_neg = llvm.icmp "slt" %v8, %c_64_0 : i64
    %v9_rhs_neg = llvm.icmp "slt" %c_64_4294967296, %c_64_0 : i64
    %v9_same_sign = llvm.icmp "eq" %v9_lhs_neg, %v9_rhs_neg : i1
    llvm.assume %v9_same_sign : i1
    %v9 = llvm.icmp "ult" %v8, %c_64_4294967296 : i64
    %c_32_65536 = llvm.mlir.constant(65536 : i32) : i32
    %v131 = llvm.icmp "ult" %v7, %c_32_65536 : i32
    %c_1_false = llvm.mlir.constant(false) : i1
    %v13 = llvm.select %v9, %v131, %c_1_false : i1
    llvm.return %v13 : i1
  }
  }]

def i154258_tgt :=
  [llvm()| {
  llvm.func @i154258_tgt(%v3 : i32, %v4 : i32) -> i1 {
  ^bb0(%v3 : i32, %v4 : i32):
    %v5 = llvm.shl %v3, %v4 : i32
    %c_32_32768 = llvm.mlir.constant(32768 : i32) : i32
    %v6 = llvm.add %v5, %c_32_32768 : i32
    %c_32_65536 = llvm.mlir.constant(65536 : i32) : i32
    %v7 = llvm.icmp "ult" %v6, %c_32_65536 : i32
    llvm.return %v7 : i1
  }
  }]
