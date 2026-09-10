import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr48353_src :=
  [llvm()| {
  llvm.func @pr48353_src(%aj : i32) -> i32 {
  ^bb0(%aj : i32):
    %c_i32_1 = llvm.mlir.constant(1 : i32) : i32
    %cmp_i = llvm.icmp "sgt" %aj, %c_i32_1 : i32
    %c_i32_3 = llvm.mlir.constant(3 : i32) : i32
    %aj_op = llvm.lshr %c_i32_3, %aj : i32
    %_op2 = llvm.and %aj_op, %c_i32_1 : i32
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %cmp41 = llvm.icmp "ne" %_op2, %c_i32_0 : i32
    %c_i1_1 = llvm.mlir.constant(1 : i1) : i1
    %cmp4 = llvm.select %cmp_i, %c_i1_1, %cmp41 : i1
    %conv5 = llvm.zext %cmp4 : i1 to i32
    llvm.return %conv5 : i32
  }
  }]

def pr48353_tgt :=
  [llvm()| {
  llvm.func @pr48353_tgt(%aj : i32) -> i32 {
  ^bb0(%aj : i32):
    %c_i32_1 = llvm.mlir.constant(1 : i32) : i32
    %cmp_i = llvm.icmp "sgt" %aj, %c_i32_1 : i32
    %c_i32_3 = llvm.mlir.constant(3 : i32) : i32
    %aj_op = llvm.lshr %c_i32_3, %aj : i32
    %_op2 = llvm.and %aj_op, %c_i32_1 : i32
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %cmp41 = llvm.icmp "ne" %_op2, %c_i32_0 : i32
    %cmp4 = llvm.or %cmp_i, %cmp41 : i1
    %conv5 = llvm.zext %cmp4 : i1 to i32
    llvm.return %conv5 : i32
  }
  }]
