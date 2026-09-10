import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i152788_src :=
  [llvm()| {
  llvm.func @i152788_src(%0 : i32) -> i64 {
  ^bb0(%0 : i32):
    %c_32_1 = llvm.mlir.constant(1 : i32) : i32
    %v0 = llvm.add %0, %c_32_1 overflow<nsw> : i32
    %v1 = llvm.shl %0, %c_32_1 overflow<nsw> : i32
    %v2_smax_cmp = llvm.icmp "sgt" %v1, %v0 : i32
    %v2 = llvm.select %v2_smax_cmp, %v1, %v0 : i32
    %c_32_4 = llvm.mlir.constant(4 : i32) : i32
    %v3_smax_cmp = llvm.icmp "sgt" %v2, %c_32_4 : i32
    %v3 = llvm.select %v3_smax_cmp, %v2, %c_32_4 : i32
    %v4 = llvm.zext nneg %v3 : i32 to i64
    %c_64_3 = llvm.mlir.constant(3 : i64) : i64
    %v5 = llvm.shl %v4, %c_64_3 overflow<nsw,nuw> : i64
    llvm.return %v5 : i64
  }
  }]

def i152788_tgt :=
  [llvm()| {
  llvm.func @i152788_tgt(%0 : i32) -> i64 {
  ^bb0(%0 : i32):
    %c_32_1 = llvm.mlir.constant(1 : i32) : i32
    %v1 = llvm.shl %0, %c_32_1 overflow<nsw> : i32
    %c_32_4 = llvm.mlir.constant(4 : i32) : i32
    %v2_smax_cmp = llvm.icmp "sgt" %v1, %c_32_4 : i32
    %v2 = llvm.select %v2_smax_cmp, %v1, %c_32_4 : i32
    %v3 = llvm.zext nneg %v2 : i32 to i64
    %c_64_3 = llvm.mlir.constant(3 : i64) : i64
    %v4 = llvm.shl %v3, %c_64_3 overflow<nsw,nuw> : i64
    llvm.return %v4 : i64
  }
  }]
