import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i85267_src :=
  [llvm()| {
  llvm.func @i85267_src(%x : i32, %C1 : i32, %C2 : i32) -> i1 {
  ^bb0(%x : i32, %C1 : i32, %C2 : i32):
    %zero = llvm.mlir.constant(0 : i32) : i32
    %one = llvm.mlir.constant(1 : i32) : i32
    %int_min = llvm.mlir.constant(2147483648 : i32) : i32
    %c1_is_positive = llvm.icmp "sgt" %C1, %zero : i32
    llvm.assume %c1_is_positive : i1
    %c2_is_not_min = llvm.icmp "ne" %C2, %int_min : i32
    llvm.assume %c2_is_not_min : i1
    %c2m1 = llvm.sub %C2, %one : i32
    %c2m1_is_non_negative = llvm.icmp "sge" %c2m1, %zero : i32
    llvm.assume %c2m1_is_non_negative : i1
    %mul = llvm.mul %x, %C1 overflow<nsw> : i32
    %cmp = llvm.icmp "slt" %mul, %C2 : i32
    llvm.return %cmp : i1
  }
  }]

def i85267_tgt :=
  [llvm()| {
  llvm.func @i85267_tgt(%x : i32, %C1 : i32, %C2 : i32) -> i1 {
  ^bb0(%x : i32, %C1 : i32, %C2 : i32):
    %zero = llvm.mlir.constant(0 : i32) : i32
    %one = llvm.mlir.constant(1 : i32) : i32
    %int_min = llvm.mlir.constant(2147483648 : i32) : i32
    %c1_is_positive = llvm.icmp "sgt" %C1, %zero : i32
    llvm.assume %c1_is_positive : i1
    %c2_is_not_min = llvm.icmp "ne" %C2, %int_min : i32
    llvm.assume %c2_is_not_min : i1
    %c2m1 = llvm.sub %C2, %one : i32
    %c2m1_is_non_negative = llvm.icmp "sge" %c2m1, %zero : i32
    llvm.assume %c2m1_is_non_negative : i1
    %div = llvm.sdiv %c2m1, %C1 : i32
    %cmp = llvm.icmp "sle" %x, %div : i32
    llvm.return %cmp : i1
  }
  }]
