import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr48353_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr48353_src(%aj : _) -> _ {
  ^bb0(%aj : _):
    %c_i32_1 = llvm.mlir.constant(1 : _) : _
    %cmp_i = llvm.icmp "sgt" %aj, %c_i32_1 : _
    %c_i32_3 = llvm.mlir.constant(3 : _) : _
    %aj_op = llvm.lshr %c_i32_3, %aj : _
    %_op2 = llvm.and %aj_op, %c_i32_1 : _
    %c_i32_0 = llvm.mlir.constant(0 : _) : _
    %cmp41 = llvm.icmp "ne" %_op2, %c_i32_0 : _
    %c_i1_1 = llvm.mlir.constant(1 : i1) : i1
    %cmp4 = llvm.select %cmp_i, %c_i1_1, %cmp41 : i1
    %conv5 = llvm.zext %cmp4 : i1 to _
    llvm.return %conv5 : _
  }
  }]

def pr48353_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr48353_tgt(%aj : _) -> _ {
  ^bb0(%aj : _):
    %c_i32_1 = llvm.mlir.constant(1 : _) : _
    %cmp_i = llvm.icmp "sgt" %aj, %c_i32_1 : _
    %c_i32_3 = llvm.mlir.constant(3 : _) : _
    %aj_op = llvm.lshr %c_i32_3, %aj : _
    %_op2 = llvm.and %aj_op, %c_i32_1 : _
    %c_i32_0 = llvm.mlir.constant(0 : _) : _
    %cmp41 = llvm.icmp "ne" %_op2, %c_i32_0 : _
    %cmp4 = llvm.or %cmp_i, %cmp41 : i1
    %conv5 = llvm.zext %cmp4 : i1 to _
    llvm.return %conv5 : _
  }
  }]
