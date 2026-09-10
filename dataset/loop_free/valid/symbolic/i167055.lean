import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i167055_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167055_src(%arg0 : _, %C1 : _, %C2 : _) -> i1 {
  ^bb0(%arg0 : _, %C1 : _, %C2 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c1_ge_0 = llvm.icmp "sge" %C1, %zero : _
    %sum = llvm.add %C1, %C2 : _
    %sum_gt_c1 = llvm.icmp "sgt" %sum, %C1 : _
    %c2_le_0 = llvm.icmp "sle" %C2, %zero : _
    %sum_le_0 = llvm.icmp "sle" %sum, %zero : _
    %cond_neg = llvm.and %c2_le_0, %sum_le_0 : i1
    %ok = llvm.or %sum_gt_c1, %cond_neg : i1
    %cond = llvm.and %c1_ge_0, %ok : i1
    llvm.assume %cond : i1
    %umin_c = llvm.icmp "ult" %arg0, %C1 : _
    %v0 = llvm.select %umin_c, %arg0, %C1 : _
    %v1 = llvm.sub %arg0, %v0 overflow<nsw> : _
    %v2 = llvm.icmp "slt" %v1, %C2 : _
    llvm.return %v2 : i1
  }
  }]

def i167055_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167055_tgt(%arg0 : _, %C1 : _, %C2 : _) -> i1 {
  ^bb0(%arg0 : _, %C1 : _, %C2 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c1_ge_0 = llvm.icmp "sge" %C1, %zero : _
    %sum = llvm.add %C1, %C2 : _
    %sum_gt_c1 = llvm.icmp "sgt" %sum, %C1 : _
    %c2_le_0 = llvm.icmp "sle" %C2, %zero : _
    %sum_le_0 = llvm.icmp "sle" %sum, %zero : _
    %cond_neg = llvm.and %c2_le_0, %sum_le_0 : i1
    %ok = llvm.or %sum_gt_c1, %cond_neg : i1
    %cond = llvm.and %c1_ge_0, %ok : i1
    llvm.assume %cond : i1
    %v0 = llvm.add %C1, %C2 : _
    %v1 = llvm.icmp "slt" %arg0, %v0 : _
    llvm.return %v1 : i1
  }
  }]
