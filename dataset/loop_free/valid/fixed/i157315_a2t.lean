import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i157315_a2t_src :=
  [llvm()| {
  llvm.func @i157315_a2t_src(%arg0 : i32, %arg1 : i32, %C0 : i32, %C1 : i32,
      %C2 : i32, %C_add : i32, %C_ub : i32) -> i1 {
  ^bb0(%arg0 : i32, %arg1 : i32, %C0 : i32, %C1 : i32, %C2 : i32,
      %C_add : i32, %C_ub : i32):
    %one = llvm.mlir.constant(1 : i32) : i32
    %minus_one = llvm.mlir.constant(4294967295 : i32) : i32
    %pre1 = llvm.icmp "sle" %C1, %C2 : i32
    llvm.assume %pre1 : i1
    %diff = llvm.sub %C0, %C1 : i32
    %pre2 = llvm.icmp "eq" %C_add, %diff : i32
    llvm.assume %pre2 : i1
    %dist = llvm.sub %C2, %C1 : i32
    %pre3 = llvm.icmp "ne" %dist, %minus_one : i32
    llvm.assume %pre3 : i1
    %dist_plus_one = llvm.add %dist, %one : i32
    %pre4 = llvm.icmp "eq" %C_ub, %dist_plus_one : i32
    llvm.assume %pre4 : i1
    %v0 = llvm.add %arg1, %C0 : i32
    %v1 = llvm.add %v0, %arg0 : i32
    %v2_cmp = llvm.icmp "sgt" %v1, %C1 : i32
    %v2 = llvm.select %v2_cmp, %v1, %C1 : i32
    %v3_cmp = llvm.icmp "slt" %v2, %C2 : i32
    %v3 = llvm.select %v3_cmp, %v2, %C2 : i32
    %v4 = llvm.icmp "eq" %v1, %v3 : i32
    llvm.return %v4 : i1
  }
  }]

def i157315_a2t_tgt :=
  [llvm()| {
  llvm.func @i157315_a2t_tgt(%arg0 : i32, %arg1 : i32, %C0 : i32, %C1 : i32,
      %C2 : i32, %C_add : i32, %C_ub : i32) -> i1 {
  ^bb0(%arg0 : i32, %arg1 : i32, %C0 : i32, %C1 : i32, %C2 : i32,
      %C_add : i32, %C_ub : i32):
    %one = llvm.mlir.constant(1 : i32) : i32
    %minus_one = llvm.mlir.constant(4294967295 : i32) : i32
    %pre1 = llvm.icmp "sle" %C1, %C2 : i32
    llvm.assume %pre1 : i1
    %diff = llvm.sub %C0, %C1 : i32
    %pre2 = llvm.icmp "eq" %C_add, %diff : i32
    llvm.assume %pre2 : i1
    %dist = llvm.sub %C2, %C1 : i32
    %pre3 = llvm.icmp "ne" %dist, %minus_one : i32
    llvm.assume %pre3 : i1
    %dist_plus_one = llvm.add %dist, %one : i32
    %pre4 = llvm.icmp "eq" %C_ub, %dist_plus_one : i32
    llvm.assume %pre4 : i1
    %sum = llvm.add %arg0, %C_add : i32
    %v1 = llvm.add %sum, %arg1 : i32
    %result = llvm.icmp "ult" %v1, %C_ub : i32
    llvm.return %result : i1
  }
  }]
