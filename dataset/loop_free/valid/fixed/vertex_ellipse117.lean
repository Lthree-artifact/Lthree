import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def vertex_ellipse117_src :=
  [llvm()| {
  llvm.func @vertex_ellipse117_src(%A : i32, %B : i32, %log_C : i32) -> i32 {
  ^bb0(%A : i32, %B : i32, %log_C : i32):
    %zero = llvm.mlir.constant(0 : i32) : i32
    %one = llvm.mlir.constant(1 : i32) : i32
    %bw_const = llvm.mlir.constant(32 : i32) : i32
    %bitwidth_A_B = llvm.add %bw_const, %zero : i32
    %bw_minus_1 = llvm.sub %bitwidth_A_B, %one : i32
    %pre = llvm.icmp "ult" %log_C, %bw_minus_1 : i32
    llvm.assume %pre : i1
    %C = llvm.shl %one, %log_C : i32
    %smin_cmp = llvm.icmp "slt" %B, %A : i32
    %smin = llvm.select %smin_cmp, %B, %A : i32
    %sub = llvm.sub %A, %smin overflow<nsw> : i32
    %sdiv = llvm.sdiv %sub, %C : i32
    %shl = llvm.shl %sdiv, %log_C overflow<nsw> : i32
    %res = llvm.add %shl, %smin : i32
    llvm.return %res : i32
  }
  }]

def vertex_ellipse117_tgt :=
  [llvm()| {
  llvm.func @vertex_ellipse117_tgt(%A : i32, %B : i32, %log_C : i32) -> i32 {
  ^bb0(%A : i32, %B : i32, %log_C : i32):
    %zero = llvm.mlir.constant(0 : i32) : i32
    %one = llvm.mlir.constant(1 : i32) : i32
    %bw_const = llvm.mlir.constant(32 : i32) : i32
    %bitwidth_A_B = llvm.add %bw_const, %zero : i32
    %bw_minus_1 = llvm.sub %bitwidth_A_B, %one : i32
    %pre = llvm.icmp "ult" %log_C, %bw_minus_1 : i32
    llvm.assume %pre : i1
    %C = llvm.shl %one, %log_C : i32
    %mask = llvm.sub %zero, %C : i32
    %smin_cmp = llvm.icmp "slt" %B, %A : i32
    %smin = llvm.select %smin_cmp, %B, %A : i32
    %sub = llvm.sub %A, %smin overflow<nsw> : i32
    %and = llvm.and %sub, %mask : i32
    %res = llvm.add %and, %smin : i32
    llvm.return %res : i32
  }
  }]
