import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr49688_src :=
  [llvm()| {
  llvm.func @pr49688_src(%g : i32, %h : i32) -> i32 {
  ^bb0(%g : i32, %h : i32):
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %cmp = llvm.icmp "slt" %g, %c_i32_0 : i32
    %c_i32_7 = llvm.mlir.constant(7 : i32) : i32
    %shr = llvm.ashr %c_i32_7, %h : i32
    %cmp1 = llvm.icmp "sgt" %g, %shr : i32
    %c_i1_true = llvm.mlir.constant(true) : i1
    %0 = llvm.select %cmp, %c_i1_true, %cmp1 : i1
    %lor_ext = llvm.zext %0 : i1 to i32
    llvm.return %lor_ext : i32
  }
  }]

def pr49688_tgt :=
  [llvm()| {
  llvm.func @pr49688_tgt(%g : i32, %h : i32) -> i32 {
  ^bb0(%g : i32, %h : i32):
    %c_i32_7 = llvm.mlir.constant(7 : i32) : i32
    %shr = llvm.lshr %c_i32_7, %h : i32
    %0 = llvm.icmp "ult" %shr, %g : i32
    %lor_ext = llvm.zext %0 : i1 to i32
    llvm.return %lor_ext : i32
  }
  }]
