import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr49688_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr49688_src(%g : _, %h : _) -> _ {
  ^bb0(%g : _, %h : _):
    %c_i32_0 = llvm.mlir.constant(0 : _) : _
    %cmp = llvm.icmp "slt" %g, %c_i32_0 : _
    %c_i32_7 = llvm.mlir.constant(7 : _) : _
    %shr = llvm.ashr %c_i32_7, %h : _
    %cmp1 = llvm.icmp "sgt" %g, %shr : _
    %c_i1_true = llvm.mlir.constant(true) : i1
    %0 = llvm.select %cmp, %c_i1_true, %cmp1 : i1
    %lor_ext = llvm.zext %0 : i1 to _
    llvm.return %lor_ext : _
  }
  }]

def pr49688_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr49688_tgt(%g : _, %h : _) -> _ {
  ^bb0(%g : _, %h : _):
    %c_i32_7 = llvm.mlir.constant(7 : _) : _
    %shr = llvm.lshr %c_i32_7, %h : _
    %0 = llvm.icmp "ult" %shr, %g : _
    %lor_ext = llvm.zext %0 : i1 to _
    llvm.return %lor_ext : _
  }
  }]
