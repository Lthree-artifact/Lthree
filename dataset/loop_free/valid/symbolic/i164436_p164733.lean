import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def ctlz_and_not_x_x_sub_1_src (w1 : Nat)(_h : 0 < w1) :=
  [llvm(w1)| {
  llvm.func @ctlz_and_not_x_x_sub_1_src(%x : _) -> _ {
  ^bb0(%x : _):
    %minus_one = llvm.mlir.constant(-1 : _) : _
    %one = llvm.mlir.constant(1 : _) : _
    %not_x = llvm.xor %x, %minus_one
    %x_sub_1 = llvm.sub %x, %one
    %masked = llvm.and %not_x, %x_sub_1
    %r = llvm.ctlz %masked, false : _
    llvm.return %r
  }
  }]

def ctlz_and_not_x_x_sub_1_tgt (w1 : Nat)(_h : 0 < w1) :=
  [llvm(w1)| {
  llvm.func @ctlz_and_not_x_x_sub_1_tgt(%x : _) -> _ {
  ^bb0(%x : _):
    %bitwidth = llvm.mlir.constant(w1 : w1) : w1
    %count = llvm.cttz %x, false : _
    %r = llvm.sub %bitwidth, %count
    llvm.return %r
  }
  }]
