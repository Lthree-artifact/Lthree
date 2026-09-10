import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr32949_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr32949_src(%x : _) -> i1 {
  ^bb0(%x : _):
    %c_i8_1 = llvm.mlir.constant(1 : _) : _
    %div1 = llvm.sdiv exact %c_i8_1, %x : _
    %c_i8_m1 = llvm.mlir.constant(-1 : _) : _
    %div2 = llvm.sdiv exact %c_i8_m1, %x : _
    %icmp = llvm.icmp "ult" %div1, %div2 : _
    llvm.return %icmp : i1
  }
  }]

def pr32949_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr32949_tgt(%x : _) -> i1 {
  ^bb0(%x : _):
    %c_i1_true = llvm.mlir.constant(true) : i1
    llvm.return %c_i1_true : i1
  }
  }]
