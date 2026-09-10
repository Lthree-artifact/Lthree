import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr32949_src :=
  [llvm()| {
  llvm.func @pr32949_src(%x : i8) -> i1 {
  ^bb0(%x : i8):
    %c_i8_1 = llvm.mlir.constant(1 : i8) : i8
    %div1 = llvm.sdiv exact %c_i8_1, %x : i8
    %c_i8_m1 = llvm.mlir.constant(-1 : i8) : i8
    %div2 = llvm.sdiv exact %c_i8_m1, %x : i8
    %icmp = llvm.icmp "ult" %div1, %div2 : i8
    llvm.return %icmp : i1
  }
  }]

def pr32949_tgt :=
  [llvm()| {
  llvm.func @pr32949_tgt(%x : i8) -> i1 {
  ^bb0(%x : i8):
    %c_i1_true = llvm.mlir.constant(true) : i1
    llvm.return %c_i1_true : i1
  }
  }]
