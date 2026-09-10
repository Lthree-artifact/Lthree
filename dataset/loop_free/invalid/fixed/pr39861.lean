import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr39861_src :=
  [llvm()| {
  llvm.func @pr39861_src(%x : i8, %y : i8) -> i1 {
  ^bb0(%x : i8, %y : i8):
    %c_i8_255 = llvm.mlir.constant(255 : i8) : i8
    %tmp0 = llvm.lshr %c_i8_255, %y : i8
    %tmp1 = llvm.and %tmp0, %x : i8
    %ret = llvm.icmp "sge" %tmp1, %x : i8
    llvm.return %ret : i1
  }
  }]

def pr39861_tgt :=
  [llvm()| {
  llvm.func @pr39861_tgt(%x : i8, %y : i8) -> i1 {
  ^bb0(%x : i8, %y : i8):
    %c_i8_255 = llvm.mlir.constant(255 : i8) : i8
    %tmp0 = llvm.lshr %c_i8_255, %y : i8
    %1 = llvm.icmp "sge" %tmp0, %x : i8
    llvm.return %1 : i1
  }
  }]
