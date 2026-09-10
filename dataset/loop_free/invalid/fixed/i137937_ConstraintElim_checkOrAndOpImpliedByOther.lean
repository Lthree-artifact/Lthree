import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i137937_ConstraintElim_checkOrAndOpImpliedByOther_src :=
  [llvm()| {
  llvm.func @i137937_ConstraintElim_checkOrAndOpImpliedByOther_src(%b : i8) -> i1 {
  ^bb0(%b : i8):
    %c_i8_1 = llvm.mlir.constant(1 : i8) : i8
    %c_1 = llvm.icmp "slt" %b, %c_i8_1 : i8
    %c_i8_0 = llvm.mlir.constant(0 : i8) : i8
    %c_2 = llvm.icmp "ne" %b, %c_i8_0 : i8
    %or = llvm.or disjoint %c_2, %c_1 : i1
    llvm.return %or : i1
  }
  }]

def i137937_ConstraintElim_checkOrAndOpImpliedByOther_tgt :=
  [llvm()| {
  llvm.func @i137937_ConstraintElim_checkOrAndOpImpliedByOther_tgt(%b : i8) -> i1 {
  ^bb0(%b : i8):
    %c_i8_0 = llvm.mlir.constant(0 : i8) : i8
    %c_2 = llvm.icmp "ne" %b, %c_i8_0 : i8
    %c_i1_1 = llvm.mlir.constant(1 : i1) : i1
    %or = llvm.or disjoint %c_2, %c_i1_1 : i1
    llvm.return %or : i1
  }
  }]
