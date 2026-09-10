import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i137937_ConstraintElim_checkOrAndOpImpliedByOther_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i137937_ConstraintElim_checkOrAndOpImpliedByOther_src(%b : _) -> i1 {
  ^bb0(%b : _):
    %c_i8_1 = llvm.mlir.constant(1 : _) : _
    %c_1 = llvm.icmp "slt" %b, %c_i8_1 : _
    %c_i8_0 = llvm.mlir.constant(0 : _) : _
    %c_2 = llvm.icmp "ne" %b, %c_i8_0 : _
    %or = llvm.or disjoint %c_2, %c_1 : i1
    llvm.return %or : i1
  }
  }]

def i137937_ConstraintElim_checkOrAndOpImpliedByOther_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i137937_ConstraintElim_checkOrAndOpImpliedByOther_tgt(%b : _) -> i1 {
  ^bb0(%b : _):
    %c_i8_0 = llvm.mlir.constant(0 : _) : _
    %c_2 = llvm.icmp "ne" %b, %c_i8_0 : _
    %c_i1_1 = llvm.mlir.constant(1 : i1) : i1
    %or = llvm.or disjoint %c_2, %c_i1_1 : i1
    llvm.return %or : i1
  }
  }]
