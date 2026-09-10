import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i201290_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i201290_src(%c1 : _, %c2 : _, %a : _, %m : _) -> i1 {
  ^bb0(%c1 : _, %c2 : _, %a : _, %m : _):
    %cond = llvm.icmp "ult" %c1, %c2 : _
    llvm.assume %cond : i1
    %a_lte_m = llvm.icmp "ule" %a, %m : _
    llvm.assume %a_lte_m : i1
    %lhs = llvm.add %a, %c1 : _
    %rhs = llvm.add %m, %c2 overflow<nuw> : _
    %cmp = llvm.icmp "ult" %lhs, %rhs : _
    llvm.return %cmp : i1
  }
  }]

def i201290_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i201290_tgt(%c1 : _, %c2 : _, %a : _, %m : _) -> i1 {
  ^bb0(%c1 : _, %c2 : _, %a : _, %m : _):
    %cond = llvm.icmp "ult" %c1, %c2 : _
    llvm.assume %cond : i1
    %a_lte_m = llvm.icmp "ule" %a, %m : _
    llvm.assume %a_lte_m : i1
    %true = llvm.mlir.constant(true) : i1
    llvm.return %true : i1
  }
  }]
