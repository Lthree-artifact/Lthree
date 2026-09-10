import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i199402_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i199402_src(%x : _, %y : _, %C : _, %cond : i1) -> i1 {
  ^bb0(%x : _, %y : _, %C : _, %cond : i1):
    %true = llvm.mlir.constant(true) : i1
    %y_ne_c = llvm.icmp "ne" %y, %C : _
    %x_eq_c = llvm.icmp "eq" %x, %C : _
    %not_cond_premise = llvm.or %y_ne_c, %x_eq_c : i1
    %precond = llvm.or %not_cond_premise, %cond : i1
    llvm.assume %precond : i1
    %x_is_c = llvm.icmp "eq" %x, %C : _
    %max = llvm.select %cond, %x, %y : _
    %max_is_c = llvm.icmp "eq" %max, %C : _
    %r = llvm.select %x_is_c, %true, %max_is_c : i1
    llvm.return %r : i1
  }
  }]

def i199402_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i199402_tgt(%x : _, %y : _, %C : _, %cond : i1) -> i1 {
  ^bb0(%x : _, %y : _, %C : _, %cond : i1):
    %y_ne_c = llvm.icmp "ne" %y, %C : _
    %x_eq_c = llvm.icmp "eq" %x, %C : _
    %not_cond_premise = llvm.or %y_ne_c, %x_eq_c : i1
    %precond = llvm.or %not_cond_premise, %cond : i1
    llvm.assume %precond : i1
    %r = llvm.icmp "eq" %x, %C : _
    llvm.return %r : i1
  }
  }]
