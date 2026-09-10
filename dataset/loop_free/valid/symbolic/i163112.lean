import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i163112_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i163112_src(%P : _, %Y : _, %X : _, %C : _) -> i1 {
  ^bb0(%P : _, %Y : _, %X : _, %C : _):
    %cond = llvm.icmp "ne" %P, %Y : _
    llvm.assume %cond : i1
    %v2 = llvm.icmp "eq" %X, %C : _
    %v3 = llvm.select %v2, %P, %Y : _
    %v4 = llvm.icmp "eq" %v3, %Y : _
    llvm.return %v4 : i1
  }
  }]

def i163112_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i163112_tgt(%P : _, %Y : _, %X : _, %C : _) -> i1 {
  ^bb0(%P : _, %Y : _, %X : _, %C : _):
    %v3 = llvm.icmp "ne" %X, %C : _
    llvm.return %v3 : i1
  }
  }]
