import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i163108_src (w : Nat) (_h : 2 ≤ w) :=
  [llvm(w)| {
  llvm.func @i163108_src(%arg0 : i1, %C1 : _, %C2 : _, %C3 : _) -> _ {
  ^bb0(%arg0 : i1, %C1 : _, %C2 : _, %C3 : _):
    %v0 = llvm.zext %arg0 : i1 to _
    %v1 = llvm.select %arg0, %C1, %C2 : _
    %v2 = llvm.or disjoint %v1, %v0 : _
    %v3 = llvm.or disjoint %v2, %C3 : _
    llvm.return %v3 : _
  }
  }]

def i163108_tgt (w : Nat) (_h : 2 ≤ w) :=
  [llvm(w)| {
  llvm.func @i163108_tgt(%arg0 : i1, %C1 : _, %C2 : _, %C3 : _) -> _ {
  ^bb0(%arg0 : i1, %C1 : _, %C2 : _, %C3 : _):
    %one = llvm.mlir.constant(1 : _) : _
    %t = llvm.or disjoint %C1, %one : _
    %t2 = llvm.or disjoint %t, %C3 : _
    %f = llvm.or disjoint %C2, %C3 : _
    %res = llvm.select %arg0, %t2, %f : _
    llvm.return %res : _
  }
  }]
