import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i167059_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167059_src(%arg0 : _, %arg1 : _, %C : _) -> i1 {
  ^bb0(%arg0 : _, %arg1 : _, %C : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %v0 = llvm.sub %arg1, %arg0 overflow<nsw> : _
    %v1 = llvm.sub %C, %arg0 overflow<nsw> : _
    %c = llvm.icmp "slt" %v1, %v0 : _
    %v2 = llvm.select %c, %v1, %v0 : _
    %v3 = llvm.icmp "sgt" %v2, %zero : _
    llvm.return %v3 : i1
  }
  }]

def i167059_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167059_tgt(%arg0 : _, %arg1 : _, %C : _) -> i1 {
  ^bb0(%arg0 : _, %arg1 : _, %C : _):
    %v0 = llvm.icmp "slt" %arg0, %C : _
    %v1 = llvm.icmp "slt" %arg0, %arg1 : _
    %v2 = llvm.and %v0, %v1 : i1
    llvm.return %v2 : i1
  }
  }]
