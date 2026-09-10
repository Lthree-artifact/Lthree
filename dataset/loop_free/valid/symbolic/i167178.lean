import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i167178_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167178_src(%V : _, %arg0 : _, %C2 : _) -> i1 {
  ^bb0(%V : _, %arg0 : _, %C2 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %cond_V = llvm.icmp "eq" %V, %zero : _
    %not_cond_arg = llvm.icmp "uge" %arg0, %C2 : _
    %assume_cond = llvm.or %not_cond_arg, %cond_V : i1
    llvm.assume %assume_cond : i1
    %v1 = llvm.add %V, %arg0 overflow<nuw> : _
    %v2 = llvm.icmp "ult" %v1, %C2 : _
    llvm.return %v2 : i1
  }
  }]

def i167178_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167178_tgt(%V : _, %arg0 : _, %C2 : _) -> i1 {
  ^bb0(%V : _, %arg0 : _, %C2 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %cond_V = llvm.icmp "eq" %V, %zero : _
    %not_cond_arg = llvm.icmp "uge" %arg0, %C2 : _
    %assume_cond = llvm.or %not_cond_arg, %cond_V : i1
    llvm.assume %assume_cond : i1
    %v2 = llvm.icmp "ult" %arg0, %C2 : _
    llvm.return %v2 : i1
  }
  }]
