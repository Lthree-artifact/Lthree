import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i167079_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167079_src(%arg0 : _, %C : _, %C1 : _, %C2 : _) -> i1 {
  ^bb0(%arg0 : _, %C : _, %C1 : _, %C2 : _):
    %cond1 = llvm.icmp "slt" %C1, %C : _
    %cond2 = llvm.icmp "sge" %C2, %C : _
    %cond3 = llvm.and %cond1, %cond2 : i1
    %cond4 = llvm.icmp "eq" %C1, %C2 : _
    %cond = llvm.or %cond3, %cond4 : i1
    llvm.assume %cond : i1
    %v0 = llvm.icmp "slt" %arg0, %C : _
    %v1 = llvm.select %v0, %C1, %C2 : _
    %v2 = llvm.sub %arg0, %v1 : _
    %zero = llvm.mlir.constant(0 : _) : _
    %v3 = llvm.icmp "eq" %v2, %zero : _
    llvm.return %v3 : i1
  }
  }]

def i167079_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167079_tgt(%arg0 : _, %C : _, %C1 : _, %C2 : _) -> i1 {
  ^bb0(%arg0 : _, %C : _, %C1 : _, %C2 : _):
    %cond1 = llvm.icmp "slt" %C1, %C : _
    %cond2 = llvm.icmp "sge" %C2, %C : _
    %cond3 = llvm.and %cond1, %cond2 : i1
    %cond4 = llvm.icmp "eq" %C1, %C2 : _
    %cond = llvm.or %cond3, %cond4 : i1
    llvm.assume %cond : i1
    %v0 = llvm.icmp "eq" %arg0, %C1 : _
    %v1 = llvm.icmp "eq" %arg0, %C2 : _
    %v2 = llvm.or %v0, %v1 : i1
    llvm.return %v2 : i1
  }
  }]
