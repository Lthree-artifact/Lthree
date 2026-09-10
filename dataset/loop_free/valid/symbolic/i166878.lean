import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i166878_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i166878_src(%C1 : _, %arg0 : _, %arg1 : _) -> _ {
  ^bb0(%C1 : _, %arg0 : _, %arg1 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %cond = llvm.icmp "sge" %C1, %zero : _
    llvm.assume %cond : i1
    %v0 = llvm.sub %C1, %arg1 overflow<nsw> : _
    %c1 = llvm.icmp "sgt" %arg0, %v0 : _
    %v1 = llvm.select %c1, %arg0, %v0 : _
    %v2 = llvm.add %v1, %arg1 overflow<nsw,nuw> : _
    llvm.return %v2 : _
  }
  }]

def i166878_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i166878_tgt(%C1 : _, %arg0 : _, %arg1 : _) -> _ {
  ^bb0(%C1 : _, %arg0 : _, %arg1 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %cond = llvm.icmp "sge" %C1, %zero : _
    llvm.assume %cond : i1
    %v0 = llvm.add %arg0, %arg1 : _
    %c1 = llvm.icmp "sgt" %v0, %C1 : _
    %v1 = llvm.select %c1, %v0, %C1 : _
    llvm.return %v1 : _
  }
  }]
