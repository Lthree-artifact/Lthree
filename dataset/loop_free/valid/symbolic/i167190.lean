import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i167190_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167190_src(%arg0 : _, %arg1 : _, %C1 : _, %C2 : _) -> _ {
  ^bb0(%arg0 : _, %arg1 : _, %C1 : _, %C2 : _):
    %C1_f = llvm.freeze %C1 : _
    %C2_f = llvm.freeze %C2 : _
    %v0 = llvm.add %arg1, %arg0 : _
    %v1 = llvm.mul %arg0, %C1_f : _
    %v2 = llvm.mul %v0, %C2_f : _
    %v3 = llvm.sub %v1, %v2 : _
    llvm.return %v3 : _
  }
  }]

def i167190_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167190_tgt(%arg0 : _, %arg1 : _, %C1 : _, %C2 : _) -> _ {
  ^bb0(%arg0 : _, %arg1 : _, %C1 : _, %C2 : _):
    %C1_f = llvm.freeze %C1 : _
    %C2_f = llvm.freeze %C2 : _
    %subC = llvm.sub %C1_f, %C2_f : _
    %v0 = llvm.mul %arg0, %subC : _
    %v1 = llvm.mul %arg1, %C2_f : _
    %v2 = llvm.sub %v0, %v1 : _
    llvm.return %v2 : _
  }
  }]
