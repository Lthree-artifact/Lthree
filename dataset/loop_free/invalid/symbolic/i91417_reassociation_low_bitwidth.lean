import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i91417_reassociation_low_bitwidth_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i91417_reassociation_low_bitwidth_src(%v0 : _) -> _ {
  ^bb0(%v0 : _):
    %v2 = llvm.mul %v0, %v0 : _
    %v3 = llvm.mul %v2, %v0 : _
    %v4 = llvm.mul %v3, %v0 : _
    %v5 = llvm.mul %v4, %v0 overflow<nsw> : _
    llvm.return %v5 : _
  }
  }]

def i91417_reassociation_low_bitwidth_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i91417_reassociation_low_bitwidth_tgt(%v0 : _) -> _ {
  ^bb0(%v0 : _):
    %v2 = llvm.mul %v0, %v0 : _
    %v3 = llvm.mul %v2, %v0 overflow<nsw> : _
    llvm.return %v3 : _
  }
  }]
