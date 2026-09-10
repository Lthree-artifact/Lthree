import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i91417_reassociation_low_bitwidth_src :=
  [llvm()| {
  llvm.func @i91417_reassociation_low_bitwidth_src(%v0 : i3) -> i3 {
  ^bb0(%v0 : i3):
    %v2 = llvm.mul %v0, %v0 : i3
    %v3 = llvm.mul %v2, %v0 : i3
    %v4 = llvm.mul %v3, %v0 : i3
    %v5 = llvm.mul %v4, %v0 overflow<nsw> : i3
    llvm.return %v5 : i3
  }
  }]

def i91417_reassociation_low_bitwidth_tgt :=
  [llvm()| {
  llvm.func @i91417_reassociation_low_bitwidth_tgt(%v0 : i3) -> i3 {
  ^bb0(%v0 : i3):
    %v2 = llvm.mul %v0, %v0 : i3
    %v3 = llvm.mul %v2, %v0 overflow<nsw> : i3
    llvm.return %v3 : i3
  }
  }]
