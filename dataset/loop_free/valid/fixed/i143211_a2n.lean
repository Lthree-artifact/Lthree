import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i143211_a2n_src :=
  [llvm()| {
  llvm.func @i143211_a2n_src(%0 : i8, %1 : i8) -> i1 {
  ^bb0(%0 : i8, %1 : i8):
    %3 = llvm.sub %1, %0 overflow<nsw> : i8
    %4 = llvm.add %1, %0 overflow<nsw> : i8
    %5 = llvm.icmp "sgt" %3, %4 : i8
    llvm.return %5 : i1
  }
  }]

def i143211_a2n_tgt :=
  [llvm()| {
  llvm.func @i143211_a2n_tgt(%0 : i8, %1 : i8) -> i1 {
  ^bb0(%0 : i8, %1 : i8):
    %c_8_0 = llvm.mlir.constant(0 : i8) : i8
    %3 = llvm.icmp "slt" %0, %c_8_0 : i8
    llvm.return %3 : i1
  }
  }]
