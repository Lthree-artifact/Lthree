import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i152237_a2n_src :=
  [llvm()| {
  llvm.func @i152237_a2n_src(%0 : i8) -> i8 {
  ^bb0(%0 : i8):
    %c_8_40 = llvm.mlir.constant(40 : i8) : i8
    %2 = llvm.mul %0, %c_8_40 overflow<nsw> : i8
    %c_8_m40 = llvm.mlir.constant(-40 : i8) : i8
    %3 = llvm.add %2, %c_8_m40 overflow<nsw> : i8
    %4 = llvm.udiv exact %3, %c_8_40 : i8
    llvm.return %4 : i8
  }
  }]

def i152237_a2n_tgt :=
  [llvm()| {
  llvm.func @i152237_a2n_tgt(%0 : i8) -> i8 {
  ^bb0(%0 : i8):
    %c_8_1 = llvm.mlir.constant(1 : i8) : i8
    %2 = llvm.sub %0, %c_8_1 overflow<nsw> : i8
    llvm.return %2 : i8
  }
  }]
