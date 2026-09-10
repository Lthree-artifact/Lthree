import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr21256_src :=
  [llvm()| {
  llvm.func @pr21256_src(%X : i8, %Op0 : i8) -> i8 {
  ^bb0(%X : i8, %Op0 : i8):
    %c_i8_0 = llvm.mlir.constant(0 : i8) : i8
    %Op1 = llvm.sub %c_i8_0, %X : i8
    %r = llvm.srem %Op0, %Op1 : i8
    llvm.return %r : i8
  }
  }]

def pr21256_tgt :=
  [llvm()| {
  llvm.func @pr21256_tgt(%X : i8, %Op0 : i8) -> i8 {
  ^bb0(%X : i8, %Op0 : i8):
    %r = llvm.srem %Op0, %X : i8
    llvm.return %r : i8
  }
  }]
