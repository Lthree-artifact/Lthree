import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i121584_InstCombine_simplifyIRemMul_src :=
  [llvm()| {
  llvm.func @i121584_InstCombine_simplifyIRemMul_src(%X : i8) -> i8 {
  ^bb0(%X : i8):
    %c_i8_127 = llvm.mlir.constant(127 : i8) : i8
    %BO0 = llvm.mul %X, %c_i8_127 overflow<nsw> : i8
    %c_i8_7 = llvm.mlir.constant(7 : i8) : i8
    %BO1 = llvm.shl %X, %c_i8_7 overflow<nsw> : i8
    %r = llvm.srem %BO1, %BO0 : i8
    llvm.return %r : i8
  }
  }]

def i121584_InstCombine_simplifyIRemMul_tgt :=
  [llvm()| {
  llvm.func @i121584_InstCombine_simplifyIRemMul_tgt(%X : i8) -> i8 {
  ^bb0(%X : i8):
    %c_i8_0 = llvm.mlir.constant(0 : i8) : i8
    %r = llvm.sub %c_i8_0, %X overflow<nsw> : i8
    llvm.return %r : i8
  }
  }]
