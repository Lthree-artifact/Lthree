import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i121584_InstCombine_simplifyIRemMul_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i121584_InstCombine_simplifyIRemMul_src(%X : _) -> _ {
  ^bb0(%X : _):
    %c_i8_127 = llvm.mlir.constant(127 : _) : _
    %BO0 = llvm.mul %X, %c_i8_127 overflow<nsw> : _
    %c_i8_7 = llvm.mlir.constant(7 : _) : _
    %BO1 = llvm.shl %X, %c_i8_7 overflow<nsw> : _
    %r = llvm.srem %BO1, %BO0 : _
    llvm.return %r : _
  }
  }]

def i121584_InstCombine_simplifyIRemMul_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i121584_InstCombine_simplifyIRemMul_tgt(%X : _) -> _ {
  ^bb0(%X : _):
    %c_i8_0 = llvm.mlir.constant(0 : _) : _
    %r = llvm.sub %c_i8_0, %X overflow<nsw> : _
    llvm.return %r : _
  }
  }]
