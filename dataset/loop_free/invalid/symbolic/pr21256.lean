import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr21256_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr21256_src(%X : _, %Op0 : _) -> _ {
  ^bb0(%X : _, %Op0 : _):
    %c_i8_0 = llvm.mlir.constant(0 : _) : _
    %Op1 = llvm.sub %c_i8_0, %X : _
    %r = llvm.srem %Op0, %Op1 : _
    llvm.return %r : _
  }
  }]

def pr21256_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr21256_tgt(%X : _, %Op0 : _) -> _ {
  ^bb0(%X : _, %Op0 : _):
    %r = llvm.srem %Op0, %X : _
    llvm.return %r : _
  }
  }]
