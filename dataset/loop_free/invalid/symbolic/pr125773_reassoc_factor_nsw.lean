import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr125773_reassoc_factor_nsw_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr125773_reassoc_factor_nsw_src(%X1 : _, %X2 : _, %g0 : _, %g1 : _) -> _ {
  ^bb0(%X1 : _, %X2 : _, %g0 : _, %g1 : _):
    %A = llvm.add %X1, %g0 overflow<nsw> : _
    %B = llvm.mul %X2, %g1 overflow<nsw> : _
    %C = llvm.mul %X2, %A overflow<nsw> : _
    %D = llvm.add %B, %C overflow<nsw> : _
    llvm.return %D : _
  }
  }]

def pr125773_reassoc_factor_nsw_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr125773_reassoc_factor_nsw_tgt(%X1 : _, %X2 : _, %g0 : _, %g1 : _) -> _ {
  ^bb0(%X1 : _, %X2 : _, %g0 : _, %g1 : _):
    %c_i64_67 = llvm.mlir.constant(67 : _) : _
    %reass_add = llvm.add %X1, %c_i64_67 : _
    %reass_mul = llvm.mul %reass_add, %X2 overflow<nsw> : _
    llvm.return %reass_mul : _
  }
  }]
