import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def d158510_negate_nsw_shl_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @d158510_negate_nsw_shl_src(%a : _, %shamt : _) -> _ {
  ^bb0(%a : _, %shamt : _):
    %c_i64_1 = llvm.mlir.constant(1 : _) : _
    %pow2 = llvm.shl %c_i64_1, %shamt : _
    %c_i64_0 = llvm.mlir.constant(0 : _) : _
    %neg_pow2 = llvm.sub %c_i64_0, %pow2 : _
    %mul = llvm.mul %a, %neg_pow2 overflow<nsw> : _
    llvm.return %mul : _
  }
  }]

def d158510_negate_nsw_shl_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @d158510_negate_nsw_shl_tgt(%a : _, %shamt : _) -> _ {
  ^bb0(%a : _, %shamt : _):
    %c_i64_1 = llvm.mlir.constant(1 : _) : _
    %pow2 = llvm.shl %c_i64_1, %shamt : _
    %c_i64_0 = llvm.mlir.constant(0 : _) : _
    %a_neg = llvm.sub %c_i64_0, %a overflow<nsw> : _
    %mul = llvm.mul %a_neg, %pow2 overflow<nsw> : _
    llvm.return %mul : _
  }
  }]
