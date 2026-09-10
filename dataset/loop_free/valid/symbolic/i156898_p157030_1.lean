import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def trunc_shr_to_i1_src_with_precond_src (w1 : Nat)(_h : 0 < w1) :=
  [llvm(w1)| {
  llvm.func @trunc_shr_to_i1_src_with_precond_src(%V : _, %C : _) -> i1 {
  ^bb0(%V : _, %C : _):
    %one = llvm.mlir.constant(1 : _) : _
    %C_plus_1 = llvm.add %C, %one
    %is_pow2 = llvm.isPowerOf2 %C_plus_1 : _
    llvm.assume %is_pow2 : i1
    %shr = llvm.lshr %C, %V
    %r = llvm.trunc %shr : _ to i1
    llvm.return %r : i1
  }
  }]

def trunc_shr_to_i1_tgt_with_precond_tgt (w1 : Nat)(_h : 0 < w1) :=
  [llvm(w1)| {
  llvm.func @trunc_shr_to_i1_tgt_with_precond_tgt(%V : _, %C : _) -> i1 {
  ^bb0(%V : _, %C : _):
    %one = llvm.mlir.constant(1 : _) : _
    %C_plus_1 = llvm.add %C, %one
    %is_pow2 = llvm.isPowerOf2 %C_plus_1 : _
    llvm.assume %is_pow2 : i1
    %log2_C_plus_1 = llvm.ctpop %C
    %r = llvm.icmp "ult" %V, %log2_C_plus_1
    llvm.return %r : i1
  }
  }]
