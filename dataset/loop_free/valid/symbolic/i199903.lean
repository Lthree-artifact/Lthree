import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i199903_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i199903_src(%newvar_idx : _, %C : _, %isnull : i1, %len : _) -> _ {
  ^bb0(%newvar_idx : _, %C : _, %isnull : i1, %len : _):
    %true = llvm.mlir.constant(true) : i1
    %notnpos = llvm.icmp "ne" %newvar_idx, %C : _
    %memchr_post = llvm.or %isnull, %notnpos : i1
    llvm.assume %memchr_post : i1
    %isnpos = llvm.icmp "eq" %newvar_idx, %C : _
    %cond = llvm.select %isnull, %true, %isnpos : i1
    %r = llvm.select %cond, %len, %newvar_idx : _
    llvm.return %r : _
  }
  }]

def i199903_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i199903_tgt(%newvar_idx : _, %C : _, %isnull : i1, %len : _) -> _ {
  ^bb0(%newvar_idx : _, %C : _, %isnull : i1, %len : _):
    %r = llvm.select %isnull, %len, %newvar_idx : _
    llvm.return %r : _
  }
  }]
