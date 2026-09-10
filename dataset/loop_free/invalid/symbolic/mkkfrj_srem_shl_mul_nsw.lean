import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def mkkfrj_srem_shl_mul_nsw_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @mkkfrj_srem_shl_mul_nsw_src(%x : _, %y : _, %z : _) -> _ {
  ^bb0(%x : _, %y : _, %z : _):
    %c_i64_1 = llvm.mlir.constant(1 : _) : _
    %yy = llvm.shl %c_i64_1, %y : _
    %cond = llvm.icmp "uge" %yy, %z : _
    llvm.assume %cond : i1
    %mul1 = llvm.shl %x, %y overflow<nsw> : _
    %mul2 = llvm.mul %x, %z overflow<nsw> : _
    %rem = llvm.srem %mul1, %mul2 : _
    llvm.return %rem : _
  }
  }]

def mkkfrj_srem_shl_mul_nsw_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @mkkfrj_srem_shl_mul_nsw_tgt(%x : _, %y : _, %z : _) -> _ {
  ^bb0(%x : _, %y : _, %z : _):
    %c_i64_1 = llvm.mlir.constant(1 : _) : _
    %yy = llvm.shl %c_i64_1, %y : _
    %rem = llvm.srem %yy, %z : _
    %mul = llvm.mul %x, %rem overflow<nsw> : _
    llvm.return %mul : _
  }
  }]
