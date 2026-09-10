import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def mkkfrj_srem_shl_mul_nsw_src :=
  [llvm()| {
  llvm.func @mkkfrj_srem_shl_mul_nsw_src(%x : i64, %y : i64, %z : i64) -> i64 {
  ^bb0(%x : i64, %y : i64, %z : i64):
    %c_i64_1 = llvm.mlir.constant(1 : i64) : i64
    %yy = llvm.shl %c_i64_1, %y : i64
    %cond = llvm.icmp "uge" %yy, %z : i64
    llvm.assume %cond : i1
    %mul1 = llvm.shl %x, %y overflow<nsw> : i64
    %mul2 = llvm.mul %x, %z overflow<nsw> : i64
    %rem = llvm.srem %mul1, %mul2 : i64
    llvm.return %rem : i64
  }
  }]

def mkkfrj_srem_shl_mul_nsw_tgt :=
  [llvm()| {
  llvm.func @mkkfrj_srem_shl_mul_nsw_tgt(%x : i64, %y : i64, %z : i64) -> i64 {
  ^bb0(%x : i64, %y : i64, %z : i64):
    %c_i64_1 = llvm.mlir.constant(1 : i64) : i64
    %yy = llvm.shl %c_i64_1, %y : i64
    %rem = llvm.srem %yy, %z : i64
    %mul = llvm.mul %x, %rem overflow<nsw> : i64
    llvm.return %mul : i64
  }
  }]
