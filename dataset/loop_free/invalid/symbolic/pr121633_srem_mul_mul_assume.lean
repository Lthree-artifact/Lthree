import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr121633_srem_mul_mul_assume_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr121633_srem_mul_mul_assume_src(%x : _, %y : _, %z : _) -> _ {
  ^bb0(%x : _, %y : _, %z : _):
    %remc = llvm.srem %y, %z : _
    %cond = llvm.icmp "eq" %remc, %y : _
    llvm.assume %cond : i1
    %mul1 = llvm.mul %x, %y : _
    %mul2 = llvm.mul %x, %z : _
    %rem = llvm.srem %mul1, %mul2 : _
    llvm.return %rem : _
  }
  }]

def pr121633_srem_mul_mul_assume_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr121633_srem_mul_mul_assume_tgt(%x : _, %y : _, %z : _) -> _ {
  ^bb0(%x : _, %y : _, %z : _):
    %mul = llvm.mul %x, %y : _
    llvm.return %mul : _
  }
  }]
