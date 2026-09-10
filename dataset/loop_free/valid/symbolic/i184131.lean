import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i184131_src (w : Nat) (_h : 2 ≤ w) :=
  [llvm(w)| {
  llvm.func @i184131_src(%x0 : _, %x1 : _, %C1 : _, %C2 : _, %C3 : _) -> _ {
  ^bb0(%x0 : _, %x1 : _, %C1 : _, %C2 : _, %C3 : _):
    %one = llvm.mlir.constant(1 : _) : _
    %shl = llvm.shl %one, %C1 : _
    %cond2 = llvm.icmp "eq" %C3, %shl : _
    llvm.assume %cond2 : i1
    %sub = llvm.sub %shl, %one : _
    %cond3 = llvm.icmp "eq" %C2, %sub : _
    llvm.assume %cond3 : i1
    %e1 = llvm.lshr %x0, %C1 : _
    %t = llvm.trunc %e1 : _ to i1
    %e2 = llvm.lshr %x1, %C1 : _
    %v0 = llvm.select %t, %e1, %e2 : _
    %v1 = llvm.select %t, %x0, %x1 : _
    %ext = llvm.and %v1, %C2 : _
    %ins = llvm.shl %v0, %C1 : _
    %r = llvm.or disjoint %ins, %ext : _
    llvm.return %r : _
  }
  }]

def i184131_tgt (w : Nat) (_h : 2 ≤ w) :=
  [llvm(w)| {
  llvm.func @i184131_tgt(%x0 : _, %x1 : _, %C1 : _, %C2 : _, %C3 : _) -> _ {
  ^bb0(%x0 : _, %x1 : _, %C1 : _, %C2 : _, %C3 : _):
    %one = llvm.mlir.constant(1 : _) : _
    %shl = llvm.shl %one, %C1 : _
    %cond2 = llvm.icmp "eq" %C3, %shl : _
    llvm.assume %cond2 : i1
    %sub = llvm.sub %shl, %one : _
    %cond3 = llvm.icmp "eq" %C2, %sub : _
    llvm.assume %cond3 : i1
    %zero = llvm.mlir.constant(0 : _) : _
    %hi = llvm.and %x0, %C3 : _
    %nn = llvm.icmp "eq" %hi, %zero : _
    %r = llvm.select %nn, %x1, %x0 : _
    llvm.return %r : _
  }
  }]
