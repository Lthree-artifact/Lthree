import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i202249_src (w1 : Nat) (_h : 2 ≤ w1) :=
  [llvm(w1)| {
  llvm.func @i202249_src(%V : w1, %C1 : w1, %C2 : w1) -> w1 {
  ^bb0(%V : w1, %C1 : w1, %C2 : w1):
    %bw = llvm.mlir.constant(w1 : w1) : w1
    %one = llvm.mlir.constant(1 : w1) : w1
    %zero = llvm.mlir.constant(0 : w1) : w1
    %cm1 = llvm.mlir.constant(-1 : w1) : w1
    %sub = llvm.sub %bw, %one : w1
    %signbit = llvm.shl %one, %sub : w1
    %cond2_1 = llvm.icmp "eq" %C2, %zero : w1
    %cond2_2 = llvm.icmp "eq" %C2, %signbit : w1
    %cond2 = llvm.or %cond2_1, %cond2_2 : i1
    llvm.assume %cond2 : i1
    %notC2 = llvm.xor %C2, %cm1 : w1
    %v_and = llvm.and %V, %notC2 : w1
    %cond3 = llvm.icmp "eq" %v_and, %C1 : w1
    llvm.assume %cond3 : i1
    %b = llvm.sub %C1, %V : w1
    llvm.return %b : w1
  }
  }]

def i202249_tgt (w1 : Nat) (_h : 2 ≤ w1) :=
  [llvm(w1)| {
  llvm.func @i202249_tgt(%V : w1, %C1 : w1, %C2 : w1) -> w1 {
  ^bb0(%V : w1, %C1 : w1, %C2 : w1):
    %bw = llvm.mlir.constant(w1 : w1) : w1
    %one = llvm.mlir.constant(1 : w1) : w1
    %zero = llvm.mlir.constant(0 : w1) : w1
    %cm1 = llvm.mlir.constant(-1 : w1) : w1
    %sub = llvm.sub %bw, %one : w1
    %signbit = llvm.shl %one, %sub : w1
    %cond2_1 = llvm.icmp "eq" %C2, %zero : w1
    %cond2_2 = llvm.icmp "eq" %C2, %signbit : w1
    %cond2 = llvm.or %cond2_1, %cond2_2 : i1
    llvm.assume %cond2 : i1
    %notC2 = llvm.xor %C2, %cm1 : w1
    %v_and = llvm.and %V, %notC2 : w1
    %cond3 = llvm.icmp "eq" %v_and, %C1 : w1
    llvm.assume %cond3 : i1
    %a = llvm.and %V, %C2 : w1
    llvm.return %a : w1
  }
  }]
