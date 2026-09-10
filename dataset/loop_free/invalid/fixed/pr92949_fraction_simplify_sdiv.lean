import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr92949_fraction_simplify_sdiv_src :=
  [llvm()| {
  llvm.func @pr92949_fraction_simplify_sdiv_src(%a : i64, %C1 : i64, %C2 : i64, %GCD : i64, %g0 : i64, %g1 : i64, %g2 : i64) -> i64 {
  ^bb0(%a : i64, %C1 : i64, %C2 : i64, %GCD : i64, %g0 : i64, %g1 : i64, %g2 : i64):
    %noZero = llvm.icmp "ne" %C2, %g0 : i64
    %noMin = llvm.icmp "ne" %C1, %g1 : i64
    %noMinNeg = llvm.icmp "ne" %C2, %g2 : i64
    %noMinC = llvm.icmp "ne" %C2, %g1 : i64
    %GCDPositive = llvm.icmp "sgt" %GCD, %g0 : i64
    %C1Rem = llvm.srem %C1, %GCD : i64
    %C2Rem = llvm.srem %C2, %GCD : i64
    %isBrem = llvm.icmp "eq" %C1Rem, %g0 : i64
    %isCrem = llvm.icmp "eq" %C2Rem, %g0 : i64
    llvm.assume %noZero : i1
    llvm.assume %GCDPositive : i1
    llvm.assume %noMin : i1
    llvm.assume %noMinNeg : i1
    llvm.assume %noMinC : i1
    llvm.assume %isBrem : i1
    llvm.assume %isCrem : i1
    %mul = llvm.mul %C1, %a overflow<nsw> : i64
    %div = llvm.sdiv %mul, %C2 : i64
    llvm.return %div : i64
  }
  }]

def pr92949_fraction_simplify_sdiv_tgt :=
  [llvm()| {
  llvm.func @pr92949_fraction_simplify_sdiv_tgt(%a : i64, %C1 : i64, %C2 : i64, %GCD : i64, %g0 : i64, %g1 : i64, %g2 : i64) -> i64 {
  ^bb0(%a : i64, %C1 : i64, %C2 : i64, %GCD : i64, %g0 : i64, %g1 : i64, %g2 : i64):
    %noZero = llvm.icmp "ne" %C2, %g0 : i64
    %noMin = llvm.icmp "ne" %C1, %g1 : i64
    %noMinNeg = llvm.icmp "ne" %C2, %g2 : i64
    %noMinC = llvm.icmp "ne" %C2, %g1 : i64
    %GCDPositive = llvm.icmp "sgt" %GCD, %g0 : i64
    %C1Rem = llvm.srem %C1, %GCD : i64
    %C2Rem = llvm.srem %C2, %GCD : i64
    %isBrem = llvm.icmp "eq" %C1Rem, %g0 : i64
    %isCrem = llvm.icmp "eq" %C2Rem, %g0 : i64
    llvm.assume %noZero : i1
    llvm.assume %GCDPositive : i1
    llvm.assume %noMin : i1
    llvm.assume %noMinNeg : i1
    llvm.assume %noMinC : i1
    llvm.assume %isBrem : i1
    llvm.assume %isCrem : i1
    %newB = llvm.sdiv %C1, %GCD : i64
    %div = llvm.sdiv %C2, %GCD : i64
    %mul = llvm.mul %newB, %a overflow<nsw> : i64
    %divr = llvm.sdiv %mul, %div : i64
    llvm.return %divr : i64
  }
  }]
