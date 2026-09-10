import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr92949_fraction_simplify_sdiv_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr92949_fraction_simplify_sdiv_src(%a : _, %C1 : _, %C2 : _, %GCD : _, %g0 : _, %g1 : _, %g2 : _) -> _ {
  ^bb0(%a : _, %C1 : _, %C2 : _, %GCD : _, %g0 : _, %g1 : _, %g2 : _):
    %noZero = llvm.icmp "ne" %C2, %g0 : _
    %noMin = llvm.icmp "ne" %C1, %g1 : _
    %noMinNeg = llvm.icmp "ne" %C2, %g2 : _
    %noMinC = llvm.icmp "ne" %C2, %g1 : _
    %GCDPositive = llvm.icmp "sgt" %GCD, %g0 : _
    %C1Rem = llvm.srem %C1, %GCD : _
    %C2Rem = llvm.srem %C2, %GCD : _
    %isBrem = llvm.icmp "eq" %C1Rem, %g0 : _
    %isCrem = llvm.icmp "eq" %C2Rem, %g0 : _
    llvm.assume %noZero : i1
    llvm.assume %GCDPositive : i1
    llvm.assume %noMin : i1
    llvm.assume %noMinNeg : i1
    llvm.assume %noMinC : i1
    llvm.assume %isBrem : i1
    llvm.assume %isCrem : i1
    %mul = llvm.mul %C1, %a overflow<nsw> : _
    %div = llvm.sdiv %mul, %C2 : _
    llvm.return %div : _
  }
  }]

def pr92949_fraction_simplify_sdiv_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr92949_fraction_simplify_sdiv_tgt(%a : _, %C1 : _, %C2 : _, %GCD : _, %g0 : _, %g1 : _, %g2 : _) -> _ {
  ^bb0(%a : _, %C1 : _, %C2 : _, %GCD : _, %g0 : _, %g1 : _, %g2 : _):
    %noZero = llvm.icmp "ne" %C2, %g0 : _
    %noMin = llvm.icmp "ne" %C1, %g1 : _
    %noMinNeg = llvm.icmp "ne" %C2, %g2 : _
    %noMinC = llvm.icmp "ne" %C2, %g1 : _
    %GCDPositive = llvm.icmp "sgt" %GCD, %g0 : _
    %C1Rem = llvm.srem %C1, %GCD : _
    %C2Rem = llvm.srem %C2, %GCD : _
    %isBrem = llvm.icmp "eq" %C1Rem, %g0 : _
    %isCrem = llvm.icmp "eq" %C2Rem, %g0 : _
    llvm.assume %noZero : i1
    llvm.assume %GCDPositive : i1
    llvm.assume %noMin : i1
    llvm.assume %noMinNeg : i1
    llvm.assume %noMinC : i1
    llvm.assume %isBrem : i1
    llvm.assume %isCrem : i1
    %newB = llvm.sdiv %C1, %GCD : _
    %div = llvm.sdiv %C2, %GCD : _
    %mul = llvm.mul %newB, %a overflow<nsw> : _
    %divr = llvm.sdiv %mul, %div : _
    llvm.return %divr : _
  }
  }]
