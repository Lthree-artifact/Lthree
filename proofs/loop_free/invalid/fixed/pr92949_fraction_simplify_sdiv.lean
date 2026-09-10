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

section pr92949_fraction_simplify_sdiv_cex

def pr92949_fraction_simplify_sdiv_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def pr92949_fraction_simplify_sdiv_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def pr92949_fraction_simplify_sdiv_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => pr92949_fraction_simplify_sdiv_ivCons x (pr92949_fraction_simplify_sdiv_ivOfHVector xs)

@[simp] theorem pr92949_fraction_simplify_sdiv_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    pr92949_fraction_simplify_sdiv_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [pr92949_fraction_simplify_sdiv_ivOfHVector, pr92949_fraction_simplify_sdiv_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [pr92949_fraction_simplify_sdiv_ivOfHVector, pr92949_fraction_simplify_sdiv_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance pr92949_fraction_simplify_sdiv_decRefSemVal (a b : LLVM.SemVal (BitVec 64)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance pr92949_fraction_simplify_sdiv_decRefIntW (a b : LLVM.IntW 64) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 64)) (LLVM.SemVal (BitVec 64)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance pr92949_fraction_simplify_sdiv_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 64)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 64)) (ImmediateUBOr (LLVM.IntW 64))
        inferInstance a b) := inferInstance
  exact d

local instance pr92949_fraction_simplify_sdiv_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance pr92949_fraction_simplify_sdiv_decRefDenote
    (a : EffectKind.impure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]))
    (b : EffectKind.impure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]))
        inferInstance a b) := inferInstance
  exact d

def pr92949_fraction_simplify_sdiv_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64]) :=
  pr92949_fraction_simplify_sdiv_ivOfHVector
    (.cons (pr92949_fraction_simplify_sdiv_valueOfNat 64 0) (.cons (pr92949_fraction_simplify_sdiv_valueOfNat 64 0) (.cons (pr92949_fraction_simplify_sdiv_valueOfNat 64 1) (.cons (pr92949_fraction_simplify_sdiv_valueOfNat 64 2) (.cons (pr92949_fraction_simplify_sdiv_valueOfNat 64 3) (.cons (pr92949_fraction_simplify_sdiv_valueOfNat 64 1) (.cons (pr92949_fraction_simplify_sdiv_valueOfNat 64 3) .nil)))))))

theorem pr92949_fraction_simplify_sdiv_correct_counterexample_witness : ¬ (pr92949_fraction_simplify_sdiv_src ⊑ pr92949_fraction_simplify_sdiv_tgt) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (pr92949_fraction_simplify_sdiv_src) (pr92949_fraction_simplify_sdiv_tgt) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (pr92949_fraction_simplify_sdiv_src) (pr92949_fraction_simplify_sdiv_tgt)).mp h
  specialize hyp pr92949_fraction_simplify_sdiv_cexInputs
  revert hyp
  decide +kernel

end pr92949_fraction_simplify_sdiv_cex

theorem pr92949_fraction_simplify_sdiv_correct_counterexample : ¬ (pr92949_fraction_simplify_sdiv_src ⊑ pr92949_fraction_simplify_sdiv_tgt) :=
  pr92949_fraction_simplify_sdiv_correct_counterexample_witness
