import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def d102864_udivmul_srem_to_zero_src :=
  [llvm()| {
  llvm.func @d102864_udivmul_srem_to_zero_src(%a : i64, %y : i64) -> i64 {
  ^bb0(%a : i64, %y : i64):
    %x = llvm.udiv %a, %y : i64
    %mul = llvm.mul %x, %y : i64
    %mod = llvm.srem %mul, %y : i64
    llvm.return %mod : i64
  }
  }]

def d102864_udivmul_srem_to_zero_tgt :=
  [llvm()| {
  llvm.func @d102864_udivmul_srem_to_zero_tgt(%a : i64, %y : i64) -> i64 {
  ^bb0(%a : i64, %y : i64):
    %c_i64_0 = llvm.mlir.constant(0 : i64) : i64
    llvm.return %c_i64_0 : i64
  }
  }]

section d102864_udivmul_srem_to_zero_cex

def d102864_udivmul_srem_to_zero_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def d102864_udivmul_srem_to_zero_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def d102864_udivmul_srem_to_zero_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => d102864_udivmul_srem_to_zero_ivCons x (d102864_udivmul_srem_to_zero_ivOfHVector xs)

@[simp] theorem d102864_udivmul_srem_to_zero_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    d102864_udivmul_srem_to_zero_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [d102864_udivmul_srem_to_zero_ivOfHVector, d102864_udivmul_srem_to_zero_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [d102864_udivmul_srem_to_zero_ivOfHVector, d102864_udivmul_srem_to_zero_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance d102864_udivmul_srem_to_zero_decRefSemVal (a b : LLVM.SemVal (BitVec 64)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance d102864_udivmul_srem_to_zero_decRefIntW (a b : LLVM.IntW 64) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 64)) (LLVM.SemVal (BitVec 64)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance d102864_udivmul_srem_to_zero_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 64)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 64)) (ImmediateUBOr (LLVM.IntW 64))
        inferInstance a b) := inferInstance
  exact d

local instance d102864_udivmul_srem_to_zero_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance d102864_udivmul_srem_to_zero_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def d102864_udivmul_srem_to_zero_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64]) :=
  d102864_udivmul_srem_to_zero_ivOfHVector
    (.cons (d102864_udivmul_srem_to_zero_valueOfNat 64 3) (.cons (d102864_udivmul_srem_to_zero_valueOfNat 64 18446744073709551615) .nil))

theorem d102864_udivmul_srem_to_zero_correct_counterexample_witness : ¬ (d102864_udivmul_srem_to_zero_src ⊑ d102864_udivmul_srem_to_zero_tgt) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (d102864_udivmul_srem_to_zero_src) (d102864_udivmul_srem_to_zero_tgt) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (d102864_udivmul_srem_to_zero_src) (d102864_udivmul_srem_to_zero_tgt)).mp h
  specialize hyp d102864_udivmul_srem_to_zero_cexInputs
  revert hyp
  decide

end d102864_udivmul_srem_to_zero_cex

theorem d102864_udivmul_srem_to_zero_correct_counterexample : ¬ (d102864_udivmul_srem_to_zero_src ⊑ d102864_udivmul_srem_to_zero_tgt) :=
  d102864_udivmul_srem_to_zero_correct_counterexample_witness
