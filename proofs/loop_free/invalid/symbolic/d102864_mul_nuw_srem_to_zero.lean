import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def d102864_mul_nuw_srem_to_zero_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @d102864_mul_nuw_srem_to_zero_src(%x : _, %y : _) -> _ {
  ^bb0(%x : _, %y : _):
    %mul = llvm.mul %x, %y overflow<nuw> : _
    %mod = llvm.srem %mul, %y : _
    llvm.return %mod : _
  }
  }]

def d102864_mul_nuw_srem_to_zero_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @d102864_mul_nuw_srem_to_zero_tgt(%x : _, %y : _) -> _ {
  ^bb0(%x : _, %y : _):
    %c_i64_0 = llvm.mlir.constant(0 : _) : _
    llvm.return %c_i64_0 : _
  }
  }]

section d102864_mul_nuw_srem_to_zero_cex

def d102864_mul_nuw_srem_to_zero_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def d102864_mul_nuw_srem_to_zero_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def d102864_mul_nuw_srem_to_zero_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => d102864_mul_nuw_srem_to_zero_ivCons x (d102864_mul_nuw_srem_to_zero_ivOfHVector xs)

@[simp] theorem d102864_mul_nuw_srem_to_zero_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    d102864_mul_nuw_srem_to_zero_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [d102864_mul_nuw_srem_to_zero_ivOfHVector, d102864_mul_nuw_srem_to_zero_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [d102864_mul_nuw_srem_to_zero_ivOfHVector, d102864_mul_nuw_srem_to_zero_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance d102864_mul_nuw_srem_to_zero_decRefSemVal (a b : LLVM.SemVal (BitVec 3)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance d102864_mul_nuw_srem_to_zero_decRefIntW (a b : LLVM.IntW 3) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 3)) (LLVM.SemVal (BitVec 3)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance d102864_mul_nuw_srem_to_zero_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 3)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 3)) (ImmediateUBOr (LLVM.IntW 3))
        inferInstance a b) := inferInstance
  exact d

local instance d102864_mul_nuw_srem_to_zero_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance d102864_mul_nuw_srem_to_zero_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def d102864_mul_nuw_srem_to_zero_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 3, InstCombine.LLVM.Ty.bitvec 3]) :=
  d102864_mul_nuw_srem_to_zero_ivOfHVector
    (.cons (d102864_mul_nuw_srem_to_zero_valueOfNat 3 3) (.cons (d102864_mul_nuw_srem_to_zero_valueOfNat 3 2) .nil))

theorem d102864_mul_nuw_srem_to_zero_correct_counterexample_witness : ¬ (d102864_mul_nuw_srem_to_zero_src 3 ⊑ d102864_mul_nuw_srem_to_zero_tgt 3) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (d102864_mul_nuw_srem_to_zero_src 3) (d102864_mul_nuw_srem_to_zero_tgt 3) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (d102864_mul_nuw_srem_to_zero_src 3) (d102864_mul_nuw_srem_to_zero_tgt 3)).mp h
  specialize hyp d102864_mul_nuw_srem_to_zero_cexInputs
  revert hyp
  decide

end d102864_mul_nuw_srem_to_zero_cex

theorem d102864_mul_nuw_srem_to_zero_correct_counterexample :
    ∃ (w : Nat), ¬ (d102864_mul_nuw_srem_to_zero_src w ⊑ d102864_mul_nuw_srem_to_zero_tgt w) :=
  ⟨3, d102864_mul_nuw_srem_to_zero_correct_counterexample_witness⟩
