import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i115458_InstCombine_mul_sext_X_Y_se_src :=
  [llvm()| {
  llvm.func @i115458_InstCombine_mul_sext_X_Y_se_src(%a : i8, %b : i1, %x : i8) -> i8 {
  ^bb0(%a : i8, %b : i1, %x : i8):
    %v1 = llvm.sext %b : i1 to i8
    %v2 = llvm.mul %a, %v1 overflow<nsw> : i8
    %v3 = llvm.select %b, %v2, %a : i8
    %v4 = llvm.sub %v1, %v3 : i8
    %f = llvm.mul %x, %v1 overflow<nuw> : i8
    %r = llvm.add %f, %v4 : i8
    llvm.return %r : i8
  }
  }]

def i115458_InstCombine_mul_sext_X_Y_se_tgt :=
  [llvm()| {
  llvm.func @i115458_InstCombine_mul_sext_X_Y_se_tgt(%a : i8, %b : i1, %x : i8) -> i8 {
  ^bb0(%a : i8, %b : i1, %x : i8):
    %c_i8_0 = llvm.mlir.constant(0 : i8) : i8
    %v1 = llvm.sub %c_i8_0, %a overflow<nsw> : i8
    %c_i8_255 = llvm.mlir.constant(255 : i8) : i8
    %v2 = llvm.xor %x, %c_i8_255 : i8
    %v3 = llvm.add %a, %v2 : i8
    %r = llvm.select %b, %v3, %v1 : i8
    llvm.return %r : i8
  }
  }]

section i115458_InstCombine_mul_sext_X_Y_se_cex

def i115458_InstCombine_mul_sext_X_Y_se_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def i115458_InstCombine_mul_sext_X_Y_se_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def i115458_InstCombine_mul_sext_X_Y_se_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => i115458_InstCombine_mul_sext_X_Y_se_ivCons x (i115458_InstCombine_mul_sext_X_Y_se_ivOfHVector xs)

@[simp] theorem i115458_InstCombine_mul_sext_X_Y_se_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    i115458_InstCombine_mul_sext_X_Y_se_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [i115458_InstCombine_mul_sext_X_Y_se_ivOfHVector, i115458_InstCombine_mul_sext_X_Y_se_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [i115458_InstCombine_mul_sext_X_Y_se_ivOfHVector, i115458_InstCombine_mul_sext_X_Y_se_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance i115458_InstCombine_mul_sext_X_Y_se_decRefSemVal (a b : LLVM.SemVal (BitVec 8)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance i115458_InstCombine_mul_sext_X_Y_se_decRefIntW (a b : LLVM.IntW 8) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 8)) (LLVM.SemVal (BitVec 8)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance i115458_InstCombine_mul_sext_X_Y_se_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 8)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 8)) (ImmediateUBOr (LLVM.IntW 8))
        inferInstance a b) := inferInstance
  exact d

local instance i115458_InstCombine_mul_sext_X_Y_se_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance i115458_InstCombine_mul_sext_X_Y_se_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def i115458_InstCombine_mul_sext_X_Y_se_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 8, InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec 8]) :=
  i115458_InstCombine_mul_sext_X_Y_se_ivOfHVector
    (.cons (i115458_InstCombine_mul_sext_X_Y_se_valueOfNat 8 0) (.cons (i115458_InstCombine_mul_sext_X_Y_se_valueOfNat 1 0) (.cons (i115458_InstCombine_mul_sext_X_Y_se_valueOfNat 8 128) .nil)))

theorem i115458_InstCombine_mul_sext_X_Y_se_correct_counterexample_witness : ¬ (i115458_InstCombine_mul_sext_X_Y_se_src ⊑ i115458_InstCombine_mul_sext_X_Y_se_tgt) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (i115458_InstCombine_mul_sext_X_Y_se_src) (i115458_InstCombine_mul_sext_X_Y_se_tgt) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (i115458_InstCombine_mul_sext_X_Y_se_src) (i115458_InstCombine_mul_sext_X_Y_se_tgt)).mp h
  specialize hyp i115458_InstCombine_mul_sext_X_Y_se_cexInputs
  revert hyp
  decide

end i115458_InstCombine_mul_sext_X_Y_se_cex

theorem i115458_InstCombine_mul_sext_X_Y_se_correct_counterexample : ¬ (i115458_InstCombine_mul_sext_X_Y_se_src ⊑ i115458_InstCombine_mul_sext_X_Y_se_tgt) :=
  i115458_InstCombine_mul_sext_X_Y_se_correct_counterexample_witness
