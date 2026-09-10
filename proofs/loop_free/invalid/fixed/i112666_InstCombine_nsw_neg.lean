import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i112666_InstCombine_nsw_neg_src :=
  [llvm()| {
  llvm.func @i112666_InstCombine_nsw_neg_src(%x : i8, %y : i8, %c : i1) -> i8 {
  ^bb0(%x : i8, %y : i8, %c : i1):
    %c_i8_0 = llvm.mlir.constant(0 : i8) : i8
    %t0 = llvm.sub %c_i8_0, %x overflow<nsw> : i8
    %t1 = llvm.select %c, %t0, %x : i8
    %t2 = llvm.sub %y, %t1 : i8
    llvm.return %t2 : i8
  }
  }]

def i112666_InstCombine_nsw_neg_tgt :=
  [llvm()| {
  llvm.func @i112666_InstCombine_nsw_neg_tgt(%x : i8, %y : i8, %c : i1) -> i8 {
  ^bb0(%x : i8, %y : i8, %c : i1):
    %c_i8_0 = llvm.mlir.constant(0 : i8) : i8
    %t0 = llvm.sub %c_i8_0, %x overflow<nsw> : i8
    %1 = llvm.select %c, %x, %t0 : i8
    %t2 = llvm.add %1, %y : i8
    llvm.return %t2 : i8
  }
  }]

section i112666_InstCombine_nsw_neg_cex

def i112666_InstCombine_nsw_neg_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def i112666_InstCombine_nsw_neg_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def i112666_InstCombine_nsw_neg_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => i112666_InstCombine_nsw_neg_ivCons x (i112666_InstCombine_nsw_neg_ivOfHVector xs)

@[simp] theorem i112666_InstCombine_nsw_neg_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    i112666_InstCombine_nsw_neg_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [i112666_InstCombine_nsw_neg_ivOfHVector, i112666_InstCombine_nsw_neg_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [i112666_InstCombine_nsw_neg_ivOfHVector, i112666_InstCombine_nsw_neg_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance i112666_InstCombine_nsw_neg_decRefSemVal (a b : LLVM.SemVal (BitVec 8)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance i112666_InstCombine_nsw_neg_decRefIntW (a b : LLVM.IntW 8) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 8)) (LLVM.SemVal (BitVec 8)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance i112666_InstCombine_nsw_neg_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 8)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 8)) (ImmediateUBOr (LLVM.IntW 8))
        inferInstance a b) := inferInstance
  exact d

local instance i112666_InstCombine_nsw_neg_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance i112666_InstCombine_nsw_neg_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def i112666_InstCombine_nsw_neg_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec 8, InstCombine.LLVM.Ty.bitvec 8]) :=
  i112666_InstCombine_nsw_neg_ivOfHVector
    (.cons (i112666_InstCombine_nsw_neg_valueOfNat 1 0) (.cons (i112666_InstCombine_nsw_neg_valueOfNat 8 0) (.cons (i112666_InstCombine_nsw_neg_valueOfNat 8 128) .nil)))

theorem i112666_InstCombine_nsw_neg_correct_counterexample_witness : ¬ (i112666_InstCombine_nsw_neg_src ⊑ i112666_InstCombine_nsw_neg_tgt) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (i112666_InstCombine_nsw_neg_src) (i112666_InstCombine_nsw_neg_tgt) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (i112666_InstCombine_nsw_neg_src) (i112666_InstCombine_nsw_neg_tgt)).mp h
  specialize hyp i112666_InstCombine_nsw_neg_cexInputs
  revert hyp
  decide

end i112666_InstCombine_nsw_neg_cex

theorem i112666_InstCombine_nsw_neg_correct_counterexample : ¬ (i112666_InstCombine_nsw_neg_src ⊑ i112666_InstCombine_nsw_neg_tgt) :=
  i112666_InstCombine_nsw_neg_correct_counterexample_witness
