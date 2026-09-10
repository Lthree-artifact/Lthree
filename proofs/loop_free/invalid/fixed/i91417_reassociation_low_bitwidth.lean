import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i91417_reassociation_low_bitwidth_src :=
  [llvm()| {
  llvm.func @i91417_reassociation_low_bitwidth_src(%v0 : i3) -> i3 {
  ^bb0(%v0 : i3):
    %v2 = llvm.mul %v0, %v0 : i3
    %v3 = llvm.mul %v2, %v0 : i3
    %v4 = llvm.mul %v3, %v0 : i3
    %v5 = llvm.mul %v4, %v0 overflow<nsw> : i3
    llvm.return %v5 : i3
  }
  }]

def i91417_reassociation_low_bitwidth_tgt :=
  [llvm()| {
  llvm.func @i91417_reassociation_low_bitwidth_tgt(%v0 : i3) -> i3 {
  ^bb0(%v0 : i3):
    %v2 = llvm.mul %v0, %v0 : i3
    %v3 = llvm.mul %v2, %v0 overflow<nsw> : i3
    llvm.return %v3 : i3
  }
  }]

section i91417_reassociation_low_bitwidth_cex

def i91417_reassociation_low_bitwidth_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def i91417_reassociation_low_bitwidth_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def i91417_reassociation_low_bitwidth_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => i91417_reassociation_low_bitwidth_ivCons x (i91417_reassociation_low_bitwidth_ivOfHVector xs)

@[simp] theorem i91417_reassociation_low_bitwidth_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    i91417_reassociation_low_bitwidth_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [i91417_reassociation_low_bitwidth_ivOfHVector, i91417_reassociation_low_bitwidth_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [i91417_reassociation_low_bitwidth_ivOfHVector, i91417_reassociation_low_bitwidth_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance i91417_reassociation_low_bitwidth_decRefSemVal (a b : LLVM.SemVal (BitVec 3)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance i91417_reassociation_low_bitwidth_decRefIntW (a b : LLVM.IntW 3) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 3)) (LLVM.SemVal (BitVec 3)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance i91417_reassociation_low_bitwidth_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 3)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 3)) (ImmediateUBOr (LLVM.IntW 3))
        inferInstance a b) := inferInstance
  exact d

local instance i91417_reassociation_low_bitwidth_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance i91417_reassociation_low_bitwidth_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def i91417_reassociation_low_bitwidth_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 3]) :=
  i91417_reassociation_low_bitwidth_ivOfHVector
    (.cons (i91417_reassociation_low_bitwidth_valueOfNat 3 2) .nil)

theorem i91417_reassociation_low_bitwidth_correct_counterexample_witness : ¬ (i91417_reassociation_low_bitwidth_src ⊑ i91417_reassociation_low_bitwidth_tgt) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (i91417_reassociation_low_bitwidth_src) (i91417_reassociation_low_bitwidth_tgt) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (i91417_reassociation_low_bitwidth_src) (i91417_reassociation_low_bitwidth_tgt)).mp h
  specialize hyp i91417_reassociation_low_bitwidth_cexInputs
  revert hyp
  decide

end i91417_reassociation_low_bitwidth_cex

theorem i91417_reassociation_low_bitwidth_correct_counterexample : ¬ (i91417_reassociation_low_bitwidth_src ⊑ i91417_reassociation_low_bitwidth_tgt) :=
  i91417_reassociation_low_bitwidth_correct_counterexample_witness
