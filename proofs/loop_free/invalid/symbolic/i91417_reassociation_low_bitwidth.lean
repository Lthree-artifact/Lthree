import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i91417_reassociation_low_bitwidth_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i91417_reassociation_low_bitwidth_src(%v0 : _) -> _ {
  ^bb0(%v0 : _):
    %v2 = llvm.mul %v0, %v0 : _
    %v3 = llvm.mul %v2, %v0 : _
    %v4 = llvm.mul %v3, %v0 : _
    %v5 = llvm.mul %v4, %v0 overflow<nsw> : _
    llvm.return %v5 : _
  }
  }]

def i91417_reassociation_low_bitwidth_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i91417_reassociation_low_bitwidth_tgt(%v0 : _) -> _ {
  ^bb0(%v0 : _):
    %v2 = llvm.mul %v0, %v0 : _
    %v3 = llvm.mul %v2, %v0 overflow<nsw> : _
    llvm.return %v3 : _
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

theorem i91417_reassociation_low_bitwidth_correct_counterexample_witness : ¬ (i91417_reassociation_low_bitwidth_src 3 ⊑ i91417_reassociation_low_bitwidth_tgt 3) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (i91417_reassociation_low_bitwidth_src 3) (i91417_reassociation_low_bitwidth_tgt 3) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (i91417_reassociation_low_bitwidth_src 3) (i91417_reassociation_low_bitwidth_tgt 3)).mp h
  specialize hyp i91417_reassociation_low_bitwidth_cexInputs
  revert hyp
  decide

end i91417_reassociation_low_bitwidth_cex

theorem i91417_reassociation_low_bitwidth_correct_counterexample :
    ∃ (w : Nat), ¬ (i91417_reassociation_low_bitwidth_src w ⊑ i91417_reassociation_low_bitwidth_tgt w) :=
  ⟨3, i91417_reassociation_low_bitwidth_correct_counterexample_witness⟩
