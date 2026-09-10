import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i137937_ConstraintElim_checkOrAndOpImpliedByOther_src :=
  [llvm()| {
  llvm.func @i137937_ConstraintElim_checkOrAndOpImpliedByOther_src(%b : i8) -> i1 {
  ^bb0(%b : i8):
    %c_i8_1 = llvm.mlir.constant(1 : i8) : i8
    %c_1 = llvm.icmp "slt" %b, %c_i8_1 : i8
    %c_i8_0 = llvm.mlir.constant(0 : i8) : i8
    %c_2 = llvm.icmp "ne" %b, %c_i8_0 : i8
    %or = llvm.or disjoint %c_2, %c_1 : i1
    llvm.return %or : i1
  }
  }]

def i137937_ConstraintElim_checkOrAndOpImpliedByOther_tgt :=
  [llvm()| {
  llvm.func @i137937_ConstraintElim_checkOrAndOpImpliedByOther_tgt(%b : i8) -> i1 {
  ^bb0(%b : i8):
    %c_i8_0 = llvm.mlir.constant(0 : i8) : i8
    %c_2 = llvm.icmp "ne" %b, %c_i8_0 : i8
    %c_i1_1 = llvm.mlir.constant(1 : i1) : i1
    %or = llvm.or disjoint %c_2, %c_i1_1 : i1
    llvm.return %or : i1
  }
  }]

section i137937_ConstraintElim_checkOrAndOpImpliedByOther_cex

def i137937_ConstraintElim_checkOrAndOpImpliedByOther_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def i137937_ConstraintElim_checkOrAndOpImpliedByOther_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def i137937_ConstraintElim_checkOrAndOpImpliedByOther_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => i137937_ConstraintElim_checkOrAndOpImpliedByOther_ivCons x (i137937_ConstraintElim_checkOrAndOpImpliedByOther_ivOfHVector xs)

@[simp] theorem i137937_ConstraintElim_checkOrAndOpImpliedByOther_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    i137937_ConstraintElim_checkOrAndOpImpliedByOther_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [i137937_ConstraintElim_checkOrAndOpImpliedByOther_ivOfHVector, i137937_ConstraintElim_checkOrAndOpImpliedByOther_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [i137937_ConstraintElim_checkOrAndOpImpliedByOther_ivOfHVector, i137937_ConstraintElim_checkOrAndOpImpliedByOther_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance i137937_ConstraintElim_checkOrAndOpImpliedByOther_decRefSemVal (a b : LLVM.SemVal (BitVec 1)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance i137937_ConstraintElim_checkOrAndOpImpliedByOther_decRefIntW (a b : LLVM.IntW 1) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 1)) (LLVM.SemVal (BitVec 1)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance i137937_ConstraintElim_checkOrAndOpImpliedByOther_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 1)) (ImmediateUBOr (LLVM.IntW 1))
        inferInstance a b) := inferInstance
  exact d

local instance i137937_ConstraintElim_checkOrAndOpImpliedByOther_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance i137937_ConstraintElim_checkOrAndOpImpliedByOther_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def i137937_ConstraintElim_checkOrAndOpImpliedByOther_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 8]) :=
  i137937_ConstraintElim_checkOrAndOpImpliedByOther_ivOfHVector
    (.cons (i137937_ConstraintElim_checkOrAndOpImpliedByOther_valueOfNat 8 1) .nil)

theorem i137937_ConstraintElim_checkOrAndOpImpliedByOther_correct_counterexample_witness : ¬ (i137937_ConstraintElim_checkOrAndOpImpliedByOther_src ⊑ i137937_ConstraintElim_checkOrAndOpImpliedByOther_tgt) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (i137937_ConstraintElim_checkOrAndOpImpliedByOther_src) (i137937_ConstraintElim_checkOrAndOpImpliedByOther_tgt) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (i137937_ConstraintElim_checkOrAndOpImpliedByOther_src) (i137937_ConstraintElim_checkOrAndOpImpliedByOther_tgt)).mp h
  specialize hyp i137937_ConstraintElim_checkOrAndOpImpliedByOther_cexInputs
  revert hyp
  decide

end i137937_ConstraintElim_checkOrAndOpImpliedByOther_cex

theorem i137937_ConstraintElim_checkOrAndOpImpliedByOther_correct_counterexample : ¬ (i137937_ConstraintElim_checkOrAndOpImpliedByOther_src ⊑ i137937_ConstraintElim_checkOrAndOpImpliedByOther_tgt) :=
  i137937_ConstraintElim_checkOrAndOpImpliedByOther_correct_counterexample_witness
