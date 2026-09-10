import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr32949_src :=
  [llvm()| {
  llvm.func @pr32949_src(%x : i8) -> i1 {
  ^bb0(%x : i8):
    %c_i8_1 = llvm.mlir.constant(1 : i8) : i8
    %div1 = llvm.sdiv exact %c_i8_1, %x : i8
    %c_i8_m1 = llvm.mlir.constant(-1 : i8) : i8
    %div2 = llvm.sdiv exact %c_i8_m1, %x : i8
    %icmp = llvm.icmp "ult" %div1, %div2 : i8
    llvm.return %icmp : i1
  }
  }]

def pr32949_tgt :=
  [llvm()| {
  llvm.func @pr32949_tgt(%x : i8) -> i1 {
  ^bb0(%x : i8):
    %c_i1_true = llvm.mlir.constant(true) : i1
    llvm.return %c_i1_true : i1
  }
  }]

section pr32949_cex

def pr32949_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def pr32949_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def pr32949_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => pr32949_ivCons x (pr32949_ivOfHVector xs)

@[simp] theorem pr32949_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    pr32949_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [pr32949_ivOfHVector, pr32949_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [pr32949_ivOfHVector, pr32949_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance pr32949_decRefSemVal (a b : LLVM.SemVal (BitVec 1)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance pr32949_decRefIntW (a b : LLVM.IntW 1) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 1)) (LLVM.SemVal (BitVec 1)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance pr32949_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 1)) (ImmediateUBOr (LLVM.IntW 1))
        inferInstance a b) := inferInstance
  exact d

local instance pr32949_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance pr32949_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def pr32949_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 8]) :=
  pr32949_ivOfHVector
    (.cons (pr32949_valueOfNat 8 255) .nil)

theorem pr32949_correct_counterexample_witness : ¬ (pr32949_src ⊑ pr32949_tgt) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (pr32949_src) (pr32949_tgt) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (pr32949_src) (pr32949_tgt)).mp h
  specialize hyp pr32949_cexInputs
  revert hyp
  decide

end pr32949_cex

theorem pr32949_correct_counterexample : ¬ (pr32949_src ⊑ pr32949_tgt) :=
  pr32949_correct_counterexample_witness
