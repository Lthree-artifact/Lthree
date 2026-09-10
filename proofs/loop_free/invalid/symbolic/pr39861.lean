import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr39861_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr39861_src(%x : _, %y : _) -> i1 {
  ^bb0(%x : _, %y : _):
    %c_i8_255 = llvm.mlir.constant(255 : _) : _
    %tmp0 = llvm.lshr %c_i8_255, %y : _
    %tmp1 = llvm.and %tmp0, %x : _
    %ret = llvm.icmp "sge" %tmp1, %x : _
    llvm.return %ret : i1
  }
  }]

def pr39861_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr39861_tgt(%x : _, %y : _) -> i1 {
  ^bb0(%x : _, %y : _):
    %c_i8_255 = llvm.mlir.constant(255 : _) : _
    %tmp0 = llvm.lshr %c_i8_255, %y : _
    %1 = llvm.icmp "sge" %tmp0, %x : _
    llvm.return %1 : i1
  }
  }]

section pr39861_cex

def pr39861_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def pr39861_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def pr39861_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => pr39861_ivCons x (pr39861_ivOfHVector xs)

@[simp] theorem pr39861_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    pr39861_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [pr39861_ivOfHVector, pr39861_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [pr39861_ivOfHVector, pr39861_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance pr39861_decRefSemVal (a b : LLVM.SemVal (BitVec 1)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance pr39861_decRefIntW (a b : LLVM.IntW 1) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 1)) (LLVM.SemVal (BitVec 1)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance pr39861_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 1)) (ImmediateUBOr (LLVM.IntW 1))
        inferInstance a b) := inferInstance
  exact d

local instance pr39861_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance pr39861_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def pr39861_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec 1]) :=
  pr39861_ivOfHVector
    (.cons (pr39861_valueOfNat 1 0) (.cons (pr39861_valueOfNat 1 0) .nil))

theorem pr39861_correct_counterexample_witness : ¬ (pr39861_src 1 ⊑ pr39861_tgt 1) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (pr39861_src 1) (pr39861_tgt 1) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (pr39861_src 1) (pr39861_tgt 1)).mp h
  specialize hyp pr39861_cexInputs
  revert hyp
  decide

end pr39861_cex

theorem pr39861_correct_counterexample :
    ∃ (w : Nat), ¬ (pr39861_src w ⊑ pr39861_tgt w) :=
  ⟨1, pr39861_correct_counterexample_witness⟩
