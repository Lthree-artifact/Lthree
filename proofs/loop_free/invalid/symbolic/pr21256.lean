import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr21256_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr21256_src(%X : _, %Op0 : _) -> _ {
  ^bb0(%X : _, %Op0 : _):
    %c_i8_0 = llvm.mlir.constant(0 : _) : _
    %Op1 = llvm.sub %c_i8_0, %X : _
    %r = llvm.srem %Op0, %Op1 : _
    llvm.return %r : _
  }
  }]

def pr21256_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr21256_tgt(%X : _, %Op0 : _) -> _ {
  ^bb0(%X : _, %Op0 : _):
    %r = llvm.srem %Op0, %X : _
    llvm.return %r : _
  }
  }]

section pr21256_cex

def pr21256_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def pr21256_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def pr21256_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => pr21256_ivCons x (pr21256_ivOfHVector xs)

@[simp] theorem pr21256_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    pr21256_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [pr21256_ivOfHVector, pr21256_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [pr21256_ivOfHVector, pr21256_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance pr21256_decRefSemVal (a b : LLVM.SemVal (BitVec 2)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance pr21256_decRefIntW (a b : LLVM.IntW 2) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 2)) (LLVM.SemVal (BitVec 2)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance pr21256_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 2)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 2)) (ImmediateUBOr (LLVM.IntW 2))
        inferInstance a b) := inferInstance
  exact d

local instance pr21256_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance pr21256_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def pr21256_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 2, InstCombine.LLVM.Ty.bitvec 2]) :=
  pr21256_ivOfHVector
    (.cons (pr21256_valueOfNat 2 2) (.cons (pr21256_valueOfNat 2 3) .nil))

theorem pr21256_correct_counterexample_witness : ¬ (pr21256_src 2 ⊑ pr21256_tgt 2) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (pr21256_src 2) (pr21256_tgt 2) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (pr21256_src 2) (pr21256_tgt 2)).mp h
  specialize hyp pr21256_cexInputs
  revert hyp
  decide

end pr21256_cex

theorem pr21256_correct_counterexample :
    ∃ (w : Nat), ¬ (pr21256_src w ⊑ pr21256_tgt w) :=
  ⟨2, pr21256_correct_counterexample_witness⟩
