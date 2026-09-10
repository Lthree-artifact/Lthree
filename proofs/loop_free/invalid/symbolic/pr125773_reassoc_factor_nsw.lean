import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr125773_reassoc_factor_nsw_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr125773_reassoc_factor_nsw_src(%X1 : _, %X2 : _, %g0 : _, %g1 : _) -> _ {
  ^bb0(%X1 : _, %X2 : _, %g0 : _, %g1 : _):
    %A = llvm.add %X1, %g0 overflow<nsw> : _
    %B = llvm.mul %X2, %g1 overflow<nsw> : _
    %C = llvm.mul %X2, %A overflow<nsw> : _
    %D = llvm.add %B, %C overflow<nsw> : _
    llvm.return %D : _
  }
  }]

def pr125773_reassoc_factor_nsw_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr125773_reassoc_factor_nsw_tgt(%X1 : _, %X2 : _, %g0 : _, %g1 : _) -> _ {
  ^bb0(%X1 : _, %X2 : _, %g0 : _, %g1 : _):
    %c_i64_67 = llvm.mlir.constant(67 : _) : _
    %reass_add = llvm.add %X1, %c_i64_67 : _
    %reass_mul = llvm.mul %reass_add, %X2 overflow<nsw> : _
    llvm.return %reass_mul : _
  }
  }]

section pr125773_reassoc_factor_nsw_cex

def pr125773_reassoc_factor_nsw_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def pr125773_reassoc_factor_nsw_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def pr125773_reassoc_factor_nsw_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => pr125773_reassoc_factor_nsw_ivCons x (pr125773_reassoc_factor_nsw_ivOfHVector xs)

@[simp] theorem pr125773_reassoc_factor_nsw_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    pr125773_reassoc_factor_nsw_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [pr125773_reassoc_factor_nsw_ivOfHVector, pr125773_reassoc_factor_nsw_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [pr125773_reassoc_factor_nsw_ivOfHVector, pr125773_reassoc_factor_nsw_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance pr125773_reassoc_factor_nsw_decRefSemVal (a b : LLVM.SemVal (BitVec 1)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance pr125773_reassoc_factor_nsw_decRefIntW (a b : LLVM.IntW 1) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 1)) (LLVM.SemVal (BitVec 1)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance pr125773_reassoc_factor_nsw_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 1)) (ImmediateUBOr (LLVM.IntW 1))
        inferInstance a b) := inferInstance
  exact d

local instance pr125773_reassoc_factor_nsw_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance pr125773_reassoc_factor_nsw_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def pr125773_reassoc_factor_nsw_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec 1]) :=
  pr125773_reassoc_factor_nsw_ivOfHVector
    (.cons (pr125773_reassoc_factor_nsw_valueOfNat 1 0) (.cons (pr125773_reassoc_factor_nsw_valueOfNat 1 0) (.cons (pr125773_reassoc_factor_nsw_valueOfNat 1 1) (.cons (pr125773_reassoc_factor_nsw_valueOfNat 1 0) .nil))))

theorem pr125773_reassoc_factor_nsw_correct_counterexample_witness : ¬ (pr125773_reassoc_factor_nsw_src 1 ⊑ pr125773_reassoc_factor_nsw_tgt 1) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (pr125773_reassoc_factor_nsw_src 1) (pr125773_reassoc_factor_nsw_tgt 1) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (pr125773_reassoc_factor_nsw_src 1) (pr125773_reassoc_factor_nsw_tgt 1)).mp h
  specialize hyp pr125773_reassoc_factor_nsw_cexInputs
  revert hyp
  decide

end pr125773_reassoc_factor_nsw_cex

theorem pr125773_reassoc_factor_nsw_correct_counterexample :
    ∃ (w : Nat), ¬ (pr125773_reassoc_factor_nsw_src w ⊑ pr125773_reassoc_factor_nsw_tgt w) :=
  ⟨1, pr125773_reassoc_factor_nsw_correct_counterexample_witness⟩
