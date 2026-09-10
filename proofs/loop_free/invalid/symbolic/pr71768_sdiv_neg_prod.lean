import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr71768_sdiv_neg_prod_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr71768_sdiv_neg_prod_src(%a : _, %b : _) -> _ {
  ^bb0(%a : _, %b : _):
    %mul = llvm.mul %a, %b : _
    %c_i64_0 = llvm.mlir.constant(0 : _) : _
    %neg = llvm.sub %c_i64_0, %mul : _
    %div = llvm.sdiv %neg, %mul : _
    llvm.return %div : _
  }
  }]

def pr71768_sdiv_neg_prod_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr71768_sdiv_neg_prod_tgt(%a : _, %b : _) -> _ {
  ^bb0(%a : _, %b : _):
    %c_i64_m1 = llvm.mlir.constant(-1 : _) : _
    llvm.return %c_i64_m1 : _
  }
  }]

section pr71768_sdiv_neg_prod_cex

def pr71768_sdiv_neg_prod_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def pr71768_sdiv_neg_prod_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def pr71768_sdiv_neg_prod_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => pr71768_sdiv_neg_prod_ivCons x (pr71768_sdiv_neg_prod_ivOfHVector xs)

@[simp] theorem pr71768_sdiv_neg_prod_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    pr71768_sdiv_neg_prod_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [pr71768_sdiv_neg_prod_ivOfHVector, pr71768_sdiv_neg_prod_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [pr71768_sdiv_neg_prod_ivOfHVector, pr71768_sdiv_neg_prod_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance pr71768_sdiv_neg_prod_decRefSemVal (a b : LLVM.SemVal (BitVec 2)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance pr71768_sdiv_neg_prod_decRefIntW (a b : LLVM.IntW 2) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 2)) (LLVM.SemVal (BitVec 2)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance pr71768_sdiv_neg_prod_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 2)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 2)) (ImmediateUBOr (LLVM.IntW 2))
        inferInstance a b) := inferInstance
  exact d

local instance pr71768_sdiv_neg_prod_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance pr71768_sdiv_neg_prod_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def pr71768_sdiv_neg_prod_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 2, InstCombine.LLVM.Ty.bitvec 2]) :=
  pr71768_sdiv_neg_prod_ivOfHVector
    (.cons (pr71768_sdiv_neg_prod_valueOfNat 2 2) (.cons (pr71768_sdiv_neg_prod_valueOfNat 2 1) .nil))

theorem pr71768_sdiv_neg_prod_correct_counterexample_witness : ¬ (pr71768_sdiv_neg_prod_src 2 ⊑ pr71768_sdiv_neg_prod_tgt 2) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (pr71768_sdiv_neg_prod_src 2) (pr71768_sdiv_neg_prod_tgt 2) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (pr71768_sdiv_neg_prod_src 2) (pr71768_sdiv_neg_prod_tgt 2)).mp h
  specialize hyp pr71768_sdiv_neg_prod_cexInputs
  revert hyp
  decide

end pr71768_sdiv_neg_prod_cex

theorem pr71768_sdiv_neg_prod_correct_counterexample :
    ∃ (w : Nat), ¬ (pr71768_sdiv_neg_prod_src w ⊑ pr71768_sdiv_neg_prod_tgt w) :=
  ⟨2, pr71768_sdiv_neg_prod_correct_counterexample_witness⟩
