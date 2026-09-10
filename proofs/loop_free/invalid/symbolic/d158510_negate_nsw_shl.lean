import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def d158510_negate_nsw_shl_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @d158510_negate_nsw_shl_src(%a : _, %shamt : _) -> _ {
  ^bb0(%a : _, %shamt : _):
    %c_i64_1 = llvm.mlir.constant(1 : _) : _
    %pow2 = llvm.shl %c_i64_1, %shamt : _
    %c_i64_0 = llvm.mlir.constant(0 : _) : _
    %neg_pow2 = llvm.sub %c_i64_0, %pow2 : _
    %mul = llvm.mul %a, %neg_pow2 overflow<nsw> : _
    llvm.return %mul : _
  }
  }]

def d158510_negate_nsw_shl_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @d158510_negate_nsw_shl_tgt(%a : _, %shamt : _) -> _ {
  ^bb0(%a : _, %shamt : _):
    %c_i64_1 = llvm.mlir.constant(1 : _) : _
    %pow2 = llvm.shl %c_i64_1, %shamt : _
    %c_i64_0 = llvm.mlir.constant(0 : _) : _
    %a_neg = llvm.sub %c_i64_0, %a overflow<nsw> : _
    %mul = llvm.mul %a_neg, %pow2 overflow<nsw> : _
    llvm.return %mul : _
  }
  }]

section d158510_negate_nsw_shl_cex

def d158510_negate_nsw_shl_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def d158510_negate_nsw_shl_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def d158510_negate_nsw_shl_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => d158510_negate_nsw_shl_ivCons x (d158510_negate_nsw_shl_ivOfHVector xs)

@[simp] theorem d158510_negate_nsw_shl_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    d158510_negate_nsw_shl_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [d158510_negate_nsw_shl_ivOfHVector, d158510_negate_nsw_shl_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [d158510_negate_nsw_shl_ivOfHVector, d158510_negate_nsw_shl_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance d158510_negate_nsw_shl_decRefSemVal (a b : LLVM.SemVal (BitVec 2)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance d158510_negate_nsw_shl_decRefIntW (a b : LLVM.IntW 2) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 2)) (LLVM.SemVal (BitVec 2)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance d158510_negate_nsw_shl_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 2)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 2)) (ImmediateUBOr (LLVM.IntW 2))
        inferInstance a b) := inferInstance
  exact d

local instance d158510_negate_nsw_shl_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance d158510_negate_nsw_shl_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def d158510_negate_nsw_shl_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 2, InstCombine.LLVM.Ty.bitvec 2]) :=
  d158510_negate_nsw_shl_ivOfHVector
    (.cons (d158510_negate_nsw_shl_valueOfNat 2 1) (.cons (d158510_negate_nsw_shl_valueOfNat 2 1) .nil))

theorem d158510_negate_nsw_shl_correct_counterexample_witness : ¬ (d158510_negate_nsw_shl_src 2 ⊑ d158510_negate_nsw_shl_tgt 2) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (d158510_negate_nsw_shl_src 2) (d158510_negate_nsw_shl_tgt 2) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (d158510_negate_nsw_shl_src 2) (d158510_negate_nsw_shl_tgt 2)).mp h
  specialize hyp d158510_negate_nsw_shl_cexInputs
  revert hyp
  decide

end d158510_negate_nsw_shl_cex

theorem d158510_negate_nsw_shl_correct_counterexample :
    ∃ (w : Nat), ¬ (d158510_negate_nsw_shl_src w ⊑ d158510_negate_nsw_shl_tgt w) :=
  ⟨2, d158510_negate_nsw_shl_correct_counterexample_witness⟩
