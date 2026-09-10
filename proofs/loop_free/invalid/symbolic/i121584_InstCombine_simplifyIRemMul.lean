import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i121584_InstCombine_simplifyIRemMul_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i121584_InstCombine_simplifyIRemMul_src(%X : _) -> _ {
  ^bb0(%X : _):
    %c_i8_127 = llvm.mlir.constant(127 : _) : _
    %BO0 = llvm.mul %X, %c_i8_127 overflow<nsw> : _
    %c_i8_7 = llvm.mlir.constant(7 : _) : _
    %BO1 = llvm.shl %X, %c_i8_7 overflow<nsw> : _
    %r = llvm.srem %BO1, %BO0 : _
    llvm.return %r : _
  }
  }]

def i121584_InstCombine_simplifyIRemMul_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i121584_InstCombine_simplifyIRemMul_tgt(%X : _) -> _ {
  ^bb0(%X : _):
    %c_i8_0 = llvm.mlir.constant(0 : _) : _
    %r = llvm.sub %c_i8_0, %X overflow<nsw> : _
    llvm.return %r : _
  }
  }]

section i121584_InstCombine_simplifyIRemMul_cex

def i121584_InstCombine_simplifyIRemMul_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def i121584_InstCombine_simplifyIRemMul_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def i121584_InstCombine_simplifyIRemMul_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => i121584_InstCombine_simplifyIRemMul_ivCons x (i121584_InstCombine_simplifyIRemMul_ivOfHVector xs)

@[simp] theorem i121584_InstCombine_simplifyIRemMul_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    i121584_InstCombine_simplifyIRemMul_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [i121584_InstCombine_simplifyIRemMul_ivOfHVector, i121584_InstCombine_simplifyIRemMul_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [i121584_InstCombine_simplifyIRemMul_ivOfHVector, i121584_InstCombine_simplifyIRemMul_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance i121584_InstCombine_simplifyIRemMul_decRefSemVal (a b : LLVM.SemVal (BitVec 8)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance i121584_InstCombine_simplifyIRemMul_decRefIntW (a b : LLVM.IntW 8) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 8)) (LLVM.SemVal (BitVec 8)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance i121584_InstCombine_simplifyIRemMul_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 8)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 8)) (ImmediateUBOr (LLVM.IntW 8))
        inferInstance a b) := inferInstance
  exact d

local instance i121584_InstCombine_simplifyIRemMul_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance i121584_InstCombine_simplifyIRemMul_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def i121584_InstCombine_simplifyIRemMul_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 8]) :=
  i121584_InstCombine_simplifyIRemMul_ivOfHVector
    (.cons (i121584_InstCombine_simplifyIRemMul_valueOfNat 8 255) .nil)

theorem i121584_InstCombine_simplifyIRemMul_correct_counterexample_witness : ¬ (i121584_InstCombine_simplifyIRemMul_src 8 ⊑ i121584_InstCombine_simplifyIRemMul_tgt 8) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (i121584_InstCombine_simplifyIRemMul_src 8) (i121584_InstCombine_simplifyIRemMul_tgt 8) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (i121584_InstCombine_simplifyIRemMul_src 8) (i121584_InstCombine_simplifyIRemMul_tgt 8)).mp h
  specialize hyp i121584_InstCombine_simplifyIRemMul_cexInputs
  revert hyp
  decide

end i121584_InstCombine_simplifyIRemMul_cex

theorem i121584_InstCombine_simplifyIRemMul_correct_counterexample :
    ∃ (w : Nat), ¬ (i121584_InstCombine_simplifyIRemMul_src w ⊑ i121584_InstCombine_simplifyIRemMul_tgt w) :=
  ⟨8, i121584_InstCombine_simplifyIRemMul_correct_counterexample_witness⟩
