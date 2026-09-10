import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr34349_src (w1 w2 : Nat) (_h : w1 < w2) (_h1 : 0 < w1) :=
  [llvm(w1, w2)| {
  llvm.func @pr34349_src(%p : w1) -> w1 {
  ^bb0(%p : w1):
    %v3 = llvm.zext %p : w1 to w2
    %c_i16_71 = llvm.mlir.constant(71 : w2) : w2
    %v4 = llvm.mul %v3, %c_i16_71 : w2
    %c_i16_8 = llvm.mlir.constant(8 : w2) : w2
    %v5 = llvm.lshr %v4, %c_i16_8 : w2
    %v6 = llvm.trunc %v5 : w2 to w1
    %v7 = llvm.sub %p, %v6 : w1
    %c_i8_1 = llvm.mlir.constant(1 : w1) : w1
    %v8 = llvm.lshr %v7, %c_i8_1 : w1
    %v9 = llvm.zext %p : w1 to w2
    %v10 = llvm.mul %v9, %c_i16_71 : w2
    %v11 = llvm.lshr %v10, %c_i16_8 : w2
    %v12 = llvm.trunc %v11 : w2 to w1
    %v13 = llvm.add %v12, %v8 : w1
    %c_i8_7 = llvm.mlir.constant(7 : w1) : w1
    %v14 = llvm.lshr %v13, %c_i8_7 : w1
    llvm.return %v14 : w1
  }
  }]

def pr34349_tgt (w1 w2 : Nat) (_h : w1 < w2) (_h1 : 0 < w1) :=
  [llvm(w1, w2)| {
  llvm.func @pr34349_tgt(%p : w1) -> w1 {
  ^bb0(%p : w1):
    %c_i8_0 = llvm.mlir.constant(0 : w1) : w1
    llvm.return %c_i8_0 : w1
  }
  }]

section pr34349_cex

def pr34349_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def pr34349_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def pr34349_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => pr34349_ivCons x (pr34349_ivOfHVector xs)

@[simp] theorem pr34349_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    pr34349_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [pr34349_ivOfHVector, pr34349_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [pr34349_ivOfHVector, pr34349_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance pr34349_decRefSemVal (a b : LLVM.SemVal (BitVec 8)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance pr34349_decRefIntW (a b : LLVM.IntW 8) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 8)) (LLVM.SemVal (BitVec 8)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance pr34349_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 8)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 8)) (ImmediateUBOr (LLVM.IntW 8))
        inferInstance a b) := inferInstance
  exact d

local instance pr34349_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance pr34349_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def pr34349_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 8]) :=
  pr34349_ivOfHVector
    (.cons (pr34349_valueOfNat 8 255) .nil)

theorem pr34349_correct_counterexample_witness : ¬ (pr34349_src 8 10 (by decide : 8 < 10) (by decide : 0 < 8) ⊑ pr34349_tgt 8 10 (by decide : 8 < 10) (by decide : 0 < 8)) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (pr34349_src 8 10 (by decide : 8 < 10) (by decide : 0 < 8)) (pr34349_tgt 8 10 (by decide : 8 < 10) (by decide : 0 < 8)) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (pr34349_src 8 10 (by decide : 8 < 10) (by decide : 0 < 8)) (pr34349_tgt 8 10 (by decide : 8 < 10) (by decide : 0 < 8))).mp h
  specialize hyp pr34349_cexInputs
  revert hyp
  decide

end pr34349_cex

theorem pr34349_correct_counterexample :
    ∃ (w1 w2 : Nat)(_h : w1 < w2) (_h1 : 0 < w1), ¬ (pr34349_src w1 w2 _h _h1 ⊑ pr34349_tgt w1 w2 _h _h1) :=
  ⟨8, 10, (by decide : 8 < 10), (by decide : 0 < 8), pr34349_correct_counterexample_witness⟩
