import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def mkkfrj_srem_shl_mul_nsw_src :=
  [llvm()| {
  llvm.func @mkkfrj_srem_shl_mul_nsw_src(%x : i64, %y : i64, %z : i64) -> i64 {
  ^bb0(%x : i64, %y : i64, %z : i64):
    %c_i64_1 = llvm.mlir.constant(1 : i64) : i64
    %yy = llvm.shl %c_i64_1, %y : i64
    %cond = llvm.icmp "uge" %yy, %z : i64
    llvm.assume %cond : i1
    %mul1 = llvm.shl %x, %y overflow<nsw> : i64
    %mul2 = llvm.mul %x, %z overflow<nsw> : i64
    %rem = llvm.srem %mul1, %mul2 : i64
    llvm.return %rem : i64
  }
  }]

def mkkfrj_srem_shl_mul_nsw_tgt :=
  [llvm()| {
  llvm.func @mkkfrj_srem_shl_mul_nsw_tgt(%x : i64, %y : i64, %z : i64) -> i64 {
  ^bb0(%x : i64, %y : i64, %z : i64):
    %c_i64_1 = llvm.mlir.constant(1 : i64) : i64
    %yy = llvm.shl %c_i64_1, %y : i64
    %rem = llvm.srem %yy, %z : i64
    %mul = llvm.mul %x, %rem overflow<nsw> : i64
    llvm.return %mul : i64
  }
  }]

section mkkfrj_srem_shl_mul_nsw_cex

def mkkfrj_srem_shl_mul_nsw_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def mkkfrj_srem_shl_mul_nsw_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def mkkfrj_srem_shl_mul_nsw_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => mkkfrj_srem_shl_mul_nsw_ivCons x (mkkfrj_srem_shl_mul_nsw_ivOfHVector xs)

@[simp] theorem mkkfrj_srem_shl_mul_nsw_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    mkkfrj_srem_shl_mul_nsw_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [mkkfrj_srem_shl_mul_nsw_ivOfHVector, mkkfrj_srem_shl_mul_nsw_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [mkkfrj_srem_shl_mul_nsw_ivOfHVector, mkkfrj_srem_shl_mul_nsw_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance mkkfrj_srem_shl_mul_nsw_decRefSemVal (a b : LLVM.SemVal (BitVec 64)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance mkkfrj_srem_shl_mul_nsw_decRefIntW (a b : LLVM.IntW 64) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 64)) (LLVM.SemVal (BitVec 64)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance mkkfrj_srem_shl_mul_nsw_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 64)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 64)) (ImmediateUBOr (LLVM.IntW 64))
        inferInstance a b) := inferInstance
  exact d

local instance mkkfrj_srem_shl_mul_nsw_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance mkkfrj_srem_shl_mul_nsw_decRefDenote
    (a : EffectKind.impure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]))
        inferInstance a (ImmediateUBOr.value b)) := inferInstance
  exact d

def mkkfrj_srem_shl_mul_nsw_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64]) :=
  mkkfrj_srem_shl_mul_nsw_ivOfHVector
    (.cons (mkkfrj_srem_shl_mul_nsw_valueOfNat 64 3) (.cons (mkkfrj_srem_shl_mul_nsw_valueOfNat 64 63) (.cons (mkkfrj_srem_shl_mul_nsw_valueOfNat 64 18446744073709551615) .nil)))

theorem mkkfrj_srem_shl_mul_nsw_correct_counterexample_witness : ¬ (mkkfrj_srem_shl_mul_nsw_src ⊑ mkkfrj_srem_shl_mul_nsw_tgt) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (mkkfrj_srem_shl_mul_nsw_src) (mkkfrj_srem_shl_mul_nsw_tgt) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (mkkfrj_srem_shl_mul_nsw_src) (mkkfrj_srem_shl_mul_nsw_tgt)).mp h
  specialize hyp mkkfrj_srem_shl_mul_nsw_cexInputs
  revert hyp
  decide

end mkkfrj_srem_shl_mul_nsw_cex

theorem mkkfrj_srem_shl_mul_nsw_correct_counterexample : ¬ (mkkfrj_srem_shl_mul_nsw_src ⊑ mkkfrj_srem_shl_mul_nsw_tgt) :=
  mkkfrj_srem_shl_mul_nsw_correct_counterexample_witness
