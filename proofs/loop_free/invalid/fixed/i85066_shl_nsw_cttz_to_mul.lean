import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i85066_shl_nsw_cttz_to_mul_src :=
  [llvm()| {
  llvm.func @i85066_shl_nsw_cttz_to_mul_src(%x : i64, %y : i64) -> i64 {
  ^bb0(%x : i64, %y : i64):
    %cttz = llvm.cttz %y, false : i64
    %res = llvm.shl %x, %cttz overflow<nsw> : i64
    llvm.return %res : i64
  }
  }]

def i85066_shl_nsw_cttz_to_mul_tgt :=
  [llvm()| {
  llvm.func @i85066_shl_nsw_cttz_to_mul_tgt(%x : i64, %y : i64) -> i64 {
  ^bb0(%x : i64, %y : i64):
    %c_i64_0 = llvm.mlir.constant(0 : i64) : i64
    %0 = llvm.sub %c_i64_0, %y : i64
    %1 = llvm.and %y, %0 : i64
    %2 = llvm.mul %1, %x overflow<nsw> : i64
    llvm.return %2 : i64
  }
  }]

section i85066_shl_nsw_cttz_to_mul_cex

def i85066_shl_nsw_cttz_to_mul_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def i85066_shl_nsw_cttz_to_mul_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def i85066_shl_nsw_cttz_to_mul_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => i85066_shl_nsw_cttz_to_mul_ivCons x (i85066_shl_nsw_cttz_to_mul_ivOfHVector xs)

@[simp] theorem i85066_shl_nsw_cttz_to_mul_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    i85066_shl_nsw_cttz_to_mul_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [i85066_shl_nsw_cttz_to_mul_ivOfHVector, i85066_shl_nsw_cttz_to_mul_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [i85066_shl_nsw_cttz_to_mul_ivOfHVector, i85066_shl_nsw_cttz_to_mul_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance i85066_shl_nsw_cttz_to_mul_decRefSemVal (a b : LLVM.SemVal (BitVec 64)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance i85066_shl_nsw_cttz_to_mul_decRefIntW (a b : LLVM.IntW 64) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 64)) (LLVM.SemVal (BitVec 64)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance i85066_shl_nsw_cttz_to_mul_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 64)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 64)) (ImmediateUBOr (LLVM.IntW 64))
        inferInstance a b) := inferInstance
  exact d

local instance i85066_shl_nsw_cttz_to_mul_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance i85066_shl_nsw_cttz_to_mul_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def i85066_shl_nsw_cttz_to_mul_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64]) :=
  i85066_shl_nsw_cttz_to_mul_ivOfHVector
    (.cons (i85066_shl_nsw_cttz_to_mul_valueOfNat 64 9223372036854775808) (.cons (i85066_shl_nsw_cttz_to_mul_valueOfNat 64 18446744073709551615) .nil))

theorem i85066_shl_nsw_cttz_to_mul_correct_counterexample_witness : ¬ (i85066_shl_nsw_cttz_to_mul_src ⊑ i85066_shl_nsw_cttz_to_mul_tgt) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (i85066_shl_nsw_cttz_to_mul_src) (i85066_shl_nsw_cttz_to_mul_tgt) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (i85066_shl_nsw_cttz_to_mul_src) (i85066_shl_nsw_cttz_to_mul_tgt)).mp h
  specialize hyp i85066_shl_nsw_cttz_to_mul_cexInputs
  revert hyp
  decide

end i85066_shl_nsw_cttz_to_mul_cex

theorem i85066_shl_nsw_cttz_to_mul_correct_counterexample : ¬ (i85066_shl_nsw_cttz_to_mul_src ⊑ i85066_shl_nsw_cttz_to_mul_tgt) :=
  i85066_shl_nsw_cttz_to_mul_correct_counterexample_witness
