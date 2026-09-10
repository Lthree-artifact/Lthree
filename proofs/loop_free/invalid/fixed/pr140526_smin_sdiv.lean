import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr140526_smin_sdiv_src :=
  [llvm()| {
  llvm.func @pr140526_smin_sdiv_src(%x : i64, %y : i64, %z : i64) -> i64 {
  ^bb0(%x : i64, %y : i64, %z : i64):
    %min_c = llvm.icmp "slt" %x, %y : i64
    %min = llvm.select %min_c, %x, %y : i64
    %res = llvm.sdiv %min, %z : i64
    llvm.return %res : i64
  }
  }]

def pr140526_smin_sdiv_tgt :=
  [llvm()| {
  llvm.func @pr140526_smin_sdiv_tgt(%x : i64, %y : i64, %z : i64) -> i64 {
  ^bb0(%x : i64, %y : i64, %z : i64):
    %xz = llvm.sdiv %x, %z : i64
    %yz = llvm.sdiv %y, %z : i64
    %res_c = llvm.icmp "slt" %xz, %yz : i64
    %res = llvm.select %res_c, %xz, %yz : i64
    llvm.return %res : i64
  }
  }]

section pr140526_smin_sdiv_cex

def pr140526_smin_sdiv_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def pr140526_smin_sdiv_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def pr140526_smin_sdiv_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => pr140526_smin_sdiv_ivCons x (pr140526_smin_sdiv_ivOfHVector xs)

@[simp] theorem pr140526_smin_sdiv_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    pr140526_smin_sdiv_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [pr140526_smin_sdiv_ivOfHVector, pr140526_smin_sdiv_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [pr140526_smin_sdiv_ivOfHVector, pr140526_smin_sdiv_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance pr140526_smin_sdiv_decRefSemVal (a b : LLVM.SemVal (BitVec 64)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance pr140526_smin_sdiv_decRefIntW (a b : LLVM.IntW 64) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 64)) (LLVM.SemVal (BitVec 64)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance pr140526_smin_sdiv_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 64)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 64)) (ImmediateUBOr (LLVM.IntW 64))
        inferInstance a b) := inferInstance
  exact d

local instance pr140526_smin_sdiv_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance pr140526_smin_sdiv_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def pr140526_smin_sdiv_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64]) :=
  pr140526_smin_sdiv_ivOfHVector
    (.cons (pr140526_smin_sdiv_valueOfNat 64 18446744073709551615) (.cons (pr140526_smin_sdiv_valueOfNat 64 1) (.cons (pr140526_smin_sdiv_valueOfNat 64 0) .nil)))

theorem pr140526_smin_sdiv_correct_counterexample_witness : ¬ (pr140526_smin_sdiv_src ⊑ pr140526_smin_sdiv_tgt) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (pr140526_smin_sdiv_src) (pr140526_smin_sdiv_tgt) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (pr140526_smin_sdiv_src) (pr140526_smin_sdiv_tgt)).mp h
  specialize hyp pr140526_smin_sdiv_cexInputs
  revert hyp
  decide

end pr140526_smin_sdiv_cex

theorem pr140526_smin_sdiv_correct_counterexample : ¬ (pr140526_smin_sdiv_src ⊑ pr140526_smin_sdiv_tgt) :=
  pr140526_smin_sdiv_correct_counterexample_witness
