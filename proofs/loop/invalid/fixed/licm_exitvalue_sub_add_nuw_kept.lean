import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def licm_exitvalue_sub_add_nuw_kept_src :=
  [llvm()| {
  llvm.func @licm_exitvalue_sub_add_nuw_kept_src(%c1 : i64, %c2 : i64) -> i64 {
  ^entry(%c1 : i64, %c2 : i64):
    %e_zero = llvm.mlir.constant 0 : i64
    %e_start = llvm.mlir.constant 1000 : i64
    llvm.br ^loop(%e_zero : i64, %e_start : i64)
  ^loop(%k : i64, %index : i64):
    %step_add = llvm.sub %index, %c1 overflow<nuw> : i64
    %index_next = llvm.add %step_add, %c2 overflow<nuw> : i64
    %l_one = llvm.mlir.constant 1 : i64
    %k1 = llvm.add %k, %l_one : i64
    %l_three = llvm.mlir.constant 3 : i64
    %cond = llvm.icmp "eq" %k1, %l_three : i64
    llvm.cond_br %cond : i1, ^out(%index_next : i64), ^loop(%k1 : i64, %index_next : i64)
  ^out(%res : i64):
    llvm.return %res : i64
  }
  }]

def licm_exitvalue_sub_add_nuw_kept_tgt :=
  [llvm()| {
  llvm.func @licm_exitvalue_sub_add_nuw_kept_tgt(%c1 : i64, %c2 : i64) -> i64 {
  ^entry(%c1 : i64, %c2 : i64):
    %e_start = llvm.mlir.constant 1000 : i64
    %invariant_op = llvm.sub %c2, %c1 overflow<nuw> : i64
    %s1 = llvm.add %e_start, %invariant_op overflow<nuw> : i64
    %s2 = llvm.add %s1, %invariant_op overflow<nuw> : i64
    %s3 = llvm.add %s2, %invariant_op overflow<nuw> : i64
    llvm.return %s3 : i64
  }
  }]

section licm_exitvalue_sub_add_nuw_kept_cex

set_option maxRecDepth 8000
set_option maxHeartbeats 40000000

def licm_exitvalue_sub_add_nuw_kept_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def licm_exitvalue_sub_add_nuw_kept_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def licm_exitvalue_sub_add_nuw_kept_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => licm_exitvalue_sub_add_nuw_kept_ivCons x (licm_exitvalue_sub_add_nuw_kept_ivOfHVector xs)

@[simp] theorem licm_exitvalue_sub_add_nuw_kept_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    licm_exitvalue_sub_add_nuw_kept_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [licm_exitvalue_sub_add_nuw_kept_ivOfHVector, licm_exitvalue_sub_add_nuw_kept_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [licm_exitvalue_sub_add_nuw_kept_ivOfHVector, licm_exitvalue_sub_add_nuw_kept_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance licm_exitvalue_sub_add_nuw_kept_decRefSemVal (a b : LLVM.SemVal (BitVec 64)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance licm_exitvalue_sub_add_nuw_kept_decRefIntW (a b : LLVM.IntW 64) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 64)) (LLVM.SemVal (BitVec 64)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance licm_exitvalue_sub_add_nuw_kept_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 64)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 64)) (ImmediateUBOr (LLVM.IntW 64))
        inferInstance a b) := inferInstance
  exact d

local instance licm_exitvalue_sub_add_nuw_kept_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

def licm_exitvalue_sub_add_nuw_kept_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64]) :=
  licm_exitvalue_sub_add_nuw_kept_ivOfHVector
    (.cons (licm_exitvalue_sub_add_nuw_kept_valueOfNat 64 0) (.cons (licm_exitvalue_sub_add_nuw_kept_valueOfNat 64 5) .nil))

def licm_exitvalue_sub_add_nuw_kept_cexState : InstCombine.LLVMMemory.State := default

def licm_exitvalue_sub_add_nuw_kept_cexFuel : Nat := 8

abbrev licm_exitvalue_sub_add_nuw_kept_tgt_impure :
    Com InstCombine.LLVM (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64]) .impure
      [InstCombine.LLVM.Ty.bitvec 64] :=
  licm_exitvalue_sub_add_nuw_kept_tgt.castPureToEff .impure

theorem licm_exitvalue_sub_add_nuw_kept_src_terminates_at_cexFuel :
    (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel licm_exitvalue_sub_add_nuw_kept_cexFuel licm_exitvalue_sub_add_nuw_kept_src
      (V := InstCombine.InputValuation.lift licm_exitvalue_sub_add_nuw_kept_cexInputs)
      licm_exitvalue_sub_add_nuw_kept_cexState).isSome = true := by
  decide +kernel

theorem licm_exitvalue_sub_add_nuw_kept_tgt_terminates_at_cexFuel :
    (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel licm_exitvalue_sub_add_nuw_kept_cexFuel licm_exitvalue_sub_add_nuw_kept_tgt_impure
      (V := InstCombine.InputValuation.lift licm_exitvalue_sub_add_nuw_kept_cexInputs)
      licm_exitvalue_sub_add_nuw_kept_cexState).isSome = true := by
  decide +kernel

def licm_exitvalue_sub_add_nuw_kept_sepBool (A B : ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]
              × InstCombine.LLVMMemory.State)) : Bool :=
  match A, B with
  | none, _ => true
  | some _, none => false
  | some a, some b => decide (a.1 ⊑ b.1)

theorem licm_exitvalue_sub_add_nuw_kept_refute_of_sepBool (A B : ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64]
              × InstCombine.LLVMMemory.State))
    (h : licm_exitvalue_sub_add_nuw_kept_sepBool A B = false) : ¬ (A ⊑ B) := by
  intro hab
  cases hab with
  | immediateUBLeft => simp [licm_exitvalue_sub_add_nuw_kept_sepBool] at h
  | bothValues hp =>
      simp only [licm_exitvalue_sub_add_nuw_kept_sepBool, decide_eq_false_iff_not] at h
      exact h hp.1

theorem licm_exitvalue_sub_add_nuw_kept_pointwise_cex :
    ¬ (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel licm_exitvalue_sub_add_nuw_kept_cexFuel licm_exitvalue_sub_add_nuw_kept_src
          (V := InstCombine.InputValuation.lift licm_exitvalue_sub_add_nuw_kept_cexInputs) licm_exitvalue_sub_add_nuw_kept_cexState ⊑
       InstCombine.LLVMMemory.Com.denoteWithMemoryFuel licm_exitvalue_sub_add_nuw_kept_cexFuel licm_exitvalue_sub_add_nuw_kept_tgt_impure
          (V := InstCombine.InputValuation.lift licm_exitvalue_sub_add_nuw_kept_cexInputs) licm_exitvalue_sub_add_nuw_kept_cexState) :=
  licm_exitvalue_sub_add_nuw_kept_refute_of_sepBool _ _ (by decide +kernel)

theorem licm_exitvalue_sub_add_nuw_kept_correct_counterexample_witness :
    ¬ (InstCombine.IsRefinedByOnIntWInputsWithMemory licm_exitvalue_sub_add_nuw_kept_src licm_exitvalue_sub_add_nuw_kept_tgt_impure) :=
  fun h => licm_exitvalue_sub_add_nuw_kept_pointwise_cex (h licm_exitvalue_sub_add_nuw_kept_cexInputs licm_exitvalue_sub_add_nuw_kept_cexState licm_exitvalue_sub_add_nuw_kept_cexFuel)

theorem licm_exitvalue_sub_add_nuw_kept_audit_relation_is_memory :
    (licm_exitvalue_sub_add_nuw_kept_src ⊑ licm_exitvalue_sub_add_nuw_kept_tgt_impure)
      = InstCombine.IsRefinedByOnIntWInputsWithMemory licm_exitvalue_sub_add_nuw_kept_src licm_exitvalue_sub_add_nuw_kept_tgt_impure := rfl

theorem licm_exitvalue_sub_add_nuw_kept_correct_counterexample_bare : ¬ (licm_exitvalue_sub_add_nuw_kept_src ⊑ licm_exitvalue_sub_add_nuw_kept_tgt_impure) :=
  licm_exitvalue_sub_add_nuw_kept_audit_relation_is_memory ▸ licm_exitvalue_sub_add_nuw_kept_correct_counterexample_witness

end licm_exitvalue_sub_add_nuw_kept_cex

theorem licm_exitvalue_sub_add_nuw_kept_correct_counterexample :
    ∃ (V : InstCombine.InputValuation (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64]))
      (s : InstCombine.LLVMMemory.State) (fuel : Nat) (_hf : 0 < fuel),
      ¬ (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel fuel licm_exitvalue_sub_add_nuw_kept_src
            (V := InstCombine.InputValuation.lift V) s ⊑
         InstCombine.LLVMMemory.Com.denoteWithMemoryFuel fuel licm_exitvalue_sub_add_nuw_kept_tgt_impure
            (V := InstCombine.InputValuation.lift V) s) :=
  ⟨licm_exitvalue_sub_add_nuw_kept_cexInputs, licm_exitvalue_sub_add_nuw_kept_cexState, licm_exitvalue_sub_add_nuw_kept_cexFuel, by decide, licm_exitvalue_sub_add_nuw_kept_pointwise_cex⟩
