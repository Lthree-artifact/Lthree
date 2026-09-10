import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def licm_exitvalue_or_disjoint_kept_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @licm_exitvalue_or_disjoint_kept_src(%c1 : _, %c2 : _) -> _ {
  ^entry(%c1 : _, %c2 : _):
    %e_zero = llvm.mlir.constant 0 : _
    %e_start = llvm.mlir.constant 0 : _
    llvm.br ^loop(%e_zero : _, %e_start : _)
  ^loop(%k : _, %index : _):
    %step_add = llvm.or %index, %c1 : _
    %index_next = llvm.or disjoint %c2, %step_add : _
    %l_one = llvm.mlir.constant 1 : _
    %k1 = llvm.add %k, %l_one : _
    %l_three = llvm.mlir.constant 3 : _
    %cond = llvm.icmp "eq" %k1, %l_three : _
    llvm.cond_br %cond : i1, ^out(%index_next : _), ^loop(%k1 : _, %index_next : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

def licm_exitvalue_or_disjoint_kept_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @licm_exitvalue_or_disjoint_kept_tgt(%c1 : _, %c2 : _) -> _ {
  ^entry(%c1 : _, %c2 : _):
    %invariant_op = llvm.or disjoint %c1, %c2 : _
    %s2 = llvm.or disjoint %invariant_op, %invariant_op : _
    %s3 = llvm.or disjoint %s2, %invariant_op : _
    llvm.return %s3 : _
  }
  }]

section licm_exitvalue_or_disjoint_kept_cex

set_option maxRecDepth 8000
set_option maxHeartbeats 40000000

def licm_exitvalue_or_disjoint_kept_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def licm_exitvalue_or_disjoint_kept_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def licm_exitvalue_or_disjoint_kept_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => licm_exitvalue_or_disjoint_kept_ivCons x (licm_exitvalue_or_disjoint_kept_ivOfHVector xs)

@[simp] theorem licm_exitvalue_or_disjoint_kept_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    licm_exitvalue_or_disjoint_kept_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [licm_exitvalue_or_disjoint_kept_ivOfHVector, licm_exitvalue_or_disjoint_kept_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [licm_exitvalue_or_disjoint_kept_ivOfHVector, licm_exitvalue_or_disjoint_kept_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance licm_exitvalue_or_disjoint_kept_decRefSemVal (a b : LLVM.SemVal (BitVec 2)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance licm_exitvalue_or_disjoint_kept_decRefIntW (a b : LLVM.IntW 2) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 2)) (LLVM.SemVal (BitVec 2)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance licm_exitvalue_or_disjoint_kept_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 2)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 2)) (ImmediateUBOr (LLVM.IntW 2))
        inferInstance a b) := inferInstance
  exact d

local instance licm_exitvalue_or_disjoint_kept_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

def licm_exitvalue_or_disjoint_kept_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 2, InstCombine.LLVM.Ty.bitvec 2]) :=
  licm_exitvalue_or_disjoint_kept_ivOfHVector
    (.cons (licm_exitvalue_or_disjoint_kept_valueOfNat 2 0) (.cons (licm_exitvalue_or_disjoint_kept_valueOfNat 2 1) .nil))

def licm_exitvalue_or_disjoint_kept_cexState : InstCombine.LLVMMemory.State := default

def licm_exitvalue_or_disjoint_kept_cexFuel : Nat := 6

abbrev licm_exitvalue_or_disjoint_kept_tgt_impure :
    Com InstCombine.LLVM (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 2, InstCombine.LLVM.Ty.bitvec 2]) .impure
      [InstCombine.LLVM.Ty.bitvec 2] :=
  (licm_exitvalue_or_disjoint_kept_tgt 2).castPureToEff .impure

theorem licm_exitvalue_or_disjoint_kept_src_terminates_at_cexFuel :
    (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel licm_exitvalue_or_disjoint_kept_cexFuel (licm_exitvalue_or_disjoint_kept_src 2)
      (V := InstCombine.InputValuation.lift licm_exitvalue_or_disjoint_kept_cexInputs)
      licm_exitvalue_or_disjoint_kept_cexState).isSome = true := by
  decide +kernel

theorem licm_exitvalue_or_disjoint_kept_tgt_terminates_at_cexFuel :
    (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel licm_exitvalue_or_disjoint_kept_cexFuel licm_exitvalue_or_disjoint_kept_tgt_impure
      (V := InstCombine.InputValuation.lift licm_exitvalue_or_disjoint_kept_cexInputs)
      licm_exitvalue_or_disjoint_kept_cexState).isSome = true := by
  decide +kernel

def licm_exitvalue_or_disjoint_kept_sepBool (A B : ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]
              × InstCombine.LLVMMemory.State)) : Bool :=
  match A, B with
  | none, _ => true
  | some _, none => false
  | some a, some b => decide (a.1 ⊑ b.1)

theorem licm_exitvalue_or_disjoint_kept_refute_of_sepBool (A B : ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]
              × InstCombine.LLVMMemory.State))
    (h : licm_exitvalue_or_disjoint_kept_sepBool A B = false) : ¬ (A ⊑ B) := by
  intro hab
  cases hab with
  | immediateUBLeft => simp [licm_exitvalue_or_disjoint_kept_sepBool] at h
  | bothValues hp =>
      simp only [licm_exitvalue_or_disjoint_kept_sepBool, decide_eq_false_iff_not] at h
      exact h hp.1

theorem licm_exitvalue_or_disjoint_kept_pointwise_cex :
    ¬ (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel licm_exitvalue_or_disjoint_kept_cexFuel (licm_exitvalue_or_disjoint_kept_src 2)
          (V := InstCombine.InputValuation.lift licm_exitvalue_or_disjoint_kept_cexInputs) licm_exitvalue_or_disjoint_kept_cexState ⊑
       InstCombine.LLVMMemory.Com.denoteWithMemoryFuel licm_exitvalue_or_disjoint_kept_cexFuel licm_exitvalue_or_disjoint_kept_tgt_impure
          (V := InstCombine.InputValuation.lift licm_exitvalue_or_disjoint_kept_cexInputs) licm_exitvalue_or_disjoint_kept_cexState) :=
  licm_exitvalue_or_disjoint_kept_refute_of_sepBool _ _ (by decide +kernel)

theorem licm_exitvalue_or_disjoint_kept_correct_counterexample_witness :
    ¬ (InstCombine.IsRefinedByOnIntWInputsWithMemory (licm_exitvalue_or_disjoint_kept_src 2) licm_exitvalue_or_disjoint_kept_tgt_impure) :=
  fun h => licm_exitvalue_or_disjoint_kept_pointwise_cex (h licm_exitvalue_or_disjoint_kept_cexInputs licm_exitvalue_or_disjoint_kept_cexState licm_exitvalue_or_disjoint_kept_cexFuel)

theorem licm_exitvalue_or_disjoint_kept_audit_relation_is_memory :
    ((licm_exitvalue_or_disjoint_kept_src 2) ⊑ licm_exitvalue_or_disjoint_kept_tgt_impure)
      = InstCombine.IsRefinedByOnIntWInputsWithMemory (licm_exitvalue_or_disjoint_kept_src 2) licm_exitvalue_or_disjoint_kept_tgt_impure := rfl

theorem licm_exitvalue_or_disjoint_kept_correct_counterexample_bare : ¬ ((licm_exitvalue_or_disjoint_kept_src 2) ⊑ licm_exitvalue_or_disjoint_kept_tgt_impure) :=
  licm_exitvalue_or_disjoint_kept_audit_relation_is_memory ▸ licm_exitvalue_or_disjoint_kept_correct_counterexample_witness

end licm_exitvalue_or_disjoint_kept_cex

theorem licm_exitvalue_or_disjoint_kept_correct_counterexample :
    ∃ (w : Nat), ¬ (licm_exitvalue_or_disjoint_kept_src w ⊑ (licm_exitvalue_or_disjoint_kept_tgt w).castPureToEff .impure) :=
  ⟨2, licm_exitvalue_or_disjoint_kept_correct_counterexample_bare⟩

theorem licm_exitvalue_or_disjoint_kept_correct_counterexample_fuel :
    ∃ (V : InstCombine.InputValuation (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 2, InstCombine.LLVM.Ty.bitvec 2]))
      (s : InstCombine.LLVMMemory.State) (fuel : Nat) (_hf : 0 < fuel),
      ¬ (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel fuel (licm_exitvalue_or_disjoint_kept_src 2)
            (V := InstCombine.InputValuation.lift V) s ⊑
         InstCombine.LLVMMemory.Com.denoteWithMemoryFuel fuel licm_exitvalue_or_disjoint_kept_tgt_impure
            (V := InstCombine.InputValuation.lift V) s) :=
  ⟨licm_exitvalue_or_disjoint_kept_cexInputs, licm_exitvalue_or_disjoint_kept_cexState, licm_exitvalue_or_disjoint_kept_cexFuel, by decide, licm_exitvalue_or_disjoint_kept_pointwise_cex⟩
