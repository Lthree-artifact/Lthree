import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def indvars_exitvalue_poison_propagated_src :=
  [llvm()| {
  llvm.func @indvars_exitvalue_poison_propagated_src(%x : i32, %n : i32) -> i32 {
  ^entry(%x : i32, %n : i32):
    %e_zero = llvm.mlir.constant 0 : i32
    llvm.br ^loop(%e_zero : i32, %e_zero : i32)
  ^loop(%acc : i32, %i : i32):
    %acc_next = llvm.add %acc, %x : i32
    %l_one = llvm.mlir.constant 1 : i32
    %i_next = llvm.add %i, %l_one : i32
    %cond = llvm.icmp "eq" %i, %n : i32
    llvm.cond_br %cond : i1, ^out(%acc : i32), ^loop(%acc_next : i32, %i_next : i32)
  ^out(%res : i32):
    llvm.return %res : i32
  }
  }]

def indvars_exitvalue_poison_propagated_tgt :=
  [llvm()| {
  llvm.func @indvars_exitvalue_poison_propagated_tgt(%x : i32, %n : i32) -> i32 {
  ^entry(%x : i32, %n : i32):
    %prod = llvm.mul %x, %n : i32
    llvm.return %prod : i32
  }
  }]

section indvars_exitvalue_poison_propagated_cex

set_option maxRecDepth 8000
set_option maxHeartbeats 40000000

def indvars_exitvalue_poison_propagated_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def indvars_exitvalue_poison_propagated_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def indvars_exitvalue_poison_propagated_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => indvars_exitvalue_poison_propagated_ivCons x (indvars_exitvalue_poison_propagated_ivOfHVector xs)

@[simp] theorem indvars_exitvalue_poison_propagated_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    indvars_exitvalue_poison_propagated_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [indvars_exitvalue_poison_propagated_ivOfHVector, indvars_exitvalue_poison_propagated_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [indvars_exitvalue_poison_propagated_ivOfHVector, indvars_exitvalue_poison_propagated_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance indvars_exitvalue_poison_propagated_decRefSemVal (a b : LLVM.SemVal (BitVec 32)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance indvars_exitvalue_poison_propagated_decRefIntW (a b : LLVM.IntW 32) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 32)) (LLVM.SemVal (BitVec 32)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance indvars_exitvalue_poison_propagated_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 32)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 32)) (ImmediateUBOr (LLVM.IntW 32))
        inferInstance a b) := inferInstance
  exact d

local instance indvars_exitvalue_poison_propagated_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 32]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

def indvars_exitvalue_poison_propagated_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]) :=
  indvars_exitvalue_poison_propagated_ivOfHVector
    (.cons (indvars_exitvalue_poison_propagated_valueOfNat 32 0) (.cons ((LLVM.SemVal.poison : LLVM.IntW 32)) .nil))

def indvars_exitvalue_poison_propagated_cexState : InstCombine.LLVMMemory.State := default

def indvars_exitvalue_poison_propagated_cexFuel : Nat := 4

abbrev indvars_exitvalue_poison_propagated_tgt_impure :
    Com InstCombine.LLVM (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]) .impure
      [InstCombine.LLVM.Ty.bitvec 32] :=
  indvars_exitvalue_poison_propagated_tgt.castPureToEff .impure

theorem indvars_exitvalue_poison_propagated_src_terminates_at_cexFuel :
    (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel indvars_exitvalue_poison_propagated_cexFuel indvars_exitvalue_poison_propagated_src
      (V := InstCombine.InputValuation.lift indvars_exitvalue_poison_propagated_cexInputs)
      indvars_exitvalue_poison_propagated_cexState).isSome = true := by
  decide +kernel

theorem indvars_exitvalue_poison_propagated_tgt_terminates_at_cexFuel :
    (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel indvars_exitvalue_poison_propagated_cexFuel indvars_exitvalue_poison_propagated_tgt_impure
      (V := InstCombine.InputValuation.lift indvars_exitvalue_poison_propagated_cexInputs)
      indvars_exitvalue_poison_propagated_cexState).isSome = true := by
  decide +kernel

def indvars_exitvalue_poison_propagated_sepBool (A B : ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 32]
              × InstCombine.LLVMMemory.State)) : Bool :=
  match A, B with
  | none, _ => true
  | some _, none => false
  | some a, some b => decide (a.1 ⊑ b.1)

theorem indvars_exitvalue_poison_propagated_refute_of_sepBool (A B : ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 32]
              × InstCombine.LLVMMemory.State))
    (h : indvars_exitvalue_poison_propagated_sepBool A B = false) : ¬ (A ⊑ B) := by
  intro hab
  cases hab with
  | immediateUBLeft => simp [indvars_exitvalue_poison_propagated_sepBool] at h
  | bothValues hp =>
      simp only [indvars_exitvalue_poison_propagated_sepBool, decide_eq_false_iff_not] at h
      exact h hp.1

theorem indvars_exitvalue_poison_propagated_pointwise_cex :
    ¬ (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel indvars_exitvalue_poison_propagated_cexFuel indvars_exitvalue_poison_propagated_src
          (V := InstCombine.InputValuation.lift indvars_exitvalue_poison_propagated_cexInputs) indvars_exitvalue_poison_propagated_cexState ⊑
       InstCombine.LLVMMemory.Com.denoteWithMemoryFuel indvars_exitvalue_poison_propagated_cexFuel indvars_exitvalue_poison_propagated_tgt_impure
          (V := InstCombine.InputValuation.lift indvars_exitvalue_poison_propagated_cexInputs) indvars_exitvalue_poison_propagated_cexState) :=
  indvars_exitvalue_poison_propagated_refute_of_sepBool _ _ (by decide +kernel)

theorem indvars_exitvalue_poison_propagated_correct_counterexample_witness :
    ¬ (InstCombine.IsRefinedByOnIntWInputsWithMemory indvars_exitvalue_poison_propagated_src indvars_exitvalue_poison_propagated_tgt_impure) :=
  fun h => indvars_exitvalue_poison_propagated_pointwise_cex (h indvars_exitvalue_poison_propagated_cexInputs indvars_exitvalue_poison_propagated_cexState indvars_exitvalue_poison_propagated_cexFuel)

theorem indvars_exitvalue_poison_propagated_audit_relation_is_memory :
    (indvars_exitvalue_poison_propagated_src ⊑ indvars_exitvalue_poison_propagated_tgt_impure)
      = InstCombine.IsRefinedByOnIntWInputsWithMemory indvars_exitvalue_poison_propagated_src indvars_exitvalue_poison_propagated_tgt_impure := rfl

theorem indvars_exitvalue_poison_propagated_correct_counterexample_bare : ¬ (indvars_exitvalue_poison_propagated_src ⊑ indvars_exitvalue_poison_propagated_tgt_impure) :=
  indvars_exitvalue_poison_propagated_audit_relation_is_memory ▸ indvars_exitvalue_poison_propagated_correct_counterexample_witness

end indvars_exitvalue_poison_propagated_cex

theorem indvars_exitvalue_poison_propagated_correct_counterexample :
    ∃ (V : InstCombine.InputValuation (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]))
      (s : InstCombine.LLVMMemory.State) (fuel : Nat) (_hf : 0 < fuel),
      ¬ (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel fuel indvars_exitvalue_poison_propagated_src
            (V := InstCombine.InputValuation.lift V) s ⊑
         InstCombine.LLVMMemory.Com.denoteWithMemoryFuel fuel indvars_exitvalue_poison_propagated_tgt_impure
            (V := InstCombine.InputValuation.lift V) s) :=
  ⟨indvars_exitvalue_poison_propagated_cexInputs, indvars_exitvalue_poison_propagated_cexState, indvars_exitvalue_poison_propagated_cexFuel, by decide, indvars_exitvalue_poison_propagated_pointwise_cex⟩
