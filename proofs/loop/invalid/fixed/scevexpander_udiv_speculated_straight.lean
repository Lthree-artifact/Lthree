import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def scevexpander_udiv_speculated_straight_src :=
  [llvm()| {
  llvm.func @scevexpander_udiv_speculated_straight_src(%d : i32, %g : i32) -> i32 {
  ^entry(%d : i32, %g : i32):
    %e_zero = llvm.mlir.constant 0 : i32
    %e_guard = llvm.icmp "ne" %g, %e_zero : i32
    llvm.cond_br %e_guard : i1, ^out(%e_zero : i32), ^loop(%e_zero : i32, %e_zero : i32)
  ^loop(%k : i32, %acc : i32):
    %l_one = llvm.mlir.constant 1 : i32
    %rem = llvm.udiv %l_one, %d : i32
    %acc_next = llvm.add %acc, %rem : i32
    %k1 = llvm.add %k, %l_one : i32
    %l_two = llvm.mlir.constant 2 : i32
    %cond = llvm.icmp "eq" %k1, %l_two : i32
    llvm.cond_br %cond : i1, ^out(%acc_next : i32), ^loop(%k1 : i32, %acc_next : i32)
  ^out(%res : i32):
    llvm.return %res : i32
  }
  }]

def scevexpander_udiv_speculated_straight_tgt :=
  [llvm()| {
  llvm.func @scevexpander_udiv_speculated_straight_tgt(%d : i32, %g : i32) -> i32 {
  ^entry(%d : i32, %g : i32):
    %l_one = llvm.mlir.constant 1 : i32
    %rem = llvm.udiv %l_one, %d : i32
    %r = llvm.add %rem, %rem : i32
    llvm.return %r : i32
  }
  }]

section scevexpander_udiv_speculated_straight_cex

set_option maxRecDepth 8000
set_option maxHeartbeats 40000000

def scevexpander_udiv_speculated_straight_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def scevexpander_udiv_speculated_straight_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def scevexpander_udiv_speculated_straight_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => scevexpander_udiv_speculated_straight_ivCons x (scevexpander_udiv_speculated_straight_ivOfHVector xs)

@[simp] theorem scevexpander_udiv_speculated_straight_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    scevexpander_udiv_speculated_straight_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [scevexpander_udiv_speculated_straight_ivOfHVector, scevexpander_udiv_speculated_straight_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [scevexpander_udiv_speculated_straight_ivOfHVector, scevexpander_udiv_speculated_straight_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance scevexpander_udiv_speculated_straight_decRefSemVal (a b : LLVM.SemVal (BitVec 32)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance scevexpander_udiv_speculated_straight_decRefIntW (a b : LLVM.IntW 32) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 32)) (LLVM.SemVal (BitVec 32)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance scevexpander_udiv_speculated_straight_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 32)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 32)) (ImmediateUBOr (LLVM.IntW 32))
        inferInstance a b) := inferInstance
  exact d

local instance scevexpander_udiv_speculated_straight_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 32]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

def scevexpander_udiv_speculated_straight_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]) :=
  scevexpander_udiv_speculated_straight_ivOfHVector
    (.cons (scevexpander_udiv_speculated_straight_valueOfNat 32 4294967295) (.cons (scevexpander_udiv_speculated_straight_valueOfNat 32 1) .nil))

def scevexpander_udiv_speculated_straight_cexState : InstCombine.LLVMMemory.State := default

def scevexpander_udiv_speculated_straight_cexFuel : Nat := 2

abbrev scevexpander_udiv_speculated_straight_tgt_impure :
    Com InstCombine.LLVM (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]) .impure
      [InstCombine.LLVM.Ty.bitvec 32] :=
  scevexpander_udiv_speculated_straight_tgt.castPureToEff .impure

theorem scevexpander_udiv_speculated_straight_src_terminates_at_cexFuel :
    (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel scevexpander_udiv_speculated_straight_cexFuel scevexpander_udiv_speculated_straight_src
      (V := InstCombine.InputValuation.lift scevexpander_udiv_speculated_straight_cexInputs)
      scevexpander_udiv_speculated_straight_cexState).isSome = true := by
  decide +kernel

theorem scevexpander_udiv_speculated_straight_tgt_terminates_at_cexFuel :
    (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel scevexpander_udiv_speculated_straight_cexFuel scevexpander_udiv_speculated_straight_tgt_impure
      (V := InstCombine.InputValuation.lift scevexpander_udiv_speculated_straight_cexInputs)
      scevexpander_udiv_speculated_straight_cexState).isSome = true := by
  decide +kernel

def scevexpander_udiv_speculated_straight_sepBool (A B : ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 32]
              × InstCombine.LLVMMemory.State)) : Bool :=
  match A, B with
  | none, _ => true
  | some _, none => false
  | some a, some b => decide (a.1 ⊑ b.1)

theorem scevexpander_udiv_speculated_straight_refute_of_sepBool (A B : ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 32]
              × InstCombine.LLVMMemory.State))
    (h : scevexpander_udiv_speculated_straight_sepBool A B = false) : ¬ (A ⊑ B) := by
  intro hab
  cases hab with
  | immediateUBLeft => simp [scevexpander_udiv_speculated_straight_sepBool] at h
  | bothValues hp =>
      simp only [scevexpander_udiv_speculated_straight_sepBool, decide_eq_false_iff_not] at h
      exact h hp.1

theorem scevexpander_udiv_speculated_straight_pointwise_cex :
    ¬ (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel scevexpander_udiv_speculated_straight_cexFuel scevexpander_udiv_speculated_straight_src
          (V := InstCombine.InputValuation.lift scevexpander_udiv_speculated_straight_cexInputs) scevexpander_udiv_speculated_straight_cexState ⊑
       InstCombine.LLVMMemory.Com.denoteWithMemoryFuel scevexpander_udiv_speculated_straight_cexFuel scevexpander_udiv_speculated_straight_tgt_impure
          (V := InstCombine.InputValuation.lift scevexpander_udiv_speculated_straight_cexInputs) scevexpander_udiv_speculated_straight_cexState) :=
  scevexpander_udiv_speculated_straight_refute_of_sepBool _ _ (by decide +kernel)

theorem scevexpander_udiv_speculated_straight_correct_counterexample_witness :
    ¬ (InstCombine.IsRefinedByOnIntWInputsWithMemory scevexpander_udiv_speculated_straight_src scevexpander_udiv_speculated_straight_tgt_impure) :=
  fun h => scevexpander_udiv_speculated_straight_pointwise_cex (h scevexpander_udiv_speculated_straight_cexInputs scevexpander_udiv_speculated_straight_cexState scevexpander_udiv_speculated_straight_cexFuel)

theorem scevexpander_udiv_speculated_straight_audit_relation_is_memory :
    (scevexpander_udiv_speculated_straight_src ⊑ scevexpander_udiv_speculated_straight_tgt_impure)
      = InstCombine.IsRefinedByOnIntWInputsWithMemory scevexpander_udiv_speculated_straight_src scevexpander_udiv_speculated_straight_tgt_impure := rfl

theorem scevexpander_udiv_speculated_straight_correct_counterexample_bare : ¬ (scevexpander_udiv_speculated_straight_src ⊑ scevexpander_udiv_speculated_straight_tgt_impure) :=
  scevexpander_udiv_speculated_straight_audit_relation_is_memory ▸ scevexpander_udiv_speculated_straight_correct_counterexample_witness

end scevexpander_udiv_speculated_straight_cex

theorem scevexpander_udiv_speculated_straight_correct_counterexample :
    ∃ (V : InstCombine.InputValuation (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]))
      (s : InstCombine.LLVMMemory.State) (fuel : Nat) (_hf : 0 < fuel),
      ¬ (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel fuel scevexpander_udiv_speculated_straight_src
            (V := InstCombine.InputValuation.lift V) s ⊑
         InstCombine.LLVMMemory.Com.denoteWithMemoryFuel fuel scevexpander_udiv_speculated_straight_tgt_impure
            (V := InstCombine.InputValuation.lift V) s) :=
  ⟨scevexpander_udiv_speculated_straight_cexInputs, scevexpander_udiv_speculated_straight_cexState, scevexpander_udiv_speculated_straight_cexFuel, by decide, scevexpander_udiv_speculated_straight_pointwise_cex⟩
