import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i115456_InstCombine_X_Y_X_Y_src :=
  [llvm()| {
  llvm.func @i115456_InstCombine_X_Y_X_Y_src(%b : i32, %z : i32) -> i32 {
  ^bb0(%b : i32, %z : i32):
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %c = llvm.sub %c_i32_0, %z : i32
    %v1 = llvm.sdiv %z, %c : i32
    %d = llvm.mul %v1, %b overflow<nsw> : i32
    %e = llvm.mul %c, %d : i32
    llvm.return %e : i32
  }
  }]

def i115456_InstCombine_X_Y_X_Y_tgt :=
  [llvm()| {
  llvm.func @i115456_InstCombine_X_Y_X_Y_tgt(%b : i32, %z : i32) -> i32 {
  ^bb0(%b : i32, %z : i32):
    %c_i32_2147483648 = llvm.mlir.constant(2147483648 : i32) : i32
    %v1 = llvm.icmp "eq" %z, %c_i32_2147483648 : i32
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %v2 = llvm.sub %c_i32_0, %b overflow<nsw> : i32
    %v3 = llvm.select %v1, %v2, %b : i32
    %_neg = llvm.mul %v3, %z : i32
    llvm.return %_neg : i32
  }
  }]

section i115456_InstCombine_X_Y_X_Y_cex

def i115456_InstCombine_X_Y_X_Y_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def i115456_InstCombine_X_Y_X_Y_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def i115456_InstCombine_X_Y_X_Y_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => i115456_InstCombine_X_Y_X_Y_ivCons x (i115456_InstCombine_X_Y_X_Y_ivOfHVector xs)

@[simp] theorem i115456_InstCombine_X_Y_X_Y_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    i115456_InstCombine_X_Y_X_Y_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [i115456_InstCombine_X_Y_X_Y_ivOfHVector, i115456_InstCombine_X_Y_X_Y_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [i115456_InstCombine_X_Y_X_Y_ivOfHVector, i115456_InstCombine_X_Y_X_Y_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance i115456_InstCombine_X_Y_X_Y_decRefSemVal (a b : LLVM.SemVal (BitVec 32)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance i115456_InstCombine_X_Y_X_Y_decRefIntW (a b : LLVM.IntW 32) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 32)) (LLVM.SemVal (BitVec 32)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance i115456_InstCombine_X_Y_X_Y_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 32)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 32)) (ImmediateUBOr (LLVM.IntW 32))
        inferInstance a b) := inferInstance
  exact d

local instance i115456_InstCombine_X_Y_X_Y_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 32]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance i115456_InstCombine_X_Y_X_Y_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 32]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 32])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 32])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 32]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def i115456_InstCombine_X_Y_X_Y_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]) :=
  i115456_InstCombine_X_Y_X_Y_ivOfHVector
    (.cons (i115456_InstCombine_X_Y_X_Y_valueOfNat 32 2147483648) (.cons (i115456_InstCombine_X_Y_X_Y_valueOfNat 32 2147483648) .nil))

theorem i115456_InstCombine_X_Y_X_Y_correct_counterexample_witness : ¬ (i115456_InstCombine_X_Y_X_Y_src ⊑ i115456_InstCombine_X_Y_X_Y_tgt) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (i115456_InstCombine_X_Y_X_Y_src) (i115456_InstCombine_X_Y_X_Y_tgt) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (i115456_InstCombine_X_Y_X_Y_src) (i115456_InstCombine_X_Y_X_Y_tgt)).mp h
  specialize hyp i115456_InstCombine_X_Y_X_Y_cexInputs
  revert hyp
  decide

end i115456_InstCombine_X_Y_X_Y_cex

theorem i115456_InstCombine_X_Y_X_Y_correct_counterexample : ¬ (i115456_InstCombine_X_Y_X_Y_src ⊑ i115456_InstCombine_X_Y_X_Y_tgt) :=
  i115456_InstCombine_X_Y_X_Y_correct_counterexample_witness
