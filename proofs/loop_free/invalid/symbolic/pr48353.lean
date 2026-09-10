import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr48353_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr48353_src(%aj : _) -> _ {
  ^bb0(%aj : _):
    %c_i32_1 = llvm.mlir.constant(1 : _) : _
    %cmp_i = llvm.icmp "sgt" %aj, %c_i32_1 : _
    %c_i32_3 = llvm.mlir.constant(3 : _) : _
    %aj_op = llvm.lshr %c_i32_3, %aj : _
    %_op2 = llvm.and %aj_op, %c_i32_1 : _
    %c_i32_0 = llvm.mlir.constant(0 : _) : _
    %cmp41 = llvm.icmp "ne" %_op2, %c_i32_0 : _
    %c_i1_1 = llvm.mlir.constant(1 : i1) : i1
    %cmp4 = llvm.select %cmp_i, %c_i1_1, %cmp41 : i1
    %conv5 = llvm.zext %cmp4 : i1 to _
    llvm.return %conv5 : _
  }
  }]

def pr48353_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr48353_tgt(%aj : _) -> _ {
  ^bb0(%aj : _):
    %c_i32_1 = llvm.mlir.constant(1 : _) : _
    %cmp_i = llvm.icmp "sgt" %aj, %c_i32_1 : _
    %c_i32_3 = llvm.mlir.constant(3 : _) : _
    %aj_op = llvm.lshr %c_i32_3, %aj : _
    %_op2 = llvm.and %aj_op, %c_i32_1 : _
    %c_i32_0 = llvm.mlir.constant(0 : _) : _
    %cmp41 = llvm.icmp "ne" %_op2, %c_i32_0 : _
    %cmp4 = llvm.or %cmp_i, %cmp41 : i1
    %conv5 = llvm.zext %cmp4 : i1 to _
    llvm.return %conv5 : _
  }
  }]

section pr48353_cex

def pr48353_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def pr48353_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def pr48353_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => pr48353_ivCons x (pr48353_ivOfHVector xs)

@[simp] theorem pr48353_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    pr48353_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [pr48353_ivOfHVector, pr48353_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [pr48353_ivOfHVector, pr48353_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance pr48353_decRefSemVal (a b : LLVM.SemVal (BitVec 3)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance pr48353_decRefIntW (a b : LLVM.IntW 3) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 3)) (LLVM.SemVal (BitVec 3)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance pr48353_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 3)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 3)) (ImmediateUBOr (LLVM.IntW 3))
        inferInstance a b) := inferInstance
  exact d

local instance pr48353_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance pr48353_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def pr48353_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 3]) :=
  pr48353_ivOfHVector
    (.cons (pr48353_valueOfNat 3 3) .nil)

theorem pr48353_correct_counterexample_witness : ¬ (pr48353_src 3 ⊑ pr48353_tgt 3) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (pr48353_src 3) (pr48353_tgt 3) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (pr48353_src 3) (pr48353_tgt 3)).mp h
  specialize hyp pr48353_cexInputs
  revert hyp
  decide

end pr48353_cex

theorem pr48353_correct_counterexample :
    ∃ (w : Nat), ¬ (pr48353_src w ⊑ pr48353_tgt w) :=
  ⟨3, pr48353_correct_counterexample_witness⟩
