import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr49688_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr49688_src(%g : _, %h : _) -> _ {
  ^bb0(%g : _, %h : _):
    %c_i32_0 = llvm.mlir.constant(0 : _) : _
    %cmp = llvm.icmp "slt" %g, %c_i32_0 : _
    %c_i32_7 = llvm.mlir.constant(7 : _) : _
    %shr = llvm.ashr %c_i32_7, %h : _
    %cmp1 = llvm.icmp "sgt" %g, %shr : _
    %c_i1_true = llvm.mlir.constant(true) : i1
    %0 = llvm.select %cmp, %c_i1_true, %cmp1 : i1
    %lor_ext = llvm.zext %0 : i1 to _
    llvm.return %lor_ext : _
  }
  }]

def pr49688_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr49688_tgt(%g : _, %h : _) -> _ {
  ^bb0(%g : _, %h : _):
    %c_i32_7 = llvm.mlir.constant(7 : _) : _
    %shr = llvm.lshr %c_i32_7, %h : _
    %0 = llvm.icmp "ult" %shr, %g : _
    %lor_ext = llvm.zext %0 : i1 to _
    llvm.return %lor_ext : _
  }
  }]

section pr49688_cex

def pr49688_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def pr49688_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def pr49688_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => pr49688_ivCons x (pr49688_ivOfHVector xs)

@[simp] theorem pr49688_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    pr49688_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [pr49688_ivOfHVector, pr49688_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [pr49688_ivOfHVector, pr49688_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance pr49688_decRefSemVal (a b : LLVM.SemVal (BitVec 1)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance pr49688_decRefIntW (a b : LLVM.IntW 1) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 1)) (LLVM.SemVal (BitVec 1)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance pr49688_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 1)) (ImmediateUBOr (LLVM.IntW 1))
        inferInstance a b) := inferInstance
  exact d

local instance pr49688_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance pr49688_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def pr49688_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec 1]) :=
  pr49688_ivOfHVector
    (.cons (pr49688_valueOfNat 1 0) (.cons (pr49688_valueOfNat 1 0) .nil))

theorem pr49688_correct_counterexample_witness : ¬ (pr49688_src 1 ⊑ pr49688_tgt 1) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (pr49688_src 1) (pr49688_tgt 1) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (pr49688_src 1) (pr49688_tgt 1)).mp h
  specialize hyp pr49688_cexInputs
  revert hyp
  decide

end pr49688_cex

theorem pr49688_correct_counterexample :
    ∃ (w : Nat), ¬ (pr49688_src w ⊑ pr49688_tgt w) :=
  ⟨1, pr49688_correct_counterexample_witness⟩
