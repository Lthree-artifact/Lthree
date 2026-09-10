import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr39510_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr39510_src(%a : _) -> i1 {
  ^bb0(%a : _):
    %c_i32_0 = llvm.mlir.constant(0 : _) : _
    %cmp = llvm.icmp "slt" %a, %c_i32_0 : _
    %sub = llvm.sub %c_i32_0, %a overflow<nsw> : _
    %cond = llvm.select %cmp, %sub, %a : _
    %c_i32_2 = llvm.mlir.constant(2 : _) : _
    %r = llvm.icmp "ne" %cond, %c_i32_2 : _
    llvm.return %r : i1
  }
  }]

def pr39510_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr39510_tgt(%a : _) -> i1 {
  ^bb0(%a : _):
    %c_i1_1 = llvm.mlir.constant(1 : i1) : i1
    llvm.return %c_i1_1 : i1
  }
  }]

section pr39510_cex

def pr39510_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def pr39510_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def pr39510_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => pr39510_ivCons x (pr39510_ivOfHVector xs)

@[simp] theorem pr39510_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    pr39510_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [pr39510_ivOfHVector, pr39510_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [pr39510_ivOfHVector, pr39510_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance pr39510_decRefSemVal (a b : LLVM.SemVal (BitVec 1)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance pr39510_decRefIntW (a b : LLVM.IntW 1) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 1)) (LLVM.SemVal (BitVec 1)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance pr39510_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 1)) (ImmediateUBOr (LLVM.IntW 1))
        inferInstance a b) := inferInstance
  exact d

local instance pr39510_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance pr39510_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def pr39510_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 1]) :=
  pr39510_ivOfHVector
    (.cons (pr39510_valueOfNat 1 0) .nil)

theorem pr39510_correct_counterexample_witness : ¬ (pr39510_src 1 ⊑ pr39510_tgt 1) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (pr39510_src 1) (pr39510_tgt 1) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (pr39510_src 1) (pr39510_tgt 1)).mp h
  specialize hyp pr39510_cexInputs
  revert hyp
  decide

end pr39510_cex

theorem pr39510_correct_counterexample :
    ∃ (w : Nat), ¬ (pr39510_src w ⊑ pr39510_tgt w) :=
  ⟨1, pr39510_correct_counterexample_witness⟩
