import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr121633_srem_mul_mul_assume_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr121633_srem_mul_mul_assume_src(%x : _, %y : _, %z : _) -> _ {
  ^bb0(%x : _, %y : _, %z : _):
    %remc = llvm.srem %y, %z : _
    %cond = llvm.icmp "eq" %remc, %y : _
    llvm.assume %cond : i1
    %mul1 = llvm.mul %x, %y : _
    %mul2 = llvm.mul %x, %z : _
    %rem = llvm.srem %mul1, %mul2 : _
    llvm.return %rem : _
  }
  }]

def pr121633_srem_mul_mul_assume_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr121633_srem_mul_mul_assume_tgt(%x : _, %y : _, %z : _) -> _ {
  ^bb0(%x : _, %y : _, %z : _):
    %mul = llvm.mul %x, %y : _
    llvm.return %mul : _
  }
  }]

section pr121633_srem_mul_mul_assume_cex

def pr121633_srem_mul_mul_assume_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def pr121633_srem_mul_mul_assume_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def pr121633_srem_mul_mul_assume_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => pr121633_srem_mul_mul_assume_ivCons x (pr121633_srem_mul_mul_assume_ivOfHVector xs)

@[simp] theorem pr121633_srem_mul_mul_assume_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    pr121633_srem_mul_mul_assume_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [pr121633_srem_mul_mul_assume_ivOfHVector, pr121633_srem_mul_mul_assume_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [pr121633_srem_mul_mul_assume_ivOfHVector, pr121633_srem_mul_mul_assume_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance pr121633_srem_mul_mul_assume_decRefSemVal (a b : LLVM.SemVal (BitVec 3)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance pr121633_srem_mul_mul_assume_decRefIntW (a b : LLVM.IntW 3) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 3)) (LLVM.SemVal (BitVec 3)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance pr121633_srem_mul_mul_assume_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 3)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 3)) (ImmediateUBOr (LLVM.IntW 3))
        inferInstance a b) := inferInstance
  exact d

local instance pr121633_srem_mul_mul_assume_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance pr121633_srem_mul_mul_assume_decRefDenote
    (a : EffectKind.impure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 3]))
        inferInstance a (ImmediateUBOr.value b)) := inferInstance
  exact d

def pr121633_srem_mul_mul_assume_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 3, InstCombine.LLVM.Ty.bitvec 3, InstCombine.LLVM.Ty.bitvec 3]) :=
  pr121633_srem_mul_mul_assume_ivOfHVector
    (.cons (pr121633_srem_mul_mul_assume_valueOfNat 3 2) (.cons (pr121633_srem_mul_mul_assume_valueOfNat 3 1) (.cons (pr121633_srem_mul_mul_assume_valueOfNat 3 3) .nil)))

theorem pr121633_srem_mul_mul_assume_correct_counterexample_witness : ¬ (pr121633_srem_mul_mul_assume_src 3 ⊑ pr121633_srem_mul_mul_assume_tgt 3) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (pr121633_srem_mul_mul_assume_src 3) (pr121633_srem_mul_mul_assume_tgt 3) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (pr121633_srem_mul_mul_assume_src 3) (pr121633_srem_mul_mul_assume_tgt 3)).mp h
  specialize hyp pr121633_srem_mul_mul_assume_cexInputs
  revert hyp
  decide

end pr121633_srem_mul_mul_assume_cex

theorem pr121633_srem_mul_mul_assume_correct_counterexample :
    ∃ (w : Nat), ¬ (pr121633_srem_mul_mul_assume_src w ⊑ pr121633_srem_mul_mul_assume_tgt w) :=
  ⟨3, pr121633_srem_mul_mul_assume_correct_counterexample_witness⟩
