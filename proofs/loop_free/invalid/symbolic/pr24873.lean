import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr24873_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr24873_src(%V : _) -> i1 {
  ^bb0(%V : _):
    %c_i64_m4611686018427387904 = llvm.mlir.constant(-4611686018427387904 : _) : _
    %ashr = llvm.ashr %c_i64_m4611686018427387904, %V : _
    %c_i64_m1 = llvm.mlir.constant(-1 : _) : _
    %icmp = llvm.icmp "eq" %ashr, %c_i64_m1 : _
    llvm.return %icmp : i1
  }
  }]

def pr24873_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr24873_tgt(%V : _) -> i1 {
  ^bb0(%V : _):
    %c_i64_62 = llvm.mlir.constant(62 : _) : _
    %icmp = llvm.icmp "eq" %V, %c_i64_62 : _
    llvm.return %icmp : i1
  }
  }]

section pr24873_cex

def pr24873_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def pr24873_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def pr24873_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => pr24873_ivCons x (pr24873_ivOfHVector xs)

@[simp] theorem pr24873_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    pr24873_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [pr24873_ivOfHVector, pr24873_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [pr24873_ivOfHVector, pr24873_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance pr24873_decRefSemVal (a b : LLVM.SemVal (BitVec 1)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance pr24873_decRefIntW (a b : LLVM.IntW 1) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 1)) (LLVM.SemVal (BitVec 1)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance pr24873_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 1)) (ImmediateUBOr (LLVM.IntW 1))
        inferInstance a b) := inferInstance
  exact d

local instance pr24873_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance pr24873_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def pr24873_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 1]) :=
  pr24873_ivOfHVector
    (.cons (pr24873_valueOfNat 1 0) .nil)

theorem pr24873_correct_counterexample_witness : ¬ (pr24873_src 1 ⊑ pr24873_tgt 1) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (pr24873_src 1) (pr24873_tgt 1) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (pr24873_src 1) (pr24873_tgt 1)).mp h
  specialize hyp pr24873_cexInputs
  revert hyp
  decide

end pr24873_cex

theorem pr24873_correct_counterexample :
    ∃ (w : Nat), ¬ (pr24873_src w ⊑ pr24873_tgt w) :=
  ⟨1, pr24873_correct_counterexample_witness⟩
