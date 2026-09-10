import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr140526_smax_udiv_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr140526_smax_udiv_src(%x : _, %y : _, %z : _) -> _ {
  ^bb0(%x : _, %y : _, %z : _):
    %max_c = llvm.icmp "sgt" %x, %y : _
    %max = llvm.select %max_c, %x, %y : _
    %res = llvm.udiv %max, %z : _
    llvm.return %res : _
  }
  }]

def pr140526_smax_udiv_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr140526_smax_udiv_tgt(%x : _, %y : _, %z : _) -> _ {
  ^bb0(%x : _, %y : _, %z : _):
    %xz = llvm.udiv %x, %z : _
    %yz = llvm.udiv %y, %z : _
    %res_c = llvm.icmp "sgt" %xz, %yz : _
    %res = llvm.select %res_c, %xz, %yz : _
    llvm.return %res : _
  }
  }]

section pr140526_smax_udiv_cex

def pr140526_smax_udiv_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def pr140526_smax_udiv_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def pr140526_smax_udiv_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => pr140526_smax_udiv_ivCons x (pr140526_smax_udiv_ivOfHVector xs)

@[simp] theorem pr140526_smax_udiv_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    pr140526_smax_udiv_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [pr140526_smax_udiv_ivOfHVector, pr140526_smax_udiv_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [pr140526_smax_udiv_ivOfHVector, pr140526_smax_udiv_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance pr140526_smax_udiv_decRefSemVal (a b : LLVM.SemVal (BitVec 2)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance pr140526_smax_udiv_decRefIntW (a b : LLVM.IntW 2) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 2)) (LLVM.SemVal (BitVec 2)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance pr140526_smax_udiv_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 2)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 2)) (ImmediateUBOr (LLVM.IntW 2))
        inferInstance a b) := inferInstance
  exact d

local instance pr140526_smax_udiv_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance pr140526_smax_udiv_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def pr140526_smax_udiv_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 2, InstCombine.LLVM.Ty.bitvec 2, InstCombine.LLVM.Ty.bitvec 2]) :=
  pr140526_smax_udiv_ivOfHVector
    (.cons (pr140526_smax_udiv_valueOfNat 2 2) (.cons (pr140526_smax_udiv_valueOfNat 2 2) (.cons (pr140526_smax_udiv_valueOfNat 2 0) .nil)))

theorem pr140526_smax_udiv_correct_counterexample_witness : ¬ (pr140526_smax_udiv_src 2 ⊑ pr140526_smax_udiv_tgt 2) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (pr140526_smax_udiv_src 2) (pr140526_smax_udiv_tgt 2) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (pr140526_smax_udiv_src 2) (pr140526_smax_udiv_tgt 2)).mp h
  specialize hyp pr140526_smax_udiv_cexInputs
  revert hyp
  decide

end pr140526_smax_udiv_cex

theorem pr140526_smax_udiv_correct_counterexample :
    ∃ (w : Nat), ¬ (pr140526_smax_udiv_src w ⊑ pr140526_smax_udiv_tgt w) :=
  ⟨2, pr140526_smax_udiv_correct_counterexample_witness⟩
