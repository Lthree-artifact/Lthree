import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i115454_InstCombine_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i115454_InstCombine_src(%x : _, %y : _) -> _ {
  ^bb0(%x : _, %y : _):
    %a = llvm.sub %x, %y overflow<nsw> : _
    %b = llvm.sub %y, %x overflow<nsw,nuw> : _
    %c_i32_4294967295 = llvm.mlir.constant(4294967295 : _) : _
    %cmp = llvm.icmp "sgt" %x, %c_i32_4294967295 : _
    %cond = llvm.select %cmp, %a, %b : _
    %c_i32_0 = llvm.mlir.constant(0 : _) : _
    %sub16 = llvm.sub %c_i32_0, %cond overflow<nsw> : _
    llvm.return %sub16 : _
  }
  }]

def i115454_InstCombine_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i115454_InstCombine_tgt(%x : _, %y : _) -> _ {
  ^bb0(%x : _, %y : _):
    %a = llvm.sub %x, %y overflow<nsw> : _
    %b = llvm.sub %y, %x overflow<nsw,nuw> : _
    %c_i32_0 = llvm.mlir.constant(0 : _) : _
    %cmp1 = llvm.icmp "slt" %x, %c_i32_0 : _
    %v1 = llvm.select %cmp1, %a, %b : _
    llvm.return %v1 : _
  }
  }]

section i115454_InstCombine_cex

def i115454_InstCombine_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def i115454_InstCombine_ivCons {Γ : Ctxt InstCombine.LLVM.Ty} {t : InstCombine.LLVM.Ty}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def i115454_InstCombine_ivOfHVector {types : List InstCombine.LLVM.Ty} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => i115454_InstCombine_ivCons x (i115454_InstCombine_ivOfHVector xs)

@[simp] theorem i115454_InstCombine_ivOfHVector_apply {types : List InstCombine.LLVM.Ty}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    i115454_InstCombine_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [i115454_InstCombine_ivOfHVector, i115454_InstCombine_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [i115454_InstCombine_ivOfHVector, i115454_InstCombine_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm

local instance i115454_InstCombine_decRefSemVal (a b : LLVM.SemVal (BitVec 2)) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance i115454_InstCombine_decRefIntW (a b : LLVM.IntW 2) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec 2)) (LLVM.SemVal (BitVec 2)) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance i115454_InstCombine_decRefElt (a b : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 2)) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW 2)) (ImmediateUBOr (LLVM.IntW 2))
        inferInstance a b) := inferInstance
  exact d

local instance i115454_InstCombine_decRefRet (a b : HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl

local instance i115454_InstCombine_decRefDenote
    (a : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]))
    (b : EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2])) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2])) (ImmediateUBOr (HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 2]))
        inferInstance (ImmediateUBOr.value a) (ImmediateUBOr.value b)) := inferInstance
  exact d

def i115454_InstCombine_cexInputs : InstCombine.InputValuation
    (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 2, InstCombine.LLVM.Ty.bitvec 2]) :=
  i115454_InstCombine_ivOfHVector
    (.cons (i115454_InstCombine_valueOfNat 2 0) (.cons (i115454_InstCombine_valueOfNat 2 1) .nil))

theorem i115454_InstCombine_correct_counterexample_witness : ¬ (i115454_InstCombine_src 2 ⊑ i115454_InstCombine_tgt 2) := by
  intro h
  have hyp : InstCombine.IsRefinedByOnIntWInputs (i115454_InstCombine_src 2) (i115454_InstCombine_tgt 2) :=
    (InstCombine.isRefinedByOnIntWInputs_iff (i115454_InstCombine_src 2) (i115454_InstCombine_tgt 2)).mp h
  specialize hyp i115454_InstCombine_cexInputs
  revert hyp
  decide

end i115454_InstCombine_cex

theorem i115454_InstCombine_correct_counterexample :
    ∃ (w : Nat), ¬ (i115454_InstCombine_src w ⊑ i115454_InstCombine_tgt w) :=
  ⟨2, i115454_InstCombine_correct_counterexample_witness⟩
