import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def hydra33_src :=
  [llvm()| {
  llvm.func @hydra33_src(%x : i32, %C : i32, %C1 : i32, %C2 : i32) -> i32 {
  ^bb0(%x : i32, %C : i32, %C1 : i32, %C2 : i32):
    %zero = llvm.mlir.constant(0 : i32) : i32
    %uint_max = llvm.mlir.constant(4294967295 : i32) : i32
    %C_not_zero = llvm.icmp "ne" %C, %zero : i32
    llvm.assume %C_not_zero : i1
    %overflow_limit = llvm.udiv %uint_max, %C : i32
    %ov = llvm.icmp "ugt" %x, %overflow_limit : i32
    %mul = llvm.mul %x, %C : i32
    %cmp = llvm.icmp "ugt" %mul, %C1 : i32
    %or = llvm.or %ov, %cmp : i1
    %sel = llvm.select %or, %C2, %mul : i32
    llvm.return %sel : i32
  }
  }]

def hydra33_tgt :=
  [llvm()| {
  llvm.func @hydra33_tgt(%x : i32, %C : i32, %C1 : i32, %C2 : i32) -> i32 {
  ^bb0(%x : i32, %C : i32, %C1 : i32, %C2 : i32):
    %zero = llvm.mlir.constant(0 : i32) : i32
    %C_not_zero = llvm.icmp "ne" %C, %zero : i32
    llvm.assume %C_not_zero : i1
    %limit = llvm.udiv %C1, %C : i32
    %is_bigger = llvm.icmp "ugt" %x, %limit : i32
    %product = llvm.mul %x, %C : i32
    %r = llvm.select %is_bigger, %C2, %product : i32
    llvm.return %r : i32
  }
  }]

private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by
  cases b <;> simp

private theorem hydra33_semval_bind_poison {α β : Type} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl

private theorem hydra33_udiv_eq_if {w : Nat} {x y : BitVec w} :
    LLVM.udiv (LLVM.SemVal.value x) (LLVM.SemVal.value y) =
      (if y = 0#w then (.immediateUB : LLVM.IntWUB w)
       else (.value (x / y) : LLVM.IntWUB w)) := by
  simp [LLVM.udiv]

private theorem hydra33_udiv_poisonL {w : Nat} (y : LLVM.IntW w) (f : LLVM.ExactFlag) :
    LLVM.udiv (LLVM.SemVal.poison) y f = (.poison : LLVM.IntWUB w) := rfl

private theorem hydra33_udiv_poisonR {w : Nat} (x : LLVM.IntW w) (f : LLVM.ExactFlag) :
    LLVM.udiv x (LLVM.SemVal.poison) f = (.poison : LLVM.IntWUB w) := by
  cases x <;> rfl

private theorem hydra33_ite_semval_value {w : Nat} {c : Prop} [Decidable c]
    (a b : BitVec w) :
    (if c then LLVM.SemVal.value a else LLVM.SemVal.value b) =
      LLVM.SemVal.value (if c then a else b) := by
  split <;> rfl

private theorem hydra33_value (x : BitVec 32) (C : BitVec 32) (C1 : BitVec 32) (C2 : BitVec 32)
    (hpre : (C != 0#32) = true)
    (hub1 : ¬ (C = 0#32)) :
    (if (((4294967295#32 / C) <ᵤ x) = true ∨ (C1 <ᵤ (x * C)) = true) then C2 else (x * C)) = (if ((C1 / C) <ᵤ x) = true then C2 else (x * C)) := by
  have _hpre_used := hpre
  have hcpos : 0 < C.toNat := by
    have hcne_nat : C.toNat ≠ 0 := by
      intro hc
      apply hub1
      apply BitVec.eq_of_toNat_eq
      simp [hc]
    exact Nat.pos_of_ne_zero hcne_nat
  have hC1_le_max : C1.toNat ≤ 4294967295 := by
    have hlt := BitVec.isLt C1
    omega
  have hiff :
      ((((4294967295#32 / C) <ᵤ x) = true ∨ (C1 <ᵤ (x * C)) = true) ↔
        ((C1 / C) <ᵤ x) = true) := by
    constructor
    · intro h
      rcases h with hA | hB
      · rw [BitVec.ult_iff_toNat_lt] at hA ⊢
        rw [BitVec.toNat_udiv] at hA ⊢
        simp [BitVec.toNat_ofNat] at hA
        have hdiv_le : C1.toNat / C.toNat ≤ 4294967295 / C.toNat :=
          Nat.div_le_div_right hC1_le_max
        exact Nat.lt_of_le_of_lt hdiv_le hA
      · rw [BitVec.ult_iff_toNat_lt] at hB ⊢
        rw [BitVec.toNat_mul] at hB
        rw [BitVec.toNat_udiv]
        have hprod : C1.toNat < x.toNat * C.toNat :=
          Nat.lt_of_lt_of_le hB (Nat.mod_le _ _)
        exact (Nat.div_lt_iff_lt_mul hcpos).2 hprod
    · intro hq
      rw [BitVec.ult_iff_toNat_lt] at hq
      rw [BitVec.toNat_udiv] at hq
      by_cases hA_nat : 4294967295 / C.toNat < x.toNat
      · left
        rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_udiv]
        simpa [BitVec.toNat_ofNat] using hA_nat
      · right
        rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_mul]
        have hprod_gt : C1.toNat < x.toNat * C.toNat :=
          (Nat.div_lt_iff_lt_mul hcpos).1 hq
        have hx_le : x.toNat ≤ 4294967295 / C.toNat := Nat.le_of_not_gt hA_nat
        have hprod_le_max : x.toNat * C.toNat ≤ 4294967295 :=
          (Nat.le_div_iff_mul_le hcpos).1 hx_le
        have hprod_lt : x.toNat * C.toNat < 2 ^ 32 := by
          omega
        rw [Nat.mod_eq_of_lt hprod_lt]
        exact hprod_gt
  by_cases hp : (((4294967295#32 / C) <ᵤ x) = true ∨ (C1 <ᵤ (x * C)) = true)
  · have hq : ((C1 / C) <ᵤ x) = true := hiff.mp hp
    simp [hp, hq]
  · have hq : ¬ (((C1 / C) <ᵤ x) = true) := by
      intro hq
      exact hp (hiff.mpr hq)
    simp [hp, hq]

set_option maxHeartbeats 4000000 in
theorem hydra33_correct : hydra33_src ⊑ hydra33_tgt := by
  intro V
  let xVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨3, by simp⟩
  let CVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨2, by simp⟩
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨1, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]) (InstCombine.LLVM.Ty.bitvec 32)
  cases hC : V CVar
  case poison =>
    simp [hydra33_src, hydra33_tgt, hydra33_semval_bind_poison, hydra33_udiv_eq_if, hydra33_udiv_poisonL, hydra33_udiv_poisonR, hydra33_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, hC, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, InstCombine.lift2UB, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C =>
    change BitVec 32 at C
    cases hcond : (C != 0#32)
    · simp [hydra33_src, hydra33_tgt, hydra33_semval_bind_poison, hydra33_udiv_eq_if, hydra33_udiv_poisonL, hydra33_udiv_poisonR, hydra33_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, hC, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, InstCombine.lift2UB, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    ·
      by_cases hub1 : C = 0#32
      ·
        simp [hydra33_src, hydra33_tgt, hydra33_semval_bind_poison, hydra33_udiv_eq_if, hydra33_udiv_poisonL, hydra33_udiv_poisonR, hydra33_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, hC, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, InstCombine.lift2UB, LLVM.assume_]
        simp [hub1]
        exact ImmediateUBOr.IsRefinedBy.bothValues (by
          constructor
          · exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
          · exact HVector.nil_isRefinedBy_nil)
      ·
        cases hC1 : V C1Var with
        | poison =>
          simp [hydra33_src, hydra33_tgt, hydra33_semval_bind_poison, hydra33_udiv_eq_if, hydra33_udiv_poisonL, hydra33_udiv_poisonR, hydra33_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, C1Var, hC, hcond, hub1, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, InstCombine.lift2UB, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.bothValues (by
            constructor
            · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                first
                | exact LLVM.SemVal.poison_isRefinedBy _
                | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                | simp [LLVM.IntW.instRefinement])
            · exact HVector.nil_isRefinedBy_nil)
        | value C1 =>
          change BitVec 32 at C1
          cases hx : V xVar with
          | poison =>
            simp [hydra33_src, hydra33_tgt, hydra33_semval_bind_poison, hydra33_udiv_eq_if, hydra33_udiv_poisonL, hydra33_udiv_poisonR, hydra33_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, C1Var, xVar, hC, hcond, hub1, hC1, hx, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, InstCombine.lift2UB, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  first
                  | exact LLVM.SemVal.poison_isRefinedBy _
                  | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                  | simp [LLVM.IntW.instRefinement])
              · exact HVector.nil_isRefinedBy_nil)
          | value x =>
            change BitVec 32 at x
            cases hC2 : V C2Var with
            | poison =>
              simp [hydra33_src, hydra33_tgt, hydra33_semval_bind_poison, hydra33_udiv_eq_if, hydra33_udiv_poisonL, hydra33_udiv_poisonR, hydra33_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, C1Var, xVar, C2Var, hC, hcond, hub1, hC1, hx, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, InstCombine.lift2UB, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.bothValues (by
                constructor
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    have hv0 := hydra33_value x C C1 (0#32) hcond hub1
                    have hv1 := hydra33_value x C C1 (1#32) hcond hub1
                    by_cases hbq : ((C1 / C) <ᵤ x) = true <;> by_cases hbp : (((4294967295#32 / C) <ᵤ x) = true ∨ (C1 <ᵤ (x * C)) = true) <;>
                      simp_all [ofBool_one_iff, hydra33_ite_semval_value, InstCombine.LLVM.Ty.width, LLVM.SemVal.bind_value, LLVM.SemVal.isRefinedBy_self, LLVM.SemVal.poison_isRefinedBy])
                · exact HVector.nil_isRefinedBy_nil)
            | value C2 =>
              change BitVec 32 at C2
              simp [hydra33_src, hydra33_tgt, hydra33_semval_bind_poison, hydra33_udiv_eq_if, hydra33_udiv_poisonL, hydra33_udiv_poisonR, hydra33_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, C1Var, xVar, C2Var, hC, hcond, hub1, hC1, hx, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, InstCombine.lift2UB, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.bothValues (by
                constructor
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    have hv := hydra33_value x C C1 C2 hcond hub1
                    simp [hv, ofBool_one_iff, hydra33_ite_semval_value, InstCombine.LLVM.Ty.width, LLVM.SemVal.bind_value, LLVM.SemVal.isRefinedBy_self])
                · exact HVector.nil_isRefinedBy_nil)
