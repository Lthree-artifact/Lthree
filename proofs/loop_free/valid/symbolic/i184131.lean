import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def i184131_src (w : Nat) (_h : 2 ≤ w) :=
  [llvm(w)| {
  llvm.func @i184131_src(%x0 : _, %x1 : _, %C1 : _, %C2 : _, %C3 : _) -> _ {
  ^bb0(%x0 : _, %x1 : _, %C1 : _, %C2 : _, %C3 : _):
    %one = llvm.mlir.constant(1 : _) : _
    %shl = llvm.shl %one, %C1 : _
    %cond2 = llvm.icmp "eq" %C3, %shl : _
    llvm.assume %cond2 : i1
    %sub = llvm.sub %shl, %one : _
    %cond3 = llvm.icmp "eq" %C2, %sub : _
    llvm.assume %cond3 : i1
    %e1 = llvm.lshr %x0, %C1 : _
    %t = llvm.trunc %e1 : _ to i1
    %e2 = llvm.lshr %x1, %C1 : _
    %v0 = llvm.select %t, %e1, %e2 : _
    %v1 = llvm.select %t, %x0, %x1 : _
    %ext = llvm.and %v1, %C2 : _
    %ins = llvm.shl %v0, %C1 : _
    %r = llvm.or disjoint %ins, %ext : _
    llvm.return %r : _
  }
  }]

def i184131_tgt (w : Nat) (_h : 2 ≤ w) :=
  [llvm(w)| {
  llvm.func @i184131_tgt(%x0 : _, %x1 : _, %C1 : _, %C2 : _, %C3 : _) -> _ {
  ^bb0(%x0 : _, %x1 : _, %C1 : _, %C2 : _, %C3 : _):
    %one = llvm.mlir.constant(1 : _) : _
    %shl = llvm.shl %one, %C1 : _
    %cond2 = llvm.icmp "eq" %C3, %shl : _
    llvm.assume %cond2 : i1
    %sub = llvm.sub %shl, %one : _
    %cond3 = llvm.icmp "eq" %C2, %sub : _
    llvm.assume %cond3 : i1
    %zero = llvm.mlir.constant(0 : _) : _
    %hi = llvm.and %x0, %C3 : _
    %nn = llvm.icmp "eq" %hi, %zero : _
    %r = llvm.select %nn, %x1, %x0 : _
    llvm.return %r : _
  }
  }]

private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by
  cases b <;> simp

private theorem i184131_semval_bind_poison {α β : Type} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl

private theorem i184131_ite_semval_value {w : Nat} {c : Prop} [Decidable c]
    (a b : BitVec w) :
    (if c then LLVM.SemVal.value a else LLVM.SemVal.value b) =
      LLVM.SemVal.value (if c then a else b) := by
  split <;> rfl

private theorem i184131_value {w : Nat} (_h : 2 ≤ w) (x0 : BitVec w) (x1 : BitVec w) (C1 : BitVec w) (C2 : BitVec w) (C3 : BitVec w)
    (hsh1 : ¬ (BitVec.ofNat w w ≤ C1))
    (hpre1 : (C3 == (1#w <<< C1.toNat)) = true)
    (hpre2 : (C2 == ((1#w <<< C1.toNat) - 1#w)) = true)
    (hdis : ((if (BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1 then (x0 >>> C1.toNat) else (x1 >>> C1.toNat)) <<< C1.toNat) &&& ((if (BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1 then x0 else x1) &&& C2) = 0#w) :
    (((if (BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1 then (x0 >>> C1.toNat) else (x1 >>> C1.toNat)) <<< C1.toNat) ||| ((if (BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1 then x0 else x1) &&& C2)) = (if (x0 &&& C3) = 0#w then x1 else x0) := by
  have _ := hdis
  have hk : C1.toNat < w := by
    by_contra h
    apply hsh1
    rw [BitVec.le_def]
    have hwlt : w < 2 ^ w := Nat.lt_pow_self (by decide : 1 < 2)
    have hwto : (BitVec.ofNat w w).toNat = w := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hwlt
    rw [hwto]
    exact Nat.le_of_not_gt h
  have hcond_iff :
      ((BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1) ↔
        x0.getLsbD C1.toNat = true := by
    constructor
    · intro h
      have hb := congrArg (fun y : BitVec 1 => y.getLsbD 0) h
      simpa [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_ofNat] using hb
    · intro hx
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      simp [BitVec.getLsbD_ushiftRight, hx]
  have hmask_get : ∀ i : Nat,
      (((1#w <<< C1.toNat) - 1#w).getLsbD i) = decide (i < C1.toNat) := by
    intro i
    have hwpos : 0 < w := Nat.lt_of_le_of_lt (Nat.zero_le C1.toNat) hk
    have hp2 : 2 ^ C1.toNat < 2 ^ w :=
      Nat.pow_lt_pow_right (by decide : 1 < 2) hk
    have hshift : (1#w <<< C1.toNat).toNat = 2 ^ C1.toNat := by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_one hwpos, Nat.one_shiftLeft]
      exact Nat.mod_eq_of_lt hp2
    have hmasknat : ((1#w <<< C1.toNat) - 1#w).toNat = 2 ^ C1.toNat - 1 := by
      rw [BitVec.toNat_sub, hshift, BitVec.toNat_one hwpos]
      have hp : 0 < 2 ^ C1.toNat := Nat.two_pow_pos C1.toNat
      have hsum :
          2 ^ w - 1 + 2 ^ C1.toNat = 2 ^ w + (2 ^ C1.toNat - 1) := by
        omega
      have hlt : 2 ^ C1.toNat - 1 < 2 ^ w := by omega
      rw [hsum, Nat.add_mod, Nat.mod_self, zero_add]
      rw [Nat.mod_eq_of_lt hlt]
      exact Nat.mod_eq_of_lt hlt
    rw [← BitVec.testBit_toNat, hmasknat]
    exact Nat.testBit_two_pow_sub_one C1.toNat i
  have hrebuild : ∀ x : BitVec w,
      (((x >>> C1.toNat) <<< C1.toNat) |||
        (x &&& ((1#w <<< C1.toNat) - 1#w))) = x := by
    intro x
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_and, hmask_get i]
    by_cases hik : i < C1.toNat
    · simp [hi, hik]
    · have hki : C1.toNat + (i - C1.toNat) = i :=
        Nat.add_sub_of_le (Nat.le_of_not_gt hik)
      simp [hi, hik, hki]
  have hC3 : C3 = (1#w <<< C1.toNat) := beq_iff_eq.mp hpre1
  have hC2 : C2 = ((1#w <<< C1.toNat) - 1#w) := beq_iff_eq.mp hpre2
  by_cases hbit : (BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1
  · have hnz : ¬ (x0 &&& C3) = 0#w := by
      rw [hC3]
      intro hz
      have hxbit : x0.getLsbD C1.toNat = true := hcond_iff.mp hbit
      rw [BitVec.getLsbD_eq_getElem hk] at hxbit
      have hb := congrArg (fun y : BitVec w => y.getLsbD C1.toNat) hz
      simp [hk, hxbit] at hb
    simp [hbit, hC2, hnz, hrebuild x0]
  · have hz : (x0 &&& C3) = 0#w := by
      rw [hC3]
      have hxbit : x0.getLsbD C1.toNat = false := by
        cases h : x0.getLsbD C1.toNat
        · rfl
        · exact False.elim (hbit (hcond_iff.mpr h))
      rw [BitVec.getLsbD_eq_getElem hk] at hxbit
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [BitVec.getLsbD_and]
      rw [← BitVec.twoPow_eq]
      rw [BitVec.getLsbD_twoPow]
      by_cases hik : C1.toNat = i
      · subst i
        simp [hk, hxbit]
      · simp [hk, hik]
    simp [hbit, hC2, hz, hrebuild x1]

private theorem i184131_poisoncover {w : Nat} (_h : 2 ≤ w) (x0 : BitVec w) (C1 : BitVec w) (C2 : BitVec w) (C3 : BitVec w)
    (hsh1 : ¬ (BitVec.ofNat w w ≤ C1))
    (hpre1 : (C3 == (1#w <<< C1.toNat)) = true)
    (hpre2 : (C2 == ((1#w <<< C1.toNat) - 1#w)) = true)
    (hbq : (x0 &&& C3) = 0#w) :
    ¬ ((BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1) := by
  have _ := hpre2
  intro hbit
  have hk : C1.toNat < w := by
    by_contra h
    apply hsh1
    rw [BitVec.le_def]
    have hwlt : w < 2 ^ w := Nat.lt_pow_self (by decide : 1 < 2)
    have hwto : (BitVec.ofNat w w).toNat = w := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hwlt
    rw [hwto]
    exact Nat.le_of_not_gt h
  have hC3 : C3 = (1#w <<< C1.toNat) := beq_iff_eq.mp hpre1
  have hcond_iff :
      ((BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1) ↔
        x0.getLsbD C1.toNat = true := by
    constructor
    · intro h
      have hb := congrArg (fun y : BitVec 1 => y.getLsbD 0) h
      simpa [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_ofNat] using hb
    · intro hx
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      simp [BitVec.getLsbD_ushiftRight, hx]
  have hxbit : x0.getLsbD C1.toNat = true := hcond_iff.mp hbit
  rw [BitVec.getLsbD_eq_getElem hk] at hxbit
  have hz : (x0 &&& (1#w <<< C1.toNat)) = 0#w := by
    simpa [hC3] using hbq
  have hb := congrArg (fun y : BitVec w => y.getLsbD C1.toNat) hz
  simp [hk, hxbit] at hb

set_option maxHeartbeats 4000000 in
theorem i184131_correct (w : Nat) (_h : 2 ≤ w) : i184131_src w _h ⊑ i184131_tgt w _h := by
  intro V
  let x0Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨4, by simp⟩
  let x1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨3, by simp⟩
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let C3Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases hC3 : V C3Var
  case poison =>
    simp [i184131_src, i184131_tgt, i184131_semval_bind_poison, i184131_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, hC3, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.lshr, LLVM.lshr?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.trunc, LLVM.trunc?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C3 =>
    change BitVec w at C3
    cases hC1 : V C1Var
    case poison =>
      simp [i184131_src, i184131_tgt, i184131_semval_bind_poison, i184131_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, hC3, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.lshr, LLVM.lshr?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.trunc, LLVM.trunc?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value C1 =>
      change BitVec w at C1
      by_cases hsh1 : BitVec.ofNat w w ≤ C1
      ·
        simp [i184131_src, i184131_tgt, i184131_semval_bind_poison, i184131_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, hC3, hC1, hsh1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.lshr, LLVM.lshr?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.trunc, LLVM.trunc?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      ·
        cases hcond1 : (C3 == (1#w <<< C1.toNat))
        · simp [i184131_src, i184131_tgt, i184131_semval_bind_poison, i184131_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, hC3, hC1, hsh1, hcond1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.lshr, LLVM.lshr?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.trunc, LLVM.trunc?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        ·
          cases hC2 : V C2Var with
          | poison =>
            simp [i184131_src, i184131_tgt, i184131_semval_bind_poison, i184131_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, C2Var, hC3, hC1, hsh1, hcond1, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.lshr, LLVM.lshr?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.trunc, LLVM.trunc?, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
          | value C2 =>
            change BitVec w at C2
            cases hcond2 : (C2 == ((1#w <<< C1.toNat) - 1#w))
            · simp [i184131_src, i184131_tgt, i184131_semval_bind_poison, i184131_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, C2Var, hC3, hC1, hsh1, hcond1, hC2, hcond2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.lshr, LLVM.lshr?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.trunc, LLVM.trunc?, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
            ·
              cases hx0 : V x0Var with
              | poison =>
                simp [i184131_src, i184131_tgt, i184131_semval_bind_poison, i184131_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, C2Var, x0Var, hC3, hC1, hsh1, hcond1, hC2, hcond2, hx0, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.lshr, LLVM.lshr?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.trunc, LLVM.trunc?, LLVM.assume_]
                exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  constructor
                  · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                      first
                      | exact LLVM.SemVal.poison_isRefinedBy _
                      | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                      | simp [LLVM.IntW.instRefinement])
                  · exact HVector.nil_isRefinedBy_nil)
              | value x0 =>
                change BitVec w at x0
                cases hx1 : V x1Var with
                | poison =>
                  simp [i184131_src, i184131_tgt, i184131_semval_bind_poison, i184131_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, C2Var, x0Var, x1Var, hC3, hC1, hsh1, hcond1, hC2, hcond2, hx0, hx1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.lshr, LLVM.lshr?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.trunc, LLVM.trunc?, LLVM.assume_]
                  by_cases hbq : (x0 &&& C3) = 0#w
                  ·
                    have hbp := i184131_poisoncover (w := w) _h x0 C1 C2 C3 hsh1 hcond1 hcond2 hbq
                    simp_all [ofBool_one_iff, i184131_ite_semval_value, i184131_semval_bind_poison, InstCombine.LLVM.Ty.width, LLVM.SemVal.bind_value, LLVM.SemVal.isRefinedBy_self, LLVM.SemVal.poison_isRefinedBy] <;>
                      exact ImmediateUBOr.IsRefinedBy.bothValues (by
                        constructor
                        · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                            first
                            | exact LLVM.SemVal.poison_isRefinedBy _
                            | exact LLVM.SemVal.isRefinedBy_self _
                            | simp [LLVM.SemVal.isRefinedBy_self, LLVM.SemVal.poison_isRefinedBy])
                        · exact HVector.nil_isRefinedBy_nil)
                  · by_cases hbp : (BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1
                    ·
                      cases hd : (((x0 >>> C1.toNat) <<< C1.toNat) &&& (x0 &&& C2) == 0#w)
                      · have hne : ¬ (((x0 >>> C1.toNat) <<< C1.toNat) &&& (x0 &&& C2) = 0#w) := by simpa using hd
                        simp_all [ofBool_one_iff, i184131_ite_semval_value, i184131_semval_bind_poison, InstCombine.LLVM.Ty.width, LLVM.SemVal.bind_value, LLVM.SemVal.isRefinedBy_self, LLVM.SemVal.poison_isRefinedBy] <;>
                          exact ImmediateUBOr.IsRefinedBy.bothValues (by
                            constructor
                            · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                                first
                                | exact LLVM.SemVal.poison_isRefinedBy _
                                | exact LLVM.SemVal.isRefinedBy_self _
                                | simp [LLVM.SemVal.isRefinedBy_self, LLVM.SemVal.poison_isRefinedBy])
                            · exact HVector.nil_isRefinedBy_nil)
                      · have hdis0 : ((if (BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1 then (x0 >>> C1.toNat) else (0#w >>> C1.toNat)) <<< C1.toNat) &&& ((if (BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1 then x0 else 0#w) &&& C2) = 0#w := by simpa [hbp] using hd
                        have hv := i184131_value (w := w) _h x0 (0#w) C1 C2 C3 hsh1 hcond1 hcond2 hdis0
                        simp_all [ofBool_one_iff, i184131_ite_semval_value, i184131_semval_bind_poison, InstCombine.LLVM.Ty.width, LLVM.SemVal.bind_value, LLVM.SemVal.isRefinedBy_self, LLVM.SemVal.poison_isRefinedBy] <;>
                          exact ImmediateUBOr.IsRefinedBy.bothValues (by
                            constructor
                            · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                                first
                                | exact LLVM.SemVal.poison_isRefinedBy _
                                | exact LLVM.SemVal.isRefinedBy_self _
                                | simp [LLVM.SemVal.isRefinedBy_self, LLVM.SemVal.poison_isRefinedBy])
                            · exact HVector.nil_isRefinedBy_nil)
                    ·
                      simp_all [ofBool_one_iff, i184131_ite_semval_value, i184131_semval_bind_poison, InstCombine.LLVM.Ty.width, LLVM.SemVal.bind_value, LLVM.SemVal.isRefinedBy_self, LLVM.SemVal.poison_isRefinedBy] <;>
                        exact ImmediateUBOr.IsRefinedBy.bothValues (by
                          constructor
                          · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                              first
                              | exact LLVM.SemVal.poison_isRefinedBy _
                              | exact LLVM.SemVal.isRefinedBy_self _
                              | simp [LLVM.SemVal.isRefinedBy_self, LLVM.SemVal.poison_isRefinedBy])
                          · exact HVector.nil_isRefinedBy_nil)
                | value x1 =>
                  change BitVec w at x1
                  cases hd : (((if (BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1 then (x0 >>> C1.toNat) else (x1 >>> C1.toNat)) <<< C1.toNat) &&& ((if (BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1 then x0 else x1) &&& C2) == 0#w)
                  · have hne : ¬ (((if (BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1 then (x0 >>> C1.toNat) else (x1 >>> C1.toNat)) <<< C1.toNat) &&& ((if (BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1 then x0 else x1) &&& C2) = 0#w) := by simpa using hd
                    simp [i184131_src, i184131_tgt, i184131_semval_bind_poison, i184131_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, C2Var, x0Var, x1Var, hC3, hC1, hsh1, hcond1, hC2, hcond2, hx0, hx1, hne, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.lshr, LLVM.lshr?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.trunc, LLVM.trunc?, LLVM.assume_]
                    exact ImmediateUBOr.IsRefinedBy.bothValues (by
                      constructor
                      · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                          first
                          | exact LLVM.SemVal.poison_isRefinedBy _
                          | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                          | simp [LLVM.IntW.instRefinement])
                      · exact HVector.nil_isRefinedBy_nil)
                  · have hdis : ((if (BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1 then (x0 >>> C1.toNat) else (x1 >>> C1.toNat)) <<< C1.toNat) &&& ((if (BitVec.setWidth 1 (x0 >>> C1.toNat)) = 1#1 then x0 else x1) &&& C2) = 0#w := by simpa using hd
                    simp [i184131_src, i184131_tgt, i184131_semval_bind_poison, i184131_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, C2Var, x0Var, x1Var, hC3, hC1, hsh1, hcond1, hC2, hcond2, hx0, hx1, hdis, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.lshr, LLVM.lshr?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.trunc, LLVM.trunc?, LLVM.assume_]
                    exact ImmediateUBOr.IsRefinedBy.bothValues (by
                      constructor
                      · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                          have hv := i184131_value (w := w) _h x0 x1 C1 C2 C3 hsh1 hcond1 hcond2 hdis
                          simp [hv, ofBool_one_iff, i184131_ite_semval_value, InstCombine.LLVM.Ty.width, LLVM.SemVal.bind_value, LLVM.SemVal.isRefinedBy_self])
                      · exact HVector.nil_isRefinedBy_nil)
