import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def i201328_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i201328_src(%x : _, %C1 : _, %C2 : _) -> _ {
  ^bb0(%x : _, %C1 : _, %C2 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %m1 = llvm.mlir.constant(-1 : _) : _
    %c2_not_zero = llvm.icmp "ne" %C2, %zero : _
    %c2_minus_1 = llvm.add %C2, %m1 : _
    %c2_and = llvm.and %C2, %c2_minus_1 : _
    %c2_is_pow2 = llvm.icmp "eq" %c2_and, %zero : _
    %c1_eq = llvm.icmp "eq" %C1, %c2_minus_1 : _
    %cond1 = llvm.and %c2_not_zero, %c2_is_pow2 : i1
    %cond = llvm.and %cond1, %c1_eq : i1
    llvm.assume %cond : i1
    %rem = llvm.and %x, %C1 : _
    %is_zero = llvm.icmp "eq" %rem, %zero : _
    %sel = llvm.select %is_zero, %C2, %rem : _
    %res = llvm.sub %x, %sel : _
    llvm.return %res : _
  }
  }]

def i201328_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i201328_tgt(%x : _, %C1 : _, %C2 : _) -> _ {
  ^bb0(%x : _, %C1 : _, %C2 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %m1 = llvm.mlir.constant(-1 : _) : _
    %c2_not_zero = llvm.icmp "ne" %C2, %zero : _
    %c2_minus_1 = llvm.add %C2, %m1 : _
    %c2_and = llvm.and %C2, %c2_minus_1 : _
    %c2_is_pow2 = llvm.icmp "eq" %c2_and, %zero : _
    %c1_eq = llvm.icmp "eq" %C1, %c2_minus_1 : _
    %cond1 = llvm.and %c2_not_zero, %c2_is_pow2 : i1
    %cond = llvm.and %cond1, %c1_eq : i1
    llvm.assume %cond : i1
    %dec = llvm.add %x, %m1 : _
    %neg_C2 = llvm.sub %zero, %C2 : _
    %res = llvm.and %dec, %neg_C2 : _
    llvm.return %res : _
  }
  }]

private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by
  cases b <;> simp

private theorem i201328_value {w : Nat} (x : BitVec w) (C1 : BitVec w) (C2 : BitVec w)
    (hpre : (((C2 != 0#w) && ((C2 &&& (C2 + (BitVec.ofInt w (-1)))) == 0#w)) && (C1 == (C2 + (BitVec.ofInt w (-1))))) = true) :
    (x - (if (x &&& C1) = 0#w then C2 else (x &&& C1))) = ((x + (BitVec.ofInt w (-1))) &&& -C2) := by
  have nat_pow2_of_and_pred_eq_zero :
      ∀ n : Nat, n ≠ 0 → n &&& (n - 1) = 0 → ∃ k, n = 2 ^ k := by
    intro n hn hpow
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hlt : n / 2 < n := Nat.div_lt_self hnpos (by omega)
        have hhalf_ne : n / 2 ≠ 0 := by
          intro hz
          have hdecomp := Nat.div_add_mod n 2
          omega
        have hpred_div : (n - 1) / 2 = n / 2 - 1 := by
          have hdecomp := Nat.div_add_mod n 2
          omega
        have hpow_half : n / 2 &&& (n / 2 - 1) = 0 := by
          have hd : (n &&& (n - 1)) / 2 = 0 := by
            simpa using congrArg (fun t : Nat => t / 2) hpow
          rw [Nat.and_div_two] at hd
          simpa [hpred_div] using hd
        obtain ⟨k, hk⟩ := ih (n / 2) hlt hhalf_ne hpow_half
        refine ⟨k + 1, ?_⟩
        have hdecomp := Nat.div_add_mod n 2
        rw [hk] at hdecomp
        rw [Nat.pow_succ]
        omega
      · have hpred_div : (n - 1) / 2 = n / 2 := by
          have hdecomp := Nat.div_add_mod n 2
          omega
        have hhalf_zero : n / 2 = 0 := by
          have hd : (n &&& (n - 1)) / 2 = 0 := by
            simpa using congrArg (fun t : Nat => t / 2) hpow
          rw [Nat.and_div_two] at hd
          simpa [hpred_div] using hd
        refine ⟨0, ?_⟩
        have hdecomp := Nat.div_add_mod n 2
        omega
  have nat_and_high_mask_eq_div_mul :
      ∀ {ww kk yy : Nat}, kk < ww → yy < 2 ^ ww →
        yy &&& (2 ^ ww - 2 ^ kk) = yy / 2 ^ kk * 2 ^ kk := by
    intro ww kk yy hkk hyy
    apply Nat.eq_of_testBit_eq
    intro i
    have hmask :
        (2 ^ ww - 2 ^ kk).testBit i = (decide (i < ww) && ! decide (i < kk)) := by
      have hlt : 2 ^ kk - 1 < 2 ^ ww := by
        have hkw : 2 ^ kk < 2 ^ ww := Nat.pow_lt_pow_of_lt (by omega : 1 < 2) hkk
        omega
      have hs : 2 ^ kk - 1 + 1 = 2 ^ kk := by
        have h2pos : 0 < 2 ^ kk := Nat.two_pow_pos kk
        omega
      simpa [hs, Nat.testBit_two_pow_sub_one] using
        (Nat.testBit_two_pow_sub_succ (x := 2 ^ kk - 1) (n := ww) hlt i)
    rw [Nat.testBit_and, hmask, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
    by_cases hki : kk ≤ i
    · have hidx : i - kk + kk = i := by omega
      by_cases hiw : i < ww
      · simp [hki, hiw, hidx, show ¬ i < kk by omega]
      · have hyfalse : yy.testBit i = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le hyy (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega))
        simp [hki, hiw, hidx, hyfalse, show ¬ i < kk by omega]
    · have hik : i < kk := by omega
      simp [hki, hik]
  have nat_round_identity_aux :
      ∀ {c d xx : Nat}, 0 < c → 1 < d → xx < c * d →
        (xx + (c * d - if xx % c = 0 then c else xx % c)) % (c * d) =
          (xx + (c * d - 1)) % (c * d) / c * c := by
    intro c d xx hc hd hx
    have hmodlt : xx % c < c := Nat.mod_lt xx hc
    have hdecomp : c * (xx / c) + xx % c = xx := Nat.div_add_mod xx c
    by_cases hr : xx % c = 0
    · simp [hr]
      by_cases hx0 : xx = 0
      · subst xx
        have hdiv : (c * d - 1) / c = d - 1 := by
          apply Nat.div_eq_of_lt_le
          · rw [Nat.mul_comm (d - 1) c]
            have hs : c * (d - 1) + c = c * d := by
              rw [← Nat.mul_succ]
              have hs' : (d - 1).succ = d := by omega
              rw [hs']
            omega
          · have hs' : d - 1 + 1 = d := by omega
            rw [hs']
            rw [Nat.mul_comm d c]
            have hprod : 0 < c * d := Nat.mul_pos hc (by omega)
            omega
        have hmul : (d - 1) * c = c * d - c := by
          rw [Nat.mul_comm (d - 1) c]
          have hs : c * (d - 1) + c = c * d := by
            rw [← Nat.mul_succ]
            have hs' : (d - 1).succ = d := by omega
            rw [hs']
          omega
        have hmd1 : (0 + (c * d - 1)) % (c * d) = c * d - 1 := by
          simp
        rw [hmd1, hdiv, hmul]
        simpa using Nat.mod_eq_of_lt (a := 0 + (c * d - c)) (b := c * d) (by omega)
      · have hqpos : 0 < xx / c := by
          by_contra hqz
          have hqz' : xx / c = 0 := Nat.eq_zero_of_not_pos hqz
          have hdecomp' := hdecomp
          rw [hr, hqz'] at hdecomp'
          omega
        have hc_le_x : c ≤ xx := by
          have hdecomp' := hdecomp
          rw [hr] at hdecomp'
          have hc_le : c ≤ c * (xx / c) := Nat.le_mul_of_pos_right c hqpos
          omega
        have hsum : xx + (c * d - c) = c * d + (xx - c) := by omega
        have hy : (xx + (c * d - 1)) % (c * d) = xx - 1 := by
          have hsum1 : xx + (c * d - 1) = c * d + (xx - 1) := by omega
          rw [hsum1, Nat.add_mod_left, Nat.mod_eq_of_lt]
          omega
        have hdiv : (xx - 1) / c = xx / c - 1 := by
          apply Nat.div_eq_of_lt_le
          · have hdecomp' := hdecomp
            rw [hr] at hdecomp'
            rw [Nat.mul_comm (xx / c - 1) c]
            have hs : c * (xx / c - 1) + c = c * (xx / c) := by
              rw [← Nat.mul_succ]
              have hs' : (xx / c - 1).succ = xx / c := by omega
              rw [hs']
            omega
          · have hdecomp' := hdecomp
            rw [hr] at hdecomp'
            have hs' : xx / c - 1 + 1 = xx / c := by omega
            rw [hs']
            rw [Nat.mul_comm (xx / c) c]
            omega
        rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega), hy, hdiv]
        have hdecomp' := hdecomp
        rw [hr] at hdecomp'
        rw [Nat.mul_comm (xx / c - 1) c]
        have hs : c * (xx / c - 1) + c = c * (xx / c) := by
          rw [← Nat.mul_succ]
          have hs' : (xx / c - 1).succ = xx / c := by omega
          rw [hs']
        omega
    · have hrpos : 0 < xx % c := Nat.pos_of_ne_zero hr
      have hsum : xx + (c * d - xx % c) = c * d + (xx - xx % c) := by omega
      have hy : (xx + (c * d - 1)) % (c * d) = xx - 1 := by
        have hsum1 : xx + (c * d - 1) = c * d + (xx - 1) := by omega
        rw [hsum1, Nat.add_mod_left, Nat.mod_eq_of_lt]
        omega
      have hdiv : (xx - 1) / c = xx / c := by
        apply Nat.div_eq_of_lt_le
        · have hdecomp' := hdecomp
          rw [Nat.mul_comm (xx / c) c]
          omega
        · have hdecomp' := hdecomp
          have hs : (xx / c + 1) * c = c * (xx / c) + c := by
            rw [Nat.mul_comm (xx / c + 1) c]
            rw [Nat.mul_succ]
          rw [hs]
          omega
      simp [hr]
      rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega), hy, hdiv]
      have hdecomp' := hdecomp
      rw [Nat.mul_comm (xx / c) c]
      omega
  have nat_round_identity :
      ∀ {ww kk xx : Nat}, kk < ww → xx < 2 ^ ww →
        (xx + (2 ^ ww - if xx % 2 ^ kk = 0 then 2 ^ kk else xx % 2 ^ kk)) % 2 ^ ww =
          (xx + (2 ^ ww - 1)) % 2 ^ ww / 2 ^ kk * 2 ^ kk := by
    intro ww kk xx hkk hxx
    have hmfac : 2 ^ ww = 2 ^ kk * 2 ^ (ww - kk) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hd : 1 < 2 ^ (ww - kk) := by
      apply Nat.one_lt_two_pow
      omega
    simpa [hmfac] using
      (nat_round_identity_aux (c := 2 ^ kk) (d := 2 ^ (ww - kk)) (xx := xx)
        (Nat.two_pow_pos kk) hd (by simpa [← hmfac] using hxx))
  have pow2_bitvec_identity :
      ∀ {ww kk : Nat}, kk < ww → (xx : BitVec ww) →
        (xx -
            (if (xx &&& (BitVec.twoPow ww kk + BitVec.ofInt ww (-1))) = 0#ww then
              BitVec.twoPow ww kk
            else
              (xx &&& (BitVec.twoPow ww kk + BitVec.ofInt ww (-1))))) =
          ((xx + (BitVec.ofInt ww (-1))) &&& -BitVec.twoPow ww kk) := by
    intro ww kk hkk xx
    apply BitVec.eq_of_toNat_eq
    have hneg1_toNat : (BitVec.ofInt ww (-1)).toNat = 2 ^ ww - 1 := by
      have hneg1 : BitVec.ofInt ww (-1) = BitVec.allOnes ww := by
        rw [show (-1 : Int) = Int.negSucc 0 by rfl]
        rw [BitVec.ofInt_negSucc_eq_not_ofNat]
        simp
      rw [hneg1]
      simp
    have htwo_toNat : (BitVec.twoPow ww kk).toNat = 2 ^ kk :=
      BitVec.toNat_twoPow_of_lt hkk
    have hmask_toNat :
        (BitVec.twoPow ww kk + BitVec.ofInt ww (-1)).toNat = 2 ^ kk - 1 := by
      rw [BitVec.toNat_add, htwo_toNat, hneg1_toNat]
      have hkw : 2 ^ kk < 2 ^ ww := Nat.pow_lt_pow_of_lt (by omega : 1 < 2) hkk
      have hsum : 2 ^ kk + (2 ^ ww - 1) = 2 ^ ww + (2 ^ kk - 1) := by
        have h2pos : 0 < 2 ^ kk := Nat.two_pow_pos kk
        omega
      rw [hsum, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    have hrem_toNat :
        (xx &&& (BitVec.twoPow ww kk + BitVec.ofInt ww (-1))).toNat =
          xx.toNat % 2 ^ kk := by
      rw [BitVec.toNat_and, hmask_toNat, Nat.and_two_pow_sub_one_eq_mod]
    have hdec_toNat :
        (xx + BitVec.ofInt ww (-1)).toNat = (xx.toNat + (2 ^ ww - 1)) % 2 ^ ww := by
      rw [BitVec.toNat_add, hneg1_toNat]
    have hneg_two_toNat : (-BitVec.twoPow ww kk).toNat = 2 ^ ww - 2 ^ kk := by
      rw [BitVec.toNat_neg_of_pos]
      · rw [htwo_toNat]
      · rw [BitVec.lt_def, htwo_toNat]
        exact Nat.two_pow_pos kk
    have hrhs :
        ((xx + BitVec.ofInt ww (-1)) &&& -BitVec.twoPow ww kk).toNat =
          (xx.toNat + (2 ^ ww - 1)) % 2 ^ ww / 2 ^ kk * 2 ^ kk := by
      rw [BitVec.toNat_and, hdec_toNat, hneg_two_toNat]
      exact nat_and_high_mask_eq_div_mul hkk (Nat.mod_lt _ (Nat.two_pow_pos ww))
    by_cases hz : (xx &&& (BitVec.twoPow ww kk + BitVec.ofInt ww (-1))) = 0#ww
    · have hzNat : xx.toNat % 2 ^ kk = 0 := by
        have h := congrArg BitVec.toNat hz
        simpa [hrem_toNat] using h
      rw [BitVec.toNat_sub, hz]
      simp only [ite_true]
      rw [htwo_toNat, hrhs]
      rw [Nat.add_comm (2 ^ ww - 2 ^ kk) xx.toNat]
      simpa [hzNat] using
        nat_round_identity (kk := kk) (xx := xx.toNat) hkk xx.isLt
    · have hzNat : xx.toNat % 2 ^ kk ≠ 0 := by
        intro hzero
        apply hz
        apply BitVec.eq_of_toNat_eq
        simp [hrem_toNat, hzero]
      rw [BitVec.toNat_sub, if_neg hz, hrem_toNat, hrhs]
      rw [Nat.add_comm (2 ^ ww - xx.toNat % 2 ^ kk) xx.toNat]
      simpa [hzNat] using
        nat_round_identity (kk := kk) (xx := xx.toNat) hkk xx.isLt
  simp at hpre
  rcases hpre with ⟨⟨hC2ne, hpowBV⟩, hC1⟩
  have hpred_toNat : (C2 + BitVec.ofInt w (-1)).toNat = C2.toNat - 1 := by
    have hpos : 0 < C2.toNat := by
      by_contra hz
      have hz' : C2.toNat = 0 := by omega
      exact hC2ne (BitVec.eq_of_toNat_eq hz')
    have hneg1_toNat : (BitVec.ofInt w (-1)).toNat = 2 ^ w - 1 := by
      have hneg1 : BitVec.ofInt w (-1) = BitVec.allOnes w := by
        rw [show (-1 : Int) = Int.negSucc 0 by rfl]
        rw [BitVec.ofInt_negSucc_eq_not_ofNat]
        simp
      rw [hneg1]
      simp
    have hlt : C2.toNat < 2 ^ w := C2.isLt
    rw [BitVec.toNat_add, hneg1_toNat]
    have hsum : C2.toNat + (2 ^ w - 1) = 2 ^ w + (C2.toNat - 1) := by omega
    rw [hsum, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hpowNat : C2.toNat &&& (C2.toNat - 1) = 0 := by
    have hp := congrArg BitVec.toNat hpowBV
    simpa [BitVec.toNat_and, hpred_toNat] using hp
  obtain ⟨k, hk⟩ := nat_pow2_of_and_pred_eq_zero C2.toNat (by
    intro hz
    exact hC2ne (BitVec.eq_of_toNat_eq hz)) hpowNat
  have hklt : k < w := by
    have hlt : C2.toNat < 2 ^ w := C2.isLt
    rw [hk] at hlt
    exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hlt
  have hC2pow : C2 = BitVec.twoPow w k := by
    apply BitVec.eq_of_toNat_eq
    rw [hk, BitVec.toNat_twoPow_of_lt hklt]
  subst C2
  rw [hC1]
  exact pow2_bitvec_identity hklt x

set_option maxHeartbeats 4000000 in
theorem i201328_correct (w : Nat) : i201328_src w ⊑ i201328_tgt w := by
  intro V
  let xVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases hC2 : V C2Var
  case poison =>
    simp [i201328_src, i201328_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C2 =>
    change BitVec w at C2
    cases hC1 : V C1Var
    case poison =>
      simp [i201328_src, i201328_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, C1Var, hC2, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value C1 =>
      change BitVec w at C1
      cases hcond : (((C2 != 0#w) && ((C2 &&& (C2 + (BitVec.ofInt w (-1)))) == 0#w)) && (C1 == (C2 + (BitVec.ofInt w (-1)))))
      · simp [i201328_src, i201328_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, C1Var, hC2, hC1, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      ·
        cases hx : V xVar
        case poison =>
          simp [i201328_src, i201328_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, C1Var, xVar, hC2, hC1, hcond, hx, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.bothValues (by
            constructor
            · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                first
                | exact LLVM.SemVal.poison_isRefinedBy _
                | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                | simp [LLVM.IntW.instRefinement])
            · exact HVector.nil_isRefinedBy_nil)
        case value x =>
          change BitVec w at x
          simp [i201328_src, i201328_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, C1Var, xVar, hC2, hC1, hcond, hx, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.bothValues (by
            constructor
            · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                have hv := i201328_value (w := w) x C1 C2 hcond
                by_cases hS1 : ((x &&& C1) == 0#w) = true <;> simp_all [InstCombine.LLVM.Ty.width, ofBool_one_iff, LLVM.SemVal.isRefinedBy_self])
            · exact HVector.nil_isRefinedBy_nil)
