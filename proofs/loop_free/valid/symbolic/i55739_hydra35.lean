import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def pow2_mul_shl_log2_src (w : Nat) (_h : 0 < w) :=
  [llvm(w)| {
  llvm.func @pow2_mul_shl_log2_src(%x : _, %C1 : _, %C2 : _, %C3 : _) -> i1 {
  ^bb0(%x : _, %C1 : _, %C2 : _, %C3 : _):
    %is_pow2_c1 = llvm.isPowerOf2 %C1 : _
    llvm.assume %is_pow2_c1 : i1
    %is_pow2_c2 = llvm.isPowerOf2 %C2 : _
    llvm.assume %is_pow2_c2 : i1
    %is_pow2_c3 = llvm.isPowerOf2 %C3 : _
    llvm.assume %is_pow2_c3 : i1
    %c3_mul_c1 = llvm.mul %C3, %C1 : _
    %c2_eq_c3_mul_c1 = llvm.icmp "eq" %C2, %c3_mul_c1 : _
    llvm.assume %c2_eq_c3_mul_c1 : i1
    %c3_shl_x = llvm.shl %C3, %x : _
    %masked = llvm.and %C2, %c3_shl_x : _
    %zero = llvm.mlir.constant(0 : _) : _
    %masked_ne_zero = llvm.icmp "ne" %masked, %zero : _
    llvm.assume %masked_ne_zero : i1
    %log2_c1 = llvm.cttz %C1, false : _
    %r = llvm.icmp "eq" %x, %log2_c1 : _
    llvm.return %r : i1
  }
  }]

def pow2_mul_shl_log2_tgt (w : Nat) (_h : 0 < w) :=
  [llvm(w)| {
  llvm.func @pow2_mul_shl_log2_tgt(%x : _, %C1 : _, %C2 : _, %C3 : _) -> i1 {
  ^bb0(%x : _, %C1 : _, %C2 : _, %C3 : _):
    %is_pow2_c1 = llvm.isPowerOf2 %C1 : _
    llvm.assume %is_pow2_c1 : i1
    %is_pow2_c2 = llvm.isPowerOf2 %C2 : _
    llvm.assume %is_pow2_c2 : i1
    %is_pow2_c3 = llvm.isPowerOf2 %C3 : _
    llvm.assume %is_pow2_c3 : i1
    %c3_mul_c1 = llvm.mul %C3, %C1 : _
    %c2_eq_c3_mul_c1 = llvm.icmp "eq" %C2, %c3_mul_c1 : _
    llvm.assume %c2_eq_c3_mul_c1 : i1
    %c3_shl_x = llvm.shl %C3, %x : _
    %masked = llvm.and %C2, %c3_shl_x : _
    %zero = llvm.mlir.constant(0 : _) : _
    %masked_ne_zero = llvm.icmp "ne" %masked, %zero : _
    llvm.assume %masked_ne_zero : i1
    %true = llvm.mlir.constant(true) : i1
    llvm.return %true : i1
  }
  }]

private theorem i55739_hydra35_semval_bind_poison {α β : Type} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl

private theorem i55739_hydra35_value {w : Nat} (_h : 0 < w) (x : BitVec w) (C1 : BitVec w) (C2 : BitVec w) (C3 : BitVec w)
    (hsh1 : ¬ (BitVec.ofNat w w ≤ x))
    (hpre1 : (((C1 &&& (C1 - 1#w)) == 0#w) && (C1 != 0#w)) = true)
    (hpre2 : (((C2 &&& (C2 - 1#w)) == 0#w) && (C2 != 0#w)) = true)
    (hpre3 : (((C3 &&& (C3 - 1#w)) == 0#w) && (C3 != 0#w)) = true)
    (hpre4 : (C2 == (C3 * C1)) = true)
    (hpre5 : ((C2 &&& (C3 <<< x.toNat)) != 0#w) = true) :
    (BitVec.ofBool (x == (BitVec.ofNat w (LLVM.countTrailingZerosNatRec C1 w 0)))) = 1#1 := by
  simp at hpre1 hpre2 hpre3 hpre4 hpre5 ⊢
  have _hpre2_used := hpre2
  clear hpre2
  rcases hpre1 with ⟨hC1and, hC1nz⟩
  rcases hpre3 with ⟨hC3and, hC3nz⟩
  have hxlt : x.toNat < w := by
    simp [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_two_pow_self (n := w))]
      at hsh1
    exact hsh1
  have natPow : ∀ n : Nat, n &&& (n - 1) = 0 → n ≠ 0 → ∃ k, n = 2 ^ k := by
    intro n h hn
    induction n using Nat.binaryRec with
    | zero => contradiction
    | bit b n ih =>
        cases b
        · have hn' : n ≠ 0 := by
            intro hz
            apply hn
            simp [Nat.bit, hz]
          have hrec : n &&& (n - 1) = 0 := by
            apply Nat.eq_of_testBit_eq
            intro i
            have hb := congrArg (fun m : Nat => m.testBit (i + 1)) h
            change (Nat.bit false n &&& (Nat.bit false n - 1)).testBit (i + 1) =
                (0 : Nat).testBit (i + 1) at hb
            rw [Nat.testBit_and] at hb
            rw [Nat.zero_testBit] at hb
            have hbit1 : (Nat.bit false n).testBit (i + 1) = n.testBit i := by
              rw [Nat.testBit_succ]
              have hdiv : (Nat.bit false n) / 2 = n := by
                simp [Nat.bit]
              rw [hdiv]
            have hbit2 : (Nat.bit false n - 1).testBit (i + 1) =
                (n - 1).testBit i := by
              rw [Nat.testBit_succ]
              have hdiv : (Nat.bit false n - 1) / 2 = n - 1 := by
                simp [Nat.bit]
                omega
              rw [hdiv]
            rw [Nat.testBit_and]
            cases hnbit : n.testBit i
            · simp
            · have : (n - 1).testBit i = false := by
                simpa [hbit1, hbit2, hnbit] using hb
              simp [this]
          rcases ih hrec hn' with ⟨k, hk⟩
          refine ⟨k + 1, ?_⟩
          simp [Nat.bit, hk, Nat.pow_succ]
          omega
        · have hnzero : n = 0 := by
            apply Nat.eq_of_testBit_eq
            intro i
            have hb := congrArg (fun m : Nat => m.testBit (i + 1)) h
            change (Nat.bit true n &&& (Nat.bit true n - 1)).testBit (i + 1) =
                (0 : Nat).testBit (i + 1) at hb
            rw [Nat.testBit_and] at hb
            rw [Nat.zero_testBit] at hb
            have hbit1 : (Nat.bit true n).testBit (i + 1) = n.testBit i := by
              rw [Nat.testBit_succ]
              have hdiv : (Nat.bit true n) / 2 = n := by
                simp [Nat.bit]
                omega
              rw [hdiv]
            have hbit2 : (Nat.bit true n - 1).testBit (i + 1) = n.testBit i := by
              rw [Nat.testBit_succ]
              have hdiv : (Nat.bit true n - 1) / 2 = n := by
                simp [Nat.bit]
              rw [hdiv]
            rw [Nat.zero_testBit]
            cases hnbit : n.testBit i
            · rfl
            · simp [hbit1, hbit2, hnbit] at hb
          refine ⟨0, ?_⟩
          simp [Nat.bit, hnzero]
  have toNatSubOne : ∀ C : BitVec w, ¬ C = 0#w → (C - 1#w).toNat = C.toNat - 1 := by
    intro C hnz
    rw [BitVec.toNat_sub]
    have h1lt : 1 < 2 ^ w := by
      simpa using (Nat.pow_lt_pow_right (a := 2) (m := 0) (n := w) (by decide : 1 < 2) _h)
    have h1 : (1#w : BitVec w).toNat = 1 := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt h1lt
    rw [h1]
    have hCpos : 0 < C.toNat := by
      by_contra hle
      have hzero : C.toNat = 0 := by omega
      apply hnz
      exact BitVec.eq_of_toNat_eq (by simp [hzero])
    have hClt : C.toNat < 2 ^ w := C.isLt
    have hrewrite : 2 ^ w - 1 + C.toNat = 2 ^ w + (C.toNat - 1) := by omega
    rw [hrewrite]
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  have onehot : ∀ C : BitVec w, C &&& C - 1#w = 0#w → ¬ C = 0#w →
      ∃ i, i < w ∧ C = BitVec.twoPow w i := by
    intro C hand hnz
    have hnzNat : C.toNat ≠ 0 := by
      intro hzero
      apply hnz
      exact BitVec.eq_of_toNat_eq (by simp [hzero])
    have handNat : C.toNat &&& (C.toNat - 1) = 0 := by
      have ht := congrArg BitVec.toNat hand
      change (C &&& (C - 1#w)).toNat = (0#w).toNat at ht
      rw [BitVec.toNat_and, toNatSubOne C hnz, BitVec.toNat_zero] at ht
      exact ht
    rcases natPow C.toNat handNat hnzNat with ⟨i, hi⟩
    have hi_lt : i < w := by
      by_contra hnot
      have hwle : w ≤ i := Nat.le_of_not_gt hnot
      have hpowle : 2 ^ w ≤ 2 ^ i := Nat.pow_le_pow_right (by decide : 0 < 2) hwle
      have hClt : C.toNat < 2 ^ w := C.isLt
      omega
    refine ⟨i, hi_lt, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [hi, BitVec.toNat_twoPow]
    exact (Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) hi_lt)).symm
  have ctzTwoPow : ∀ {i : Nat}, i < w →
      LLVM.countTrailingZerosNatRec (BitVec.twoPow w i) w 0 = i := by
    intro i hi
    have aux : ∀ rem acc : Nat, acc ≤ i → i < acc + rem →
        LLVM.countTrailingZerosNatRec (BitVec.twoPow w i) rem acc = i := by
      intro rem
      induction rem with
      | zero =>
          intro acc hacc hlt
          omega
      | succ rem ih =>
          intro acc hacc hlt
          simp [LLVM.countTrailingZerosNatRec, BitVec.getLsbD_twoPow, hi]
          by_cases heq : i = acc
          · simp [heq]
          · simp [heq]
            apply ih
            · omega
            · omega
    exact aux w 0 (by omega) (by simpa using hi)
  rcases onehot C1 hC1and hC1nz with ⟨a, ha_lt, hC1⟩
  rcases onehot C3 hC3and hC3nz with ⟨c, hc_lt, hC3⟩
  have hmask : BitVec.twoPow w (c + a) &&& BitVec.twoPow w (c + x.toNat) ≠ 0#w := by
    have h := hpre5
    rw [hpre4, hC1, hC3] at h
    rw [BitVec.twoPow_mul_twoPow_eq] at h
    simpa [BitVec.twoPow_eq, ← BitVec.shiftLeft_add] using h
  have hxa : x.toNat = a := by
    rw [BitVec.twoPow_and] at hmask
    simp [BitVec.getLsbD_twoPow] at hmask
    omega
  have hx_eq : x = BitVec.ofNat w a := by
    apply BitVec.eq_of_toNat_eq
    rw [hxa, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (Nat.lt_trans ha_lt (Nat.lt_two_pow_self (n := w)))).symm
  have hctz : LLVM.countTrailingZerosNatRec C1 w 0 = a := by
    rw [hC1]
    exact ctzTwoPow ha_lt
  have hx_ctz : x = BitVec.ofNat w (LLVM.countTrailingZerosNatRec C1 w 0) := by
    rw [hctz]
    exact hx_eq
  simp [hx_ctz]

set_option maxHeartbeats 4000000 in
theorem i55739_hydra35_correct (w : Nat) (_h : 0 < w) : pow2_mul_shl_log2_src w _h ⊑ pow2_mul_shl_log2_tgt w _h := by
  intro V
  let xVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨3, by simp⟩
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let C3Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases hC1 : V C1Var
  case poison =>
    simp [pow2_mul_shl_log2_src, pow2_mul_shl_log2_tgt, i55739_hydra35_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.cttz, LLVM.cttz?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.mul, LLVM.mul?, LLVM.shl, LLVM.shl?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C1 =>
    change BitVec w at C1
    cases hcond1 : (((C1 &&& (C1 - 1#w)) == 0#w) && (C1 != 0#w))
    · simp [pow2_mul_shl_log2_src, pow2_mul_shl_log2_tgt, i55739_hydra35_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, hcond1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.cttz, LLVM.cttz?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.mul, LLVM.mul?, LLVM.shl, LLVM.shl?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    ·
      cases hC2 : V C2Var
      case poison =>
        simp [pow2_mul_shl_log2_src, pow2_mul_shl_log2_tgt, i55739_hydra35_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hcond1, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.cttz, LLVM.cttz?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.mul, LLVM.mul?, LLVM.shl, LLVM.shl?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      case value C2 =>
        change BitVec w at C2
        cases hcond2 : (((C2 &&& (C2 - 1#w)) == 0#w) && (C2 != 0#w))
        · simp [pow2_mul_shl_log2_src, pow2_mul_shl_log2_tgt, i55739_hydra35_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hcond1, hC2, hcond2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.cttz, LLVM.cttz?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.mul, LLVM.mul?, LLVM.shl, LLVM.shl?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        ·
          cases hC3 : V C3Var
          case poison =>
            simp [pow2_mul_shl_log2_src, pow2_mul_shl_log2_tgt, i55739_hydra35_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C3Var, hC1, hcond1, hC2, hcond2, hC3, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.cttz, LLVM.cttz?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.mul, LLVM.mul?, LLVM.shl, LLVM.shl?, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
          case value C3 =>
            change BitVec w at C3
            cases hcond3 : (((C3 &&& (C3 - 1#w)) == 0#w) && (C3 != 0#w))
            · simp [pow2_mul_shl_log2_src, pow2_mul_shl_log2_tgt, i55739_hydra35_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C3Var, hC1, hcond1, hC2, hcond2, hC3, hcond3, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.cttz, LLVM.cttz?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.mul, LLVM.mul?, LLVM.shl, LLVM.shl?, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
            ·
              cases hcond4 : (C2 == (C3 * C1))
              · simp [pow2_mul_shl_log2_src, pow2_mul_shl_log2_tgt, i55739_hydra35_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C3Var, hC1, hcond1, hC2, hcond2, hC3, hcond3, hcond4, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.cttz, LLVM.cttz?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.mul, LLVM.mul?, LLVM.shl, LLVM.shl?, LLVM.assume_]
                exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
              ·
                cases hx : V xVar
                case poison =>
                  simp [pow2_mul_shl_log2_src, pow2_mul_shl_log2_tgt, i55739_hydra35_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C3Var, xVar, hC1, hcond1, hC2, hcond2, hC3, hcond3, hcond4, hx, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.cttz, LLVM.cttz?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.mul, LLVM.mul?, LLVM.shl, LLVM.shl?, LLVM.assume_]
                  exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                case value x =>
                  change BitVec w at x
                  by_cases hsh1 : BitVec.ofNat w w ≤ x
                  ·
                    simp [pow2_mul_shl_log2_src, pow2_mul_shl_log2_tgt, i55739_hydra35_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C3Var, xVar, hC1, hcond1, hC2, hcond2, hC3, hcond3, hcond4, hx, hsh1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.cttz, LLVM.cttz?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.mul, LLVM.mul?, LLVM.shl, LLVM.shl?, LLVM.assume_]
                    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                  ·
                    cases hcond5 : ((C2 &&& (C3 <<< x.toNat)) != 0#w)
                    · simp [pow2_mul_shl_log2_src, pow2_mul_shl_log2_tgt, i55739_hydra35_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C3Var, xVar, hC1, hcond1, hC2, hcond2, hC3, hcond3, hcond4, hx, hsh1, hcond5, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.cttz, LLVM.cttz?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.mul, LLVM.mul?, LLVM.shl, LLVM.shl?, LLVM.assume_]
                      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                    ·
                      simp [pow2_mul_shl_log2_src, pow2_mul_shl_log2_tgt, i55739_hydra35_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C3Var, xVar, hC1, hcond1, hC2, hcond2, hC3, hcond3, hcond4, hx, hsh1, hcond5, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.cttz, LLVM.cttz?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.mul, LLVM.mul?, LLVM.shl, LLVM.shl?, LLVM.assume_]
                      have hv := i55739_hydra35_value (w := w) _h x C1 C2 C3 hsh1 hcond1 hcond2 hcond3 hcond4 hcond5
                      exact ImmediateUBOr.IsRefinedBy.bothValues (by
                        constructor
                        · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv] <;> rfl)
                        · exact HVector.nil_isRefinedBy_nil)
