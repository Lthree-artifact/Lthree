import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def hydra38_54856_src (w1 : Nat) (_h1 : 0 < w1) :=
[llvm(w1)| {
llvm.func @hydra38_54856_src(%x : w1, %C1 : w1, %C2 : w1) -> i1 {
^bb0(%x : w1, %C1 : w1, %C2 : w1):
  %is_pow2 = llvm.isPowerOf2 %C1 : w1
  llvm.assume %is_pow2 : i1
  %one = llvm.mlir.constant(1 : w1) : w1
  %diff = llvm.sub %C1, %C2 : w1
  %is_diff_one = llvm.icmp "eq" %diff, %one : w1
  llvm.assume %is_diff_one : i1
  %c2_and_x = llvm.and %C2, %x : w1
  %c2_ne_and = llvm.icmp "ne" %C2, %c2_and_x : w1
  %x_ult_c1 = llvm.icmp "ult" %x, %C1 : w1
  %result = llvm.and %c2_ne_and, %x_ult_c1 : i1
  llvm.return %result : i1
}
}]

def hydra38_54856_tgt (w1 : Nat) (_h1 : 0 < w1) :=
[llvm(w1)| {
llvm.func @hydra38_54856_tgt(%x : w1, %C1 : w1, %C2 : w1) -> i1 {
^bb0(%x : w1, %C1 : w1, %C2 : w1):
  %is_pow2 = llvm.isPowerOf2 %C1 : w1
  llvm.assume %is_pow2 : i1
  %one = llvm.mlir.constant(1 : w1) : w1
  %diff = llvm.sub %C1, %C2 : w1
  %is_diff_one = llvm.icmp "eq" %diff, %one : w1
  llvm.assume %is_diff_one : i1
  %result = llvm.icmp "ult" %x, %C2 : w1
  llvm.return %result : i1
}
}]

private theorem i54856_hydra38_value {w1 : Nat} (_h1 : 0 < w1) (x : BitVec w1) (C1 : BitVec w1) (C2 : BitVec w1)
    (hpre1 : (((C1 &&& (C1 - 1#w1)) == 0#w1) && (C1 != 0#w1)) = true)
    (hpre2 : ((C1 - C2) == 1#w1) = true) :
    ((C2 != (C2 &&& x)) && (x <ᵤ C1)) = (x <ᵤ C2) := by
  simp at hpre1 hpre2
  have hC1and : C1 &&& (C1 - 1#w1) = 0#w1 := hpre1.1
  have hC1ne : C1 ≠ 0#w1 := hpre1.2
  have hcpos : 0 < C1.toNat := by
    by_contra h
    have hc0 : C1.toNat = 0 := by omega
    apply hC1ne
    exact BitVec.eq_of_toNat_eq (by simpa using hc0)
  have hpred_C1 : (C1 - 1#w1).toNat = C1.toNat - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_one _h1]
    have hc_lt : C1.toNat < 2 ^ w1 := C1.isLt
    have heq : 2 ^ w1 - 1 + C1.toNat = (C1.toNat - 1) + 2 ^ w1 := by omega
    rw [heq]
    nth_rewrite 1 [← Nat.mul_one (2 ^ w1)]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hnat_and : C1.toNat &&& (C1.toNat - 1) = 0 := by
    have h := congrArg BitVec.toNat hC1and
    simpa [BitVec.toNat_and, hpred_C1] using h
  have hbit_of_bounds :
      ∀ {n k : Nat}, 2 ^ k ≤ n → n < 2 ^ (k + 1) → n.testBit k = true := by
    intro n k hle hlt
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
    have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hdiv_ge : 1 ≤ n / 2 ^ k := by
      rw [Nat.le_div_iff_mul_le hkpos]
      simpa using hle
    have hdiv_lt : n / 2 ^ k < 2 := by
      rw [Nat.div_lt_iff_lt_mul hkpos]
      simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt
    have hdiv_eq : n / 2 ^ k = 1 := by omega
    simp [hdiv_eq]
  obtain ⟨k, hklt, hC1pow⟩ : ∃ k, k < w1 ∧ C1.toNat = 2 ^ k := by
    let k := C1.toNat.log2
    have hcne : C1.toNat ≠ 0 := by omega
    have hlog : 2 ^ k ≤ C1.toNat ∧ C1.toNat < 2 ^ (k + 1) := by
      exact (Nat.log2_eq_iff hcne).mp rfl
    have hc_eq_pow : C1.toNat = 2 ^ k := by
      by_contra hne
      have hgt : 2 ^ k < C1.toNat := by omega
      have hpred_ge : 2 ^ k ≤ C1.toNat - 1 := by omega
      have hpred_lt : C1.toNat - 1 < 2 ^ (k + 1) := by omega
      have hbit_c : C1.toNat.testBit k = true := hbit_of_bounds hlog.1 hlog.2
      have hbit_pred : (C1.toNat - 1).testBit k = true :=
        hbit_of_bounds hpred_ge hpred_lt
      have hzero := congrArg (fun n : Nat => n.testBit k) hnat_and
      simp [Nat.testBit_and, hbit_c, hbit_pred] at hzero
    have hklt : k < w1 := by
      have hc_lt : C1.toNat < 2 ^ w1 := C1.isLt
      by_contra hnot
      have hwle : w1 ≤ k := by omega
      have hp_le : 2 ^ w1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hwle
      omega
    exact ⟨k, hklt, hc_eq_pow⟩
  have hC2pred : C2.toNat = C1.toNat - 1 := by
    have hc1lt : C1.toNat < 2 ^ w1 := C1.isLt
    have hc2lt : C2.toNat < 2 ^ w1 := C2.isLt
    have h := congrArg BitVec.toNat hpre2
    rw [BitVec.toNat_sub, BitVec.toNat_one _h1] at h
    by_cases hlt : 2 ^ w1 - C2.toNat + C1.toNat < 2 ^ w1
    · have ha : 2 ^ w1 - C2.toNat + C1.toNat = 1 := by
        rw [Nat.mod_eq_of_lt hlt] at h
        exact h
      omega
    · have hge : 2 ^ w1 ≤ 2 ^ w1 - C2.toNat + C1.toNat := by omega
      have hlt2 : 2 ^ w1 - C2.toNat + C1.toNat - 2 ^ w1 < 2 ^ w1 := by omega
      have hmod : (2 ^ w1 - C2.toNat + C1.toNat) % 2 ^ w1 =
          (2 ^ w1 - C2.toNat + C1.toNat - 2 ^ w1) % 2 ^ w1 := by
        exact Nat.mod_eq_sub_mod hge
      rw [hmod, Nat.mod_eq_of_lt hlt2] at h
      omega
  have hC2pow : C2.toNat = 2 ^ k - 1 := by omega
  have hmask_and : ∀ {n : Nat}, n < 2 ^ k → (2 ^ k - 1) &&& n = n := by
    intro n hn
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < k
    · simp [hi]
    · have hki : k ≤ i := by omega
      have hpowle : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hki
      have hni : n < 2 ^ i := by omega
      have hnbit : n.testBit i = false := Nat.testBit_lt_two_pow hni
      simp [hi, hnbit]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    simp [Bool.and_eq_true, BitVec.ult_eq_decide, decide_eq_true_eq, bne_iff_ne] at h ⊢
    have hxltpow : x.toNat < 2 ^ k := by omega
    have hand_nat : (C2 &&& x).toNat = x.toNat := by
      rw [BitVec.toNat_and, hC2pow]
      exact hmask_and hxltpow
    have hxne : x.toNat ≠ C2.toNat := by
      intro hxeq
      apply h.1
      exact BitVec.eq_of_toNat_eq (by rw [hand_nat, hxeq])
    have hp : 0 < 2 ^ k := Nat.two_pow_pos k
    omega
  · intro h
    simp [Bool.and_eq_true, BitVec.ult_eq_decide, decide_eq_true_eq, bne_iff_ne] at h ⊢
    have hxltpow : x.toNat < 2 ^ k := by
      have hp : 0 < 2 ^ k := Nat.two_pow_pos k
      omega
    have hand_nat : (C2 &&& x).toNat = x.toNat := by
      rw [BitVec.toNat_and, hC2pow]
      exact hmask_and hxltpow
    constructor
    · intro heq
      have hnat := congrArg BitVec.toNat heq
      rw [hand_nat] at hnat
      omega
    · omega

set_option maxHeartbeats 4000000 in
theorem i54856_hydra38_correct (w1 : Nat) (_h1 : 0 < w1) : hydra38_54856_src w1 _h1 ⊑ hydra38_54856_tgt w1 _h1 := by
  intro V
  let xVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w1, InstCombine.LLVM.Ty.bitvec w1, InstCombine.LLVM.Ty.bitvec w1]).Var (InstCombine.LLVM.Ty.bitvec w1) := ⟨2, by simp⟩
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w1, InstCombine.LLVM.Ty.bitvec w1, InstCombine.LLVM.Ty.bitvec w1]).Var (InstCombine.LLVM.Ty.bitvec w1) := ⟨1, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w1, InstCombine.LLVM.Ty.bitvec w1, InstCombine.LLVM.Ty.bitvec w1]).Var (InstCombine.LLVM.Ty.bitvec w1) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w1, InstCombine.LLVM.Ty.bitvec w1]) (InstCombine.LLVM.Ty.bitvec w1)
  cases hC1 : V C1Var
  case poison =>
    simp [hydra38_54856_src, hydra38_54856_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.sub, LLVM.sub?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C1 =>
    change BitVec w1 at C1
    cases hcond1 : (((C1 &&& (C1 - 1#w1)) == 0#w1) && (C1 != 0#w1))
    · simp [hydra38_54856_src, hydra38_54856_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, hcond1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.sub, LLVM.sub?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    ·
      cases hC2 : V C2Var
      case poison =>
        simp [hydra38_54856_src, hydra38_54856_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hcond1, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.sub, LLVM.sub?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      case value C2 =>
        change BitVec w1 at C2
        cases hcond2 : ((C1 - C2) == 1#w1)
        · simp [hydra38_54856_src, hydra38_54856_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hcond1, hC2, hcond2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.sub, LLVM.sub?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        ·
          cases hx : V xVar
          case poison =>
            simp [hydra38_54856_src, hydra38_54856_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, xVar, hC1, hcond1, hC2, hcond2, hx, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.sub, LLVM.sub?, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  first
                  | exact LLVM.SemVal.poison_isRefinedBy _
                  | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                  | simp [LLVM.IntW.instRefinement])
              · exact HVector.nil_isRefinedBy_nil)
          case value x =>
            change BitVec w1 at x
            simp [hydra38_54856_src, hydra38_54856_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, xVar, hC1, hcond1, hC2, hcond2, hx, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.sub, LLVM.sub?, LLVM.assume_]
            have hv := i54856_hydra38_value (w1 := w1) _h1 x C1 C2 hcond1 hcond2
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv] <;> rfl)
              · exact HVector.nil_isRefinedBy_nil)
