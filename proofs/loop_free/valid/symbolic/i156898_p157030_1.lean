import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def trunc_shr_to_i1_src_with_precond_src (w1 : Nat)(_h : 0 < w1) :=
  [llvm(w1)| {
  llvm.func @trunc_shr_to_i1_src_with_precond_src(%V : _, %C : _) -> i1 {
  ^bb0(%V : _, %C : _):
    %one = llvm.mlir.constant(1 : _) : _
    %C_plus_1 = llvm.add %C, %one
    %is_pow2 = llvm.isPowerOf2 %C_plus_1 : _
    llvm.assume %is_pow2 : i1
    %shr = llvm.lshr %C, %V
    %r = llvm.trunc %shr : _ to i1
    llvm.return %r : i1
  }
  }]

def trunc_shr_to_i1_tgt_with_precond_tgt (w1 : Nat)(_h : 0 < w1) :=
  [llvm(w1)| {
  llvm.func @trunc_shr_to_i1_tgt_with_precond_tgt(%V : _, %C : _) -> i1 {
  ^bb0(%V : _, %C : _):
    %one = llvm.mlir.constant(1 : _) : _
    %C_plus_1 = llvm.add %C, %one
    %is_pow2 = llvm.isPowerOf2 %C_plus_1 : _
    llvm.assume %is_pow2 : i1
    %log2_C_plus_1 = llvm.ctpop %C
    %r = llvm.icmp "ult" %V, %log2_C_plus_1
    llvm.return %r : i1
  }
  }]

private theorem i156898_p157030_1_semval_bind_poison {α β : Type} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl

private theorem i156898_p157030_1_value {w1 : Nat} (_h : 0 < w1) (Vv : BitVec w1) (C : BitVec w1)
    (hpre : ((((C + 1#w1) &&& ((C + 1#w1) - 1#w1)) == 0#w1) && ((C + 1#w1) != 0#w1)) = true)
    (hsh1 : ¬ (BitVec.ofNat w1 w1 ≤ Vv)) :
    (BitVec.setWidth 1 (C >>> Vv.toNat)) = (BitVec.ofBool (Vv <ᵤ (BitVec.ofNat w1 (LLVM.popCountNatRec C w1 0)))) := by
  have land_self : ∀ n : Nat, Nat.land n n = n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rw [Nat.land, Nat.bitwise.eq_1]
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn]
        have hdivlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
        have ihdiv : Nat.bitwise and (n / 2) (n / 2) = n / 2 := by
          simpa [Nat.land] using ih (n / 2) hdivlt
        rw [ihdiv]
        have hmod := Nat.mod_two_eq_zero_or_one n
        rcases hmod with hmod | hmod <;> simp [hmod]
        · omega
        · omega
  have mask_of_land_succ : ∀ n : Nat, Nat.land (n + 1) n = 0 -> ∃ k, n = 2 ^ k - 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hland
      by_cases hn : n = 0
      · subst n
        exact ⟨0, by decide⟩
      · have hmod_cases := Nat.mod_two_eq_zero_or_one n
        rcases hmod_cases with hmod | hmod
        · rw [Nat.land, Nat.bitwise.eq_1] at hland
          simp [hn, hmod] at hland
          have hdiv : (n + 1) / 2 = n / 2 := by omega
          rw [hdiv] at hland
          have ihself : Nat.bitwise and (n / 2) (n / 2) = n / 2 := by
            simpa [Nat.land] using land_self (n / 2)
          rw [ihself] at hland
          have hn_div_zero : n / 2 = 0 := hland
          omega
        · rw [Nat.land, Nat.bitwise.eq_1] at hland
          have hsuccmod : (n + 1) % 2 = 0 := by omega
          simp [hn, hmod, hsuccmod] at hland
          have hsuccdiv : (n + 1) / 2 = n / 2 + 1 := by omega
          rw [hsuccdiv] at hland
          have hland' : Nat.land (n / 2 + 1) (n / 2) = 0 := by
            simpa [Nat.land] using hland
          have hdivlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
          rcases ih (n / 2) hdivlt hland' with ⟨k, hk⟩
          refine ⟨k + 1, ?_⟩
          have hdecomp : 2 * (n / 2) + n % 2 = n := by
            simpa [Nat.mul_comm] using (Nat.div_add_mod n 2)
          rw [hmod] at hdecomp
          rw [← hdecomp, hk, Nat.pow_succ]
          have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide : 0 < 2)
          omega
  have hlandC : Nat.land (C.toNat + 1) C.toNat = 0 := by
    have hp := hpre
    simp at hp
    rcases hp with ⟨hand, hne⟩
    have hsub : (C + 1#w1 - 1#w1) = C := by
      apply BitVec.eq_of_toNat_eq
      by_cases hw : w1 = 0
      · subst w1
        simp
      · have hMgt1 : 1 < 2 ^ w1 := Nat.one_lt_two_pow hw
        have hc_lt : C.toNat < 2 ^ w1 := C.toFin.isLt
        have hone : 1 % 2 ^ w1 = 1 := Nat.mod_eq_of_lt hMgt1
        simp [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, hone]
        have hsum : 2 ^ w1 - 1 + (C.toNat + 1) = 2 ^ w1 + C.toNat := by omega
        rw [hsum, Nat.add_mod, Nat.mod_self, Nat.mod_eq_of_lt hc_lt]
        simp
    rw [hsub] at hand
    have handNat : (C + 1#w1 &&& C).toNat = (0#w1).toNat := by rw [hand]
    simp [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ofNat] at handNat
    have hnowrap : C.toNat + 1 < 2 ^ w1 := by
      have hneNat : (C + 1#w1).toNat ≠ (0#w1).toNat := by
        intro h
        exact hne (BitVec.eq_of_toNat_eq h)
      simp [BitVec.toNat_add, BitVec.toNat_ofNat] at hneNat
      have hle : C.toNat + 1 ≤ 2 ^ w1 := by
        have hc := C.toFin.isLt
        omega
      by_contra hlt
      have heq : C.toNat + 1 = 2 ^ w1 := by omega
      simp [heq, Nat.mod_self] at hneNat
    rw [Nat.mod_eq_of_lt hnowrap] at handNat
    exact handNat
  rcases mask_of_land_succ C.toNat hlandC with ⟨k, hCnat⟩
  have hk_le_w : k ≤ w1 := by
    by_contra hnot
    have hwk : w1 < k := Nat.lt_of_not_ge hnot
    have hp : 2 ^ w1 < 2 ^ k := Nat.pow_lt_pow_right (by decide : 1 < 2) hwk
    have hc_lt : C.toNat < 2 ^ w1 := C.toFin.isLt
    omega
  have hbit : ∀ i, C.getLsbD i = decide (i < k) := by
    intro i
    simp [BitVec.getLsbD, hCnat, Nat.testBit_two_pow_sub_one]
  have hpop_aux : ∀ pos acc, LLVM.popCountNatRec C pos acc = acc + Nat.min pos k := by
    intro pos
    induction pos with
    | zero =>
        intro acc
        simp [LLVM.popCountNatRec]
    | succ n ih =>
        intro acc
        rw [LLVM.popCountNatRec, ih]
        rw [hbit n]
        by_cases hn : n < k
        · have hminn : Nat.min n k = n := Nat.min_eq_left (Nat.le_of_lt hn)
          have hminsucc : Nat.min (n + 1) k = n + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hn)
          simp [hn, hminn, hminsucc]
          omega
        · have hklen : k ≤ n := Nat.le_of_not_gt hn
          have hminn : Nat.min n k = k := Nat.min_eq_right hklen
          have hminsucc : Nat.min (n + 1) k = k := Nat.min_eq_right (Nat.le_trans hklen (Nat.le_succ n))
          simp [hn, hminn, hminsucc]
  have hpop : LLVM.popCountNatRec C w1 0 = k := by
    rw [hpop_aux]
    simp [Nat.min_eq_right hk_le_w]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  simp [BitVec.getLsbD_ushiftRight]
  rw [hbit Vv.toNat]
  rw [hpop]
  have hk_lt_pow : k < 2 ^ w1 := lt_of_le_of_lt hk_le_w Nat.lt_two_pow_self
  simp [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk_lt_pow]

set_option maxHeartbeats 4000000 in
theorem i156898_p157030_1_correct (w1 : Nat) (_h : 0 < w1) : trunc_shr_to_i1_src_with_precond_src w1 _h ⊑ trunc_shr_to_i1_tgt_with_precond_tgt w1 _h := by
  intro V
  let VVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w1, InstCombine.LLVM.Ty.bitvec w1]).Var (InstCombine.LLVM.Ty.bitvec w1) := ⟨1, by simp⟩
  let CVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w1, InstCombine.LLVM.Ty.bitvec w1]).Var (InstCombine.LLVM.Ty.bitvec w1) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w1]) (InstCombine.LLVM.Ty.bitvec w1)
  cases hC : V CVar
  case poison =>
    simp [trunc_shr_to_i1_src_with_precond_src, trunc_shr_to_i1_tgt_with_precond_tgt, i156898_p157030_1_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, hC, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.ctpop, LLVM.ctpop?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.lshr, LLVM.lshr?, LLVM.trunc, LLVM.trunc?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C =>
    change BitVec w1 at C
    cases hcond : ((((C + 1#w1) &&& ((C + 1#w1) - 1#w1)) == 0#w1) && ((C + 1#w1) != 0#w1))
    · simp [trunc_shr_to_i1_src_with_precond_src, trunc_shr_to_i1_tgt_with_precond_tgt, i156898_p157030_1_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, hC, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.ctpop, LLVM.ctpop?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.lshr, LLVM.lshr?, LLVM.trunc, LLVM.trunc?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    ·
      cases hV : V VVar
      case poison =>
        simp [trunc_shr_to_i1_src_with_precond_src, trunc_shr_to_i1_tgt_with_precond_tgt, i156898_p157030_1_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, VVar, hC, hcond, hV, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.ctpop, LLVM.ctpop?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.lshr, LLVM.lshr?, LLVM.trunc, LLVM.trunc?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.bothValues (by
          constructor
          · exact ImmediateUBOr.IsRefinedBy.bothValues (by
              first
              | exact LLVM.SemVal.poison_isRefinedBy _
              | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
              | simp [LLVM.IntW.instRefinement])
          · exact HVector.nil_isRefinedBy_nil)
      case value Vv =>
        change BitVec w1 at Vv
        by_cases hsh1 : BitVec.ofNat w1 w1 ≤ Vv
        ·
          simp [trunc_shr_to_i1_src_with_precond_src, trunc_shr_to_i1_tgt_with_precond_tgt, i156898_p157030_1_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, VVar, hC, hcond, hV, hsh1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.ctpop, LLVM.ctpop?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.lshr, LLVM.lshr?, LLVM.trunc, LLVM.trunc?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.bothValues (by
            constructor
            · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                first
                | exact LLVM.SemVal.poison_isRefinedBy _
                | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                | simp [LLVM.IntW.instRefinement])
            · exact HVector.nil_isRefinedBy_nil)
        ·
          simp [trunc_shr_to_i1_src_with_precond_src, trunc_shr_to_i1_tgt_with_precond_tgt, i156898_p157030_1_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, VVar, hC, hcond, hV, hsh1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.ctpop, LLVM.ctpop?, LLVM.isPowerOf2, LLVM.isPowerOf2?, LLVM.lshr, LLVM.lshr?, LLVM.trunc, LLVM.trunc?, LLVM.assume_]
          have hv := i156898_p157030_1_value (w1 := w1) _h Vv C hcond hsh1
          exact ImmediateUBOr.IsRefinedBy.bothValues (by
            constructor
            · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv] <;> rfl)
            · exact HVector.nil_isRefinedBy_nil)
