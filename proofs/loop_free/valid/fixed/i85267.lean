import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def i85267_src :=
  [llvm()| {
  llvm.func @i85267_src(%x : i32, %C1 : i32, %C2 : i32) -> i1 {
  ^bb0(%x : i32, %C1 : i32, %C2 : i32):
    %zero = llvm.mlir.constant(0 : i32) : i32
    %one = llvm.mlir.constant(1 : i32) : i32
    %int_min = llvm.mlir.constant(2147483648 : i32) : i32
    %c1_is_positive = llvm.icmp "sgt" %C1, %zero : i32
    llvm.assume %c1_is_positive : i1
    %c2_is_not_min = llvm.icmp "ne" %C2, %int_min : i32
    llvm.assume %c2_is_not_min : i1
    %c2m1 = llvm.sub %C2, %one : i32
    %c2m1_is_non_negative = llvm.icmp "sge" %c2m1, %zero : i32
    llvm.assume %c2m1_is_non_negative : i1
    %mul = llvm.mul %x, %C1 overflow<nsw> : i32
    %cmp = llvm.icmp "slt" %mul, %C2 : i32
    llvm.return %cmp : i1
  }
  }]

def i85267_tgt :=
  [llvm()| {
  llvm.func @i85267_tgt(%x : i32, %C1 : i32, %C2 : i32) -> i1 {
  ^bb0(%x : i32, %C1 : i32, %C2 : i32):
    %zero = llvm.mlir.constant(0 : i32) : i32
    %one = llvm.mlir.constant(1 : i32) : i32
    %int_min = llvm.mlir.constant(2147483648 : i32) : i32
    %c1_is_positive = llvm.icmp "sgt" %C1, %zero : i32
    llvm.assume %c1_is_positive : i1
    %c2_is_not_min = llvm.icmp "ne" %C2, %int_min : i32
    llvm.assume %c2_is_not_min : i1
    %c2m1 = llvm.sub %C2, %one : i32
    %c2m1_is_non_negative = llvm.icmp "sge" %c2m1, %zero : i32
    llvm.assume %c2m1_is_non_negative : i1
    %div = llvm.sdiv %c2m1, %C1 : i32
    %cmp = llvm.icmp "sle" %x, %div : i32
    llvm.return %cmp : i1
  }
  }]

private theorem i85267_semval_bind_poison {α β : Type} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl

private theorem i85267_sdiv_eq_if {w : Nat} {x y : BitVec w} :
    LLVM.sdiv (LLVM.SemVal.value x) (LLVM.SemVal.value y) =
      (if (y = 0#w) ∨ (¬ w = 1 ∧ x = BitVec.intMin w ∧ y = BitVec.ofInt w (-1))
       then (.immediateUB : LLVM.IntWUB w)
       else (.value (x.sdiv y) : LLVM.IntWUB w)) := by
  have hneg : BitVec.ofInt w (-1) = -1 := by simp [BitVec.ofInt_neg, BitVec.ofInt_ofNat]
  simp [LLVM.sdiv, hneg]
  split_ifs <;> simp_all

private theorem i85267_sdiv_poisonL {w : Nat} (y : LLVM.IntW w) (f : LLVM.ExactFlag) :
    LLVM.sdiv (LLVM.SemVal.poison) y f = (.poison : LLVM.IntWUB w) := rfl

private theorem i85267_sdiv_poisonR {w : Nat} (x : LLVM.IntW w) (f : LLVM.ExactFlag) :
    LLVM.sdiv x (LLVM.SemVal.poison) f = (.poison : LLVM.IntWUB w) := by
  cases x <;> rfl

private theorem i85267_value (x : BitVec 32) (C1 : BitVec 32) (C2 : BitVec 32)
    (hpre1 : (0#32 <ₛ C1) = true)
    (hpre2 : (C2 != 2147483648#32) = true)
    (hpre3 : (0#32 ≤ₛ (C2 - 1#32)) = true)
    (htub1 : ¬ (C1 = 0#32 ∨ ((C2 - 1#32) = BitVec.intMin 32 ∧ C1 = 4294967295#32)))
    (hov : x.smulOverflow C1 = false) :
    ((x * C1) <ₛ C2) = (x ≤ₛ ((C2 - 1#32).sdiv C1)) := by
  let A : BitVec 32 := C2 - 1#32
  have hC1pos : 0 < C1.toInt := by
    simpa [BitVec.slt_eq_decide] using hpre1
  have hAnonneg : 0 ≤ A.toInt := by
    simpa [A, BitVec.sle_eq_decide] using hpre3
  have hC1msb : C1.msb = false := by
    cases h : C1.msb
    · rfl
    · have hn : C1.toInt < 0 := BitVec.toInt_neg_of_msb_true h
      omega
  have hAmsb : A.msb = false := by
    cases h : A.msb
    · rfl
    · have hn : A.toInt < 0 := BitVec.toInt_neg_of_msb_true h
      omega
  have hC1toNat : C1.toInt = C1.toNat := BitVec.toInt_eq_toNat_of_msb hC1msb
  have hAtoNat : A.toInt = A.toNat := BitVec.toInt_eq_toNat_of_msb hAmsb
  have hC2posB : (0#32 <ₛ C2) = true := by
    simp only [BitVec.slt, BitVec.sle, bne_iff_ne, ne_eq, decide_eq_true_eq] at hpre2 hpre3 ⊢
    simp only [BitVec.toInt_eq_toNat_cond] at hpre3 ⊢
    bv_omega
  have hC2pos : 0 < C2.toInt := by
    simpa [BitVec.slt_eq_decide] using hC2posB
  have hC2msb : C2.msb = false := by
    cases h : C2.msb
    · rfl
    · have hn : C2.toInt < 0 := BitVec.toInt_neg_of_msb_true h
      omega
  have hC2toNat : C2.toInt = C2.toNat := BitVec.toInt_eq_toNat_of_msb hC2msb
  have hC2natpos : 0 < C2.toNat := by omega
  have hAtoNatSub : A.toNat = C2.toNat - 1 := by
    change (C2 - 1#32).toNat = C2.toNat - 1
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have hAtoIntSub : A.toInt = C2.toInt - 1 := by
    rw [hAtoNat, hAtoNatSub, hC2toNat]
    omega
  have hsdiv : A.sdiv C1 = A / C1 := by
    rw [BitVec.sdiv_eq]
    simp [hAmsb, hC1msb]
  have hq_le : (A / C1).toNat ≤ A.toNat := by
    rw [BitVec.toNat_udiv]
    exact Nat.div_le_self A.toNat C1.toNat
  have hAmsbNat : 2 * A.toNat < 2 ^ 32 := BitVec.msb_eq_false_iff_two_mul_lt.mp hAmsb
  have hqmsb : (A / C1).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    omega
  have hq : ((C2 - 1#32).sdiv C1).toInt = (C2.toInt - 1) / C1.toInt := by
    rw [show (C2 - 1#32).sdiv C1 = A.sdiv C1 by rfl, hsdiv]
    rw [BitVec.toInt_eq_toNat_of_msb hqmsb, BitVec.toNat_udiv]
    rw [← hAtoIntSub, hAtoNat, hC1toNat]
    exact Int.natCast_ediv A.toNat C1.toNat
  have hmul : (x * C1).toInt = x.toInt * C1.toInt := by
    have hno : ¬x.smulOverflow C1 = true := by
      simp [hov]
    exact BitVec.toInt_mul_of_not_smulOverflow hno
  rw [BitVec.slt_eq_decide, BitVec.sle_eq_decide]
  rw [hmul, hq]
  exact decide_eq_decide.mpr (by
    constructor
    · intro hlt
      exact (Int.le_ediv_iff_mul_le hC1pos).2 (by omega)
    · intro hle
      have hmle : x.toInt * C1.toInt ≤ C2.toInt - 1 :=
        (Int.le_ediv_iff_mul_le hC1pos).1 hle
      omega)

private theorem i85267_tgtub1 (C1 : BitVec 32) (C2 : BitVec 32)
    (hpre1 : (0#32 <ₛ C1) = true)
    (hpre2 : (C2 != 2147483648#32) = true)
    (hpre3 : (0#32 ≤ₛ (C2 - 1#32)) = true)
    (htub1 : C1 = 0#32 ∨ ((C2 - 1#32) = BitVec.intMin 32 ∧ C1 = 4294967295#32)) :
    False := by
  simp only [BitVec.slt, BitVec.sle, bne_iff_ne, ne_eq, decide_eq_true_eq] at hpre1 hpre2 hpre3
  simp only [BitVec.toInt_eq_toNat_cond] at hpre1 hpre3
  bv_omega

set_option maxHeartbeats 4000000 in
theorem i85267_correct : i85267_src ⊑ i85267_tgt := by
  intro V
  let xVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨2, by simp⟩
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨1, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]) (InstCombine.LLVM.Ty.bitvec 32)
  cases hC1 : V C1Var
  case poison =>
    simp [i85267_src, i85267_tgt, i85267_semval_bind_poison, i85267_sdiv_eq_if, i85267_sdiv_poisonL, i85267_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, InstCombine.lift2UB, LLVM.sub, LLVM.sub?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C1 =>
    change BitVec 32 at C1
    cases hcond1 : (0#32 <ₛ C1)
    · simp [i85267_src, i85267_tgt, i85267_semval_bind_poison, i85267_sdiv_eq_if, i85267_sdiv_poisonL, i85267_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, hcond1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, InstCombine.lift2UB, LLVM.sub, LLVM.sub?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    ·
      cases hC2 : V C2Var
      case poison =>
        simp [i85267_src, i85267_tgt, i85267_semval_bind_poison, i85267_sdiv_eq_if, i85267_sdiv_poisonL, i85267_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hcond1, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, InstCombine.lift2UB, LLVM.sub, LLVM.sub?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      case value C2 =>
        change BitVec 32 at C2
        cases hcond2 : (C2 != 2147483648#32)
        · simp [i85267_src, i85267_tgt, i85267_semval_bind_poison, i85267_sdiv_eq_if, i85267_sdiv_poisonL, i85267_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hcond1, hC2, hcond2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, InstCombine.lift2UB, LLVM.sub, LLVM.sub?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        ·
          cases hcond3 : (0#32 ≤ₛ (C2 - 1#32))
          · simp [i85267_src, i85267_tgt, i85267_semval_bind_poison, i85267_sdiv_eq_if, i85267_sdiv_poisonL, i85267_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hcond1, hC2, hcond2, hcond3, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, InstCombine.lift2UB, LLVM.sub, LLVM.sub?, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
          ·
            by_cases htub1 : C1 = 0#32 ∨ ((C2 - 1#32) = BitVec.intMin 32 ∧ C1 = 4294967295#32)
            ·
              exfalso
              exact i85267_tgtub1 C1 C2 hcond1 hcond2 hcond3 htub1
            ·
              cases hx : V xVar with
              | poison =>
                simp [i85267_src, i85267_tgt, i85267_semval_bind_poison, i85267_sdiv_eq_if, i85267_sdiv_poisonL, i85267_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, xVar, hC1, hcond1, hC2, hcond2, hcond3, htub1, hx, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, InstCombine.lift2UB, LLVM.sub, LLVM.sub?, LLVM.assume_]
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
                cases hov : x.smulOverflow C1
                · simp [i85267_src, i85267_tgt, i85267_semval_bind_poison, i85267_sdiv_eq_if, i85267_sdiv_poisonL, i85267_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, xVar, hC1, hcond1, hC2, hcond2, hcond3, htub1, hx, hov, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, InstCombine.lift2UB, LLVM.sub, LLVM.sub?, LLVM.assume_]
                  have hv := i85267_value x C1 C2 hcond1 hcond2 hcond3 htub1 hov
                  exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    constructor
                    · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv] <;> rfl)
                    · exact HVector.nil_isRefinedBy_nil)
                · simp [i85267_src, i85267_tgt, i85267_semval_bind_poison, i85267_sdiv_eq_if, i85267_sdiv_poisonL, i85267_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, xVar, hC1, hcond1, hC2, hcond2, hcond3, htub1, hx, hov, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, InstCombine.lift2UB, LLVM.sub, LLVM.sub?, LLVM.assume_]
                  exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    constructor
                    · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                        first
                        | exact LLVM.SemVal.poison_isRefinedBy _
                        | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                        | simp [LLVM.IntW.instRefinement])
                    · exact HVector.nil_isRefinedBy_nil)
