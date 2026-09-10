import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def i167055_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167055_src(%arg0 : _, %C1 : _, %C2 : _) -> i1 {
  ^bb0(%arg0 : _, %C1 : _, %C2 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c1_ge_0 = llvm.icmp "sge" %C1, %zero : _
    %sum = llvm.add %C1, %C2 : _
    %sum_gt_c1 = llvm.icmp "sgt" %sum, %C1 : _
    %c2_le_0 = llvm.icmp "sle" %C2, %zero : _
    %sum_le_0 = llvm.icmp "sle" %sum, %zero : _
    %cond_neg = llvm.and %c2_le_0, %sum_le_0 : i1
    %ok = llvm.or %sum_gt_c1, %cond_neg : i1
    %cond = llvm.and %c1_ge_0, %ok : i1
    llvm.assume %cond : i1
    %umin_c = llvm.icmp "ult" %arg0, %C1 : _
    %v0 = llvm.select %umin_c, %arg0, %C1 : _
    %v1 = llvm.sub %arg0, %v0 overflow<nsw> : _
    %v2 = llvm.icmp "slt" %v1, %C2 : _
    llvm.return %v2 : i1
  }
  }]

def i167055_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167055_tgt(%arg0 : _, %C1 : _, %C2 : _) -> i1 {
  ^bb0(%arg0 : _, %C1 : _, %C2 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c1_ge_0 = llvm.icmp "sge" %C1, %zero : _
    %sum = llvm.add %C1, %C2 : _
    %sum_gt_c1 = llvm.icmp "sgt" %sum, %C1 : _
    %c2_le_0 = llvm.icmp "sle" %C2, %zero : _
    %sum_le_0 = llvm.icmp "sle" %sum, %zero : _
    %cond_neg = llvm.and %c2_le_0, %sum_le_0 : i1
    %ok = llvm.or %sum_gt_c1, %cond_neg : i1
    %cond = llvm.and %c1_ge_0, %ok : i1
    llvm.assume %cond : i1
    %v0 = llvm.add %C1, %C2 : _
    %v1 = llvm.icmp "slt" %arg0, %v0 : _
    llvm.return %v1 : i1
  }
  }]

private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by
  cases b <;> simp

private theorem i167055_value {w : Nat} (arg0 : BitVec w) (C1 : BitVec w) (C2 : BitVec w)
    (hpre : ((0#w ≤ₛ C1) && ((C1 <ₛ (C1 + C2)) || ((C2 ≤ₛ 0#w) && ((C1 + C2) ≤ₛ 0#w)))) = true)
    (hov : arg0.ssubOverflow (if (arg0 <ᵤ C1) = true then arg0 else C1) = false) :
    ((arg0 - (if (arg0 <ᵤ C1) = true then arg0 else C1)) <ₛ C2) = (arg0 <ₛ (C1 + C2)) := by
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hpre
  rcases hpre with ⟨hC1nonneg, hpos | hneg⟩
  · have hC1i : 0 ≤ C1.toInt := by
      simpa using (BitVec.sle_iff_toInt_le.mp hC1nonneg)
    have hposi : C1.toInt < (C1 + C2).toInt := by
      exact BitVec.slt_iff_toInt_lt.mp hpos
    have hC1msb : C1.msb = false := by
      rw [BitVec.msb_eq_toInt]
      exact decide_eq_false (not_lt.mpr hC1i)
    have hadd : ¬C1.saddOverflow C2 = true := by
      have hsum_msb : (C1 + C2).msb = false := by
        rw [BitVec.msb_eq_toInt]
        have : 0 ≤ (C1 + C2).toInt := by omega
        exact decide_eq_false (not_lt.mpr this)
      rw [BitVec.saddOverflow_eq, hC1msb, hsum_msb]
      simp
    rw [BitVec.toInt_add_of_not_saddOverflow hadd] at hposi
    by_cases hfs : (arg0 <ᵤ C1) = true
    · simp [hfs]
      have harg0_nat_lt : arg0.toNat < C1.toNat := by
        exact BitVec.ult_iff_toNat_lt.mp hfs
      have harg0_msb : arg0.msb = false := by
        rw [BitVec.msb_eq_decide]
        apply decide_eq_false
        simp only [Nat.not_le]
        have hC1nat_lt : C1.toNat < 2 ^ (w - 1) := BitVec.toNat_lt_of_msb_false hC1msb
        omega
      have harg0i : arg0.toInt < C1.toInt := by
        have harg0_toInt := BitVec.toInt_eq_toNat_of_msb harg0_msb
        have hC1_toInt := BitVec.toInt_eq_toNat_of_msb hC1msb
        omega
      rw [Bool.eq_iff_iff]
      simp only [BitVec.slt_iff_toInt_lt, BitVec.toInt_zero]
      rw [BitVec.toInt_add_of_not_saddOverflow hadd]
      omega
    · simp [hfs]
      have hsubf : arg0.ssubOverflow C1 = false := by
        simpa [hfs] using hov
      have hsub : ¬arg0.ssubOverflow C1 = true := by
        simp [hsubf]
      rw [Bool.eq_iff_iff]
      simp only [BitVec.slt_iff_toInt_lt]
      rw [BitVec.toInt_sub_of_not_ssubOverflow hsub, BitVec.toInt_add_of_not_saddOverflow hadd]
      omega
  · rcases hneg with ⟨hC2nonpos, hsum_nonpos⟩
    have hC1i : 0 ≤ C1.toInt := by
      simpa using (BitVec.sle_iff_toInt_le.mp hC1nonneg)
    have hC2i : C2.toInt ≤ 0 := by
      simpa using (BitVec.sle_iff_toInt_le.mp hC2nonpos)
    have hsumi : (C1 + C2).toInt ≤ 0 := by
      simpa using (BitVec.sle_iff_toInt_le.mp hsum_nonpos)
    have hC1msb : C1.msb = false := by
      rw [BitVec.msb_eq_toInt]
      exact decide_eq_false (not_lt.mpr hC1i)
    have hadd : ¬C1.saddOverflow C2 = true := by
      rw [BitVec.saddOverflow_eq, hC1msb]
      simp
      intro hC2msb
      have hC2nonneg : 0 ≤ C2.toInt := BitVec.toInt_nonneg_of_msb_false hC2msb
      have hC2zero : C2 = 0#w := by
        apply BitVec.eq_of_toInt_eq
        simp [show C2.toInt = 0 by omega]
      subst C2
      simp [hC1msb]
    by_cases hfs : (arg0 <ᵤ C1) = true
    · simp [hfs]
      have harg0_nat_lt : arg0.toNat < C1.toNat := by
        exact BitVec.ult_iff_toNat_lt.mp hfs
      have harg0_msb : arg0.msb = false := by
        rw [BitVec.msb_eq_decide]
        apply decide_eq_false
        simp only [Nat.not_le]
        have hC1nat_lt : C1.toNat < 2 ^ (w - 1) := BitVec.toNat_lt_of_msb_false hC1msb
        omega
      have harg0i_nonneg : 0 ≤ arg0.toInt := BitVec.toInt_nonneg_of_msb_false harg0_msb
      rw [Bool.eq_iff_iff]
      simp only [BitVec.slt_iff_toInt_lt, BitVec.toInt_zero]
      omega
    · simp [hfs]
      have hsubf : arg0.ssubOverflow C1 = false := by
        simpa [hfs] using hov
      have hsub : ¬arg0.ssubOverflow C1 = true := by
        simp [hsubf]
      rw [Bool.eq_iff_iff]
      simp only [BitVec.slt_iff_toInt_lt]
      rw [BitVec.toInt_sub_of_not_ssubOverflow hsub, BitVec.toInt_add_of_not_saddOverflow hadd]
      omega

set_option maxHeartbeats 4000000 in
theorem i167055_correct (w : Nat) : i167055_src w ⊑ i167055_tgt w := by
  intro V
  let arg0Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases hC1 : V C1Var
  case poison =>
    simp [i167055_src, i167055_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C1 =>
    change BitVec w at C1
    cases hC2 : V C2Var
    case poison =>
      simp [i167055_src, i167055_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value C2 =>
      change BitVec w at C2
      cases hcond : ((0#w ≤ₛ C1) && ((C1 <ₛ (C1 + C2)) || ((C2 ≤ₛ 0#w) && ((C1 + C2) ≤ₛ 0#w))))
      · simp [i167055_src, i167055_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hC2, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      ·
        cases harg0 : V arg0Var
        case poison =>
          simp [i167055_src, i167055_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, arg0Var, hC1, hC2, hcond, harg0, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.bothValues (by
            constructor
            · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                first
                | exact LLVM.SemVal.poison_isRefinedBy _
                | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                | simp [LLVM.IntW.instRefinement])
            · exact HVector.nil_isRefinedBy_nil)
        case value arg0 =>
          change BitVec w at arg0
          by_cases hfs : (arg0 <ᵤ C1) = true
          ·
            cases hov : arg0.ssubOverflow arg0
            ·
              simp [i167055_src, i167055_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, arg0Var, hC1, hC2, hcond, harg0, ofBool_one_iff, hfs, hov, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.bothValues (by
                constructor
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    have hv := i167055_value (w := w) arg0 C1 C2 hcond (by simpa [hfs] using hov)
                    by_cases hS1 : (arg0 <ᵤ C1) = true <;> simp_all [InstCombine.LLVM.Ty.width, ofBool_one_iff, LLVM.SemVal.isRefinedBy_self])
                · exact HVector.nil_isRefinedBy_nil)
            · simp [i167055_src, i167055_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, arg0Var, hC1, hC2, hcond, harg0, ofBool_one_iff, hfs, hov, ofBool_one_iff, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.bothValues (by
                constructor
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    first
                    | exact LLVM.SemVal.poison_isRefinedBy _
                    | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                    | simp [LLVM.IntW.instRefinement])
                · exact HVector.nil_isRefinedBy_nil)
          ·
            cases hov : arg0.ssubOverflow C1
            ·
              simp [i167055_src, i167055_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, arg0Var, hC1, hC2, hcond, harg0, ofBool_one_iff, hfs, hov, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.bothValues (by
                constructor
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    have hv := i167055_value (w := w) arg0 C1 C2 hcond (by simpa [hfs] using hov)
                    by_cases hS1 : (arg0 <ᵤ C1) = true <;> simp_all [InstCombine.LLVM.Ty.width, ofBool_one_iff, LLVM.SemVal.isRefinedBy_self])
                · exact HVector.nil_isRefinedBy_nil)
            · simp [i167055_src, i167055_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, arg0Var, hC1, hC2, hcond, harg0, ofBool_one_iff, hfs, hov, ofBool_one_iff, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.bothValues (by
                constructor
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    first
                    | exact LLVM.SemVal.poison_isRefinedBy _
                    | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                    | simp [LLVM.IntW.instRefinement])
                · exact HVector.nil_isRefinedBy_nil)
