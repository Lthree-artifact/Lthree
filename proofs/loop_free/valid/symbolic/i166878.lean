import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def i166878_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i166878_src(%C1 : _, %arg0 : _, %arg1 : _) -> _ {
  ^bb0(%C1 : _, %arg0 : _, %arg1 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %cond = llvm.icmp "sge" %C1, %zero : _
    llvm.assume %cond : i1
    %v0 = llvm.sub %C1, %arg1 overflow<nsw> : _
    %c1 = llvm.icmp "sgt" %arg0, %v0 : _
    %v1 = llvm.select %c1, %arg0, %v0 : _
    %v2 = llvm.add %v1, %arg1 overflow<nsw,nuw> : _
    llvm.return %v2 : _
  }
  }]

def i166878_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i166878_tgt(%C1 : _, %arg0 : _, %arg1 : _) -> _ {
  ^bb0(%C1 : _, %arg0 : _, %arg1 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %cond = llvm.icmp "sge" %C1, %zero : _
    llvm.assume %cond : i1
    %v0 = llvm.add %arg0, %arg1 : _
    %c1 = llvm.icmp "sgt" %v0, %C1 : _
    %v1 = llvm.select %c1, %v0, %C1 : _
    llvm.return %v1 : _
  }
  }]

private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by
  cases b <;> simp

private theorem i166878_value {w : Nat} (C1 : BitVec w) (arg0 : BitVec w) (arg1 : BitVec w)
    (hpre : (0#w ≤ₛ C1) = true)
    (hov1 : C1.ssubOverflow arg1 = false)
    (hov2 : (if ((C1 - arg1) <ₛ arg0) = true then arg0 else (C1 - arg1)).saddOverflow arg1 = false)
    (hov3 : (if ((C1 - arg1) <ₛ arg0) = true then arg0 else (C1 - arg1)).uaddOverflow arg1 = false) :
    ((if ((C1 - arg1) <ₛ arg0) = true then arg0 else (C1 - arg1)) + arg1) = (if (C1 <ₛ (arg0 + arg1)) = true then (arg0 + arg1) else C1) := by
  by_cases hfs : ((C1 - arg1) <ₛ arg0) = true
  · have hsub : (C1 - arg1).toInt = C1.toInt - arg1.toInt :=
      BitVec.toInt_sub_of_not_ssubOverflow (x := C1) (y := arg1) (by simp [hov1])
    have hnoadd : ¬ arg0.saddOverflow arg1 = true := by
      have hfalse : arg0.saddOverflow arg1 = false := by simpa [hfs] using hov2
      simp [hfalse]
    have hadd : (arg0 + arg1).toInt = arg0.toInt + arg1.toInt :=
      BitVec.toInt_add_of_not_saddOverflow (x := arg0) (y := arg1) hnoadd
    have hlt : (C1 - arg1).toInt < arg0.toInt := by
      rw [BitVec.slt_eq_decide] at hfs
      exact of_decide_eq_true hfs
    have hcmp : (C1 <ₛ (arg0 + arg1)) = true := by
      rw [BitVec.slt_eq_decide]
      apply decide_eq_true
      rw [hadd]
      rw [hsub] at hlt
      omega
    simp [hfs, hcmp]
  · have hsub : (C1 - arg1).toInt = C1.toInt - arg1.toInt :=
      BitVec.toInt_sub_of_not_ssubOverflow (x := C1) (y := arg1) (by simp [hov1])
    have hseladd : ((C1 - arg1) + arg1).toInt = (C1 - arg1).toInt + arg1.toInt := by
      apply BitVec.toInt_add_of_not_saddOverflow (x := C1 - arg1) (y := arg1)
      have hfalse : (C1 - arg1).saddOverflow arg1 = false := by simpa [hfs] using hov2
      simp [hfalse]
    have hnatadd : ((C1 - arg1) + arg1).toNat = (C1 - arg1).toNat + arg1.toNat := by
      apply BitVec.toNat_add_of_not_uaddOverflow (x := C1 - arg1) (y := arg1)
      have hfalse : (C1 - arg1).uaddOverflow arg1 = false := by simpa [hfs] using hov3
      simp [hfalse]
    have hle : arg0.toInt ≤ (C1 - arg1).toInt := by
      have hnlt : ¬ (C1 - arg1).toInt < arg0.toInt := by
        intro hlt
        apply hfs
        rw [BitVec.slt_eq_decide]
        exact decide_eq_true hlt
      omega
    have hy_nonneg : 0 ≤ arg1.toInt := by
      have hC1int : 0 ≤ C1.toInt := by
        simpa [BitVec.sle_eq_decide] using hpre
      have hC1nat : C1.toInt.toNat = C1.toNat := BitVec.toNat_toInt_of_sle hpre
      rw [BitVec.sub_add_cancel] at hseladd hnatadd
      simp [BitVec.toInt_eq_toNat_cond] at *
      omega
    have hnoadd : ¬ arg0.saddOverflow arg1 = true := by
      have hC1le : C1.toInt ≤ 2 ^ (w - 1) - 1 := BitVec.toInt_le
      have hx_lb : -2 ^ (w - 1) ≤ arg0.toInt := BitVec.le_toInt arg0
      rw [BitVec.sub_add_cancel] at hseladd
      rw [hsub] at hle
      have hnupper : ¬ arg0.toInt + arg1.toInt ≥ 2 ^ (w - 1) := by omega
      have hnlower : ¬ arg0.toInt + arg1.toInt < -2 ^ (w - 1) := by omega
      simp [BitVec.saddOverflow, hnupper, hnlower]
    have hadd : (arg0 + arg1).toInt = arg0.toInt + arg1.toInt :=
      BitVec.toInt_add_of_not_saddOverflow (x := arg0) (y := arg1) hnoadd
    have hcmp : (C1 <ₛ (arg0 + arg1)) = false := by
      rw [BitVec.slt_eq_decide]
      apply decide_eq_false
      rw [hadd]
      rw [BitVec.sub_add_cancel] at hseladd
      rw [hsub] at hle
      omega
    simp [hfs, hcmp, BitVec.sub_add_cancel]

set_option maxHeartbeats 4000000 in
theorem i166878_correct (w : Nat) : i166878_src w ⊑ i166878_tgt w := by
  intro V
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let arg0Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let arg1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases hC1 : V C1Var
  case poison =>
    simp [i166878_src, i166878_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C1 =>
    change BitVec w at C1
    cases hcond : (0#w ≤ₛ C1)
    · simp [i166878_src, i166878_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    ·
      cases harg0 : V arg0Var
      case poison =>
        cases harg1 : V arg1Var
        case poison =>
          simp [i166878_src, i166878_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, arg0Var, arg1Var, hC1, hcond, harg0, harg1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.bothValues (by
            constructor
            · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                first
                | exact LLVM.SemVal.poison_isRefinedBy _
                | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                | simp [LLVM.IntW.instRefinement])
            · exact HVector.nil_isRefinedBy_nil)
        case value arg1 =>
          change BitVec w at arg1
          simp [i166878_src, i166878_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, arg0Var, arg1Var, hC1, hcond, harg0, harg1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
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
        cases harg1 : V arg1Var
        case poison =>
          simp [i166878_src, i166878_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, arg0Var, arg1Var, hC1, hcond, harg0, harg1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.bothValues (by
            constructor
            · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                first
                | exact LLVM.SemVal.poison_isRefinedBy _
                | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                | simp [LLVM.IntW.instRefinement])
            · exact HVector.nil_isRefinedBy_nil)
        case value arg1 =>
          change BitVec w at arg1
          cases hov1 : C1.ssubOverflow arg1
          ·
            by_cases hfs : ((C1 - arg1) <ₛ arg0) = true
            ·
              cases hov2 : arg0.saddOverflow arg1
              ·
                cases hov3 : arg0.uaddOverflow arg1
                ·
                  simp [i166878_src, i166878_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, arg0Var, arg1Var, hC1, hcond, harg0, harg1, ofBool_one_iff, hov1, hfs, hov2, hov3, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                  exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    constructor
                    · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                        have hv := i166878_value (w := w) C1 arg0 arg1 hcond hov1 (by simpa [hfs] using hov2) (by simpa [hfs] using hov3)
                        by_cases hS1 : ((C1 - arg1) <ₛ arg0) = true <;> by_cases hS2 : (C1 <ₛ (arg0 + arg1)) = true <;> simp_all [InstCombine.LLVM.Ty.width, ofBool_one_iff, LLVM.SemVal.isRefinedBy_self])
                    · exact HVector.nil_isRefinedBy_nil)
                · simp [i166878_src, i166878_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, arg0Var, arg1Var, hC1, hcond, harg0, harg1, ofBool_one_iff, hov1, hfs, hov2, hov3, ofBool_one_iff, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                  exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    constructor
                    · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                        first
                        | exact LLVM.SemVal.poison_isRefinedBy _
                        | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                        | simp [LLVM.IntW.instRefinement])
                    · exact HVector.nil_isRefinedBy_nil)
              · simp [i166878_src, i166878_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, arg0Var, arg1Var, hC1, hcond, harg0, harg1, ofBool_one_iff, hov1, hfs, hov2, ofBool_one_iff, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  constructor
                  · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                      first
                      | exact LLVM.SemVal.poison_isRefinedBy _
                      | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                      | simp [LLVM.IntW.instRefinement])
                  · exact HVector.nil_isRefinedBy_nil)
            ·
              cases hov2 : (C1 - arg1).saddOverflow arg1
              ·
                cases hov3 : (C1 - arg1).uaddOverflow arg1
                ·
                  simp [i166878_src, i166878_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, arg0Var, arg1Var, hC1, hcond, harg0, harg1, ofBool_one_iff, hov1, hfs, hov2, hov3, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                  exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    constructor
                    · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                        have hv := i166878_value (w := w) C1 arg0 arg1 hcond hov1 (by simpa [hfs] using hov2) (by simpa [hfs] using hov3)
                        by_cases hS1 : ((C1 - arg1) <ₛ arg0) = true <;> by_cases hS2 : (C1 <ₛ (arg0 + arg1)) = true <;> simp_all [InstCombine.LLVM.Ty.width, ofBool_one_iff, LLVM.SemVal.isRefinedBy_self])
                    · exact HVector.nil_isRefinedBy_nil)
                · simp [i166878_src, i166878_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, arg0Var, arg1Var, hC1, hcond, harg0, harg1, ofBool_one_iff, hov1, hfs, hov2, hov3, ofBool_one_iff, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                  exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    constructor
                    · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                        first
                        | exact LLVM.SemVal.poison_isRefinedBy _
                        | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                        | simp [LLVM.IntW.instRefinement])
                    · exact HVector.nil_isRefinedBy_nil)
              · simp [i166878_src, i166878_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, arg0Var, arg1Var, hC1, hcond, harg0, harg1, ofBool_one_iff, hov1, hfs, hov2, ofBool_one_iff, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  constructor
                  · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                      first
                      | exact LLVM.SemVal.poison_isRefinedBy _
                      | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                      | simp [LLVM.IntW.instRefinement])
                  · exact HVector.nil_isRefinedBy_nil)
          · simp [i166878_src, i166878_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, arg0Var, arg1Var, hC1, hcond, harg0, harg1, ofBool_one_iff, hov1, ofBool_one_iff, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  first
                  | exact LLVM.SemVal.poison_isRefinedBy _
                  | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                  | simp [LLVM.IntW.instRefinement])
              · exact HVector.nil_isRefinedBy_nil)
