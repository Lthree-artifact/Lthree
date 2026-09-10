import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def i199806_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i199806_src(%x : _, %c : _, %max : _) -> _ {
  ^bb0(%x : _, %c : _, %max : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c_ge_0 = llvm.icmp "sge" %c, %zero : _
    llvm.assume %c_ge_0 : i1
    %max_ge_0 = llvm.icmp "sge" %max, %zero : _
    llvm.assume %max_ge_0 : i1
    %ugt = llvm.icmp "ugt" %x, %c : _
    %u = llvm.select %ugt, %x, %c : _
    %sum = llvm.add %u, %x overflow<nsw> : _
    %ov = llvm.icmp "ult" %sum, %x : _
    %ult = llvm.icmp "ult" %sum, %max : _
    %clamp = llvm.select %ult, %sum, %max : _
    %r = llvm.select %ov, %max, %clamp : _
    llvm.return %r : _
  }
  }]

def i199806_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i199806_tgt(%x : _, %c : _, %max : _) -> _ {
  ^bb0(%x : _, %c : _, %max : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c_ge_0 = llvm.icmp "sge" %c, %zero : _
    llvm.assume %c_ge_0 : i1
    %max_ge_0 = llvm.icmp "sge" %max, %zero : _
    llvm.assume %max_ge_0 : i1
    %ugt = llvm.icmp "ugt" %x, %c : _
    %u = llvm.select %ugt, %x, %c : _
    %sum = llvm.add %u, %x : _
    %ult = llvm.icmp "ult" %sum, %max : _
    %clamp = llvm.select %ult, %sum, %max : _
    llvm.return %clamp : _
  }
  }]

private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by
  cases b <;> simp

private theorem i199806_value {w : Nat} (x : BitVec w) (c : BitVec w) (max : BitVec w)
    (hpre1 : (0#w ≤ₛ c) = true)
    (hpre2 : (0#w ≤ₛ max) = true)
    (hov : (if (c <ᵤ x) = true then x else c).saddOverflow x = false) :
    (if (((if (c <ᵤ x) = true then x else c) + x) <ᵤ x) = true then max else (if (((if (c <ᵤ x) = true then x else c) + x) <ᵤ max) = true then ((if (c <ᵤ x) = true then x else c) + x) else max)) = (if (((if (c <ᵤ x) = true then x else c) + x) <ᵤ max) = true then ((if (c <ᵤ x) = true then x else c) + x) else max) := by
  by_cases hwrap : (((if (c <ᵤ x) = true then x else c) + x) <ᵤ x) = true
  · by_cases hlt : (((if (c <ᵤ x) = true then x else c) + x) <ᵤ max) = true
    · exfalso
      have hmax_msb : max.msb = false := by
        have hmax_int : 0 ≤ max.toInt := by
          simpa using (BitVec.sle_iff_toInt_le.mp hpre2)
        rw [BitVec.msb_eq_toInt]
        exact decide_eq_false_iff_not.mpr (not_lt.mpr hmax_int)
      have hmax_half : 2 * max.toNat < 2 ^ w :=
        BitVec.msb_eq_false_iff_two_mul_lt.mp hmax_msb
      have hltNat := BitVec.ult_iff_toNat_lt.mp hlt
      have hwrapNat := BitVec.ult_iff_toNat_lt.mp hwrap
      by_cases hcx : (c <ᵤ x) = true
      · by_cases hx_msb_true : x.msb = true
        · have hs_sign : (x + x).msb = x.msb := by
            rw [BitVec.saddOverflow_eq] at hov
            simp [hcx] at hov
            exact hov
          have hs_msb : (((if (c <ᵤ x) = true then x else c) + x).msb) = true := by
            simpa [hcx, hx_msb_true] using hs_sign
          have hs_half : 2 * (((if (c <ᵤ x) = true then x else c) + x).toNat) ≥ 2 ^ w :=
            BitVec.msb_eq_true_iff_two_mul_ge.mp hs_msb
          omega
        · have hx_msb_false : x.msb = false := Bool.eq_false_of_not_eq_true hx_msb_true
          have hx_half : 2 * x.toNat < 2 ^ w :=
            BitVec.msb_eq_false_iff_two_mul_lt.mp hx_msb_false
          have hsumNat : (x + x).toNat = x.toNat + x.toNat :=
            BitVec.toNat_add_of_lt (by omega)
          simp [hcx, hsumNat] at hwrapNat
          omega
      · have hc_msb : c.msb = false := by
          have hc_int : 0 ≤ c.toInt := by
            simpa using (BitVec.sle_iff_toInt_le.mp hpre1)
          rw [BitVec.msb_eq_toInt]
          exact decide_eq_false_iff_not.mpr (not_lt.mpr hc_int)
        have hc_half : 2 * c.toNat < 2 ^ w :=
          BitVec.msb_eq_false_iff_two_mul_lt.mp hc_msb
        have hnotNat : ¬ c.toNat < x.toNat := by
          intro h
          exact hcx (BitVec.ult_iff_toNat_lt.mpr h)
        have hx_le_c : x.toNat ≤ c.toNat := Nat.le_of_not_gt hnotNat
        have hsumNat : (c + x).toNat = c.toNat + x.toNat :=
          BitVec.toNat_add_of_lt (by omega)
        simp [hcx, hsumNat] at hwrapNat
        omega
    · simp [hwrap, hlt]
  · simp [hwrap]

set_option maxHeartbeats 4000000 in
theorem i199806_correct (w : Nat) : i199806_src w ⊑ i199806_tgt w := by
  intro V
  let xVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let cVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let maxVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases hc : V cVar
  case poison =>
    simp [i199806_src, i199806_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, cVar, hc, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value c =>
    change BitVec w at c
    cases hcond1 : (0#w ≤ₛ c)
    · simp [i199806_src, i199806_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, cVar, hc, hcond1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    ·
      cases hmax : V maxVar
      case poison =>
        simp [i199806_src, i199806_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, cVar, maxVar, hc, hcond1, hmax, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      case value max =>
        change BitVec w at max
        cases hcond2 : (0#w ≤ₛ max)
        · simp [i199806_src, i199806_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, cVar, maxVar, hc, hcond1, hmax, hcond2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        ·
          cases hx : V xVar
          case poison =>
            simp [i199806_src, i199806_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, cVar, maxVar, xVar, hc, hcond1, hmax, hcond2, hx, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.assume_]
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
            by_cases hfs : (c <ᵤ x) = true
            · cases hov : x.saddOverflow x
              · simp [i199806_src, i199806_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, cVar, maxVar, xVar, hc, hcond1, hmax, hcond2, hx, hfs, hov, ofBool_one_iff, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.assume_]
                exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  constructor
                  · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                      have hv := i199806_value (w := w) x c max hcond1 hcond2 (by simpa [hfs] using hov)
                      by_cases hS1 : (((if (c <ᵤ x) = true then x else c) + x) <ᵤ x) = true <;> by_cases hS2 : (c <ᵤ x) = true <;> by_cases hS3 : (((if (c <ᵤ x) = true then x else c) + x) <ᵤ max) = true <;> simp_all [InstCombine.LLVM.Ty.width, ofBool_one_iff, LLVM.SemVal.isRefinedBy_self])
                  · exact HVector.nil_isRefinedBy_nil)
              · simp [i199806_src, i199806_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, cVar, maxVar, xVar, hc, hcond1, hmax, hcond2, hx, hfs, hov, ofBool_one_iff, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.assume_]
                exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  constructor
                  · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                      first
                      | exact LLVM.SemVal.poison_isRefinedBy _
                      | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                      | simp [LLVM.IntW.instRefinement])
                  · exact HVector.nil_isRefinedBy_nil)
            · cases hov : c.saddOverflow x
              · simp [i199806_src, i199806_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, cVar, maxVar, xVar, hc, hcond1, hmax, hcond2, hx, hfs, hov, ofBool_one_iff, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.assume_]
                exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  constructor
                  · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                      have hv := i199806_value (w := w) x c max hcond1 hcond2 (by simpa [hfs] using hov)
                      by_cases hS1 : (((if (c <ᵤ x) = true then x else c) + x) <ᵤ x) = true <;> by_cases hS2 : (c <ᵤ x) = true <;> by_cases hS3 : (((if (c <ᵤ x) = true then x else c) + x) <ᵤ max) = true <;> simp_all [InstCombine.LLVM.Ty.width, ofBool_one_iff, LLVM.SemVal.isRefinedBy_self])
                  · exact HVector.nil_isRefinedBy_nil)
              · simp [i199806_src, i199806_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, cVar, maxVar, xVar, hc, hcond1, hmax, hcond2, hx, hfs, hov, ofBool_one_iff, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.assume_]
                exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  constructor
                  · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                      first
                      | exact LLVM.SemVal.poison_isRefinedBy _
                      | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                      | simp [LLVM.IntW.instRefinement])
                  · exact HVector.nil_isRefinedBy_nil)
