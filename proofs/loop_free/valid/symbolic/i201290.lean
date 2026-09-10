import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def i201290_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i201290_src(%c1 : _, %c2 : _, %a : _, %m : _) -> i1 {
  ^bb0(%c1 : _, %c2 : _, %a : _, %m : _):
    %cond = llvm.icmp "ult" %c1, %c2 : _
    llvm.assume %cond : i1
    %a_lte_m = llvm.icmp "ule" %a, %m : _
    llvm.assume %a_lte_m : i1
    %lhs = llvm.add %a, %c1 : _
    %rhs = llvm.add %m, %c2 overflow<nuw> : _
    %cmp = llvm.icmp "ult" %lhs, %rhs : _
    llvm.return %cmp : i1
  }
  }]

def i201290_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i201290_tgt(%c1 : _, %c2 : _, %a : _, %m : _) -> i1 {
  ^bb0(%c1 : _, %c2 : _, %a : _, %m : _):
    %cond = llvm.icmp "ult" %c1, %c2 : _
    llvm.assume %cond : i1
    %a_lte_m = llvm.icmp "ule" %a, %m : _
    llvm.assume %a_lte_m : i1
    %true = llvm.mlir.constant(true) : i1
    llvm.return %true : i1
  }
  }]

private theorem i201290_value {w : Nat} (c1 : BitVec w) (c2 : BitVec w) (a : BitVec w) (m : BitVec w)
    (hpre1 : (c1 <ᵤ c2) = true)
    (hpre2 : (a ≤ᵤ m) = true)
    (hov : m.uaddOverflow c2 = false) :
    (BitVec.ofBool ((a + c1) <ᵤ (m + c2))) = 1#1 := by
  have hc1_lt : c1.toNat < c2.toNat := by
    exact of_decide_eq_true (by simpa [BitVec.ult] using hpre1)
  have ha_le : a.toNat ≤ m.toNat := by
    exact of_decide_eq_true (by simpa [BitVec.ule] using hpre2)
  have hright_lt : m.toNat + c2.toNat < 2 ^ w := by
    have hnot : ¬ m.toNat + c2.toNat ≥ 2 ^ w := by
      exact of_decide_eq_false (by simpa [BitVec.uaddOverflow] using hov)
    exact Nat.lt_of_not_ge hnot
  have hsum_lt : a.toNat + c1.toNat < m.toNat + c2.toNat := by
    exact Nat.add_lt_add_of_le_of_lt ha_le hc1_lt
  have hleft_lt : a.toNat + c1.toNat < 2 ^ w := Nat.lt_trans hsum_lt hright_lt
  have hcmp : ((a + c1) <ᵤ (m + c2)) = true := by
    rw [BitVec.ult]
    apply decide_eq_true
    rw [BitVec.toNat_add, BitVec.toNat_add]
    rw [Nat.mod_eq_of_lt hleft_lt, Nat.mod_eq_of_lt hright_lt]
    exact hsum_lt
  simp [BitVec.ofBool, hcmp]

set_option maxHeartbeats 4000000 in
theorem i201290_correct (w : Nat) : i201290_src w ⊑ i201290_tgt w := by
  intro V
  let c1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨3, by simp⟩
  let c2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let aVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let mVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases hc1 : V c1Var
  case poison =>
    simp [i201290_src, i201290_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, c1Var, hc1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value c1 =>
    change BitVec w at c1
    cases hc2 : V c2Var
    case poison =>
      simp [i201290_src, i201290_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, c1Var, c2Var, hc1, hc2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value c2 =>
      change BitVec w at c2
      cases hcond1 : (c1 <ᵤ c2)
      · simp [i201290_src, i201290_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, c1Var, c2Var, hc1, hc2, hcond1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      ·
        cases ha : V aVar
        case poison =>
          simp [i201290_src, i201290_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, c1Var, c2Var, aVar, hc1, hc2, hcond1, ha, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        case value a =>
          change BitVec w at a
          cases hm : V mVar
          case poison =>
            simp [i201290_src, i201290_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, c1Var, c2Var, aVar, mVar, hc1, hc2, hcond1, ha, hm, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
          case value m =>
            change BitVec w at m
            cases hcond2 : (a ≤ᵤ m)
            · simp [i201290_src, i201290_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, c1Var, c2Var, aVar, mVar, hc1, hc2, hcond1, ha, hm, hcond2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
            ·
              cases hov : m.uaddOverflow c2
              · simp [i201290_src, i201290_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, c1Var, c2Var, aVar, mVar, hc1, hc2, hcond1, ha, hm, hcond2, hov, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.assume_]
                have hv := i201290_value (w := w) c1 c2 a m hcond1 hcond2 hov
                exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  constructor
                  · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv] <;> rfl)
                  · exact HVector.nil_isRefinedBy_nil)
              · simp [i201290_src, i201290_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, c1Var, c2Var, aVar, mVar, hc1, hc2, hcond1, ha, hm, hcond2, hov, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.assume_]
                exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  constructor
                  · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                      first
                      | exact LLVM.SemVal.poison_isRefinedBy _
                      | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                      | simp [LLVM.IntW.instRefinement])
                  · exact HVector.nil_isRefinedBy_nil)
