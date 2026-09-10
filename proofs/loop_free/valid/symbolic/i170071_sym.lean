import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def i170071_sym_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i170071_sym_src(%C2 : _, %V : _, %v0 : _) -> _ {
  ^bb0(%C2 : _, %V : _, %v0 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c2 = llvm.icmp "sge" %C2, %zero : _
    llvm.assume %c2 : i1
    %xor = llvm.xor %V, %v0 : _
    %same_sign = llvm.icmp "sge" %xor, %zero : _
    llvm.assume %same_sign : i1
    %v2 = llvm.add %V, %v0 overflow<nsw> : _
    %v3 = llvm.icmp "ult" %v2, %v0 : _
    %umin_c = llvm.icmp "ult" %v2, %C2 : _
    %v4 = llvm.select %umin_c, %v2, %C2 : _
    %v5 = llvm.select %v3, %C2, %v4 : _
    llvm.return %v5 : _
  }
  }]

def i170071_sym_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i170071_sym_tgt(%C2 : _, %V : _, %v0 : _) -> _ {
  ^bb0(%C2 : _, %V : _, %v0 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c2 = llvm.icmp "sge" %C2, %zero : _
    llvm.assume %c2 : i1
    %xor = llvm.xor %V, %v0 : _
    %same_sign = llvm.icmp "sge" %xor, %zero : _
    llvm.assume %same_sign : i1
    %v2 = llvm.add %V, %v0 : _
    %umin_c = llvm.icmp "ult" %v2, %C2 : _
    %v4 = llvm.select %umin_c, %v2, %C2 : _
    llvm.return %v4 : _
  }
  }]

private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by
  cases b <;> simp

private theorem i170071_sym_value {w : Nat} (C2 : BitVec w) (Vv : BitVec w) (v0 : BitVec w)
    (hpre1 : (0#w ≤ₛ C2) = true)
    (hpre2 : (0#w ≤ₛ (Vv ^^^ v0)) = true)
    (hov : Vv.saddOverflow v0 = false) :
    (if ((Vv + v0) <ᵤ v0) = true then C2 else (if ((Vv + v0) <ᵤ C2) = true then (Vv + v0) else C2)) = (if ((Vv + v0) <ᵤ C2) = true then (Vv + v0) else C2) := by
  have nonneg_msb_false :
      ∀ (x : BitVec w), (0#w ≤ₛ x) = true → x.msb = false := by
    intro x h
    rw [BitVec.msb_eq_decide]
    rw [decide_eq_false_iff_not]
    intro hx
    have hi : (0#w).toInt ≤ x.toInt := (BitVec.sle_iff_toInt_le).mp h
    have hi0 : 0 ≤ x.toInt := by
      simpa [BitVec.toInt_eq_toNat_cond, Nat.two_pow_pos] using hi
    have hx2 : 2 ^ w ≤ 2 * x.toNat := by
      cases w with
      | zero =>
          have hlt := BitVec.isLt x
          simp at hx hlt ⊢
          omega
      | succ n =>
          simp [Nat.pow_succ] at hx ⊢
          omega
    have hneg : x.toInt < 0 := (BitVec.toInt_neg_iff).mpr hx2
    omega
  have msb_false_lt :
      ∀ (x : BitVec w), x.msb = false → x.toNat < 2 ^ (w - 1) := by
    intro x h
    rw [BitVec.msb_eq_decide] at h
    have hn : ¬2 ^ (w - 1) ≤ x.toNat := of_decide_eq_false h
    omega
  have msb_true_ge :
      ∀ (x : BitVec w), x.msb = true → 2 ^ (w - 1) ≤ x.toNat := by
    intro x h
    rw [BitVec.msb_eq_decide] at h
    exact of_decide_eq_true h
  have hC2msb : C2.msb = false := nonneg_msb_false C2 hpre1
  have hxormsb : (Vv ^^^ v0).msb = false := nonneg_msb_false (Vv ^^^ v0) hpre2
  have hsame : Vv.msb = v0.msb := by
    simpa [BitVec.msb_xor] using hxormsb
  have hresSign : (Vv + v0).msb = Vv.msb := by
    have hresSignV0 : (Vv + v0).msb = v0.msb := by
      simpa [BitVec.saddOverflow_eq, hsame] using hov
    exact hresSignV0.trans hsame.symm
  by_cases hwrap : ((Vv + v0) <ᵤ v0) = true
  · have hwrapNat : (Vv + v0).toNat < v0.toNat := by
      simpa [BitVec.ult_eq_decide] using hwrap
    have hv0msb : v0.msb = true := by
      cases hv0 : v0.msb
      · have hVmsb : Vv.msb = false := hsame.trans hv0
        have hVlt : Vv.toNat < 2 ^ (w - 1) := msb_false_lt Vv hVmsb
        have hv0lt : v0.toNat < 2 ^ (w - 1) := msb_false_lt v0 hv0
        have hsumlt : Vv.toNat + v0.toNat < 2 ^ w := by
          cases w with
          | zero =>
              simp at hVlt hv0lt ⊢
              omega
          | succ n =>
              simp [Nat.pow_succ] at hVlt hv0lt ⊢
              omega
        have hsumNat : (Vv + v0).toNat = Vv.toNat + v0.toNat :=
          BitVec.toNat_add_of_lt hsumlt
        omega
      · rfl
    have hVmsb_true : Vv.msb = true := hsame.trans hv0msb
    have hsum_msb : (Vv + v0).msb = true := hresSign.trans hVmsb_true
    have hC2lt : C2.toNat < 2 ^ (w - 1) := msb_false_lt C2 hC2msb
    have hsumge : 2 ^ (w - 1) ≤ (Vv + v0).toNat := msb_true_ge (Vv + v0) hsum_msb
    have hnot : ¬(Vv + v0).toNat < C2.toNat := by omega
    have hcmp : ((Vv + v0) <ᵤ C2) = false := by
      rw [BitVec.ult_eq_decide]
      exact decide_eq_false hnot
    simp [hwrap, hcmp]
  · simp [hwrap]

set_option maxHeartbeats 4000000 in
theorem i170071_sym_correct (w : Nat) : i170071_sym_src w ⊑ i170071_sym_tgt w := by
  intro V
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let VVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let v0Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases hC2 : V C2Var
  case poison =>
    simp [i170071_sym_src, i170071_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.xor, LLVM.xor?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C2 =>
    change BitVec w at C2
    cases hcond1 : (0#w ≤ₛ C2)
    · simp [i170071_sym_src, i170071_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, hC2, hcond1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.xor, LLVM.xor?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    ·
      cases hV : V VVar
      case poison =>
        simp [i170071_sym_src, i170071_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, VVar, hC2, hcond1, hV, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.xor, LLVM.xor?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      case value Vv =>
        change BitVec w at Vv
        cases hv0 : V v0Var
        case poison =>
          simp [i170071_sym_src, i170071_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, VVar, v0Var, hC2, hcond1, hV, hv0, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.xor, LLVM.xor?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        case value v0 =>
          change BitVec w at v0
          cases hcond2 : (0#w ≤ₛ (Vv ^^^ v0))
          · simp [i170071_sym_src, i170071_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, VVar, v0Var, hC2, hcond1, hV, hv0, hcond2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.xor, LLVM.xor?, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
          ·
            cases hov : Vv.saddOverflow v0
            · simp [i170071_sym_src, i170071_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, VVar, v0Var, hC2, hcond1, hV, hv0, hcond2, hov, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.xor, LLVM.xor?, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.bothValues (by
                constructor
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    have hv := i170071_sym_value (w := w) C2 Vv v0 hcond1 hcond2 hov
                    by_cases hS1 : ((Vv + v0) <ᵤ v0) = true <;> by_cases hS2 : ((Vv + v0) <ᵤ C2) = true <;> simp_all [InstCombine.LLVM.Ty.width, ofBool_one_iff, LLVM.SemVal.isRefinedBy_self])
                · exact HVector.nil_isRefinedBy_nil)
            · simp [i170071_sym_src, i170071_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, VVar, v0Var, hC2, hcond1, hV, hv0, hcond2, hov, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.xor, LLVM.xor?, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.bothValues (by
                constructor
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    first
                    | exact LLVM.SemVal.poison_isRefinedBy _
                    | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                    | simp [LLVM.IntW.instRefinement])
                · exact HVector.nil_isRefinedBy_nil)
