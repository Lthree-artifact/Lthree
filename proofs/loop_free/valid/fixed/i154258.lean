import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i154258_src :=
  [llvm()| {
  llvm.func @i154258_src(%v3 : i32, %v4 : i32) -> i1 {
  ^bb0(%v3 : i32, %v4 : i32):
    %v5 = llvm.shl %v3, %v4 : i32
    %v6 = llvm.sext %v5 : i32 to i64
    %c_32_32768 = llvm.mlir.constant(32768 : i32) : i32
    %v7 = llvm.add %v5, %c_32_32768 : i32
    %c_64_2147516416 = llvm.mlir.constant(2147516416 : i64) : i64
    %v8 = llvm.add %v6, %c_64_2147516416 overflow<nsw> : i64
    %c_64_4294967296 = llvm.mlir.constant(4294967296 : i64) : i64
    %c_64_0 = llvm.mlir.constant(0 : i64) : i64
    %v9_lhs_neg = llvm.icmp "slt" %v8, %c_64_0 : i64
    %v9_rhs_neg = llvm.icmp "slt" %c_64_4294967296, %c_64_0 : i64
    %v9_same_sign = llvm.icmp "eq" %v9_lhs_neg, %v9_rhs_neg : i1
    llvm.assume %v9_same_sign : i1
    %v9 = llvm.icmp "ult" %v8, %c_64_4294967296 : i64
    %c_32_65536 = llvm.mlir.constant(65536 : i32) : i32
    %v131 = llvm.icmp "ult" %v7, %c_32_65536 : i32
    %c_1_false = llvm.mlir.constant(false) : i1
    %v13 = llvm.select %v9, %v131, %c_1_false : i1
    llvm.return %v13 : i1
  }
  }]

def i154258_tgt :=
  [llvm()| {
  llvm.func @i154258_tgt(%v3 : i32, %v4 : i32) -> i1 {
  ^bb0(%v3 : i32, %v4 : i32):
    %v5 = llvm.shl %v3, %v4 : i32
    %c_32_32768 = llvm.mlir.constant(32768 : i32) : i32
    %v6 = llvm.add %v5, %c_32_32768 : i32
    %c_32_65536 = llvm.mlir.constant(65536 : i32) : i32
    %v7 = llvm.icmp "ult" %v6, %c_32_65536 : i32
    llvm.return %v7 : i1
  }
  }]

private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by
  cases b <;> simp

private theorem i154258_ofBool_zero_iff {b : Bool} : (BitVec.ofBool b = 0#1) ↔ (b = false) := by
  cases b <;> simp

private theorem i154258_one_eq_ofBool_iff {b : Bool} : (1#1 = BitVec.ofBool b) ↔ (b = true) := by
  cases b <;> simp

private theorem i154258_zero_eq_ofBool_iff {b : Bool} : (0#1 = BitVec.ofBool b) ↔ (b = false) := by
  cases b <;> simp

private theorem i154258_shift_sum_ge (t : BitVec 32)
    (hge : ¬ (((BitVec.signExtend 64 t) + 2147516416#64) <ᵤ 4294967296#64) = true) :
    ¬ ((t + 32768#32).toNat < (65536#32).toNat) := by
  rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
    BitVec.msb_eq_decide] at hge
  have hn : t.toNat < 4294967296 := t.isLt
  split at hge <;> rename_i h <;> rw [decide_eq_true_eq] at h <;> bv_omega

private theorem i154258_value (v3 : BitVec 32) (v4 : BitVec 32)
    (hsh1 : ¬ (BitVec.ofNat 32 32 ≤ v4))
    (hov1 : (BitVec.signExtend 64 (v3 <<< v4.toNat)).saddOverflow 2147516416#64 = false)
    (hc1 : (BitVec.ofBool (((BitVec.signExtend 64 (v3 <<< v4.toNat)) + 2147516416#64) <ₛ 0#64) == 0#1) = true) :
    (if (((BitVec.signExtend 64 (v3 <<< v4.toNat)) + 2147516416#64) <ᵤ 4294967296#64) = true then (BitVec.ofBool (((v3 <<< v4.toNat) + 32768#32) <ᵤ 65536#32)) else 0#1) = (BitVec.ofBool (((v3 <<< v4.toNat) + 32768#32) <ᵤ 65536#32)) := by
  generalize v3 <<< v4.toNat = t at *
  split
  · rfl
  · rename_i hge
    have hnot := i154258_shift_sum_ge t hge
    simp only [BitVec.ult, hnot, decide_false, BitVec.ofBool_false]
    rfl

set_option maxHeartbeats 8000000 in
theorem i154258_correct : i154258_src ⊑ i154258_tgt := by
  intro V
  let v3Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨1, by simp⟩
  let v4Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32]) (InstCombine.LLVM.Ty.bitvec 32)
  cases hv3 : V v3Var <;> cases hv4 : V v4Var
  all_goals (
    try (
      simp [i154258_src, i154258_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, v3Var, v4Var, hv3, hv4, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sext, LLVM.sext?, LLVM.shl, LLVM.shl?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft))
  rename_i v3 v4
  change BitVec 32 at v3
  change BitVec 32 at v4
  by_cases hsh1 : BitVec.ofNat 32 32 ≤ v4
  ·
    simp [i154258_src, i154258_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, v3Var, v4Var, hv3, hv4, hsh1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sext, LLVM.sext?, LLVM.shl, LLVM.shl?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  ·
    cases hov1 : (BitVec.signExtend 64 (v3 <<< v4.toNat)).saddOverflow 2147516416#64
    ·
      cases hc1 : (BitVec.ofBool (((BitVec.signExtend 64 (v3 <<< v4.toNat)) + 2147516416#64) <ₛ 0#64) == 0#1)
      ·
        simp [i154258_src, i154258_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, v3Var, v4Var, hv3, hv4, hsh1, hov1, hc1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sext, LLVM.sext?, LLVM.shl, LLVM.shl?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      ·
        simp [i154258_src, i154258_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, v3Var, v4Var, hv3, hv4, hsh1, hov1, hc1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sext, LLVM.sext?, LLVM.shl, LLVM.shl?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.bothValues (by
          constructor
          · exact ImmediateUBOr.IsRefinedBy.bothValues (by
              have hval := i154258_value v3 v4 hsh1 hov1 hc1
              by_cases hS1 : (((BitVec.signExtend 64 (v3 <<< v4.toNat)) + 2147516416#64) <ᵤ 4294967296#64) = true <;> simp_all [InstCombine.LLVM.Ty.width, v3Var, v4Var, ofBool_one_iff, i154258_ofBool_zero_iff, i154258_one_eq_ofBool_iff, i154258_zero_eq_ofBool_iff])
          · exact HVector.nil_isRefinedBy_nil)
    ·
      simp [i154258_src, i154258_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, v3Var, v4Var, hv3, hv4, hsh1, hov1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sext, LLVM.sext?, LLVM.shl, LLVM.shl?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
