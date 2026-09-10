import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

def vertex_ellipse117_src :=
  [llvm()| {
  llvm.func @vertex_ellipse117_src(%A : i32, %B : i32, %log_C : i32) -> i32 {
  ^bb0(%A : i32, %B : i32, %log_C : i32):
    %zero = llvm.mlir.constant(0 : i32) : i32
    %one = llvm.mlir.constant(1 : i32) : i32
    %bw_const = llvm.mlir.constant(32 : i32) : i32
    %bitwidth_A_B = llvm.add %bw_const, %zero : i32
    %bw_minus_1 = llvm.sub %bitwidth_A_B, %one : i32
    %pre = llvm.icmp "ult" %log_C, %bw_minus_1 : i32
    llvm.assume %pre : i1
    %C = llvm.shl %one, %log_C : i32
    %smin_cmp = llvm.icmp "slt" %B, %A : i32
    %smin = llvm.select %smin_cmp, %B, %A : i32
    %sub = llvm.sub %A, %smin overflow<nsw> : i32
    %sdiv = llvm.sdiv %sub, %C : i32
    %shl = llvm.shl %sdiv, %log_C overflow<nsw> : i32
    %res = llvm.add %shl, %smin : i32
    llvm.return %res : i32
  }
  }]

def vertex_ellipse117_tgt :=
  [llvm()| {
  llvm.func @vertex_ellipse117_tgt(%A : i32, %B : i32, %log_C : i32) -> i32 {
  ^bb0(%A : i32, %B : i32, %log_C : i32):
    %zero = llvm.mlir.constant(0 : i32) : i32
    %one = llvm.mlir.constant(1 : i32) : i32
    %bw_const = llvm.mlir.constant(32 : i32) : i32
    %bitwidth_A_B = llvm.add %bw_const, %zero : i32
    %bw_minus_1 = llvm.sub %bitwidth_A_B, %one : i32
    %pre = llvm.icmp "ult" %log_C, %bw_minus_1 : i32
    llvm.assume %pre : i1
    %C = llvm.shl %one, %log_C : i32
    %mask = llvm.sub %zero, %C : i32
    %smin_cmp = llvm.icmp "slt" %B, %A : i32
    %smin = llvm.select %smin_cmp, %B, %A : i32
    %sub = llvm.sub %A, %smin overflow<nsw> : i32
    %and = llvm.and %sub, %mask : i32
    %res = llvm.add %and, %smin : i32
    llvm.return %res : i32
  }
  }]

private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by
  cases b <;> simp

private theorem vertex_ellipse117_semval_bind_poison {α β : Type} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl

private theorem vertex_ellipse117_sdiv_eq_if {w : Nat} {x y : BitVec w} :
    LLVM.sdiv (LLVM.SemVal.value x) (LLVM.SemVal.value y) =
      (if (y = 0#w) ∨ (¬ w = 1 ∧ x = BitVec.intMin w ∧ y = BitVec.ofInt w (-1))
       then (.immediateUB : LLVM.IntWUB w)
       else (.value (x.sdiv y) : LLVM.IntWUB w)) := by
  have hneg : BitVec.ofInt w (-1) = -1 := by simp [BitVec.ofInt_neg, BitVec.ofInt_ofNat]
  simp [LLVM.sdiv, hneg]
  split_ifs <;> simp_all

private theorem vertex_ellipse117_sdiv_poisonL {w : Nat} (y : LLVM.IntW w) (f : LLVM.ExactFlag) :
    LLVM.sdiv (LLVM.SemVal.poison) y f = (.poison : LLVM.IntWUB w) := rfl

private theorem vertex_ellipse117_sdiv_poisonR {w : Nat} (x : LLVM.IntW w) (f : LLVM.ExactFlag) :
    LLVM.sdiv x (LLVM.SemVal.poison) f = (.poison : LLVM.IntWUB w) := by
  cases x <;> rfl

private theorem vertex_ellipse117_value (A : BitVec 32) (B : BitVec 32) (log_C : BitVec 32)
    (hpre : (log_C <ᵤ 31#32) = true)
    (hsh1 : ¬ (BitVec.ofNat 32 32 ≤ log_C))
    (hub1 : ¬ ((1#32 <<< log_C.toNat) = 0#32 ∨ ((A - (if (B <ₛ A) = true then B else A)) = BitVec.intMin 32 ∧ (1#32 <<< log_C.toNat) = 4294967295#32)))
    (hov : A.ssubOverflow (if (B <ₛ A) = true then B else A) = false)
    (hso1 : (((A - (if (B <ₛ A) = true then B else A)).sdiv (1#32 <<< log_C.toNat)) <<< log_C.toNat).sshiftRight log_C.toNat = ((A - (if (B <ₛ A) = true then B else A)).sdiv (1#32 <<< log_C.toNat))) :
    ((((A - (if (B <ₛ A) = true then B else A)).sdiv (1#32 <<< log_C.toNat)) <<< log_C.toNat) + (if (B <ₛ A) = true then B else A)) = (((A - (if (B <ₛ A) = true then B else A)) &&& -(1#32 <<< log_C.toNat)) + (if (B <ₛ A) = true then B else A)) := by
  have _ := hsh1
  have _ := hub1
  have _ := hso1
  have hn : log_C.toNat < 31 := by
    simpa [BitVec.ult_eq_decide, BitVec.toNat_ofNat] using hpre
  have hxmsb : (A - (if (B <ₛ A) = true then B else A)).msb = false := by
    by_cases hfs : (B <ₛ A) = true
    · have hlt : B.toInt < A.toInt := by
        simpa [BitVec.slt_eq_decide] using hfs
      have hovB : A.ssubOverflow B = false := by
        simpa [hfs] using hov
      have hno : ¬ A.ssubOverflow B = true := by
        rw [hovB]
        simp
      have hsub := BitVec.toInt_sub_of_not_ssubOverflow (x := A) (y := B) hno
      rw [BitVec.msb_eq_toInt]
      simp [hfs, hsub, show ¬ A.toInt - B.toInt < 0 by omega]
    · rw [BitVec.msb_eq_toInt]
      simp [hfs]
  have hymsb : (1#32 <<< log_C.toNat).msb = false := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
    simp [show ¬ 31 < log_C.toNat by omega, show 31 - log_C.toNat ≠ 0 by omega]
  have hq :
      (A - (if (B <ₛ A) = true then B else A)).sdiv (1#32 <<< log_C.toNat) =
        (A - (if (B <ₛ A) = true then B else A)) >>> log_C.toNat := by
    rw [BitVec.sdiv_eq, hxmsb, hymsb]
    apply BitVec.eq_of_toNat_eq
    have hyNat : (1#32 <<< log_C.toNat).toNat = 2 ^ log_C.toNat := by
      rw [BitVec.toNat_shiftLeft]
      simp [Nat.shiftLeft_eq]
      exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : log_C.toNat < 32)
    simp [BitVec.toNat_udiv, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hyNat]
  calc
    ((((A - (if (B <ₛ A) = true then B else A)).sdiv (1#32 <<< log_C.toNat)) <<< log_C.toNat) +
          (if (B <ₛ A) = true then B else A)) =
        (((A - (if (B <ₛ A) = true then B else A)) >>> log_C.toNat <<< log_C.toNat) +
          (if (B <ₛ A) = true then B else A)) := by
      rw [hq]
    _ = (((A - (if (B <ₛ A) = true then B else A)) &&& -(1#32 <<< log_C.toNat)) +
          (if (B <ₛ A) = true then B else A)) := by
      rw [BitVec.shiftLeft_ushiftRight]
      rw [← BitVec.neg_one_eq_allOnes]
      rw [BitVec.shiftLeft_neg]

set_option maxHeartbeats 4000000 in
theorem vertex_ellipse117_correct : vertex_ellipse117_src ⊑ vertex_ellipse117_tgt := by
  intro V
  let AVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨2, by simp⟩
  let BVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨1, by simp⟩
  let log_CVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]) (InstCombine.LLVM.Ty.bitvec 32)
  cases hlog_C : V log_CVar
  case poison =>
    simp [vertex_ellipse117_src, vertex_ellipse117_tgt, vertex_ellipse117_semval_bind_poison, vertex_ellipse117_sdiv_eq_if, vertex_ellipse117_sdiv_poisonL, vertex_ellipse117_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, log_CVar, hlog_C, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, InstCombine.lift2UB, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value log_C =>
    change BitVec 32 at log_C
    cases hcond : (log_C <ᵤ 31#32)
    · simp [vertex_ellipse117_src, vertex_ellipse117_tgt, vertex_ellipse117_semval_bind_poison, vertex_ellipse117_sdiv_eq_if, vertex_ellipse117_sdiv_poisonL, vertex_ellipse117_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, log_CVar, hlog_C, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, InstCombine.lift2UB, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    ·
      cases hA : V AVar
      case poison =>
        simp [vertex_ellipse117_src, vertex_ellipse117_tgt, vertex_ellipse117_semval_bind_poison, vertex_ellipse117_sdiv_eq_if, vertex_ellipse117_sdiv_poisonL, vertex_ellipse117_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, log_CVar, AVar, hlog_C, hcond, hA, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, InstCombine.lift2UB, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.bothValues (by
          constructor
          · exact ImmediateUBOr.IsRefinedBy.bothValues (by
              first
              | exact LLVM.SemVal.poison_isRefinedBy _
              | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
              | simp [LLVM.IntW.instRefinement])
          · exact HVector.nil_isRefinedBy_nil)
      case value A =>
        change BitVec 32 at A
        cases hB : V BVar
        case poison =>
          simp [vertex_ellipse117_src, vertex_ellipse117_tgt, vertex_ellipse117_semval_bind_poison, vertex_ellipse117_sdiv_eq_if, vertex_ellipse117_sdiv_poisonL, vertex_ellipse117_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, log_CVar, AVar, BVar, hlog_C, hcond, hA, hB, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, InstCombine.lift2UB, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.bothValues (by
            constructor
            · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                first
                | exact LLVM.SemVal.poison_isRefinedBy _
                | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                | simp [LLVM.IntW.instRefinement])
            · exact HVector.nil_isRefinedBy_nil)
        case value B =>
          change BitVec 32 at B
          by_cases hsh1 : BitVec.ofNat 32 32 ≤ log_C
          ·
            simp [vertex_ellipse117_src, vertex_ellipse117_tgt, vertex_ellipse117_semval_bind_poison, vertex_ellipse117_sdiv_eq_if, vertex_ellipse117_sdiv_poisonL, vertex_ellipse117_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, log_CVar, AVar, BVar, hlog_C, hcond, hA, hB, hsh1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, InstCombine.lift2UB, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  first
                  | exact LLVM.SemVal.poison_isRefinedBy _
                  | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                  | simp [LLVM.IntW.instRefinement])
              · exact HVector.nil_isRefinedBy_nil)
          ·
            by_cases hfs : (B <ₛ A) = true
            ·
              cases hov : A.ssubOverflow B
              ·
                by_cases hub1 : (1#32 <<< log_C.toNat) = 0#32 ∨ ((A - B) = BitVec.intMin 32 ∧ (1#32 <<< log_C.toNat) = 4294967295#32)
                ·
                  simp [vertex_ellipse117_src, vertex_ellipse117_tgt, vertex_ellipse117_semval_bind_poison, vertex_ellipse117_sdiv_eq_if, vertex_ellipse117_sdiv_poisonL, vertex_ellipse117_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, log_CVar, AVar, BVar, hlog_C, hcond, hA, hB, hsh1, ofBool_one_iff, hfs, hov, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, InstCombine.lift2UB, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.assume_]
                  simp [hub1]
                  exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    constructor
                    · exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                    · exact HVector.nil_isRefinedBy_nil)
                ·
                  by_cases hso1 : (((A - B).sdiv (1#32 <<< log_C.toNat)) <<< log_C.toNat).sshiftRight log_C.toNat = ((A - B).sdiv (1#32 <<< log_C.toNat))
                  ·
                    simp [vertex_ellipse117_src, vertex_ellipse117_tgt, vertex_ellipse117_semval_bind_poison, vertex_ellipse117_sdiv_eq_if, vertex_ellipse117_sdiv_poisonL, vertex_ellipse117_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, log_CVar, AVar, BVar, hlog_C, hcond, hA, hB, hsh1, ofBool_one_iff, hfs, hov, hub1, hso1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, InstCombine.lift2UB, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.assume_]
                    exact ImmediateUBOr.IsRefinedBy.bothValues (by
                      constructor
                      · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                          have hv := vertex_ellipse117_value A B log_C hcond hsh1 (by simpa [hfs] using hub1) (by simpa [hfs] using hov) (by simpa [hfs] using hso1)
                          by_cases hS1 : (B <ₛ A) = true <;> simp_all [InstCombine.LLVM.Ty.width, ofBool_one_iff, LLVM.SemVal.isRefinedBy_self])
                      · exact HVector.nil_isRefinedBy_nil)
                  ·
                    simp [vertex_ellipse117_src, vertex_ellipse117_tgt, vertex_ellipse117_semval_bind_poison, vertex_ellipse117_sdiv_eq_if, vertex_ellipse117_sdiv_poisonL, vertex_ellipse117_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, log_CVar, AVar, BVar, hlog_C, hcond, hA, hB, hsh1, ofBool_one_iff, hfs, hov, hub1, hso1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, InstCombine.lift2UB, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.assume_]
                    exact ImmediateUBOr.IsRefinedBy.bothValues (by
                      constructor
                      · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                          first
                          | exact LLVM.SemVal.poison_isRefinedBy _
                          | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                          | simp [LLVM.IntW.instRefinement])
                      · exact HVector.nil_isRefinedBy_nil)
              ·
                simp [vertex_ellipse117_src, vertex_ellipse117_tgt, vertex_ellipse117_semval_bind_poison, vertex_ellipse117_sdiv_eq_if, vertex_ellipse117_sdiv_poisonL, vertex_ellipse117_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, log_CVar, AVar, BVar, hlog_C, hcond, hA, hB, hsh1, ofBool_one_iff, hfs, hov, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, InstCombine.lift2UB, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.assume_]
                exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  constructor
                  · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                      first
                      | exact LLVM.SemVal.poison_isRefinedBy _
                      | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                      | simp [LLVM.IntW.instRefinement])
                  · exact HVector.nil_isRefinedBy_nil)
            ·
              cases hov : A.ssubOverflow A
              ·
                by_cases hub1 : (1#32 <<< log_C.toNat) = 0#32 ∨ (0#32 = BitVec.intMin 32 ∧ (1#32 <<< log_C.toNat) = 4294967295#32)
                ·
                  simp [vertex_ellipse117_src, vertex_ellipse117_tgt, vertex_ellipse117_semval_bind_poison, vertex_ellipse117_sdiv_eq_if, vertex_ellipse117_sdiv_poisonL, vertex_ellipse117_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, log_CVar, AVar, BVar, hlog_C, hcond, hA, hB, hsh1, ofBool_one_iff, hfs, hov, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, InstCombine.lift2UB, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.assume_]
                  simp [hub1]
                  exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    constructor
                    · exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                    · exact HVector.nil_isRefinedBy_nil)
                ·
                  by_cases hso1 : (((0#32).sdiv (1#32 <<< log_C.toNat)) <<< log_C.toNat).sshiftRight log_C.toNat = ((0#32).sdiv (1#32 <<< log_C.toNat))
                  ·
                    simp [vertex_ellipse117_src, vertex_ellipse117_tgt, vertex_ellipse117_semval_bind_poison, vertex_ellipse117_sdiv_eq_if, vertex_ellipse117_sdiv_poisonL, vertex_ellipse117_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, log_CVar, AVar, BVar, hlog_C, hcond, hA, hB, hsh1, ofBool_one_iff, hfs, hov, hub1, hso1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, InstCombine.lift2UB, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.assume_]
                    exact ImmediateUBOr.IsRefinedBy.bothValues (by
                      constructor
                      · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                          have hv := vertex_ellipse117_value A B log_C hcond hsh1 (by simpa [hfs] using hub1) (by simpa [hfs] using hov) (by simpa [hfs] using hso1)
                          by_cases hS1 : (B <ₛ A) = true <;> simp_all [InstCombine.LLVM.Ty.width, ofBool_one_iff, LLVM.SemVal.isRefinedBy_self])
                      · exact HVector.nil_isRefinedBy_nil)
                  ·
                    simp [vertex_ellipse117_src, vertex_ellipse117_tgt, vertex_ellipse117_semval_bind_poison, vertex_ellipse117_sdiv_eq_if, vertex_ellipse117_sdiv_poisonL, vertex_ellipse117_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, log_CVar, AVar, BVar, hlog_C, hcond, hA, hB, hsh1, ofBool_one_iff, hfs, hov, hub1, hso1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, InstCombine.lift2UB, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.assume_]
                    exact ImmediateUBOr.IsRefinedBy.bothValues (by
                      constructor
                      · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                          first
                          | exact LLVM.SemVal.poison_isRefinedBy _
                          | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                          | simp [LLVM.IntW.instRefinement])
                      · exact HVector.nil_isRefinedBy_nil)
              ·
                simp [vertex_ellipse117_src, vertex_ellipse117_tgt, vertex_ellipse117_semval_bind_poison, vertex_ellipse117_sdiv_eq_if, vertex_ellipse117_sdiv_poisonL, vertex_ellipse117_sdiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, log_CVar, AVar, BVar, hlog_C, hcond, hA, hB, hsh1, ofBool_one_iff, hfs, hov, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, InstCombine.lift2UB, LLVM.select, InstCombine.lift3, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.assume_]
                exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  constructor
                  · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                      first
                      | exact LLVM.SemVal.poison_isRefinedBy _
                      | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                      | simp [LLVM.IntW.instRefinement])
                  · exact HVector.nil_isRefinedBy_nil)
