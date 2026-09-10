import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def i157315_a2t_src :=
  [llvm()| {
  llvm.func @i157315_a2t_src(%arg0 : i32, %arg1 : i32, %C0 : i32, %C1 : i32,
      %C2 : i32, %C_add : i32, %C_ub : i32) -> i1 {
  ^bb0(%arg0 : i32, %arg1 : i32, %C0 : i32, %C1 : i32, %C2 : i32,
      %C_add : i32, %C_ub : i32):
    %one = llvm.mlir.constant(1 : i32) : i32
    %minus_one = llvm.mlir.constant(4294967295 : i32) : i32
    %pre1 = llvm.icmp "sle" %C1, %C2 : i32
    llvm.assume %pre1 : i1
    %diff = llvm.sub %C0, %C1 : i32
    %pre2 = llvm.icmp "eq" %C_add, %diff : i32
    llvm.assume %pre2 : i1
    %dist = llvm.sub %C2, %C1 : i32
    %pre3 = llvm.icmp "ne" %dist, %minus_one : i32
    llvm.assume %pre3 : i1
    %dist_plus_one = llvm.add %dist, %one : i32
    %pre4 = llvm.icmp "eq" %C_ub, %dist_plus_one : i32
    llvm.assume %pre4 : i1
    %v0 = llvm.add %arg1, %C0 : i32
    %v1 = llvm.add %v0, %arg0 : i32
    %v2_cmp = llvm.icmp "sgt" %v1, %C1 : i32
    %v2 = llvm.select %v2_cmp, %v1, %C1 : i32
    %v3_cmp = llvm.icmp "slt" %v2, %C2 : i32
    %v3 = llvm.select %v3_cmp, %v2, %C2 : i32
    %v4 = llvm.icmp "eq" %v1, %v3 : i32
    llvm.return %v4 : i1
  }
  }]

def i157315_a2t_tgt :=
  [llvm()| {
  llvm.func @i157315_a2t_tgt(%arg0 : i32, %arg1 : i32, %C0 : i32, %C1 : i32,
      %C2 : i32, %C_add : i32, %C_ub : i32) -> i1 {
  ^bb0(%arg0 : i32, %arg1 : i32, %C0 : i32, %C1 : i32, %C2 : i32,
      %C_add : i32, %C_ub : i32):
    %one = llvm.mlir.constant(1 : i32) : i32
    %minus_one = llvm.mlir.constant(4294967295 : i32) : i32
    %pre1 = llvm.icmp "sle" %C1, %C2 : i32
    llvm.assume %pre1 : i1
    %diff = llvm.sub %C0, %C1 : i32
    %pre2 = llvm.icmp "eq" %C_add, %diff : i32
    llvm.assume %pre2 : i1
    %dist = llvm.sub %C2, %C1 : i32
    %pre3 = llvm.icmp "ne" %dist, %minus_one : i32
    llvm.assume %pre3 : i1
    %dist_plus_one = llvm.add %dist, %one : i32
    %pre4 = llvm.icmp "eq" %C_ub, %dist_plus_one : i32
    llvm.assume %pre4 : i1
    %sum = llvm.add %arg0, %C_add : i32
    %v1 = llvm.add %sum, %arg1 : i32
    %result = llvm.icmp "ult" %v1, %C_ub : i32
    llvm.return %result : i1
  }
  }]

private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by
  cases b <;> simp

private theorem i157315_a2t_semval_bind_poison {α β : Type} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl

private theorem i157315_a2t_interval (x lo hi : BitVec 32)
    (hle : (lo ≤ₛ hi) = true)
    (hne : ((hi - lo) != 4294967295#32) = true) :
    (x == (if ((if (lo <ₛ x) = true then x else lo) <ₛ hi) = true then (if (lo <ₛ x) = true then x else lo) else hi)) =
      ((x - lo) <ᵤ ((hi - lo) + 1#32)) := by
  simp only [BitVec.slt, BitVec.sle, BitVec.ult, bne_iff_ne, ne_eq, decide_eq_true_eq] at *
  rw [BitVec.toNat_eq] at hne
  split_ifs with h1 h2 h3 <;> apply Bool.eq_iff_iff.mpr <;>
    simp only [beq_iff_eq, decide_eq_true_eq, true_iff, BitVec.toNat_eq] <;>
    simp only [BitVec.toInt_eq_toNat_cond] at * <;> bv_omega

private opaque i157315_a2t_value_aux (arg0 : BitVec 32) (arg1 : BitVec 32) (C0 : BitVec 32) (C1 : BitVec 32) (C2 : BitVec 32) (C_add : BitVec 32) (C_ub : BitVec 32)
    (hpre1 : (C1 ≤ₛ C2) = true)
    (hpre2 : (C_add == (C0 - C1)) = true)
    (hpre3 : ((C2 - C1) != 4294967295#32) = true)
    (hpre4 : (C_ub == ((C2 - C1) + 1#32)) = true) :
    (((arg1 + C0) + arg0) == (if ((if (C1 <ₛ ((arg1 + C0) + arg0)) = true then ((arg1 + C0) + arg0) else C1) <ₛ C2) = true then (if (C1 <ₛ ((arg1 + C0) + arg0)) = true then ((arg1 + C0) + arg0) else C1) else C2)) = (((arg0 + C_add) + arg1) <ᵤ C_ub) := by
  have hCadd : C_add = C0 - C1 := by simpa using hpre2
  have hCub : C_ub = (C2 - C1) + 1#32 := by simpa using hpre4
  subst C_add
  subst C_ub
  have hsum : (arg0 + (C0 - C1)) + arg1 = ((arg1 + C0) + arg0) - C1 := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg]
    ac_rfl
  rw [hsum]
  exact i157315_a2t_interval ((arg1 + C0) + arg0) C1 C2 hpre1 hpre3

private theorem i157315_a2t_value (arg0 : BitVec 32) (arg1 : BitVec 32) (C0 : BitVec 32) (C1 : BitVec 32) (C2 : BitVec 32) (C_add : BitVec 32) (C_ub : BitVec 32)
    (hpre1 : (C1 ≤ₛ C2) = true)
    (hpre2 : (C_add == (C0 - C1)) = true)
    (hpre3 : ((C2 - C1) != 4294967295#32) = true)
    (hpre4 : (C_ub == ((C2 - C1) + 1#32)) = true) :
    (((arg1 + C0) + arg0) == (if ((if (C1 <ₛ ((arg1 + C0) + arg0)) = true then ((arg1 + C0) + arg0) else C1) <ₛ C2) = true then (if (C1 <ₛ ((arg1 + C0) + arg0)) = true then ((arg1 + C0) + arg0) else C1) else C2)) = (((arg0 + C_add) + arg1) <ᵤ C_ub) := by
  exact i157315_a2t_value_aux arg0 arg1 C0 C1 C2 C_add C_ub hpre1 hpre2 hpre3 hpre4

set_option maxHeartbeats 4000000 in
theorem i157315_a2t_correct : i157315_a2t_src ⊑ i157315_a2t_tgt := by
  intro V
  let arg0Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨6, by simp⟩
  let arg1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨5, by simp⟩
  let C0Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨4, by simp⟩
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨3, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨2, by simp⟩
  let C_addVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨1, by simp⟩
  let C_ubVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]) (InstCombine.LLVM.Ty.bitvec 32)
  cases hC1 : V C1Var
  case poison =>
    simp [i157315_a2t_src, i157315_a2t_tgt, i157315_a2t_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C1 =>
    change BitVec 32 at C1
    cases hC2 : V C2Var
    case poison =>
      simp [i157315_a2t_src, i157315_a2t_tgt, i157315_a2t_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value C2 =>
      change BitVec 32 at C2
      cases hcond1 : (C1 ≤ₛ C2)
      · simp [i157315_a2t_src, i157315_a2t_tgt, i157315_a2t_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hC2, hcond1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      ·
        cases hC_add : V C_addVar
        case poison =>
          simp [i157315_a2t_src, i157315_a2t_tgt, i157315_a2t_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C_addVar, hC1, hC2, hcond1, hC_add, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        case value C_add =>
          change BitVec 32 at C_add
          cases hC0 : V C0Var
          case poison =>
            simp [i157315_a2t_src, i157315_a2t_tgt, i157315_a2t_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C_addVar, C0Var, hC1, hC2, hcond1, hC_add, hC0, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
          case value C0 =>
            change BitVec 32 at C0
            cases hcond2 : (C_add == (C0 - C1))
            · simp [i157315_a2t_src, i157315_a2t_tgt, i157315_a2t_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C_addVar, C0Var, hC1, hC2, hcond1, hC_add, hC0, hcond2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
            ·
              cases hcond3 : ((C2 - C1) != 4294967295#32)
              · simp [i157315_a2t_src, i157315_a2t_tgt, i157315_a2t_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C_addVar, C0Var, hC1, hC2, hcond1, hC_add, hC0, hcond2, hcond3, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
              ·
                cases hC_ub : V C_ubVar
                case poison =>
                  simp [i157315_a2t_src, i157315_a2t_tgt, i157315_a2t_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C_addVar, C0Var, C_ubVar, hC1, hC2, hcond1, hC_add, hC0, hcond2, hcond3, hC_ub, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                  exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                case value C_ub =>
                  change BitVec 32 at C_ub
                  cases hcond4 : (C_ub == ((C2 - C1) + 1#32))
                  · simp [i157315_a2t_src, i157315_a2t_tgt, i157315_a2t_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C_addVar, C0Var, C_ubVar, hC1, hC2, hcond1, hC_add, hC0, hcond2, hcond3, hC_ub, hcond4, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                  ·
                    cases harg1 : V arg1Var
                    case poison =>
                      simp [i157315_a2t_src, i157315_a2t_tgt, i157315_a2t_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C_addVar, C0Var, C_ubVar, arg1Var, hC1, hC2, hcond1, hC_add, hC0, hcond2, hcond3, hC_ub, hcond4, harg1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                      exact ImmediateUBOr.IsRefinedBy.bothValues (by
                        constructor
                        · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                            first
                            | exact LLVM.SemVal.poison_isRefinedBy _
                            | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                            | simp [LLVM.IntW.instRefinement])
                        · exact HVector.nil_isRefinedBy_nil)
                    case value arg1 =>
                      change BitVec 32 at arg1
                      cases harg0 : V arg0Var
                      case poison =>
                        simp [i157315_a2t_src, i157315_a2t_tgt, i157315_a2t_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C_addVar, C0Var, C_ubVar, arg1Var, arg0Var, hC1, hC2, hcond1, hC_add, hC0, hcond2, hcond3, hC_ub, hcond4, harg1, harg0, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                        exact ImmediateUBOr.IsRefinedBy.bothValues (by
                          constructor
                          · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                              first
                              | exact LLVM.SemVal.poison_isRefinedBy _
                              | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                              | simp [LLVM.IntW.instRefinement])
                          · exact HVector.nil_isRefinedBy_nil)
                      case value arg0 =>
                        change BitVec 32 at arg0
                        simp [i157315_a2t_src, i157315_a2t_tgt, i157315_a2t_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C_addVar, C0Var, C_ubVar, arg1Var, arg0Var, hC1, hC2, hcond1, hC_add, hC0, hcond2, hcond3, hC_ub, hcond4, harg1, harg0, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                        exact ImmediateUBOr.IsRefinedBy.bothValues (by
                          constructor
                          · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                              have hv := i157315_a2t_value arg0 arg1 C0 C1 C2 C_add C_ub hcond1 hcond2 hcond3 hcond4
                              by_cases hS1 : ((if (C1 <ₛ ((arg1 + C0) + arg0)) = true then ((arg1 + C0) + arg0) else C1) <ₛ C2) = true <;> by_cases hS2 : (C1 <ₛ ((arg1 + C0) + arg0)) = true <;> simp_all [InstCombine.LLVM.Ty.width, ofBool_one_iff, LLVM.SemVal.isRefinedBy_self])
                          · exact HVector.nil_isRefinedBy_nil)
