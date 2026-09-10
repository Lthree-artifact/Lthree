import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def F_wide_symbolic__minimal_src :=
  [llvm()| {
  llvm.func @F_wide_symbolic__minimal_src(%a0 : i32, %a1 : i32, %C0 : i32, %C1 : i32, %C2 : i32, %Ca : i32, %Cu : i32) -> i1 {
  ^bb0(%a0 : i32, %a1 : i32, %C0 : i32, %C1 : i32, %C2 : i32, %Ca : i32, %Cu : i32):
    %p1 = llvm.icmp "sle" %C1, %C2 : i32
    llvm.assume %p1 : i1
    %d = llvm.sub %C0, %C1 : i32
    %p2 = llvm.icmp "eq" %Ca, %d : i32
    llvm.assume %p2 : i1
    %ds = llvm.sub %C2, %C1 : i32
    %c_i32_m1 = llvm.mlir.constant(-1 : i32) : i32
    %p3 = llvm.icmp "ne" %ds, %c_i32_m1 : i32
    llvm.assume %p3 : i1
    %c_i32_1 = llvm.mlir.constant(1 : i32) : i32
    %d1 = llvm.add %ds, %c_i32_1 : i32
    %p4 = llvm.icmp "eq" %Cu, %d1 : i32
    llvm.assume %p4 : i1
    %v0 = llvm.add %a1, %C0 : i32
    %v1 = llvm.add %v0, %a0 : i32
    %c1 = llvm.icmp "sgt" %v1, %C1 : i32
    %m1 = llvm.select %c1, %v1, %C1 : i32
    %c2 = llvm.icmp "slt" %m1, %C2 : i32
    %m2 = llvm.select %c2, %m1, %C2 : i32
    %r = llvm.icmp "eq" %v1, %m2 : i32
    llvm.return %r : i1
  }
  }]

def F_wide_symbolic__minimal_tgt :=
  [llvm()| {
  llvm.func @F_wide_symbolic__minimal_tgt(%a0 : i32, %a1 : i32, %C0 : i32, %C1 : i32, %C2 : i32, %Ca : i32, %Cu : i32) -> i1 {
  ^bb0(%a0 : i32, %a1 : i32, %C0 : i32, %C1 : i32, %C2 : i32, %Ca : i32, %Cu : i32):
    %p1 = llvm.icmp "sle" %C1, %C2 : i32
    llvm.assume %p1 : i1
    %d = llvm.sub %C0, %C1 : i32
    %p2 = llvm.icmp "eq" %Ca, %d : i32
    llvm.assume %p2 : i1
    %ds = llvm.sub %C2, %C1 : i32
    %c_i32_m1 = llvm.mlir.constant(-1 : i32) : i32
    %p3 = llvm.icmp "ne" %ds, %c_i32_m1 : i32
    llvm.assume %p3 : i1
    %c_i32_1 = llvm.mlir.constant(1 : i32) : i32
    %d1 = llvm.add %ds, %c_i32_1 : i32
    %p4 = llvm.icmp "eq" %Cu, %d1 : i32
    llvm.assume %p4 : i1
    %s = llvm.add %a0, %Ca : i32
    %v1 = llvm.add %s, %a1 : i32
    %r = llvm.icmp "ult" %v1, %Cu : i32
    llvm.return %r : i1
  }
  }]

private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by
  cases b <;> simp

private theorem F_wide_symbolic__minimal_semval_bind_poison {α β : Type} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl

private theorem F_wide_symbolic__minimal_value (a0 : BitVec 32) (a1 : BitVec 32) (C0 : BitVec 32) (C1 : BitVec 32) (C2 : BitVec 32) (Ca : BitVec 32) (Cu : BitVec 32)
    (hpre1 : (C1 ≤ₛ C2) = true)
    (hpre2 : (Ca == (C0 - C1)) = true)
    (hpre3 : ((C2 - C1) != 4294967295#32) = true)
    (hpre4 : (Cu == ((C2 - C1) + 1#32)) = true) :
    (((a1 + C0) + a0) == (if ((if (C1 <ₛ ((a1 + C0) + a0)) = true then ((a1 + C0) + a0) else C1) <ₛ C2) = true then (if (C1 <ₛ ((a1 + C0) + a0)) = true then ((a1 + C0) + a0) else C1) else C2)) = (((a0 + Ca) + a1) <ᵤ Cu) := by
  have hRange : ∀ (x lo hi : BitVec 32),
      (lo ≤ₛ hi) = true →
      ((hi - lo) != 4294967295#32) = true →
      (x == (if ((if (lo <ₛ x) = true then x else lo) <ₛ hi) = true then
        (if (lo <ₛ x) = true then x else lo) else hi)) =
      ((x - lo) <ᵤ ((hi - lo) + 1#32)) := by
    intro x lo hi hlohi hne
    simp only [BitVec.slt, BitVec.sle, BitVec.ult, bne_iff_ne, ne_eq, decide_eq_true_eq] at *
    rw [BitVec.toNat_eq] at hne
    split_ifs with h1 h2 h3 <;> apply Bool.eq_iff_iff.mpr <;>
      simp only [beq_iff_eq, decide_eq_true_eq, true_iff, BitVec.toNat_eq] <;>
      simp only [BitVec.toInt_eq_toNat_cond] at * <;> bv_omega
  have hCa : Ca = C0 - C1 := beq_iff_eq.mp hpre2
  have hCu : Cu = (C2 - C1) + 1#32 := beq_iff_eq.mp hpre4
  subst Ca
  subst Cu
  rw [hRange ((a1 + C0) + a0) C1 C2 hpre1 hpre3]
  congr 1
  bv_omega

set_option maxHeartbeats 4000000 in
theorem F_wide_symbolic__minimal_correct : F_wide_symbolic__minimal_src ⊑ F_wide_symbolic__minimal_tgt := by
  intro V
  let a0Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨6, by simp⟩
  let a1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨5, by simp⟩
  let C0Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨4, by simp⟩
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨3, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨2, by simp⟩
  let CaVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨1, by simp⟩
  let CuVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]) (InstCombine.LLVM.Ty.bitvec 32)
  cases hC1 : V C1Var
  case poison =>
    simp [F_wide_symbolic__minimal_src, F_wide_symbolic__minimal_tgt, F_wide_symbolic__minimal_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C1 =>
    change BitVec 32 at C1
    cases hC2 : V C2Var
    case poison =>
      simp [F_wide_symbolic__minimal_src, F_wide_symbolic__minimal_tgt, F_wide_symbolic__minimal_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value C2 =>
      change BitVec 32 at C2
      cases hcond1 : (C1 ≤ₛ C2)
      · simp [F_wide_symbolic__minimal_src, F_wide_symbolic__minimal_tgt, F_wide_symbolic__minimal_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hC2, hcond1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      ·
        cases hCa : V CaVar
        case poison =>
          simp [F_wide_symbolic__minimal_src, F_wide_symbolic__minimal_tgt, F_wide_symbolic__minimal_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, CaVar, hC1, hC2, hcond1, hCa, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        case value Ca =>
          change BitVec 32 at Ca
          cases hC0 : V C0Var
          case poison =>
            simp [F_wide_symbolic__minimal_src, F_wide_symbolic__minimal_tgt, F_wide_symbolic__minimal_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, CaVar, C0Var, hC1, hC2, hcond1, hCa, hC0, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
          case value C0 =>
            change BitVec 32 at C0
            cases hcond2 : (Ca == (C0 - C1))
            · simp [F_wide_symbolic__minimal_src, F_wide_symbolic__minimal_tgt, F_wide_symbolic__minimal_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, CaVar, C0Var, hC1, hC2, hcond1, hCa, hC0, hcond2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
            ·
              cases hcond3 : ((C2 - C1) != 4294967295#32)
              · simp [F_wide_symbolic__minimal_src, F_wide_symbolic__minimal_tgt, F_wide_symbolic__minimal_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, CaVar, C0Var, hC1, hC2, hcond1, hCa, hC0, hcond2, hcond3, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
              ·
                cases hCu : V CuVar
                case poison =>
                  simp [F_wide_symbolic__minimal_src, F_wide_symbolic__minimal_tgt, F_wide_symbolic__minimal_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, CaVar, C0Var, CuVar, hC1, hC2, hcond1, hCa, hC0, hcond2, hcond3, hCu, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                  exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                case value Cu =>
                  change BitVec 32 at Cu
                  cases hcond4 : (Cu == ((C2 - C1) + 1#32))
                  · simp [F_wide_symbolic__minimal_src, F_wide_symbolic__minimal_tgt, F_wide_symbolic__minimal_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, CaVar, C0Var, CuVar, hC1, hC2, hcond1, hCa, hC0, hcond2, hcond3, hCu, hcond4, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                  ·
                    cases ha1 : V a1Var
                    case poison =>
                      simp [F_wide_symbolic__minimal_src, F_wide_symbolic__minimal_tgt, F_wide_symbolic__minimal_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, CaVar, C0Var, CuVar, a1Var, hC1, hC2, hcond1, hCa, hC0, hcond2, hcond3, hCu, hcond4, ha1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                      exact ImmediateUBOr.IsRefinedBy.bothValues (by
                        constructor
                        · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                            first
                            | exact LLVM.SemVal.poison_isRefinedBy _
                            | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                            | simp [LLVM.IntW.instRefinement])
                        · exact HVector.nil_isRefinedBy_nil)
                    case value a1 =>
                      change BitVec 32 at a1
                      cases ha0 : V a0Var
                      case poison =>
                        simp [F_wide_symbolic__minimal_src, F_wide_symbolic__minimal_tgt, F_wide_symbolic__minimal_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, CaVar, C0Var, CuVar, a1Var, a0Var, hC1, hC2, hcond1, hCa, hC0, hcond2, hcond3, hCu, hcond4, ha1, ha0, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                        exact ImmediateUBOr.IsRefinedBy.bothValues (by
                          constructor
                          · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                              first
                              | exact LLVM.SemVal.poison_isRefinedBy _
                              | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                              | simp [LLVM.IntW.instRefinement])
                          · exact HVector.nil_isRefinedBy_nil)
                      case value a0 =>
                        change BitVec 32 at a0
                        simp [F_wide_symbolic__minimal_src, F_wide_symbolic__minimal_tgt, F_wide_symbolic__minimal_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, CaVar, C0Var, CuVar, a1Var, a0Var, hC1, hC2, hcond1, hCa, hC0, hcond2, hcond3, hCu, hcond4, ha1, ha0, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
                        exact ImmediateUBOr.IsRefinedBy.bothValues (by
                          constructor
                          · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                              have hv := F_wide_symbolic__minimal_value a0 a1 C0 C1 C2 Ca Cu hcond1 hcond2 hcond3 hcond4
                              by_cases hS1 : ((if (C1 <ₛ ((a1 + C0) + a0)) = true then ((a1 + C0) + a0) else C1) <ₛ C2) = true <;> by_cases hS2 : (C1 <ₛ ((a1 + C0) + a0)) = true <;> simp_all [InstCombine.LLVM.Ty.width, ofBool_one_iff, LLVM.SemVal.isRefinedBy_self])
                          · exact HVector.nil_isRefinedBy_nil)
