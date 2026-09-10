import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i167079_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167079_src(%arg0 : _, %C : _, %C1 : _, %C2 : _) -> i1 {
  ^bb0(%arg0 : _, %C : _, %C1 : _, %C2 : _):
    %cond1 = llvm.icmp "slt" %C1, %C : _
    %cond2 = llvm.icmp "sge" %C2, %C : _
    %cond3 = llvm.and %cond1, %cond2 : i1
    %cond4 = llvm.icmp "eq" %C1, %C2 : _
    %cond = llvm.or %cond3, %cond4 : i1
    llvm.assume %cond : i1
    %v0 = llvm.icmp "slt" %arg0, %C : _
    %v1 = llvm.select %v0, %C1, %C2 : _
    %v2 = llvm.sub %arg0, %v1 : _
    %zero = llvm.mlir.constant(0 : _) : _
    %v3 = llvm.icmp "eq" %v2, %zero : _
    llvm.return %v3 : i1
  }
  }]

def i167079_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167079_tgt(%arg0 : _, %C : _, %C1 : _, %C2 : _) -> i1 {
  ^bb0(%arg0 : _, %C : _, %C1 : _, %C2 : _):
    %cond1 = llvm.icmp "slt" %C1, %C : _
    %cond2 = llvm.icmp "sge" %C2, %C : _
    %cond3 = llvm.and %cond1, %cond2 : i1
    %cond4 = llvm.icmp "eq" %C1, %C2 : _
    %cond = llvm.or %cond3, %cond4 : i1
    llvm.assume %cond : i1
    %v0 = llvm.icmp "eq" %arg0, %C1 : _
    %v1 = llvm.icmp "eq" %arg0, %C2 : _
    %v2 = llvm.or %v0, %v1 : i1
    llvm.return %v2 : i1
  }
  }]

private theorem i167079_value {w : Nat} (arg0 : BitVec w) (C : BitVec w) (C1 : BitVec w) (C2 : BitVec w)
    (hpre : (((C1 <ₛ C) && (C ≤ₛ C2)) || (C1 == C2)) = true) :
    ((arg0 - (if (arg0 <ₛ C) = true then C1 else C2)) == 0#w) = ((arg0 == C1) || (arg0 == C2)) := by
  have hsub_eq (x y : BitVec w) : ((x - y) == 0#w) = (x == y) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq]
    rw [BitVec.sub_eq_iff_eq_add]
    simp
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hpre
  by_cases hlt : (arg0 <ₛ C) = true
  · simp [hlt, hsub_eq]
    intro harg0
    subst arg0
    cases hpre with
    | inl hordered =>
        have harg_lt : C2.toInt < C.toInt := by
          simpa [BitVec.slt_eq_decide] using hlt
        have hC_le : C.toInt ≤ C2.toInt := by
          simpa [BitVec.sle_eq_decide] using hordered.2
        exfalso
        omega
    | inr hEq =>
        exact hEq.symm
  · simp [hlt, hsub_eq]
    intro harg0
    subst arg0
    cases hpre with
    | inl hordered =>
        have harg_nlt : ¬ C1.toInt < C.toInt := by
          simpa [BitVec.slt_eq_decide] using hlt
        have hC1_lt : C1.toInt < C.toInt := by
          simpa [BitVec.slt_eq_decide] using hordered.1
        exfalso
        omega
    | inr hEq =>
        exact hEq

set_option maxHeartbeats 4000000 in
theorem i167079_correct (w : Nat) : i167079_src w ⊑ i167079_tgt w := by
  intro V
  let arg0Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨3, by simp⟩
  let CVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases hC1 : V C1Var
  case poison =>
    simp [i167079_src, i167079_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C1 =>
    cases hC : V CVar
    case poison =>
      simp [i167079_src, i167079_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, CVar, hC1, hC, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value C =>
      cases hC2 : V C2Var
      case poison =>
        simp [i167079_src, i167079_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, CVar, C2Var, hC1, hC, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      case value C2 =>
        cases hcond : (((C1 <ₛ C) && (C ≤ₛ C2)) || (C1 == C2))
        · simp [i167079_src, i167079_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, CVar, C2Var, hC1, hC, hC2, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        ·
          cases harg0 : V arg0Var
          case poison =>
            simp [i167079_src, i167079_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, CVar, C2Var, arg0Var, hC1, hC, hC2, hcond, harg0, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (LLVM.SemVal.poison_isRefinedBy _)
              · exact HVector.nil_isRefinedBy_nil)
          case value arg0 =>
            simp [i167079_src, i167079_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, CVar, C2Var, arg0Var, hC1, hC, hC2, hcond, harg0, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
            have hv := i167079_value (w := w) arg0 C C1 C2 hcond
            have hite : (if BitVec.ofBool (arg0 <ₛ C) = 1#1 then LLVM.SemVal.value C1 else LLVM.SemVal.value C2)
                = LLVM.SemVal.value (if (arg0 <ₛ C) = true then C1 else C2) := by
              cases hite_c : (arg0 <ₛ C) <;> simp [hite_c]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · refine ImmediateUBOr.IsRefinedBy.bothValues ?_
                rw [hite]
                simp [hv, beq_iff_eq, bne_iff_ne]
              · exact HVector.nil_isRefinedBy_nil)
