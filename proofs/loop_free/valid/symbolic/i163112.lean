import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i163112_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i163112_src(%P : _, %Y : _, %X : _, %C : _) -> i1 {
  ^bb0(%P : _, %Y : _, %X : _, %C : _):
    %cond = llvm.icmp "ne" %P, %Y : _
    llvm.assume %cond : i1
    %v2 = llvm.icmp "eq" %X, %C : _
    %v3 = llvm.select %v2, %P, %Y : _
    %v4 = llvm.icmp "eq" %v3, %Y : _
    llvm.return %v4 : i1
  }
  }]

def i163112_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i163112_tgt(%P : _, %Y : _, %X : _, %C : _) -> i1 {
  ^bb0(%P : _, %Y : _, %X : _, %C : _):
    %v3 = llvm.icmp "ne" %X, %C : _
    llvm.return %v3 : i1
  }
  }]

private theorem i163112_value {w : Nat} (P : BitVec w) (Y : BitVec w) (X : BitVec w) (C : BitVec w)
    (hpre : (P != Y) = true) :
    ((if X = C then P else Y) == Y) = (X != C) := by
  have hPY : P ≠ Y := by
    simpa [bne_iff_ne] using hpre
  by_cases hXC : X = C
  · simp [hXC, hPY]
  · simp [hXC]

set_option maxHeartbeats 4000000 in
theorem i163112_correct (w : Nat) : i163112_src w ⊑ i163112_tgt w := by
  intro V
  let PVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨3, by simp⟩
  let YVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let XVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let CVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases hP : V PVar
  case poison =>
    simp [i163112_src, i163112_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, PVar, hP, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.select, InstCombine.lift3, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value P =>
    cases hY : V YVar
    case poison =>
      simp [i163112_src, i163112_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, PVar, YVar, hP, hY, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.select, InstCombine.lift3, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value Y =>
      cases hcond : (P != Y)
      · simp [i163112_src, i163112_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, PVar, YVar, hP, hY, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.select, InstCombine.lift3, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      ·
        cases hX : V XVar
        case poison =>
          simp [i163112_src, i163112_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, PVar, YVar, XVar, hP, hY, hcond, hX, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.select, InstCombine.lift3, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.bothValues (by
            constructor
            · exact ImmediateUBOr.IsRefinedBy.bothValues (LLVM.SemVal.poison_isRefinedBy _)
            · exact HVector.nil_isRefinedBy_nil)
        case value X =>
          cases hC : V CVar
          case poison =>
            simp [i163112_src, i163112_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, PVar, YVar, XVar, CVar, hP, hY, hcond, hX, hC, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.select, InstCombine.lift3, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (LLVM.SemVal.poison_isRefinedBy _)
              · exact HVector.nil_isRefinedBy_nil)
          case value C =>
            simp [i163112_src, i163112_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, PVar, YVar, XVar, CVar, hP, hY, hcond, hX, hC, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.select, InstCombine.lift3, LLVM.assume_]
            have hv := i163112_value (w := w) P Y X C hcond
            have hite : (if BitVec.ofBool (X == C) = 1#1 then LLVM.SemVal.value P else LLVM.SemVal.value Y)
                = LLVM.SemVal.value (if (X == C) = true then P else Y) := by
              cases hite_c : (X == C) <;> simp [hite_c]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · refine ImmediateUBOr.IsRefinedBy.bothValues ?_
                rw [hite]
                simp [hv, beq_iff_eq, bne_iff_ne]
              · exact HVector.nil_isRefinedBy_nil)
