import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i191169_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i191169_src(%C1 : _, %C2 : _, %C3 : _, %X : _, %Y : _) -> _ {
  ^bb0(%C1 : _, %C2 : _, %C3 : _, %X : _, %Y : _):
    %xor_c = llvm.xor %C1, %C2 : _
    %cmp = llvm.icmp "eq" %C3, %xor_c : _
    llvm.assume %cmp : i1
    %or = llvm.or disjoint %X, %C1 : _
    %xor1 = llvm.xor %Y, %or : _
    %res = llvm.xor %xor1, %C2 : _
    llvm.return %res : _
  }
  }]

def i191169_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i191169_tgt(%C1 : _, %C2 : _, %C3 : _, %X : _, %Y : _) -> _ {
  ^bb0(%C1 : _, %C2 : _, %C3 : _, %X : _, %Y : _):
    %xor_c = llvm.xor %C1, %C2 : _
    %cmp = llvm.icmp "eq" %C3, %xor_c : _
    llvm.assume %cmp : i1
    %xor1 = llvm.xor %X, %Y : _
    %res = llvm.xor %xor1, %C3 : _
    llvm.return %res : _
  }
  }]

private theorem i191169_value {w : Nat} (C1 : BitVec w) (C2 : BitVec w) (C3 : BitVec w) (X : BitVec w) (Y : BitVec w)
    (hpre : C3 = (C1 ^^^ C2))
    (hdis : X &&& C1 = 0#w) :
    ((Y ^^^ (X ||| C1)) ^^^ C2) = ((X ^^^ Y) ^^^ C3) := by
  subst C3
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hdis_i := congrArg (fun z : BitVec w => z[i]) hdis
  simp [BitVec.getElem_and, BitVec.getElem_zero] at hdis_i
  simp [BitVec.getElem_xor, BitVec.getElem_or]
  generalize hx : X[i] = xb
  generalize hc1 : C1[i] = c1b
  generalize hc2 : C2[i] = c2b
  generalize hy : Y[i] = yb
  cases xb <;> cases c1b <;> cases c2b <;> cases yb <;> simp [hx, hc1] at hdis_i ⊢

set_option maxHeartbeats 4000000 in
theorem i191169_correct (w : Nat) : i191169_src w ⊑ i191169_tgt w := by
  intro V
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨4, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨3, by simp⟩
  let C3Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let XVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let YVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases hC3 : V C3Var
  case poison =>
    simp [i191169_src, i191169_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, hC3, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.xor, LLVM.xor?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C3 =>
    cases hC1 : V C1Var
    case poison =>
      simp [i191169_src, i191169_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, hC3, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.xor, LLVM.xor?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value C1 =>
      cases hC2 : V C2Var
      case poison =>
        simp [i191169_src, i191169_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, C2Var, hC3, hC1, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.xor, LLVM.xor?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      case value C2 =>
        cases hcond : (C3 == (C1 ^^^ C2))
        · simp [i191169_src, i191169_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, C2Var, hC3, hC1, hC2, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.xor, LLVM.xor?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        ·
          cases hY : V YVar
          case poison =>
            cases hX : V XVar
            case poison =>
              simp [i191169_src, i191169_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, C2Var, YVar, XVar, hC3, hC1, hC2, hcond, hY, hX, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.xor, LLVM.xor?, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.bothValues (by
                constructor
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp)
                · exact HVector.nil_isRefinedBy_nil)
            case value X =>
              simp [i191169_src, i191169_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, C2Var, YVar, XVar, hC3, hC1, hC2, hcond, hY, hX, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.xor, LLVM.xor?, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.bothValues (by
                constructor
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp)
                · exact HVector.nil_isRefinedBy_nil)
          case value Y =>
            cases hX : V XVar
            case poison =>
              simp [i191169_src, i191169_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, C2Var, YVar, XVar, hC3, hC1, hC2, hcond, hY, hX, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.xor, LLVM.xor?, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.bothValues (by
                constructor
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp)
                · exact HVector.nil_isRefinedBy_nil)
            case value X =>
              cases hd : (X &&& C1 == 0#w)
              · have hne : ¬ (X &&& C1 = 0#w) := by simpa using hd
                simp [i191169_src, i191169_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, C2Var, YVar, XVar, hC3, hC1, hC2, hcond, hY, hX, hne, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.xor, LLVM.xor?, LLVM.assume_]
                exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  constructor
                  · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp)
                  · exact HVector.nil_isRefinedBy_nil)
              · have hpre : C3 = (C1 ^^^ C2) := by simpa using hcond
                have hdis : X &&& C1 = 0#w := by simpa using hd
                have hval : ((Y ^^^ (X ||| C1)) ^^^ C2) = ((X ^^^ Y) ^^^ C3) :=
                  i191169_value (w := w) C1 C2 C3 X Y hpre hdis
                simp [i191169_src, i191169_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C3Var, C1Var, C2Var, YVar, XVar, hC3, hC1, hC2, hcond, hY, hX, hdis, hval, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.xor, LLVM.xor?, LLVM.assume_]
                exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  constructor
                  · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp)
                  · exact HVector.nil_isRefinedBy_nil)
