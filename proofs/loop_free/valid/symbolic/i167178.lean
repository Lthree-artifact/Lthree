import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i167178_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167178_src(%V : _, %arg0 : _, %C2 : _) -> i1 {
  ^bb0(%V : _, %arg0 : _, %C2 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %cond_V = llvm.icmp "eq" %V, %zero : _
    %not_cond_arg = llvm.icmp "uge" %arg0, %C2 : _
    %assume_cond = llvm.or %not_cond_arg, %cond_V : i1
    llvm.assume %assume_cond : i1
    %v1 = llvm.add %V, %arg0 overflow<nuw> : _
    %v2 = llvm.icmp "ult" %v1, %C2 : _
    llvm.return %v2 : i1
  }
  }]

def i167178_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167178_tgt(%V : _, %arg0 : _, %C2 : _) -> i1 {
  ^bb0(%V : _, %arg0 : _, %C2 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %cond_V = llvm.icmp "eq" %V, %zero : _
    %not_cond_arg = llvm.icmp "uge" %arg0, %C2 : _
    %assume_cond = llvm.or %not_cond_arg, %cond_V : i1
    llvm.assume %assume_cond : i1
    %v2 = llvm.icmp "ult" %arg0, %C2 : _
    llvm.return %v2 : i1
  }
  }]

private theorem i167178_value {w : Nat} (Vv : BitVec w) (arg0 : BitVec w) (C2 : BitVec w)
    (hpre : ((C2 ≤ᵤ arg0) || (Vv == 0#w)) = true)
    (hov : Vv.uaddOverflow arg0 = false) :
    ((Vv + arg0) <ᵤ C2) = (arg0 <ᵤ C2) := by
  rw [Bool.or_eq_true] at hpre
  cases hpre with
  | inl hle =>
      have hleNat : C2.toNat ≤ arg0.toNat := by
        change decide (C2.toNat ≤ arg0.toNat) = true at hle
        exact of_decide_eq_true hle
      have hsum : (Vv + arg0).toNat = Vv.toNat + arg0.toNat := by
        exact BitVec.toNat_add_of_not_uaddOverflow (by simp [hov])
      have hleft : ((Vv + arg0) <ᵤ C2) = false := by
        change decide ((Vv + arg0).toNat < C2.toNat) = false
        apply decide_eq_false_iff_not.mpr
        intro hlt
        rw [hsum] at hlt
        omega
      have hright : (arg0 <ᵤ C2) = false := by
        change decide (arg0.toNat < C2.toNat) = false
        apply decide_eq_false_iff_not.mpr
        omega
      rw [hleft, hright]
  | inr hzBool =>
      have hz : Vv = 0#w := beq_iff_eq.mp hzBool
      subst Vv
      simp

set_option maxHeartbeats 4000000 in
theorem i167178_correct (w : Nat) : i167178_src w ⊑ i167178_tgt w := by
  intro V
  let VVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let arg0Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases harg0 : V arg0Var
  case poison =>
    simp [i167178_src, i167178_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, arg0Var, harg0, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.or, LLVM.or?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value arg0 =>
    cases hC2 : V C2Var
    case poison =>
      simp [i167178_src, i167178_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, arg0Var, C2Var, harg0, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.or, LLVM.or?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value C2 =>
      cases hV : V VVar
      case poison =>
        simp [i167178_src, i167178_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, arg0Var, C2Var, VVar, harg0, hC2, hV, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.or, LLVM.or?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      case value Vv =>
        cases hcond : ((C2 ≤ᵤ arg0) || (Vv == 0#w))
        · simp [i167178_src, i167178_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, arg0Var, C2Var, VVar, harg0, hC2, hV, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.or, LLVM.or?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        ·
          cases hov : Vv.uaddOverflow arg0
          · simp [i167178_src, i167178_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, arg0Var, C2Var, VVar, harg0, hC2, hV, hcond, hov, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.or, LLVM.or?, LLVM.assume_]
            have hv := i167178_value (w := w) Vv arg0 C2 hcond hov
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv])
              · exact HVector.nil_isRefinedBy_nil)
          · simp [i167178_src, i167178_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, arg0Var, C2Var, VVar, harg0, hC2, hV, hcond, hov, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.or, LLVM.or?, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (LLVM.SemVal.poison_isRefinedBy _)
              · exact HVector.nil_isRefinedBy_nil)
