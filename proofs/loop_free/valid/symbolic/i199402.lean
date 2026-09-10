import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def i199402_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i199402_src(%x : _, %y : _, %C : _, %cond : i1) -> i1 {
  ^bb0(%x : _, %y : _, %C : _, %cond : i1):
    %true = llvm.mlir.constant(true) : i1
    %y_ne_c = llvm.icmp "ne" %y, %C : _
    %x_eq_c = llvm.icmp "eq" %x, %C : _
    %not_cond_premise = llvm.or %y_ne_c, %x_eq_c : i1
    %precond = llvm.or %not_cond_premise, %cond : i1
    llvm.assume %precond : i1
    %x_is_c = llvm.icmp "eq" %x, %C : _
    %max = llvm.select %cond, %x, %y : _
    %max_is_c = llvm.icmp "eq" %max, %C : _
    %r = llvm.select %x_is_c, %true, %max_is_c : i1
    llvm.return %r : i1
  }
  }]

def i199402_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i199402_tgt(%x : _, %y : _, %C : _, %cond : i1) -> i1 {
  ^bb0(%x : _, %y : _, %C : _, %cond : i1):
    %y_ne_c = llvm.icmp "ne" %y, %C : _
    %x_eq_c = llvm.icmp "eq" %x, %C : _
    %not_cond_premise = llvm.or %y_ne_c, %x_eq_c : i1
    %precond = llvm.or %not_cond_premise, %cond : i1
    llvm.assume %precond : i1
    %r = llvm.icmp "eq" %x, %C : _
    llvm.return %r : i1
  }
  }]

private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by
  cases b <;> simp

private theorem i199402_semval_bind_poison {α β : Type} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl

private theorem i199402_ite_semval_value {w : Nat} {c : Prop} [Decidable c]
    (a b : BitVec w) :
    (if c then LLVM.SemVal.value a else LLVM.SemVal.value b) =
      LLVM.SemVal.value (if c then a else b) := by
  split <;> rfl

private theorem i199402_bv1_eq_zero (b : BitVec 1) (h : ¬ b = 1#1) : b = 0#1 := by
  cases b with
  | ofFin f =>
      cases f with
      | mk n hn =>
          have hn' : n = 0 ∨ n = 1 := by omega
          rcases hn' with rfl | rfl
          · rfl
          · simp [BitVec.ofNat] at h

private theorem i199402_assume_zero_option :
    (match LLVM.SemVal.value (0#1 : BitVec 1) with
    | LLVM.SemVal.value 1#1 => (some () : Option Unit)
    | _ => none) = none := by
  decide

private theorem i199402_value {w : Nat} (x : BitVec w) (y : BitVec w) (C : BitVec w) (cond : BitVec 1)
    (hpre : ((BitVec.ofBool ((y != C) || (x == C))) ||| cond) = 1#1) :
    (if x = C then 1#1 else (BitVec.ofBool ((if cond = 1#1 then x else y) == C))) = (BitVec.ofBool (x == C)) := by
  by_cases hx : x = C
  · simp [hx]
  · by_cases hc : cond = 1#1
    · simp [hx, hc]
    · have hcond0 : cond = 0#1 := i199402_bv1_eq_zero cond hc
      have hpre0 : BitVec.ofBool ((y != C) || (x == C)) = 1#1 := by
        simpa [hcond0] using hpre
      have hpreb : ((y != C) || (x == C)) = true := ofBool_one_iff.mp hpre0
      have hxbeq : (x == C) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        exact hx ((beq_iff_eq.mp h))
      simp [hxbeq] at hpreb
      have hybeq : (y == C) = false := by
        simpa using hpreb
      simp [hx, hc, hxbeq, hybeq]

set_option maxHeartbeats 4000000 in
theorem i199402_correct (w : Nat) : i199402_src w ⊑ i199402_tgt w := by
  intro V
  let xVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨3, by simp⟩
  let yVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let CVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let condVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec 1) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec 1)
  cases hy : V yVar
  case poison =>
    simp [i199402_src, i199402_tgt, i199402_semval_bind_poison, i199402_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, yVar, hy, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value y =>
    change BitVec w at y
    cases hC : V CVar
    case poison =>
      simp [i199402_src, i199402_tgt, i199402_semval_bind_poison, i199402_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, yVar, CVar, hy, hC, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value C =>
      change BitVec w at C
      cases hx : V xVar
      case poison =>
        simp [i199402_src, i199402_tgt, i199402_semval_bind_poison, i199402_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, yVar, CVar, xVar, hy, hC, hx, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      case value x =>
        change BitVec w at x
        cases hcond : V condVar
        case poison =>
          simp [i199402_src, i199402_tgt, i199402_semval_bind_poison, i199402_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, yVar, CVar, xVar, condVar, hy, hC, hx, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        case value cond =>
          change BitVec 1 at cond
          by_cases hcondq : ((BitVec.ofBool ((y != C) || (x == C))) ||| cond) = 1#1
          ·
            simp [i199402_src, i199402_tgt, i199402_semval_bind_poison, i199402_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, yVar, CVar, xVar, condVar, hy, hC, hx, hcond, hcondq, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  have hv := i199402_value (w := w) x y C cond hcondq
                  simp [hv, ofBool_one_iff, i199402_ite_semval_value, InstCombine.LLVM.Ty.width, LLVM.SemVal.bind_value, LLVM.SemVal.isRefinedBy_self])
              · exact HVector.nil_isRefinedBy_nil)
          · simp [i199402_src, i199402_tgt, i199402_semval_bind_poison, i199402_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, yVar, CVar, xVar, condVar, hy, hC, hx, hcond, i199402_bv1_eq_zero _ hcondq, i199402_assume_zero_option, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
