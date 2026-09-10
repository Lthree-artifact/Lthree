import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def D_chained_rem__corpus1_src :=
  [llvm()| {
  llvm.func @D_chained_rem__corpus1_src(%x : i32, %C1 : i32, %C2 : i32) -> i32 {
  ^bb0(%x : i32, %C1 : i32, %C2 : i32):
    %rem = llvm.urem %C1, %C2 : i32
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %cond = llvm.icmp "eq" %rem, %c_i32_0 : i32
    llvm.assume %cond : i1
    %v1 = llvm.urem %x, %C1 : i32
    %v2 = llvm.urem %v1, %C2 : i32
    llvm.return %v2 : i32
  }
  }]

def D_chained_rem__corpus1_tgt :=
  [llvm()| {
  llvm.func @D_chained_rem__corpus1_tgt(%x : i32, %C1 : i32, %C2 : i32) -> i32 {
  ^bb0(%x : i32, %C1 : i32, %C2 : i32):
    %rem = llvm.urem %C1, %C2 : i32
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %cond = llvm.icmp "eq" %rem, %c_i32_0 : i32
    llvm.assume %cond : i1
    %v2 = llvm.urem %x, %C2 : i32
    llvm.return %v2 : i32
  }
  }]

private theorem D_chained_rem__corpus1_semval_bind_poison {α β : Type} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl

private theorem D_chained_rem__corpus1_urem_eq_if {w : Nat} {x y : BitVec w} :
    LLVM.urem? x y =
      (if y = 0#w then (.immediateUB : LLVM.IntWUB w)
       else (.value (x % y) : LLVM.IntWUB w)) := rfl

private theorem D_chained_rem__corpus1_value (x : BitVec 32) (C1 : BitVec 32) (C2 : BitVec 32)
    (hub1 : ¬ (C2 = 0#32))
    (hpre : ((C1 % C2) == 0#32) = true)
    (hub2 : ¬ (C1 = 0#32)) :
    ((x % C1) % C2) = (x % C2) := by
  have _ : C2 ≠ 0#32 := hub1
  have _ : C1 ≠ 0#32 := hub2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_umod, BitVec.toNat_umod]
  have hrem : C1 % C2 = 0#32 := by
    simpa using hpre
  have hmod : C1.toNat % C2.toNat = 0 := by
    have h := congrArg BitVec.toNat hrem
    simpa [BitVec.toNat_umod] using h
  exact Nat.mod_mod_of_dvd x.toNat (Nat.dvd_of_mod_eq_zero hmod)

set_option maxHeartbeats 4000000 in
theorem D_chained_rem__corpus1_correct : D_chained_rem__corpus1_src ⊑ D_chained_rem__corpus1_tgt := by
  intro V
  let xVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨2, by simp⟩
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨1, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]) (InstCombine.LLVM.Ty.bitvec 32)
  cases hC1 : V C1Var
  case poison =>
    simp [D_chained_rem__corpus1_src, D_chained_rem__corpus1_tgt, D_chained_rem__corpus1_semval_bind_poison, D_chained_rem__corpus1_urem_eq_if, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.urem, InstCombine.lift2UB, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C1 =>
    change BitVec 32 at C1
    cases hC2 : V C2Var
    case poison =>
      simp [D_chained_rem__corpus1_src, D_chained_rem__corpus1_tgt, D_chained_rem__corpus1_semval_bind_poison, D_chained_rem__corpus1_urem_eq_if, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.urem, InstCombine.lift2UB, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value C2 =>
      change BitVec 32 at C2
      by_cases hub1 : C2 = 0#32
      ·
        simp [D_chained_rem__corpus1_src, D_chained_rem__corpus1_tgt, D_chained_rem__corpus1_semval_bind_poison, D_chained_rem__corpus1_urem_eq_if, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hC2, hub1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.urem, InstCombine.lift2UB, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      ·
        cases hcond : ((C1 % C2) == 0#32)
        · simp [D_chained_rem__corpus1_src, D_chained_rem__corpus1_tgt, D_chained_rem__corpus1_semval_bind_poison, D_chained_rem__corpus1_urem_eq_if, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hC2, hub1, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.urem, InstCombine.lift2UB, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        ·
          by_cases hub2 : C1 = 0#32
          ·
            first
            | (exfalso; simp_all; done)
            | (cases hxu : V xVar <;>
               simp [D_chained_rem__corpus1_src, D_chained_rem__corpus1_tgt, D_chained_rem__corpus1_semval_bind_poison, D_chained_rem__corpus1_urem_eq_if, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, xVar, hC1, hC2, hub1, hcond, hxu, hub2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.urem, InstCombine.lift2UB, LLVM.assume_] <;>
               refine ImmediateUBOr.IsRefinedBy.bothValues ?_ <;>
               constructor <;>
               first
               | exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
               | exact HVector.nil_isRefinedBy_nil
               | (refine ImmediateUBOr.IsRefinedBy.bothValues ?_
                  first
                  | exact LLVM.SemVal.poison_isRefinedBy _
                  | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                  | simp [LLVM.IntW.instRefinement]))
            | (simp [D_chained_rem__corpus1_src, D_chained_rem__corpus1_tgt, D_chained_rem__corpus1_semval_bind_poison, D_chained_rem__corpus1_urem_eq_if, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hC2, hub1, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.urem, InstCombine.lift2UB, LLVM.assume_]
               simp [hub2]
               exact ImmediateUBOr.IsRefinedBy.bothValues (by
                 constructor
                 · exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                 · exact HVector.nil_isRefinedBy_nil))
          ·
            cases hx : V xVar with
            | poison =>
              simp [D_chained_rem__corpus1_src, D_chained_rem__corpus1_tgt, D_chained_rem__corpus1_semval_bind_poison, D_chained_rem__corpus1_urem_eq_if, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, xVar, hC1, hC2, hub1, hcond, hub2, hx, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.urem, InstCombine.lift2UB, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.bothValues (by
                constructor
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    first
                    | exact LLVM.SemVal.poison_isRefinedBy _
                    | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                    | simp [LLVM.IntW.instRefinement])
                · exact HVector.nil_isRefinedBy_nil)
            | value x =>
              change BitVec 32 at x
              simp [D_chained_rem__corpus1_src, D_chained_rem__corpus1_tgt, D_chained_rem__corpus1_semval_bind_poison, D_chained_rem__corpus1_urem_eq_if, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, xVar, hC1, hC2, hub1, hcond, hub2, hx, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.urem, InstCombine.lift2UB, LLVM.assume_]
              have hv := D_chained_rem__corpus1_value x C1 C2 hub1 hcond hub2
              exact ImmediateUBOr.IsRefinedBy.bothValues (by
                constructor
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv] <;> rfl)
                · exact HVector.nil_isRefinedBy_nil)
