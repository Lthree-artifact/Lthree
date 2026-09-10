import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def C_signed_unsigned_rem__minimal_src :=
  [llvm()| {
  llvm.func @C_signed_unsigned_rem__minimal_src(%x : i32, %d : i32) -> i32 {
  ^bb0(%x : i32, %d : i32):
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %p = llvm.icmp "sgt" %d, %c_i32_0 : i32
    llvm.assume %p : i1
    %nn = llvm.icmp "sge" %x, %c_i32_0 : i32
    llvm.assume %nn : i1
    %r = llvm.srem %x, %d : i32
    llvm.return %r : i32
  }
  }]

def C_signed_unsigned_rem__minimal_tgt :=
  [llvm()| {
  llvm.func @C_signed_unsigned_rem__minimal_tgt(%x : i32, %d : i32) -> i32 {
  ^bb0(%x : i32, %d : i32):
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %p = llvm.icmp "sgt" %d, %c_i32_0 : i32
    llvm.assume %p : i1
    %nn = llvm.icmp "sge" %x, %c_i32_0 : i32
    llvm.assume %nn : i1
    %r = llvm.urem %x, %d : i32
    llvm.return %r : i32
  }
  }]

private theorem C_signed_unsigned_rem__minimal_semval_bind_poison {α β : Type} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl

private theorem C_signed_unsigned_rem__minimal_srem_eq_if {w : Nat} {x y : BitVec w} :
    LLVM.srem? x y =
      (if (y = 0#w) ∨ (¬ w = 1 ∧ x = BitVec.intMin w ∧ y = BitVec.ofInt w (-1))
       then (.immediateUB : LLVM.IntWUB w)
       else (.value (x.srem y) : LLVM.IntWUB w)) := by
  have hneg : BitVec.ofInt w (-1) = -1 := by simp [BitVec.ofInt_neg, BitVec.ofInt_ofNat]
  simp [LLVM.srem?, hneg]
  split_ifs <;> try tauto

private theorem C_signed_unsigned_rem__minimal_urem_eq_if {w : Nat} {x y : BitVec w} :
    LLVM.urem? x y =
      (if y = 0#w then (.immediateUB : LLVM.IntWUB w)
       else (.value (x % y) : LLVM.IntWUB w)) := rfl

private theorem C_signed_unsigned_rem__minimal_value (x : BitVec 32) (d : BitVec 32)
    (hpre1 : (0#32 <ₛ d) = true)
    (hpre2 : (0#32 ≤ₛ x) = true)
    (hub1 : ¬ (d = 0#32 ∨ (x = BitVec.intMin 32 ∧ d = 4294967295#32)))
    (htub1 : ¬ (d = 0#32)) :
    (x.srem d) = (x % d) := by
  have _ := hub1
  have _ := htub1
  have hxmsb : x.msb = false := by
    rw [BitVec.msb_eq_toInt]
    rw [decide_eq_false_iff_not]
    intro hxneg
    have hxnonneg : (0 : Int) ≤ x.toInt := by
      simpa [BitVec.sle_eq_decide] using hpre2
    omega
  have hdmsb : d.msb = false := by
    rw [BitVec.msb_eq_toInt]
    rw [decide_eq_false_iff_not]
    intro hdneg
    have hdpos : (0 : Int) < d.toInt := by
      simpa [BitVec.slt_eq_decide] using hpre1
    omega
  rw [BitVec.srem_eq, hxmsb, hdmsb]

set_option maxHeartbeats 4000000 in
theorem C_signed_unsigned_rem__minimal_correct : C_signed_unsigned_rem__minimal_src ⊑ C_signed_unsigned_rem__minimal_tgt := by
  intro V
  let xVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨1, by simp⟩
  let dVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32]) (InstCombine.LLVM.Ty.bitvec 32)
  cases hd : V dVar
  case poison =>
    simp [C_signed_unsigned_rem__minimal_src, C_signed_unsigned_rem__minimal_tgt, C_signed_unsigned_rem__minimal_semval_bind_poison, C_signed_unsigned_rem__minimal_srem_eq_if, C_signed_unsigned_rem__minimal_urem_eq_if, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, dVar, hd, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.srem, InstCombine.lift2UB, LLVM.urem, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value d =>
    change BitVec 32 at d
    cases hcond1 : (0#32 <ₛ d)
    · simp [C_signed_unsigned_rem__minimal_src, C_signed_unsigned_rem__minimal_tgt, C_signed_unsigned_rem__minimal_semval_bind_poison, C_signed_unsigned_rem__minimal_srem_eq_if, C_signed_unsigned_rem__minimal_urem_eq_if, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, dVar, hd, hcond1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.srem, InstCombine.lift2UB, LLVM.urem, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    ·
      cases hx : V xVar
      case poison =>
        simp [C_signed_unsigned_rem__minimal_src, C_signed_unsigned_rem__minimal_tgt, C_signed_unsigned_rem__minimal_semval_bind_poison, C_signed_unsigned_rem__minimal_srem_eq_if, C_signed_unsigned_rem__minimal_urem_eq_if, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, dVar, xVar, hd, hcond1, hx, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.srem, InstCombine.lift2UB, LLVM.urem, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      case value x =>
        change BitVec 32 at x
        cases hcond2 : (0#32 ≤ₛ x)
        · simp [C_signed_unsigned_rem__minimal_src, C_signed_unsigned_rem__minimal_tgt, C_signed_unsigned_rem__minimal_semval_bind_poison, C_signed_unsigned_rem__minimal_srem_eq_if, C_signed_unsigned_rem__minimal_urem_eq_if, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, dVar, xVar, hd, hcond1, hx, hcond2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.srem, InstCombine.lift2UB, LLVM.urem, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        ·
          by_cases hub1 : d = 0#32 ∨ (x = BitVec.intMin 32 ∧ d = 4294967295#32)
          ·
            simp [C_signed_unsigned_rem__minimal_src, C_signed_unsigned_rem__minimal_tgt, C_signed_unsigned_rem__minimal_semval_bind_poison, C_signed_unsigned_rem__minimal_srem_eq_if, C_signed_unsigned_rem__minimal_urem_eq_if, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, dVar, xVar, hd, hcond1, hx, hcond2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.srem, InstCombine.lift2UB, LLVM.urem, LLVM.assume_]
            simp [hub1]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
              · exact HVector.nil_isRefinedBy_nil)
          ·
            by_cases htub1 : d = 0#32
            ·
              exfalso
              simp_all
            ·
              simp [C_signed_unsigned_rem__minimal_src, C_signed_unsigned_rem__minimal_tgt, C_signed_unsigned_rem__minimal_semval_bind_poison, C_signed_unsigned_rem__minimal_srem_eq_if, C_signed_unsigned_rem__minimal_urem_eq_if, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, dVar, xVar, hd, hcond1, hx, hcond2, hub1, htub1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.srem, InstCombine.lift2UB, LLVM.urem, LLVM.assume_]
              try rw [if_neg (fun h => hub1 (Or.inr h))]
              have hv := C_signed_unsigned_rem__minimal_value x d hcond1 hcond2 hub1 htub1
              exact ImmediateUBOr.IsRefinedBy.bothValues (by
                constructor
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv] <;> rfl)
                · exact HVector.nil_isRefinedBy_nil)
