import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def all17_src :=
  [llvm()| {
  llvm.func @all17_src(%a : i32, %b : i32, %C_low : i32, %C_high : i32) -> i1 {
  ^bb0(%a : i32, %b : i32, %C_low : i32, %C_high : i32):
    %precond = llvm.icmp "slt" %C_low, %C_high : i32
    llvm.assume %precond : i1
    %v0 = llvm.icmp "sgt" %b, %C_high : i32
    %v1 = llvm.select %v0, %C_high, %b : i32
    %v2 = llvm.icmp "sgt" %v1, %C_low : i32
    %v3 = llvm.select %v2, %v1, %C_low : i32
    %v4 = llvm.icmp "sgt" %a, %C_high : i32
    %v5 = llvm.select %v4, %C_high, %a : i32
    %v6 = llvm.icmp "sgt" %v5, %C_low : i32
    %v7 = llvm.select %v6, %v5, %C_low : i32
    %v8 = llvm.icmp "eq" %v3, %C_high : i32
    %v9 = llvm.icmp "eq" %v7, %C_high : i32
    %v10 = llvm.and %v8, %v9 : i1
    llvm.return %v10 : i1
  }
  }]

def all17_tgt :=
  [llvm()| {
  llvm.func @all17_tgt(%a : i32, %b : i32, %C_low : i32, %C_high : i32) -> i1 {
  ^bb0(%a : i32, %b : i32, %C_low : i32, %C_high : i32):
    %precond = llvm.icmp "slt" %C_low, %C_high : i32
    llvm.assume %precond : i1
    %cmp_a = llvm.icmp "sge" %a, %C_high : i32
    %cmp_b = llvm.icmp "sge" %b, %C_high : i32
    %result = llvm.and %cmp_a, %cmp_b : i1
    llvm.return %result : i1
  }
  }]

private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by
  cases b <;> simp

private theorem all17_bv1_one_and (x : BitVec 1) : 1#1 &&& x = x := by
  have h : (1#1 : BitVec 1) = BitVec.allOnes 1 := rfl
  rw [h, BitVec.allOnes_and]

private theorem all17_bv1_and_one (x : BitVec 1) : x &&& 1#1 = x := by
  have h : (1#1 : BitVec 1) = BitVec.allOnes 1 := rfl
  rw [h, BitVec.and_allOnes]

private theorem all17_bv1_one_or (x : BitVec 1) : 1#1 ||| x = 1#1 := by
  have h : (1#1 : BitVec 1) = BitVec.allOnes 1 := rfl
  rw [h, BitVec.allOnes_or]

private theorem all17_bv1_or_one (x : BitVec 1) : x ||| 1#1 = 1#1 := by
  have h : (1#1 : BitVec 1) = BitVec.allOnes 1 := rfl
  rw [h, BitVec.or_allOnes]

private theorem all17_semval_bind_poison {α β : Type} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl

private theorem all17_value (a : BitVec 32) (b : BitVec 32) (C_low : BitVec 32) (C_high : BitVec 32)
    (hpre : (C_low <ₛ C_high) = true) :
    (((if (C_low <ₛ (if (C_high <ₛ b) = true then C_high else b)) = true then (if (C_high <ₛ b) = true then C_high else b) else C_low) == C_high) && ((if (C_low <ₛ (if (C_high <ₛ a) = true then C_high else a)) = true then (if (C_high <ₛ a) = true then C_high else a) else C_low) == C_high)) = ((C_high ≤ₛ a) && (C_high ≤ₛ b)) := by
  simp [BitVec.slt_eq_decide, BitVec.sle_eq_decide] at *
  have hclamp (x : BitVec 32) :
      ((if C_low.toInt < (if C_high.toInt < x.toInt then C_high else x).toInt then
          if C_high.toInt < x.toInt then C_high else x
        else C_low) == C_high) = decide (C_high.toInt ≤ x.toInt) := by
    by_cases hxhi : C_high.toInt < x.toInt
    · simp [hxhi, hpre, le_of_lt hxhi]
    · have hxle : x.toInt ≤ C_high.toInt := le_of_not_gt hxhi
      by_cases hxlow : C_low.toInt < x.toInt
      · by_cases hxeq : x = C_high
        · simp [hxeq, hpre]
        · have hnotle : ¬ C_high.toInt ≤ x.toInt := by
            intro hle
            have hto : x.toInt = C_high.toInt := by omega
            exact hxeq (BitVec.eq_of_toInt_eq hto)
          simp [hxhi, hxlow, hnotle, hxeq]
      · have hnotle : ¬ C_high.toInt ≤ x.toInt := by omega
        have hclowne : C_low ≠ C_high := by
          intro h
          subst C_low
          omega
        simp [hxhi, hxlow, hnotle, hclowne]
  rw [hclamp a, hclamp b]
  rw [Bool.and_comm]

set_option maxHeartbeats 4000000 in
theorem all17_correct : all17_src ⊑ all17_tgt := by
  intro V
  let aVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨3, by simp⟩
  let bVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨2, by simp⟩
  let C_lowVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨1, by simp⟩
  let C_highVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]) (InstCombine.LLVM.Ty.bitvec 32)
  cases hC_low : V C_lowVar
  case poison =>
    simp [all17_src, all17_tgt, all17_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C_lowVar, hC_low, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C_low =>
    change BitVec 32 at C_low
    cases hC_high : V C_highVar
    case poison =>
      simp [all17_src, all17_tgt, all17_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C_lowVar, C_highVar, hC_low, hC_high, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value C_high =>
      change BitVec 32 at C_high
      cases hcond : (C_low <ₛ C_high)
      · simp [all17_src, all17_tgt, all17_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C_lowVar, C_highVar, hC_low, hC_high, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      ·
        cases hb : V bVar
        case poison =>
          simp [all17_src, all17_tgt, all17_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C_lowVar, C_highVar, bVar, hC_low, hC_high, hcond, hb, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.bothValues (by
            constructor
            · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                first
                | exact LLVM.SemVal.poison_isRefinedBy _
                | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                | simp [LLVM.IntW.instRefinement])
            · exact HVector.nil_isRefinedBy_nil)
        case value b =>
          change BitVec 32 at b
          cases ha : V aVar
          case poison =>
            simp [all17_src, all17_tgt, all17_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C_lowVar, C_highVar, bVar, aVar, hC_low, hC_high, hcond, hb, ha, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  first
                  | exact LLVM.SemVal.poison_isRefinedBy _
                  | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                  | simp [LLVM.IntW.instRefinement])
              · exact HVector.nil_isRefinedBy_nil)
          case value a =>
            change BitVec 32 at a
            simp [all17_src, all17_tgt, all17_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C_lowVar, C_highVar, bVar, aVar, hC_low, hC_high, hcond, hb, ha, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  have hv := all17_value a b C_low C_high hcond
                  by_cases hS1 : (C_low <ₛ (if (C_high <ₛ b) = true then C_high else b)) = true <;> by_cases hS2 : (C_high <ₛ b) = true <;> by_cases hS3 : (C_low <ₛ (if (C_high <ₛ a) = true then C_high else a)) = true <;> by_cases hS4 : (C_high <ₛ a) = true <;> simp_all [InstCombine.LLVM.Ty.width, ofBool_one_iff, all17_bv1_one_and, all17_bv1_and_one, all17_bv1_one_or, all17_bv1_or_one, LLVM.SemVal.isRefinedBy_self])
              · exact HVector.nil_isRefinedBy_nil)
