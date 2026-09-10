import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i157524_sym_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i157524_sym_src(%arg0 : _, %C : _, %newvar_v0 : _) -> _ {
  ^bb0(%arg0 : _, %C : _, %newvar_v0 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c_pos = llvm.icmp "sge" %C, %zero : _
    %v2 = llvm.add %arg0, %C overflow<nsw> : _
    %cond1 = llvm.icmp "sle" %newvar_v0, %arg0 : _
    %cond2 = llvm.icmp "sge" %newvar_v0, %v2 : _
    %cond = llvm.or %cond1, %cond2 : i1
    %pre = llvm.and %cond, %c_pos : i1
    llvm.assume %pre : i1
    %s1 = llvm.icmp "slt" %arg0, %newvar_v0 : _
    %v1 = llvm.select %s1, %arg0, %newvar_v0 : _
    %s2 = llvm.icmp "slt" %v2, %newvar_v0 : _
    %v3 = llvm.select %s2, %v2, %newvar_v0 : _
    %v4 = llvm.sub %v3, %v1 : _
    llvm.return %v4 : _
  }
  }]

def i157524_sym_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i157524_sym_tgt(%arg0 : _, %C : _, %newvar_v0 : _) -> _ {
  ^bb0(%arg0 : _, %C : _, %newvar_v0 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c_pos = llvm.icmp "sge" %C, %zero : _
    %v2 = llvm.add %arg0, %C : _
    %cond1 = llvm.icmp "sle" %newvar_v0, %arg0 : _
    %cond2 = llvm.icmp "sge" %newvar_v0, %v2 : _
    %cond = llvm.or %cond1, %cond2 : i1
    %pre = llvm.and %cond, %c_pos : i1
    llvm.assume %pre : i1
    %v1 = llvm.icmp "slt" %arg0, %newvar_v0 : _
    %v3 = llvm.select %v1, %C, %zero : _
    llvm.return %v3 : _
  }
  }]

private theorem i157524_sym_value {w : Nat} (arg0 : BitVec w) (C : BitVec w) (newvar_v0 : BitVec w)
    (hov1 : arg0.saddOverflow C = false)
    (hc1 : (0#w ≤ₛ C) = true)
    (hcond : ((newvar_v0 ≤ₛ arg0) = true) ∨ (((arg0 + C) ≤ₛ newvar_v0) = true)) :
    ((if ((arg0 + C) <ₛ newvar_v0) = true then (arg0 + C) else newvar_v0) - (if (arg0 <ₛ newvar_v0) = true then arg0 else newvar_v0)) = (if (arg0 <ₛ newvar_v0) = true then C else 0#w) := by
  have hAddInt : (arg0 + C).toInt = arg0.toInt + C.toInt := by
    exact BitVec.toInt_add_of_not_saddOverflow (by simp [hov1])
  have hCnonneg : 0 ≤ C.toInt := by
    simpa [BitVec.sle, BitVec.toInt_zero] using hc1
  have hcondInt : newvar_v0.toInt ≤ arg0.toInt ∨ (arg0 + C).toInt ≤ newvar_v0.toInt := by
    rcases hcond with hle | hle
    · exact Or.inl (by simpa [BitVec.sle] using hle)
    · exact Or.inr (by simpa [BitVec.sle] using hle)
  by_cases hxlt : (arg0 <ₛ newvar_v0) = true
  · have hxltInt : arg0.toInt < newvar_v0.toInt := by
      simpa [BitVec.slt] using hxlt
    have haddLe : (arg0 + C).toInt ≤ newvar_v0.toInt := by
      rcases hcondInt with hle | hle
      · omega
      · exact hle
    by_cases haddlt : ((arg0 + C) <ₛ newvar_v0) = true
    · simp only [haddlt, hxlt, if_true]
      rw [BitVec.add_comm arg0 C]
      exact BitVec.add_sub_cancel C arg0
    · have hnEqAddInt : newvar_v0.toInt = (arg0 + C).toInt := by
        have hnot : ¬ (arg0 + C).toInt < newvar_v0.toInt := by
          simpa [BitVec.slt] using haddlt
        omega
      have hnEqAdd : newvar_v0 = arg0 + C := by
        exact BitVec.eq_of_toInt_eq hnEqAddInt
      simp only [haddlt, hxlt, if_true]
      rw [hnEqAdd, BitVec.add_comm arg0 C]
      exact BitVec.add_sub_cancel C arg0
  · have hnleX : newvar_v0.toInt ≤ arg0.toInt := by
      have hnlt : ¬ arg0.toInt < newvar_v0.toInt := by
        simpa [BitVec.slt] using hxlt
      omega
    have hnotAdd : ¬ ((arg0 + C) <ₛ newvar_v0) = true := by
      have hnotAddInt : ¬ (arg0 + C).toInt < newvar_v0.toInt := by
        omega
      simpa [BitVec.slt] using hnotAddInt
    simp only [hnotAdd, hxlt]
    exact BitVec.sub_self newvar_v0

set_option maxHeartbeats 8000000 in
theorem i157524_sym_correct (w : Nat) : i157524_sym_src w ⊑ i157524_sym_tgt w := by
  intro V
  let arg0Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let CVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let newvar_v0Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases harg0 : V arg0Var <;> cases hC : V CVar <;> cases hnewvar_v0 : V newvar_v0Var
  all_goals (
    try (
      simp [i157524_sym_src, i157524_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, arg0Var, CVar, newvar_v0Var, harg0, hC, hnewvar_v0, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft))
  rename_i arg0 C newvar_v0
  cases hov1 : arg0.saddOverflow C
  ·
    cases hc1 : (0#w ≤ₛ C)
    ·
      simp [i157524_sym_src, i157524_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, arg0Var, CVar, newvar_v0Var, harg0, hC, hnewvar_v0, hov1, hc1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    ·
      cases hp1 : (newvar_v0 ≤ₛ arg0) <;> cases hp2 : ((arg0 + C) ≤ₛ newvar_v0)
      ·
        simp [i157524_sym_src, i157524_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, arg0Var, CVar, newvar_v0Var, harg0, hC, hnewvar_v0, hov1, hc1, hp1, hp2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      ·
        simp [i157524_sym_src, i157524_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, arg0Var, CVar, newvar_v0Var, harg0, hC, hnewvar_v0, hov1, hc1, hp1, hp2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.bothValues (by
          constructor
          · exact ImmediateUBOr.IsRefinedBy.bothValues (by
              have hval := i157524_sym_value (w := w) arg0 C newvar_v0 hov1 hc1 (Or.inr hp2)
              by_cases hS1 : ((arg0 + C) <ₛ newvar_v0) = true <;> by_cases hS2 : (arg0 <ₛ newvar_v0) = true <;> simp_all [InstCombine.LLVM.Ty.width])
          · exact HVector.nil_isRefinedBy_nil)
      ·
        simp [i157524_sym_src, i157524_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, arg0Var, CVar, newvar_v0Var, harg0, hC, hnewvar_v0, hov1, hc1, hp1, hp2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.bothValues (by
          constructor
          · exact ImmediateUBOr.IsRefinedBy.bothValues (by
              have hval := i157524_sym_value (w := w) arg0 C newvar_v0 hov1 hc1 (Or.inl hp1)
              by_cases hS1 : ((arg0 + C) <ₛ newvar_v0) = true <;> by_cases hS2 : (arg0 <ₛ newvar_v0) = true <;> simp_all [InstCombine.LLVM.Ty.width])
          · exact HVector.nil_isRefinedBy_nil)
      ·
        simp [i157524_sym_src, i157524_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, arg0Var, CVar, newvar_v0Var, harg0, hC, hnewvar_v0, hov1, hc1, hp1, hp2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.bothValues (by
          constructor
          · exact ImmediateUBOr.IsRefinedBy.bothValues (by
              have hval := i157524_sym_value (w := w) arg0 C newvar_v0 hov1 hc1 (Or.inl hp1)
              by_cases hS1 : ((arg0 + C) <ₛ newvar_v0) = true <;> by_cases hS2 : (arg0 <ₛ newvar_v0) = true <;> simp_all [InstCombine.LLVM.Ty.width])
          · exact HVector.nil_isRefinedBy_nil)
  ·
    simp [i157524_sym_src, i157524_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, arg0Var, CVar, newvar_v0Var, harg0, hC, hnewvar_v0, hov1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.sub, LLVM.sub?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
