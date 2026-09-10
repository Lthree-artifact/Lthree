import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def i199903_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i199903_src(%newvar_idx : _, %C : _, %isnull : i1, %len : _) -> _ {
  ^bb0(%newvar_idx : _, %C : _, %isnull : i1, %len : _):
    %true = llvm.mlir.constant(true) : i1
    %notnpos = llvm.icmp "ne" %newvar_idx, %C : _
    %memchr_post = llvm.or %isnull, %notnpos : i1
    llvm.assume %memchr_post : i1
    %isnpos = llvm.icmp "eq" %newvar_idx, %C : _
    %cond = llvm.select %isnull, %true, %isnpos : i1
    %r = llvm.select %cond, %len, %newvar_idx : _
    llvm.return %r : _
  }
  }]

def i199903_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i199903_tgt(%newvar_idx : _, %C : _, %isnull : i1, %len : _) -> _ {
  ^bb0(%newvar_idx : _, %C : _, %isnull : i1, %len : _):
    %r = llvm.select %isnull, %len, %newvar_idx : _
    llvm.return %r : _
  }
  }]

private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by
  cases b <;> simp

private theorem i199903_semval_bind_poison {α β : Type} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl

private theorem i199903_ite_semval_value {w : Nat} {c : Prop} [Decidable c]
    (a b : BitVec w) :
    (if c then LLVM.SemVal.value a else LLVM.SemVal.value b) =
      LLVM.SemVal.value (if c then a else b) := by
  split <;> rfl

private theorem i199903_bv1_eq_zero (b : BitVec 1) (h : ¬ b = 1#1) : b = 0#1 := by
  cases b with
  | ofFin f =>
      cases f with
      | mk n hn =>
          have hn' : n = 0 ∨ n = 1 := by omega
          rcases hn' with rfl | rfl
          · rfl
          · simp [BitVec.ofNat] at h

private theorem i199903_assume_zero_option :
    (match LLVM.SemVal.value (0#1 : BitVec 1) with
    | LLVM.SemVal.value 1#1 => (some () : Option Unit)
    | _ => none) = none := by
  decide

private theorem i199903_bv1_cases (b : BitVec 1) : b = 0#1 ∨ b = 1#1 := by
  cases b with
  | ofFin f =>
      cases f with
      | mk n hn =>
          have hn' : n = 0 ∨ n = 1 := by omega
          rcases hn' with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl

private theorem i199903_value {w : Nat} (newvar_idx : BitVec w) (C : BitVec w) (isnull : BitVec 1)
    (hpre : (isnull ||| (BitVec.ofBool (newvar_idx != C))) = 1#1) :
    (if isnull = 1#1 then 1#1 else (BitVec.ofBool (newvar_idx == C))) = isnull := by
  rcases i199903_bv1_cases isnull with hnull | hnull
  · subst isnull
    simp [ofBool_one_iff] at hpre ⊢
    have hbeqfalse : (newvar_idx == C) = false := by
      rw [Bool.eq_false_iff]
      intro htrue
      exact hpre (beq_iff_eq.mp htrue)
    rw [hbeqfalse]
    exact BitVec.ofBool_false
  · subst isnull
    simp

set_option maxHeartbeats 4000000 in
theorem i199903_correct (w : Nat) : i199903_src w ⊑ i199903_tgt w := by
  intro V
  let newvar_idxVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨3, by simp⟩
  let CVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let isnullVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec 1) := ⟨1, by simp⟩
  let lenVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases hisnull : V isnullVar
  case poison =>
    simp [i199903_src, i199903_tgt, i199903_semval_bind_poison, i199903_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, isnullVar, hisnull, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value isnull =>
    change BitVec 1 at isnull
    cases hnewvar_idx : V newvar_idxVar
    case poison =>
      simp [i199903_src, i199903_tgt, i199903_semval_bind_poison, i199903_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, isnullVar, newvar_idxVar, hisnull, hnewvar_idx, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value newvar_idx =>
      change BitVec w at newvar_idx
      cases hC : V CVar
      case poison =>
        simp [i199903_src, i199903_tgt, i199903_semval_bind_poison, i199903_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, isnullVar, newvar_idxVar, CVar, hisnull, hnewvar_idx, hC, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      case value C =>
        change BitVec w at C
        by_cases hcond : (isnull ||| (BitVec.ofBool (newvar_idx != C))) = 1#1
        ·
          cases hlen : V lenVar with
          | poison =>
            simp [i199903_src, i199903_tgt, i199903_semval_bind_poison, i199903_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, isnullVar, newvar_idxVar, CVar, lenVar, hisnull, hnewvar_idx, hC, hcond, hlen, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  have hv := i199903_value (w := w) newvar_idx C isnull hcond
                  rcases i199903_bv1_cases isnull with h1c1 | h1c1 <;> simp_all [ofBool_one_iff, i199903_ite_semval_value, InstCombine.LLVM.Ty.width, LLVM.SemVal.bind_value, LLVM.SemVal.isRefinedBy_self, LLVM.SemVal.poison_isRefinedBy])
              · exact HVector.nil_isRefinedBy_nil)
          | value len =>
            change BitVec w at len
            simp [i199903_src, i199903_tgt, i199903_semval_bind_poison, i199903_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, isnullVar, newvar_idxVar, CVar, lenVar, hisnull, hnewvar_idx, hC, hcond, hlen, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  have hv := i199903_value (w := w) newvar_idx C isnull hcond
                  rcases i199903_bv1_cases isnull with h1c1 | h1c1 <;> simp_all [ofBool_one_iff, i199903_ite_semval_value, InstCombine.LLVM.Ty.width, LLVM.SemVal.bind_value, LLVM.SemVal.isRefinedBy_self, LLVM.SemVal.poison_isRefinedBy])
              · exact HVector.nil_isRefinedBy_nil)
        · simp [i199903_src, i199903_tgt, i199903_semval_bind_poison, i199903_ite_semval_value, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, isnullVar, newvar_idxVar, CVar, hisnull, hnewvar_idx, hC, i199903_bv1_eq_zero _ hcond, i199903_assume_zero_option, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.select, InstCombine.lift3, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
