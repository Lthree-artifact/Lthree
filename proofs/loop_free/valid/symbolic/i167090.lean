import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def i167090_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167090_src(%i16arg0 : _, %C1 : _, %C2 : _, %C3 : _) -> _ {
  ^bb0(%i16arg0 : _, %C1 : _, %C2 : _, %C3 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c12 = llvm.add %C1, %C2 : _
    %cond_nuw1 = llvm.icmp "uge" %c12, %C1 : _
    %cond_c2_pos = llvm.icmp "sge" %C2, %zero : _
    %cond_c12_c1 = llvm.icmp "sge" %c12, %C1 : _
    %cond_nsw1 = llvm.icmp "eq" %cond_c2_pos, %cond_c12_c1 : i1
    %a1 = llvm.and %cond_nuw1, %cond_nsw1 : i1
    %c123 = llvm.add %c12, %C3 : _
    %cond_nuw2 = llvm.icmp "uge" %c123, %c12 : _
    %cond_c3_pos = llvm.icmp "sge" %C3, %zero : _
    %cond_c123_c12 = llvm.icmp "sge" %c123, %c12 : _
    %cond_nsw2 = llvm.icmp "eq" %cond_c3_pos, %cond_c123_c12 : i1
    %a2 = llvm.and %cond_nuw2, %cond_nsw2 : i1
    %a3 = llvm.and %a1, %a2 : i1
    llvm.assume %a3 : i1
    %umin0 = llvm.icmp "ult" %i16arg0, %C1 : _
    %v0 = llvm.select %umin0, %i16arg0, %C1 : _
    %v1 = llvm.add %v0, %C2 : _
    %umin1 = llvm.icmp "ult" %i16arg0, %v1 : _
    %v2 = llvm.select %umin1, %i16arg0, %v1 : _
    %v3 = llvm.add %v2, %C3 : _
    %umin2 = llvm.icmp "ult" %i16arg0, %v3 : _
    %v4 = llvm.select %umin2, %i16arg0, %v3 : _
    llvm.return %v4 : _
  }
  }]

def i167090_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167090_tgt(%i16arg0 : _, %C1 : _, %C2 : _, %C3 : _) -> _ {
  ^bb0(%i16arg0 : _, %C1 : _, %C2 : _, %C3 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c12 = llvm.add %C1, %C2 : _
    %cond_nuw1 = llvm.icmp "uge" %c12, %C1 : _
    %cond_c2_pos = llvm.icmp "sge" %C2, %zero : _
    %cond_c12_c1 = llvm.icmp "sge" %c12, %C1 : _
    %cond_nsw1 = llvm.icmp "eq" %cond_c2_pos, %cond_c12_c1 : i1
    %a1 = llvm.and %cond_nuw1, %cond_nsw1 : i1
    %c123 = llvm.add %c12, %C3 : _
    %cond_nuw2 = llvm.icmp "uge" %c123, %c12 : _
    %cond_c3_pos = llvm.icmp "sge" %C3, %zero : _
    %cond_c123_c12 = llvm.icmp "sge" %c123, %c12 : _
    %cond_nsw2 = llvm.icmp "eq" %cond_c3_pos, %cond_c123_c12 : i1
    %a2 = llvm.and %cond_nuw2, %cond_nsw2 : i1
    %a3 = llvm.and %a1, %a2 : i1
    llvm.assume %a3 : i1
    %c12_tgt = llvm.add %C1, %C2 : _
    %c123_tgt = llvm.add %c12_tgt, %C3 : _
    %umin0 = llvm.icmp "ult" %i16arg0, %c123_tgt : _
    %v0 = llvm.select %umin0, %i16arg0, %c123_tgt : _
    llvm.return %v0 : _
  }
  }]

private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by
  cases b <;> simp

private theorem i167090_value {w : Nat} (i16arg0 : BitVec w) (C1 : BitVec w) (C2 : BitVec w) (C3 : BitVec w)
    (hpre : (((C1 ≤ᵤ (C1 + C2)) && (BitVec.ofBool (0#w ≤ₛ C2) == BitVec.ofBool (C1 ≤ₛ (C1 + C2)))) && (((C1 + C2) ≤ᵤ ((C1 + C2) + C3)) && (BitVec.ofBool (0#w ≤ₛ C3) == BitVec.ofBool ((C1 + C2) ≤ₛ ((C1 + C2) + C3))))) = true) :
    (if (i16arg0 <ᵤ ((if (i16arg0 <ᵤ ((if (i16arg0 <ᵤ C1) = true then i16arg0 else C1) + C2)) = true then i16arg0 else ((if (i16arg0 <ᵤ C1) = true then i16arg0 else C1) + C2)) + C3)) = true then i16arg0 else ((if (i16arg0 <ᵤ ((if (i16arg0 <ᵤ C1) = true then i16arg0 else C1) + C2)) = true then i16arg0 else ((if (i16arg0 <ᵤ C1) = true then i16arg0 else C1) + C2)) + C3)) = (if (i16arg0 <ᵤ ((C1 + C2) + C3)) = true then i16arg0 else ((C1 + C2) + C3)) := by
  have add_lt_of_le_mod : ∀ {a b n : Nat}, a < n → b < n → a ≤ (a + b) % n → a + b < n := by
    intro a b n ha hb h
    by_contra hnot
    rw [Nat.not_lt] at hnot
    have hmod_eq : (a + b) % n = (a + b - n) % n := Nat.mod_eq_sub_mod hnot
    have hsub_lt_n : a + b - n < n := by omega
    have hmod_sub : (a + b - n) % n = a + b - n := Nat.mod_eq_of_lt hsub_lt_n
    have hsub_lt_a : a + b - n < a := by omega
    have : (a + b) % n < a := by
      rw [hmod_eq, hmod_sub]
      exact hsub_lt_a
    omega
  have nat_identity : ∀ a b c d : Nat,
      (if a < (if a < (if a < b then a else b) + c then a else (if a < b then a else b) + c) + d then a else (if a < (if a < b then a else b) + c then a else (if a < b then a else b) + c) + d) =
        (if a < b + c + d then a else b + c + d) := by
    intro a b c d
    split_ifs <;> omega
  simp only [Bool.and_eq_true] at hpre
  rcases hpre with ⟨⟨h12, _hnsw1⟩, ⟨h123, _hnsw2⟩⟩
  rw [BitVec.ule_eq_decide, decide_eq_true_eq] at h12 h123
  have h12mod : C1.toNat ≤ (C1.toNat + C2.toNat) % 2 ^ w := by
    simpa [BitVec.toNat_add] using h12
  have h12lt : C1.toNat + C2.toNat < 2 ^ w :=
    add_lt_of_le_mod C1.isLt C2.isLt h12mod
  have h12nat : (C1 + C2).toNat = C1.toNat + C2.toNat :=
    BitVec.toNat_add_of_lt h12lt
  have h123mod : (C1 + C2).toNat ≤ ((C1 + C2).toNat + C3.toNat) % 2 ^ w := by
    simpa [BitVec.toNat_add] using h123
  have h123lt : (C1 + C2).toNat + C3.toNat < 2 ^ w :=
    add_lt_of_le_mod (C1 + C2).isLt C3.isLt h123mod
  have h123nat : (C1 + C2 + C3).toNat = (C1 + C2).toNat + C3.toNat :=
    BitVec.toNat_add_of_lt h123lt
  have hsum_nat : (C1 + C2 + C3).toNat = C1.toNat + C2.toNat + C3.toNat := by
    rw [h123nat, h12nat]
  let m0 : BitVec w := if (i16arg0 <ᵤ C1) = true then i16arg0 else C1
  let m1 : BitVec w := if (i16arg0 <ᵤ (m0 + C2)) = true then i16arg0 else m0 + C2
  let sum : BitVec w := C1 + C2 + C3
  change (if (i16arg0 <ᵤ (m1 + C3)) = true then i16arg0 else m1 + C3) =
    (if (i16arg0 <ᵤ sum) = true then i16arg0 else sum)
  have hm0le : m0.toNat ≤ C1.toNat := by
    dsimp [m0]
    rw [BitVec.ult_eq_decide]
    simp only [decide_eq_true_eq, apply_ite]
    split_ifs with h
    · exact Nat.le_of_lt h
    · exact Nat.le_refl C1.toNat
  have hm0add_lt : m0.toNat + C2.toNat < 2 ^ w := by
    omega
  have hm0add_nat : (m0 + C2).toNat = m0.toNat + C2.toNat :=
    BitVec.toNat_add_of_lt hm0add_lt
  have hm0add_le_c12 : (m0 + C2).toNat ≤ (C1 + C2).toNat := by
    rw [hm0add_nat, h12nat]
    omega
  have hm1le : m1.toNat ≤ (C1 + C2).toNat := by
    dsimp [m1]
    rw [BitVec.ult_eq_decide]
    simp only [decide_eq_true_eq, apply_ite]
    split_ifs with h
    · exact Nat.le_trans (Nat.le_of_lt h) hm0add_le_c12
    · exact hm0add_le_c12
  have hm1add_lt : m1.toNat + C3.toNat < 2 ^ w := by
    omega
  have hm1add_nat : (m1 + C3).toNat = m1.toNat + C3.toNat :=
    BitVec.toNat_add_of_lt hm1add_lt
  apply BitVec.eq_of_toNat_eq
  dsimp [sum]
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq, apply_ite]
  rw [hm1add_nat, hsum_nat]
  dsimp [m1]
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq, apply_ite]
  rw [hm0add_nat]
  dsimp [m0]
  simp only [BitVec.ult_eq_decide, decide_eq_true_eq, apply_ite]
  by_cases hR : i16arg0.toNat < C1.toNat + C2.toNat + C3.toNat
  · simpa [hR] using nat_identity i16arg0.toNat C1.toNat C2.toNat C3.toNat
  · simpa [hR] using nat_identity i16arg0.toNat C1.toNat C2.toNat C3.toNat

set_option maxHeartbeats 4000000 in
theorem i167090_correct (w : Nat) : i167090_src w ⊑ i167090_tgt w := by
  intro V
  let i16arg0Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨3, by simp⟩
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let C3Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases hC1 : V C1Var
  case poison =>
    simp [i167090_src, i167090_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C1 =>
    change BitVec w at C1
    cases hC2 : V C2Var
    case poison =>
      simp [i167090_src, i167090_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, hC1, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value C2 =>
      change BitVec w at C2
      cases hC3 : V C3Var
      case poison =>
        simp [i167090_src, i167090_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C3Var, hC1, hC2, hC3, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      case value C3 =>
        change BitVec w at C3
        cases hcond : (((C1 ≤ᵤ (C1 + C2)) && (BitVec.ofBool (0#w ≤ₛ C2) == BitVec.ofBool (C1 ≤ₛ (C1 + C2)))) && (((C1 + C2) ≤ᵤ ((C1 + C2) + C3)) && (BitVec.ofBool (0#w ≤ₛ C3) == BitVec.ofBool ((C1 + C2) ≤ₛ ((C1 + C2) + C3)))))
        · simp [i167090_src, i167090_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C3Var, hC1, hC2, hC3, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        ·
          cases hi16arg0 : V i16arg0Var
          case poison =>
            simp [i167090_src, i167090_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C3Var, i16arg0Var, hC1, hC2, hC3, hcond, hi16arg0, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  first
                  | exact LLVM.SemVal.poison_isRefinedBy _
                  | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                  | simp [LLVM.IntW.instRefinement])
              · exact HVector.nil_isRefinedBy_nil)
          case value i16arg0 =>
            change BitVec w at i16arg0
            simp [i167090_src, i167090_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, C2Var, C3Var, i16arg0Var, hC1, hC2, hC3, hcond, hi16arg0, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.select, InstCombine.lift3, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  have hv := i167090_value (w := w) i16arg0 C1 C2 C3 hcond
                  by_cases hS1 : (i16arg0 <ᵤ ((if (i16arg0 <ᵤ ((if (i16arg0 <ᵤ C1) = true then i16arg0 else C1) + C2)) = true then i16arg0 else ((if (i16arg0 <ᵤ C1) = true then i16arg0 else C1) + C2)) + C3)) = true <;> by_cases hS2 : (i16arg0 <ᵤ ((if (i16arg0 <ᵤ C1) = true then i16arg0 else C1) + C2)) = true <;> by_cases hS3 : (i16arg0 <ᵤ C1) = true <;> by_cases hS4 : (i16arg0 <ᵤ ((C1 + C2) + C3)) = true <;> simp_all [InstCombine.LLVM.Ty.width, ofBool_one_iff, LLVM.SemVal.isRefinedBy_self])
              · exact HVector.nil_isRefinedBy_nil)
