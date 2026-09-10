import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def E_ovf_vs_div__corpus1_src :=
  [llvm()| {
  llvm.func @E_ovf_vs_div__corpus1_src(%v0 : i32, %C1 : i32, %C2 : i32) -> i1 {
  ^bb0(%v0 : i32, %C1 : i32, %C2 : i32):
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %nz = llvm.icmp "ne" %C1, %c_i32_0 : i32
    llvm.assume %nz : i1
    %v3 = llvm.mul %v0, %C1 : i32
    %v4_p = llvm.mul %v0, %C1 : i32
    %v4_q = llvm.udiv %v4_p, %C1 : i32
    %v4 = llvm.icmp "ne" %v4_q, %v0 : i32
    %v5 = llvm.icmp "ugt" %v3, %C2 : i32
    %v6 = llvm.or %v4, %v5 : i1
    llvm.return %v6 : i1
  }
  }]

def E_ovf_vs_div__corpus1_tgt :=
  [llvm()| {
  llvm.func @E_ovf_vs_div__corpus1_tgt(%v0 : i32, %C1 : i32, %C2 : i32) -> i1 {
  ^bb0(%v0 : i32, %C1 : i32, %C2 : i32):
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %nz = llvm.icmp "ne" %C1, %c_i32_0 : i32
    llvm.assume %nz : i1
    %c3 = llvm.udiv %C2, %C1 : i32
    %r = llvm.icmp "ugt" %v0, %c3 : i32
    llvm.return %r : i1
  }
  }]

private theorem E_ovf_vs_div__corpus1_bv1_one_and (x : BitVec 1) : 1#1 &&& x = x := by
  have h : (1#1 : BitVec 1) = BitVec.allOnes 1 := rfl
  rw [h, BitVec.allOnes_and]

private theorem E_ovf_vs_div__corpus1_bv1_and_one (x : BitVec 1) : x &&& 1#1 = x := by
  have h : (1#1 : BitVec 1) = BitVec.allOnes 1 := rfl
  rw [h, BitVec.and_allOnes]

private theorem E_ovf_vs_div__corpus1_bv1_one_or (x : BitVec 1) : 1#1 ||| x = 1#1 := by
  have h : (1#1 : BitVec 1) = BitVec.allOnes 1 := rfl
  rw [h, BitVec.allOnes_or]

private theorem E_ovf_vs_div__corpus1_bv1_or_one (x : BitVec 1) : x ||| 1#1 = 1#1 := by
  have h : (1#1 : BitVec 1) = BitVec.allOnes 1 := rfl
  rw [h, BitVec.or_allOnes]

private theorem E_ovf_vs_div__corpus1_semval_bind_poison {α β : Type} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl

private theorem E_ovf_vs_div__corpus1_udiv_eq_if {w : Nat} {x y : BitVec w} :
    LLVM.udiv (LLVM.SemVal.value x) (LLVM.SemVal.value y) =
      (if y = 0#w then (.immediateUB : LLVM.IntWUB w)
       else (.value (x / y) : LLVM.IntWUB w)) := by
  simp [LLVM.udiv]

private theorem E_ovf_vs_div__corpus1_udiv_poisonL {w : Nat} (y : LLVM.IntW w) (f : LLVM.ExactFlag) :
    LLVM.udiv (LLVM.SemVal.poison) y f = (.poison : LLVM.IntWUB w) := rfl

private theorem E_ovf_vs_div__corpus1_udiv_poisonR {w : Nat} (x : LLVM.IntW w) (f : LLVM.ExactFlag) :
    LLVM.udiv x (LLVM.SemVal.poison) f = (.poison : LLVM.IntWUB w) := by
  cases x <;> rfl

private theorem E_ovf_vs_div__corpus1_value (v0 : BitVec 32) (C1 : BitVec 32) (C2 : BitVec 32)
    (hpre : (C1 != 0#32) = true)
    (hub1 : ¬ (C1 = 0#32)) :
    ((((v0 * C1) / C1) != v0) || (C2 <ᵤ (v0 * C1))) = ((C2 / C1) <ᵤ v0) := by
  have _ : C1 ≠ 0#32 := (bne_iff_ne).mp hpre
  let a := v0.toNat
  let b := C1.toNat
  let c := C2.toNat
  let M := 2 ^ 32
  have hb_ne : b ≠ 0 := by
    intro hb0
    apply hub1
    apply BitVec.eq_of_toNat_eq
    simpa [b] using hb0
  have hb : 0 < b := Nat.pos_of_ne_zero hb_ne
  have hM : 0 < M := by simp [M]
  have hcM : c < M := by simpa [c, M] using BitVec.isLt C2
  have hkey : ((((a * b % M) / b ≠ a) ∨ c < a * b % M) ↔ c / b < a) := by
    by_cases hp : a * b < M
    · have hmod : a * b % M = a * b := Nat.mod_eq_of_lt hp
      have hdiv : (a * b % M) / b = a := by
        rw [hmod]
        exact Nat.mul_div_left a hb
      have hiff : c / b < a ↔ c < a * b := Nat.div_lt_iff_lt_mul hb
      constructor
      · intro h
        rcases h with hneq | hlt
        · exact False.elim (hneq hdiv)
        · exact hiff.mpr (by simpa [hmod] using hlt)
      · intro hr
        right
        exact by simpa [hmod] using hiff.mp hr
    · have hMp : M ≤ a * b := Nat.le_of_not_gt hp
      have hlt_prod : a * b % M < a * b := Nat.lt_of_lt_of_le (Nat.mod_lt _ hM) hMp
      have hdiv_lt : (a * b % M) / b < a := (Nat.div_lt_iff_lt_mul hb).mpr hlt_prod
      have hneq : (a * b % M) / b ≠ a := Nat.ne_of_lt hdiv_lt
      have hr : c / b < a :=
        (Nat.div_lt_iff_lt_mul hb).mpr (Nat.lt_of_lt_of_le hcM hMp)
      constructor
      · intro _
        exact hr
      · intro _
        exact Or.inl hneq
  apply Bool.eq_iff_iff.mpr
  simpa [Bool.or_eq_true, bne_iff_ne, BitVec.ult_iff_toNat_lt, BitVec.toNat_udiv,
    BitVec.toNat_mul, BitVec.toNat_eq, a, b, c, M] using hkey

set_option maxHeartbeats 4000000 in
theorem E_ovf_vs_div__corpus1_correct : E_ovf_vs_div__corpus1_src ⊑ E_ovf_vs_div__corpus1_tgt := by
  intro V
  let v0Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨2, by simp⟩
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨1, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]) (InstCombine.LLVM.Ty.bitvec 32)
  cases hC1 : V C1Var
  case poison =>
    simp [E_ovf_vs_div__corpus1_src, E_ovf_vs_div__corpus1_tgt, E_ovf_vs_div__corpus1_semval_bind_poison, E_ovf_vs_div__corpus1_udiv_eq_if, E_ovf_vs_div__corpus1_udiv_poisonL, E_ovf_vs_div__corpus1_udiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, LLVM.or, LLVM.or?, InstCombine.lift2UB, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C1 =>
    change BitVec 32 at C1
    cases hcond : (C1 != 0#32)
    · simp [E_ovf_vs_div__corpus1_src, E_ovf_vs_div__corpus1_tgt, E_ovf_vs_div__corpus1_semval_bind_poison, E_ovf_vs_div__corpus1_udiv_eq_if, E_ovf_vs_div__corpus1_udiv_poisonL, E_ovf_vs_div__corpus1_udiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, LLVM.or, LLVM.or?, InstCombine.lift2UB, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    ·
      by_cases hub1 : C1 = 0#32
      ·
        first
        | (exfalso; simp_all; done)
        | (cases hv0u : V v0Var <;>
           cases hC2u : V C2Var <;>
           simp [E_ovf_vs_div__corpus1_src, E_ovf_vs_div__corpus1_tgt, E_ovf_vs_div__corpus1_semval_bind_poison, E_ovf_vs_div__corpus1_udiv_eq_if, E_ovf_vs_div__corpus1_udiv_poisonL, E_ovf_vs_div__corpus1_udiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, v0Var, C2Var, hC1, hcond, hv0u, hC2u, hub1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, LLVM.or, LLVM.or?, InstCombine.lift2UB, LLVM.assume_] <;>
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
        | (simp [E_ovf_vs_div__corpus1_src, E_ovf_vs_div__corpus1_tgt, E_ovf_vs_div__corpus1_semval_bind_poison, E_ovf_vs_div__corpus1_udiv_eq_if, E_ovf_vs_div__corpus1_udiv_poisonL, E_ovf_vs_div__corpus1_udiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, hC1, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, LLVM.or, LLVM.or?, InstCombine.lift2UB, LLVM.assume_]
           simp [hub1]
           exact ImmediateUBOr.IsRefinedBy.bothValues (by
             constructor
             · exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
             · exact HVector.nil_isRefinedBy_nil))
      ·
        cases hv0 : V v0Var with
        | poison =>
          cases hC2 : V C2Var with
          | poison =>
            simp [E_ovf_vs_div__corpus1_src, E_ovf_vs_div__corpus1_tgt, E_ovf_vs_div__corpus1_semval_bind_poison, E_ovf_vs_div__corpus1_udiv_eq_if, E_ovf_vs_div__corpus1_udiv_poisonL, E_ovf_vs_div__corpus1_udiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, v0Var, C2Var, hC1, hcond, hub1, hv0, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, LLVM.or, LLVM.or?, InstCombine.lift2UB, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  first
                  | exact LLVM.SemVal.poison_isRefinedBy _
                  | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                  | simp [LLVM.IntW.instRefinement])
              · exact HVector.nil_isRefinedBy_nil)
          | value C2 =>
            change BitVec 32 at C2
            simp [E_ovf_vs_div__corpus1_src, E_ovf_vs_div__corpus1_tgt, E_ovf_vs_div__corpus1_semval_bind_poison, E_ovf_vs_div__corpus1_udiv_eq_if, E_ovf_vs_div__corpus1_udiv_poisonL, E_ovf_vs_div__corpus1_udiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, v0Var, C2Var, hC1, hcond, hub1, hv0, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, LLVM.or, LLVM.or?, InstCombine.lift2UB, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  first
                  | exact LLVM.SemVal.poison_isRefinedBy _
                  | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                  | simp [LLVM.IntW.instRefinement])
              · exact HVector.nil_isRefinedBy_nil)
        | value v0 =>
          change BitVec 32 at v0
          cases hC2 : V C2Var with
          | poison =>
            simp [E_ovf_vs_div__corpus1_src, E_ovf_vs_div__corpus1_tgt, E_ovf_vs_div__corpus1_semval_bind_poison, E_ovf_vs_div__corpus1_udiv_eq_if, E_ovf_vs_div__corpus1_udiv_poisonL, E_ovf_vs_div__corpus1_udiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, v0Var, C2Var, hC1, hcond, hub1, hv0, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, LLVM.or, LLVM.or?, InstCombine.lift2UB, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                  first
                  | exact LLVM.SemVal.poison_isRefinedBy _
                  | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
                  | simp [LLVM.IntW.instRefinement])
              · exact HVector.nil_isRefinedBy_nil)
          | value C2 =>
            change BitVec 32 at C2
            simp [E_ovf_vs_div__corpus1_src, E_ovf_vs_div__corpus1_tgt, E_ovf_vs_div__corpus1_semval_bind_poison, E_ovf_vs_div__corpus1_udiv_eq_if, E_ovf_vs_div__corpus1_udiv_poisonL, E_ovf_vs_div__corpus1_udiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C1Var, v0Var, C2Var, hC1, hcond, hub1, hv0, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, LLVM.or, LLVM.or?, InstCombine.lift2UB, LLVM.assume_]
            have hv := E_ovf_vs_div__corpus1_value v0 C1 C2 hcond hub1
            exact ImmediateUBOr.IsRefinedBy.bothValues (by
              constructor
              · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv, E_ovf_vs_div__corpus1_bv1_one_and, E_ovf_vs_div__corpus1_bv1_and_one, E_ovf_vs_div__corpus1_bv1_one_or, E_ovf_vs_div__corpus1_bv1_or_one] <;> rfl)
              · exact HVector.nil_isRefinedBy_nil)
