import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def A_mul_div__minimal_src :=
  [llvm()| {
  llvm.func @A_mul_div__minimal_src(%x : i32, %C : i32) -> i1 {
  ^bb0(%x : i32, %C : i32):
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %nz = llvm.icmp "ne" %C, %c_i32_0 : i32
    llvm.assume %nz : i1
    %c_i32_m1 = llvm.mlir.constant(-1 : i32) : i32
    %lim = llvm.udiv %c_i32_m1, %C : i32
    %ov = llvm.icmp "ugt" %x, %lim : i32
    llvm.return %ov : i1
  }
  }]

def A_mul_div__minimal_tgt :=
  [llvm()| {
  llvm.func @A_mul_div__minimal_tgt(%x : i32, %C : i32) -> i1 {
  ^bb0(%x : i32, %C : i32):
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %nz = llvm.icmp "ne" %C, %c_i32_0 : i32
    llvm.assume %nz : i1
    %ov_p = llvm.mul %x, %C : i32
    %ov_q = llvm.udiv %ov_p, %C : i32
    %ov = llvm.icmp "ne" %ov_q, %x : i32
    llvm.return %ov : i1
  }
  }]

private theorem A_mul_div__minimal_semval_bind_poison {α β : Type} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl

private theorem A_mul_div__minimal_udiv_eq_if {w : Nat} {x y : BitVec w} :
    LLVM.udiv (LLVM.SemVal.value x) (LLVM.SemVal.value y) =
      (if y = 0#w then (.immediateUB : LLVM.IntWUB w)
       else (.value (x / y) : LLVM.IntWUB w)) := by
  simp [LLVM.udiv]

private theorem A_mul_div__minimal_udiv_poisonL {w : Nat} (y : LLVM.IntW w) (f : LLVM.ExactFlag) :
    LLVM.udiv (LLVM.SemVal.poison) y f = (.poison : LLVM.IntWUB w) := rfl

private theorem A_mul_div__minimal_udiv_poisonR {w : Nat} (x : LLVM.IntW w) (f : LLVM.ExactFlag) :
    LLVM.udiv x (LLVM.SemVal.poison) f = (.poison : LLVM.IntWUB w) := by
  cases x <;> rfl

private theorem A_mul_div__minimal_value (x : BitVec 32) (C : BitVec 32)
    (hpre : (C != 0#32) = true)
    (hub1 : ¬ (C = 0#32)) :
    ((4294967295#32 / C) <ᵤ x) = (((x * C) / C) != x) := by
  have _hpre := hpre
  have hcpos : 0 < C.toNat := by
    have hcne : C.toNat ≠ 0 := by
      intro hc
      apply hub1
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, hc]
    omega
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    simp [BitVec.ult, BitVec.toNat_udiv, BitVec.toNat_mul, BitVec.toNat_ofNat, bne,
      BitVec.toNat_eq] at h ⊢
    intro hq
    have hprod : 4294967296 ≤ x.toNat * C.toNat := by
      have hlt := (Nat.div_lt_iff_lt_mul hcpos).mp h
      omega
    have hle : x.toNat * C.toNat ≤ x.toNat * C.toNat % 4294967296 := by
      have hxlediv : x.toNat ≤ x.toNat * C.toNat % 4294967296 / C.toNat := by
        omega
      exact (Nat.le_div_iff_mul_le hcpos).mp hxlediv
    have hMpos : 0 < 4294967296 := by omega
    have hmodlt : x.toNat * C.toNat % 4294967296 < 4294967296 := Nat.mod_lt _ hMpos
    omega
  · intro h
    simp [BitVec.ult, BitVec.toNat_udiv, BitVec.toNat_mul, BitVec.toNat_ofNat, bne,
      BitVec.toNat_eq] at h ⊢
    by_contra hnot
    have hnle : x.toNat ≤ 4294967295 / C.toNat := by
      omega
    have hprodle : x.toNat * C.toNat ≤ 4294967295 :=
      (Nat.le_div_iff_mul_le hcpos).mp hnle
    have hprodlt : x.toNat * C.toNat < 4294967296 := by
      omega
    have hmod : x.toNat * C.toNat % 4294967296 = x.toNat * C.toNat :=
      Nat.mod_eq_of_lt hprodlt
    have hdiv : x.toNat * C.toNat / C.toNat = x.toNat := by
      rw [Nat.mul_comm]
      exact Nat.mul_div_right x.toNat hcpos
    apply h
    rw [hmod, hdiv]

set_option maxHeartbeats 4000000 in
theorem A_mul_div__minimal_correct : A_mul_div__minimal_src ⊑ A_mul_div__minimal_tgt := by
  intro V
  let xVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨1, by simp⟩
  let CVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32]) (InstCombine.LLVM.Ty.bitvec 32)
  cases hC : V CVar
  case poison =>
    simp [A_mul_div__minimal_src, A_mul_div__minimal_tgt, A_mul_div__minimal_semval_bind_poison, A_mul_div__minimal_udiv_eq_if, A_mul_div__minimal_udiv_poisonL, A_mul_div__minimal_udiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, hC, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, InstCombine.lift2UB, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C =>
    change BitVec 32 at C
    cases hcond : (C != 0#32)
    · simp [A_mul_div__minimal_src, A_mul_div__minimal_tgt, A_mul_div__minimal_semval_bind_poison, A_mul_div__minimal_udiv_eq_if, A_mul_div__minimal_udiv_poisonL, A_mul_div__minimal_udiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, hC, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, InstCombine.lift2UB, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    ·
      by_cases hub1 : C = 0#32
      ·
        first
        | (exfalso; simp_all; done)
        | (cases hxu : V xVar <;>
           simp [A_mul_div__minimal_src, A_mul_div__minimal_tgt, A_mul_div__minimal_semval_bind_poison, A_mul_div__minimal_udiv_eq_if, A_mul_div__minimal_udiv_poisonL, A_mul_div__minimal_udiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, xVar, hC, hcond, hxu, hub1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, InstCombine.lift2UB, LLVM.assume_] <;>
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
        | (simp [A_mul_div__minimal_src, A_mul_div__minimal_tgt, A_mul_div__minimal_semval_bind_poison, A_mul_div__minimal_udiv_eq_if, A_mul_div__minimal_udiv_poisonL, A_mul_div__minimal_udiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, hC, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, InstCombine.lift2UB, LLVM.assume_]
           simp [hub1]
           exact ImmediateUBOr.IsRefinedBy.bothValues (by
             constructor
             · exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
             · exact HVector.nil_isRefinedBy_nil))
      ·
        cases hx : V xVar with
        | poison =>
          simp [A_mul_div__minimal_src, A_mul_div__minimal_tgt, A_mul_div__minimal_semval_bind_poison, A_mul_div__minimal_udiv_eq_if, A_mul_div__minimal_udiv_poisonL, A_mul_div__minimal_udiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, xVar, hC, hcond, hub1, hx, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, InstCombine.lift2UB, LLVM.assume_]
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
          simp [A_mul_div__minimal_src, A_mul_div__minimal_tgt, A_mul_div__minimal_semval_bind_poison, A_mul_div__minimal_udiv_eq_if, A_mul_div__minimal_udiv_poisonL, A_mul_div__minimal_udiv_poisonR, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, CVar, xVar, hC, hcond, hub1, hx, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.mul, LLVM.mul?, InstCombine.lift2UB, LLVM.assume_]
          have hv := A_mul_div__minimal_value x C hcond hub1
          exact ImmediateUBOr.IsRefinedBy.bothValues (by
            constructor
            · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv] <;> rfl)
            · exact HVector.nil_isRefinedBy_nil)
