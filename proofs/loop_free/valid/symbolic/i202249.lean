import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def i202249_src (w1 : Nat) (_h : 2 ≤ w1) :=
  [llvm(w1)| {
  llvm.func @i202249_src(%V : w1, %C1 : w1, %C2 : w1) -> w1 {
  ^bb0(%V : w1, %C1 : w1, %C2 : w1):
    %bw = llvm.mlir.constant(w1 : w1) : w1
    %one = llvm.mlir.constant(1 : w1) : w1
    %zero = llvm.mlir.constant(0 : w1) : w1
    %cm1 = llvm.mlir.constant(-1 : w1) : w1
    %sub = llvm.sub %bw, %one : w1
    %signbit = llvm.shl %one, %sub : w1
    %cond2_1 = llvm.icmp "eq" %C2, %zero : w1
    %cond2_2 = llvm.icmp "eq" %C2, %signbit : w1
    %cond2 = llvm.or %cond2_1, %cond2_2 : i1
    llvm.assume %cond2 : i1
    %notC2 = llvm.xor %C2, %cm1 : w1
    %v_and = llvm.and %V, %notC2 : w1
    %cond3 = llvm.icmp "eq" %v_and, %C1 : w1
    llvm.assume %cond3 : i1
    %b = llvm.sub %C1, %V : w1
    llvm.return %b : w1
  }
  }]

def i202249_tgt (w1 : Nat) (_h : 2 ≤ w1) :=
  [llvm(w1)| {
  llvm.func @i202249_tgt(%V : w1, %C1 : w1, %C2 : w1) -> w1 {
  ^bb0(%V : w1, %C1 : w1, %C2 : w1):
    %bw = llvm.mlir.constant(w1 : w1) : w1
    %one = llvm.mlir.constant(1 : w1) : w1
    %zero = llvm.mlir.constant(0 : w1) : w1
    %cm1 = llvm.mlir.constant(-1 : w1) : w1
    %sub = llvm.sub %bw, %one : w1
    %signbit = llvm.shl %one, %sub : w1
    %cond2_1 = llvm.icmp "eq" %C2, %zero : w1
    %cond2_2 = llvm.icmp "eq" %C2, %signbit : w1
    %cond2 = llvm.or %cond2_1, %cond2_2 : i1
    llvm.assume %cond2 : i1
    %notC2 = llvm.xor %C2, %cm1 : w1
    %v_and = llvm.and %V, %notC2 : w1
    %cond3 = llvm.icmp "eq" %v_and, %C1 : w1
    llvm.assume %cond3 : i1
    %a = llvm.and %V, %C2 : w1
    llvm.return %a : w1
  }
  }]

private theorem i202249_semval_bind_poison {α β : Type} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl

private theorem i202249_value {w1 : Nat} (_h : 2 ≤ w1) (Vv : BitVec w1) (C1 : BitVec w1) (C2 : BitVec w1)
    (hsh1 : ¬ (BitVec.ofNat w1 w1 ≤ ((BitVec.ofNat w1 w1) - 1#w1)))
    (hpre1 : ((C2 == 0#w1) || (C2 == (1#w1 <<< ((2 ^ w1 - 1 % 2 ^ w1 + w1) % 2 ^ w1)))) = true)
    (hpre2 : ((Vv &&& (C2 ^^^ (BitVec.ofInt w1 (-1)))) == C1) = true) :
    (C1 - Vv) = (Vv &&& C2) := by
  simp at hpre1 hpre2
  have _ := hsh1
  have hones : BitVec.ofInt w1 (-1) = BitVec.allOnes w1 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt, BitVec.toNat_allOnes]
    change (Int.negSucc 0 % ↑(2 ^ w1)).toNat = 2 ^ w1 - 1
    rw [Int.negSucc_emod]
    · simp
      have hcast : (↑(2 ^ w1) : Int).toNat = 2 ^ w1 := Int.toNat_natCast (2 ^ w1)
      rw [hcast]
    · exact_mod_cast (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ w1)
  have hshift : (2 ^ w1 - 1 % 2 ^ w1 + w1) % 2 ^ w1 = w1 - 1 := by
    have h1lt : 1 < 2 ^ w1 := by
      have hwne : w1 ≠ 0 := by omega
      exact Nat.one_lt_two_pow hwne
    have hmod1 : 1 % 2 ^ w1 = 1 := Nat.mod_eq_of_lt h1lt
    rw [hmod1]
    have hge : 2 ^ w1 ≤ 2 ^ w1 - 1 + w1 := by omega
    rw [Nat.mod_eq_sub_mod hge]
    have hsub : 2 ^ w1 - 1 + w1 - 2 ^ w1 = w1 - 1 := by omega
    rw [hsub]
    exact Nat.mod_eq_of_lt (by
      have hwlt : w1 < 2 ^ w1 := Nat.lt_two_pow_self
      omega)
  rcases hpre1 with hC2 | hC2
  · subst C2
    rw [hones, BitVec.zero_xor, BitVec.and_allOnes] at hpre2
    subst C1
    rw [BitVec.sub_self, BitVec.and_zero]
  · subst C2
    rw [hshift, hones, BitVec.xor_allOnes] at hpre2
    subst C1
    rw [hshift]
    by_cases hm : Vv.msb = true
    · have hright : Vv &&& (1#w1 <<< (w1 - 1)) = (1#w1 <<< (w1 - 1)) := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        rw [BitVec.getLsbD_and]
        have hmask : (1#w1 <<< (w1 - 1)).getLsbD i = decide (i = w1 - 1) := by
          rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
          by_cases hiw : i = w1 - 1
          · subst i
            simp
            omega
          · simp [hi, hiw]
            omega
        rw [hmask]
        by_cases hiw : i = w1 - 1
        · subst i
          rw [BitVec.msb_eq_getLsbD_last] at hm
          simp [hm]
        · simp [hiw]
      have hle : 2 ^ (w1 - 1) ≤ Vv.toNat := by
        rw [BitVec.msb_eq_decide] at hm
        simp at hm
        exact hm
      have hN : 2 ^ w1 = 2 ^ (w1 - 1) * 2 := by
        have hw : w1 = (w1 - 1) + 1 := by omega
        conv_lhs => rw [hw]
        rw [Nat.pow_succ]
      have hxlt : Vv.toNat - 2 ^ (w1 - 1) < 2 ^ (w1 - 1) := by
        have hvlt : Vv.toNat < 2 ^ w1 := BitVec.isLt Vv
        rw [hN] at hvlt
        omega
      have hlow :
          Vv &&& ~~~(1#w1 <<< (w1 - 1)) =
            BitVec.ofNat w1 (Vv.toNat - 2 ^ (w1 - 1)) := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
        have hmask : (1#w1 <<< (w1 - 1)).getLsbD i = decide (i = w1 - 1) := by
          rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
          by_cases hiw : i = w1 - 1
          · subst i
            simp
            omega
          · simp [hi, hiw]
            omega
        rw [hmask]
        simp [hi]
        by_cases hiw : i = w1 - 1
        · subst i
          have htb : (Vv.toNat - 2 ^ (w1 - 1)).testBit (w1 - 1) = false :=
            Nat.testBit_lt_two_pow hxlt
          rw [BitVec.msb_eq_getLsbD_last] at hm
          simp [htb]
        · have hik : i < w1 - 1 := by omega
          have hxmod : Vv.toNat % 2 ^ (w1 - 1) = Vv.toNat - 2 ^ (w1 - 1) := by
            rw [Nat.mod_eq_sub_mod hle]
            exact Nat.mod_eq_of_lt hxlt
          have htb := Nat.testBit_mod_two_pow Vv.toNat (w1 - 1) i
          rw [hxmod] at htb
          simp [hik] at htb
          rw [BitVec.getElem_eq_testBit_toNat Vv i hi]
          simp [hiw]
          exact htb.symm
      rw [hright, hlow]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub]
      have hmaskToNat : (1#w1 <<< (w1 - 1)).toNat = 2 ^ (w1 - 1) := by
        rw [BitVec.toNat_shiftLeft]
        simp [BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        have hlt : 2 ^ (w1 - 1) < 2 ^ w1 := by
          rw [hN]
          omega
        exact Nat.mod_eq_of_lt hlt
      rw [hmaskToNat, BitVec.toNat_ofNat]
      have hxmod : (Vv.toNat - 2 ^ (w1 - 1)) % 2 ^ w1 =
          Vv.toNat - 2 ^ (w1 - 1) := by
        exact Nat.mod_eq_of_lt (by
          rw [hN]
          omega)
      rw [hxmod]
      have hvlt : Vv.toNat < 2 ^ w1 := BitVec.isLt Vv
      have hcalc :
          2 ^ w1 - Vv.toNat + (Vv.toNat - 2 ^ (w1 - 1)) = 2 ^ (w1 - 1) := by
        rw [hN] at hvlt ⊢
        omega
      rw [hcalc]
      exact Nat.mod_eq_of_lt (by
        rw [hN]
        omega)
    · have hmfalse : Vv.msb = false := by
        cases hmsb : Vv.msb <;> simp [hmsb] at hm ⊢
      have hright : Vv &&& (1#w1 <<< (w1 - 1)) = 0#w1 := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        rw [BitVec.getLsbD_and, BitVec.getLsbD_zero]
        have hmask : (1#w1 <<< (w1 - 1)).getLsbD i = decide (i = w1 - 1) := by
          rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
          by_cases hiw : i = w1 - 1
          · subst i
            simp
            omega
          · simp [hi, hiw]
            omega
        rw [hmask]
        by_cases hiw : i = w1 - 1
        · subst i
          rw [BitVec.msb_eq_getLsbD_last] at hmfalse
          simp [hmfalse]
        · simp [hiw]
      have hlow : Vv &&& ~~~(1#w1 <<< (w1 - 1)) = Vv := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        rw [BitVec.getLsbD_and, BitVec.getLsbD_not]
        have hmask : (1#w1 <<< (w1 - 1)).getLsbD i = decide (i = w1 - 1) := by
          rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
          by_cases hiw : i = w1 - 1
          · subst i
            simp
            omega
          · simp [hi, hiw]
            omega
        rw [hmask]
        by_cases hiw : i = w1 - 1
        · subst i
          rw [BitVec.msb_eq_getLsbD_last] at hmfalse
          simp [hmfalse]
        · simp [hi, hiw]
      rw [hright, hlow, BitVec.sub_self]

set_option maxHeartbeats 4000000 in
theorem i202249_correct (w1 : Nat) (_h : 2 ≤ w1) : i202249_src w1 _h ⊑ i202249_tgt w1 _h := by
  intro V
  let VVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w1, InstCombine.LLVM.Ty.bitvec w1, InstCombine.LLVM.Ty.bitvec w1]).Var (InstCombine.LLVM.Ty.bitvec w1) := ⟨2, by simp⟩
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w1, InstCombine.LLVM.Ty.bitvec w1, InstCombine.LLVM.Ty.bitvec w1]).Var (InstCombine.LLVM.Ty.bitvec w1) := ⟨1, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w1, InstCombine.LLVM.Ty.bitvec w1, InstCombine.LLVM.Ty.bitvec w1]).Var (InstCombine.LLVM.Ty.bitvec w1) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w1, InstCombine.LLVM.Ty.bitvec w1]) (InstCombine.LLVM.Ty.bitvec w1)
  cases hC2 : V C2Var
  case poison =>
    simp [i202249_src, i202249_tgt, i202249_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.xor, LLVM.xor?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value C2 =>
    change BitVec w1 at C2
    by_cases hsh1 : BitVec.ofNat w1 w1 ≤ ((BitVec.ofNat w1 w1) - 1#w1)
    ·
      simp [i202249_src, i202249_tgt, i202249_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, hC2, hsh1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.xor, LLVM.xor?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    ·
      cases hcond1 : ((C2 == 0#w1) || (C2 == (1#w1 <<< ((2 ^ w1 - 1 % 2 ^ w1 + w1) % 2 ^ w1))))
      · simp [i202249_src, i202249_tgt, i202249_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, hC2, hsh1, hcond1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.xor, LLVM.xor?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      ·
        cases hV : V VVar with
        | poison =>
          simp [i202249_src, i202249_tgt, i202249_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, VVar, hC2, hsh1, hcond1, hV, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.xor, LLVM.xor?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        | value Vv =>
          change BitVec w1 at Vv
          cases hC1 : V C1Var with
          | poison =>
            simp [i202249_src, i202249_tgt, i202249_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, VVar, C1Var, hC2, hsh1, hcond1, hV, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.xor, LLVM.xor?, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
          | value C1 =>
            change BitVec w1 at C1
            cases hcond2 : ((Vv &&& (C2 ^^^ (BitVec.ofInt w1 (-1)))) == C1)
            · simp [i202249_src, i202249_tgt, i202249_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, VVar, C1Var, hC2, hsh1, hcond1, hV, hC1, hcond2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.xor, LLVM.xor?, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
            ·
              simp [i202249_src, i202249_tgt, i202249_semval_bind_poison, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, C2Var, VVar, C1Var, hC2, hsh1, hcond1, hV, hC1, hcond2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.shl, LLVM.shl?, LLVM.sub, LLVM.sub?, LLVM.xor, LLVM.xor?, LLVM.assume_]
              have hv := i202249_value (w1 := w1) _h Vv C1 C2 hsh1 hcond1 hcond2
              exact ImmediateUBOr.IsRefinedBy.bothValues (by
                constructor
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv] <;> rfl)
                · exact HVector.nil_isRefinedBy_nil)
