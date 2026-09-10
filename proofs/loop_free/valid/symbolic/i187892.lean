import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i187892_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i187892_src(%p : _, %q : _, %C1 : _) -> _ {
  ^bb0(%p : _, %q : _, %C1 : _):
    %m1 = llvm.mlir.constant(-1 : _) : _
    %not_p = llvm.xor %p, %C1 : _
    %imp = llvm.or %not_p, %q : _
    %cond = llvm.icmp "eq" %imp, %m1 : _
    llvm.assume %cond : i1
    %mask = llvm.xor %C1, %m1 : _
    %p_masked = llvm.xor %p, %mask : _
    %r = llvm.or %p_masked, %q : _
    llvm.return %r : _
  }
  }]

def i187892_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i187892_tgt(%p : _, %q : _, %C1 : _) -> _ {
  ^bb0(%p : _, %q : _, %C1 : _):
    %m1 = llvm.mlir.constant(-1 : _) : _
    %not_p = llvm.xor %p, %C1 : _
    %imp = llvm.or %not_p, %q : _
    %cond = llvm.icmp "eq" %imp, %m1 : _
    llvm.assume %cond : i1
    llvm.return %q : _
  }
  }]

private theorem i187892_value {w : Nat} (p : BitVec w) (q : BitVec w) (C1 : BitVec w)
    (hpre : (((p ^^^ C1) ||| q) == (BitVec.ofInt w (-1))) = true) :
    ((p ^^^ (C1 ^^^ (BitVec.ofInt w (-1)))) ||| q) = q := by
  have hm1 : BitVec.ofInt w (-1) = BitVec.allOnes w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt, BitVec.toNat_allOnes]
    change ((Int.negSucc 0) % ((2 : Int) ^ w)).toNat = 2 ^ w - 1
    rw [Int.negSucc_emod 0 (show (0 : Int) < (2 : Int) ^ w by
      exact_mod_cast Nat.two_pow_pos w)]
    simp
    exact congrArg Nat.pred (Int.toNat_natCast (2 ^ w))
  have hpre_eq : ((p ^^^ C1) ||| q) = BitVec.ofInt w (-1) := beq_iff_eq.mp hpre
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hbit : ((p ^^^ C1) ||| q).getLsbD i = (BitVec.ofInt w (-1)).getLsbD i := by
    rw [hpre_eq]
  rw [hm1, BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_allOnes] at hbit
  rw [BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_xor, hm1,
    BitVec.getLsbD_allOnes]
  simp [hi] at hbit ⊢
  intro hpc
  rcases hbit with hnot | hq
  · cases hp : p[i] <;> cases hC : C1[i] <;> simp [hp, hC] at hpc hnot
  · exact hq

set_option maxHeartbeats 4000000 in
theorem i187892_correct (w : Nat) : i187892_src w ⊑ i187892_tgt w := by
  intro V
  let pVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let qVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases hp : V pVar
  case poison =>
    simp [i187892_src, i187892_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, pVar, hp, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.xor, LLVM.xor?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value p =>
    cases hC1 : V C1Var
    case poison =>
      simp [i187892_src, i187892_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, pVar, C1Var, hp, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.xor, LLVM.xor?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value C1 =>
      cases hq : V qVar
      case poison =>
        simp [i187892_src, i187892_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, pVar, C1Var, qVar, hp, hC1, hq, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.xor, LLVM.xor?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      case value q =>
        cases hcond : (((p ^^^ C1) ||| q) == (BitVec.ofInt w (-1)))
        · simp [i187892_src, i187892_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, pVar, C1Var, qVar, hp, hC1, hq, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.xor, LLVM.xor?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        ·
          simp [i187892_src, i187892_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, pVar, C1Var, qVar, hp, hC1, hq, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.xor, LLVM.xor?, LLVM.assume_]
          have hv := i187892_value (w := w) p q C1 hcond
          exact ImmediateUBOr.IsRefinedBy.bothValues (by
            constructor
            · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv])
            · exact HVector.nil_isRefinedBy_nil)
