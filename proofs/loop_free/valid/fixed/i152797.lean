import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def i152797_src :=
  [llvm()| {
  llvm.func @i152797_src(%load_v1 : i32, %ptr_v0 : i64) -> i1 {
  ^bb0(%load_v1 : i32, %ptr_v0 : i64):
    %c_64_3 = llvm.mlir.constant(3 : i64) : i64
    %c_64_0 = llvm.mlir.constant(0 : i64) : i64
    %ptr_v0_low = llvm.and %ptr_v0, %c_64_3 : i64
    %ptr_v0_aligned = llvm.icmp "eq" %ptr_v0_low, %c_64_0 : i64
    llvm.assume %ptr_v0_aligned : i1
    %v2 = llvm.zext %load_v1 : i32 to i64
    %v4 = llvm.add %v2, %ptr_v0 : i64
    %c_64_2 = llvm.mlir.constant(2 : i64) : i64
    %v5 = llvm.and %v4, %c_64_2 : i64
    %v6 = llvm.icmp "eq" %v5, %c_64_0 : i64
    llvm.return %v6 : i1
  }
  }]

def i152797_tgt :=
  [llvm()| {
  llvm.func @i152797_tgt(%load_v1 : i32, %ptr_v0 : i64) -> i1 {
  ^bb0(%load_v1 : i32, %ptr_v0 : i64):
    %c_64_3 = llvm.mlir.constant(3 : i64) : i64
    %c_64_0 = llvm.mlir.constant(0 : i64) : i64
    %ptr_v0_low = llvm.and %ptr_v0, %c_64_3 : i64
    %ptr_v0_aligned = llvm.icmp "eq" %ptr_v0_low, %c_64_0 : i64
    llvm.assume %ptr_v0_aligned : i1
    %c_32_2 = llvm.mlir.constant(2 : i32) : i32
    %v2 = llvm.and %load_v1, %c_32_2 : i32
    %c_32_0 = llvm.mlir.constant(0 : i32) : i32
    %v3 = llvm.icmp "eq" %v2, %c_32_0 : i32
    llvm.return %v3 : i1
  }
  }]

private theorem i152797_value (load_v1 : BitVec 32) (ptr_v0 : BitVec 64)
    (hpre : ((ptr_v0 &&& 3#64) == 0#64) = true) :
    ((((BitVec.setWidth 64 load_v1) + ptr_v0) &&& 2#64) == 0#64) = ((load_v1 &&& 2#32) == 0#32) := by
  simp at hpre ⊢
  have mask64 : ∀ x : BitVec 64, (x &&& 2#64 = 0#64) ↔ x.getLsbD 1 = false := by
    intro x
    constructor
    · intro h
      have hbit := congrArg (fun y : BitVec 64 => y.getLsbD 1) h
      simpa [BitVec.getLsbD_and, BitVec.getLsbD_ofNat] using hbit
    · intro h
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      by_cases hi1 : i = 1
      · subst i
        simpa [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, h]
      · have htest : Nat.testBit 2 i = false := by
          rw [show 2 = 2 ^ 1 by rfl, Nat.testBit_two_pow]
          have hne : ¬1 = i := by
            intro h
            exact hi1 h.symm
          simp [hne]
        simp [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, htest]
  have mask32 : ∀ x : BitVec 32, (x &&& 2#32 = 0#32) ↔ x.getLsbD 1 = false := by
    intro x
    constructor
    · intro h
      have hbit := congrArg (fun y : BitVec 32 => y.getLsbD 1) h
      simpa [BitVec.getLsbD_and, BitVec.getLsbD_ofNat] using hbit
    · intro h
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      by_cases hi1 : i = 1
      · subst i
        simpa [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, h]
      · have htest : Nat.testBit 2 i = false := by
          rw [show 2 = 2 ^ 1 by rfl, Nat.testBit_two_pow]
          have hne : ¬1 = i := by
            intro h
            exact hi1 h.symm
          simp [hne]
        simp [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, htest]
  have hptr0 : ptr_v0.getLsbD 0 = false := by
    have hbit := congrArg (fun y : BitVec 64 => y.getLsbD 0) hpre
    simpa [BitVec.getLsbD_and, BitVec.getLsbD_ofNat] using hbit
  have hptr1 : ptr_v0.getLsbD 1 = false := by
    have hbit := congrArg (fun y : BitVec 64 => y.getLsbD 1) hpre
    simpa [BitVec.getLsbD_and, BitVec.getLsbD_ofNat] using hbit
  have hptr0e : ptr_v0[0] = false := by
    simpa [BitVec.getLsbD_eq_getElem (x := ptr_v0) (i := 0) (by decide)] using hptr0
  have hptr1e : ptr_v0[1] = false := by
    simpa [BitVec.getLsbD_eq_getElem (x := ptr_v0) (i := 1) (by decide)] using hptr1
  have hbit : (BitVec.setWidth 64 load_v1 + ptr_v0).getLsbD 1 = load_v1.getLsbD 1 := by
    rw [BitVec.getLsbD_add (by decide)]
    rw [BitVec.getLsbD_setWidth]
    simp [hptr0e, hptr1e, BitVec.carry_succ, BitVec.carry_zero]
  rw [mask64, mask32, hbit]

set_option maxHeartbeats 4000000 in
theorem i152797_correct : i152797_src ⊑ i152797_tgt := by
  intro V
  let load_v1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 32) := ⟨1, by simp⟩
  let ptr_v0Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 32]).Var (InstCombine.LLVM.Ty.bitvec 64) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32]) (InstCombine.LLVM.Ty.bitvec 64)
  cases hptr_v0 : V ptr_v0Var
  case poison =>
    simp [i152797_src, i152797_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, ptr_v0Var, hptr_v0, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.zext, LLVM.zext?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value ptr_v0 =>
    change BitVec 64 at ptr_v0
    cases hcond : ((ptr_v0 &&& 3#64) == 0#64)
    · simp [i152797_src, i152797_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, ptr_v0Var, hptr_v0, hcond, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.zext, LLVM.zext?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    ·
      cases hload_v1 : V load_v1Var
      case poison =>
        simp [i152797_src, i152797_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, ptr_v0Var, load_v1Var, hptr_v0, hcond, hload_v1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.zext, LLVM.zext?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.bothValues (by
          constructor
          · exact ImmediateUBOr.IsRefinedBy.bothValues (by
              first
              | exact LLVM.SemVal.poison_isRefinedBy _
              | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)
              | simp [LLVM.IntW.instRefinement])
          · exact HVector.nil_isRefinedBy_nil)
      case value load_v1 =>
        change BitVec 32 at load_v1
        simp [i152797_src, i152797_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, ptr_v0Var, load_v1Var, hptr_v0, hcond, hload_v1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.zext, LLVM.zext?, LLVM.assume_]
        have hv := i152797_value load_v1 ptr_v0 hcond
        exact ImmediateUBOr.IsRefinedBy.bothValues (by
          constructor
          · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv] <;> rfl)
          · exact HVector.nil_isRefinedBy_nil)
