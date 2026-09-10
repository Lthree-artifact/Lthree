import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i139641_a2n_src :=
  [llvm()| {
  llvm.func @i139641_a2n_src(%arg0 : i32) -> i64 {
  ^bb0(%arg0 : i32):
    %c_32_0 = llvm.mlir.constant(0 : i32) : i32
    %1 = llvm.sub %c_32_0, %arg0 : i32
    %c_32_63 = llvm.mlir.constant(63 : i32) : i32
    %2 = llvm.and %1, %c_32_63 : i32
    %3 = llvm.zext nneg %2 : i32 to i64
    %c_64_0 = llvm.mlir.constant(0 : i64) : i64
    %4 = llvm.sub %c_64_0, %3 overflow<nsw> : i64
    %c_64_8 = llvm.mlir.constant(8 : i64) : i64
    %5 = llvm.lshr %4, %c_64_8 : i64
    %6 = llvm.or %5, %4 : i64
    llvm.return %6 : i64
  }
  }]

def i139641_a2n_tgt :=
  [llvm()| {
  llvm.func @i139641_a2n_tgt(%arg0 : i32) -> i64 {
  ^bb0(%arg0 : i32):
    %c_32_63 = llvm.mlir.constant(63 : i32) : i32
    %1 = llvm.and %arg0, %c_32_63 : i32
    %c_32_0 = llvm.mlir.constant(0 : i32) : i32
    %2 = llvm.icmp "ne" %1, %c_32_0 : i32
    %3 = llvm.sext %2 : i1 to i64
    llvm.return %3 : i64
  }
  }]

abbrev i139641_a2n_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32]
def i139641_a2n_arg0 (V : InstCombine.InputValuation i139641_a2n_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := i139641_a2n_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 0 (by simp [i139641_a2n_ctx]))
def i139641_a2n_src_sem (V : InstCombine.InputValuation i139641_a2n_ctx) : LLVM.IntW 64 :=
  (LLVM.or (LLVM.lshr (LLVM.sub (LLVM.const? 64 0) (LLVM.zext 64 (LLVM.and (LLVM.sub (LLVM.const? 32 0) (i139641_a2n_arg0 V)) (LLVM.const? 32 63)) (LLVM.NonNegFlag.mk true)) (LLVM.NoWrapFlags.mk true false)) (LLVM.const? 64 8)) (LLVM.sub (LLVM.const? 64 0) (LLVM.zext 64 (LLVM.and (LLVM.sub (LLVM.const? 32 0) (i139641_a2n_arg0 V)) (LLVM.const? 32 63)) (LLVM.NonNegFlag.mk true)) (LLVM.NoWrapFlags.mk true false)))
def i139641_a2n_tgt_sem (V : InstCombine.InputValuation i139641_a2n_ctx) : LLVM.IntW 64 :=
  (LLVM.sext 64 (LLVM.icmp LLVM.IntPred.ne (LLVM.and (i139641_a2n_arg0 V) (LLVM.const? 32 63)) (LLVM.const? 32 0)))
def i139641_a2n_ret (x : LLVM.IntW 64) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 64)) ::ₕ HVector.nil

theorem i139641_a2n_value (arg0 : LLVM.IntW 32) :
    (LLVM.or (LLVM.lshr (LLVM.sub (LLVM.const? 64 0) (LLVM.zext 64 (LLVM.and (LLVM.sub (LLVM.const? 32 0) arg0) (LLVM.const? 32 63)) (LLVM.NonNegFlag.mk true)) (LLVM.NoWrapFlags.mk true false)) (LLVM.const? 64 8)) (LLVM.sub (LLVM.const? 64 0) (LLVM.zext 64 (LLVM.and (LLVM.sub (LLVM.const? 32 0) arg0) (LLVM.const? 32 63)) (LLVM.NonNegFlag.mk true)) (LLVM.NoWrapFlags.mk true false)))
      ⊑ (LLVM.sext 64 (LLVM.icmp LLVM.IntPred.ne (LLVM.and arg0 (LLVM.const? 32 63)) (LLVM.const? 32 0))) := by
  cases arg0 with
  | poison =>
      simp [LLVM.or, LLVM.lshr, LLVM.sub, LLVM.zext, LLVM.and, LLVM.sext, LLVM.icmp,
        LLVM.or?, LLVM.lshr?, LLVM.sub?, LLVM.zext?, LLVM.and?, LLVM.sext?, LLVM.icmp?,
        LLVM.icmp', LLVM.const?]
  | value a =>
      simp [LLVM.or, LLVM.lshr, LLVM.sub, LLVM.zext, LLVM.and, LLVM.sext, LLVM.icmp,
        LLVM.or?, LLVM.lshr?, LLVM.sub?, LLVM.zext?, LLVM.and?, LLVM.sext?, LLVM.icmp?,
        LLVM.icmp', LLVM.const?, BitVec.ssubOverflow_eq, BitVec.msb_eq_getLsbD_last]
      have hmask64 : ∀ x : BitVec 64, x &&& 63#64 = setWidth 64 (setWidth 6 x) := by
        intro x
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        by_cases hi6 : i < 6
        · have hmaskbit : (63#64)[i] = true := by
            rw [BitVec.getElem_eq_testBit_toNat]
            exact (by decide : ∀ i : Nat, i < 6 → Nat.testBit 63 i = true) i hi6
          simp [hi, hi6, hmaskbit]
        · have hmaskbit : (63#64)[i] = false := by
            rw [BitVec.getElem_eq_testBit_toNat]
            exact (by decide : ∀ i : Nat, 6 ≤ i → i < 64 → Nat.testBit 63 i = false) i (by omega) hi
          simp [hi, hi6, hmaskbit]
      have hmask32 : ∀ x : BitVec 32, x &&& 63#32 = setWidth 32 (setWidth 6 x) := by
        intro x
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        by_cases hi6 : i < 6
        · have hmaskbit : (63#32)[i] = true := by
            rw [BitVec.getElem_eq_testBit_toNat]
            exact (by decide : ∀ i : Nat, i < 6 → Nat.testBit 63 i = true) i hi6
          simp [hi, hi6, hmaskbit]
        · have hmaskbit : (63#32)[i] = false := by
            rw [BitVec.getElem_eq_testBit_toNat]
            exact (by decide : ∀ i : Nat, 6 ≤ i → i < 32 → Nat.testBit 63 i = false) i (by omega) hi
          simp [hi, hi6, hmaskbit]
      have hcomp : setWidth 64 (-a) &&& 63#64 = setWidth 64 (-setWidth 6 a) := by
        rw [hmask64]
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_setWidth, BitVec.toNat_neg]
      have hzext_ne_zero : ∀ b : BitVec 6, (setWidth 32 b != 0#32) = (b != 0#6) := by
        intro b
        by_cases h : b = 0#6
        · simp [h]
        · have hz : setWidth 32 b ≠ 0#32 := by
            intro hz
            apply h
            apply BitVec.eq_of_toNat_eq
            have hzNat := congrArg BitVec.toNat hz
            simp [BitVec.toNat_setWidth] at hzNat
            have hb := BitVec.isLt b
            simp [BitVec.toNat_ofNat]
            omega
          simp [bne, h, hz]
      have hcond : (a &&& 63#32 != 0#32) = (setWidth 6 a != 0#6) := by
        rw [hmask32, hzext_ne_zero]
      have h6 : ∀ b : BitVec 6,
          (-(zeroExtend 64 (-b))) >>> 8 ||| -(zeroExtend 64 (-b)) =
            signExtend 64 (ofBool (b != 0#6)) := by
        decide
      rw [hcomp, hcond]
      simpa using h6 (setWidth 6 a)

theorem i139641_a2n_correct : i139641_a2n_src ⊑ i139641_a2n_tgt := by
  unfold i139641_a2n_src i139641_a2n_tgt
  intro V
  change
    (some (i139641_a2n_ret (i139641_a2n_src_sem V)) ⊑ some (i139641_a2n_ret (i139641_a2n_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i139641_a2n_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i139641_a2n_src_sem, i139641_a2n_tgt_sem] using
        i139641_a2n_value (i139641_a2n_arg0 V)
  · exact True.intro
