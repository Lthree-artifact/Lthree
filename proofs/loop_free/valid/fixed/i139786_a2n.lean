import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i139786_a2n_src :=
  [llvm()| {
  llvm.func @i139786_a2n_src(%arg0 : i8) -> i8 {
  ^bb0(%arg0 : i8):
    %c_8_1 = llvm.mlir.constant(1 : i8) : i8
    %v1_umax_cmp = llvm.icmp "ugt" %arg0, %c_8_1 : i8
    %1 = llvm.select %v1_umax_cmp, %arg0, %c_8_1 : i8
    %2 = llvm.shl %1, %c_8_1 overflow<nuw> : i8
    %c_8_16 = llvm.mlir.constant(16 : i8) : i8
    %v3_umax_cmp = llvm.icmp "ugt" %2, %c_8_16 : i8
    %3 = llvm.select %v3_umax_cmp, %2, %c_8_16 : i8
    %c_8_m1 = llvm.mlir.constant(-1 : i8) : i8
    %4 = llvm.icmp "sgt" %1, %c_8_m1 : i8
    %5 = llvm.select %4, %3, %c_8_m1 : i8
    llvm.return %3 : i8
  }
  }]

def i139786_a2n_tgt :=
  [llvm()| {
  llvm.func @i139786_a2n_tgt(%arg0 : i8) -> i8 {
  ^bb0(%arg0 : i8):
    %c_8_1 = llvm.mlir.constant(1 : i8) : i8
    %1 = llvm.shl %arg0, %c_8_1 overflow<nuw> : i8
    %c_8_16 = llvm.mlir.constant(16 : i8) : i8
    %v2_umax_cmp = llvm.icmp "ugt" %1, %c_8_16 : i8
    %2 = llvm.select %v2_umax_cmp, %1, %c_8_16 : i8
    %c_8_m1 = llvm.mlir.constant(-1 : i8) : i8
    %3 = llvm.icmp "sgt" %2, %c_8_m1 : i8
    %4 = llvm.select %3, %2, %c_8_m1 : i8
    llvm.return %2 : i8
  }
  }]

abbrev i139786_a2n_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 8]
def i139786_a2n_arg0 (V : InstCombine.InputValuation i139786_a2n_ctx) : LLVM.IntW 8 :=
  V (Ctxt.Var.mk (Γ := i139786_a2n_ctx) (t := InstCombine.LLVM.Ty.bitvec 8) 0 (by simp [i139786_a2n_ctx]))
def i139786_a2n_src_sem (V : InstCombine.InputValuation i139786_a2n_ctx) : LLVM.IntW 8 :=
  (LLVM.select (LLVM.icmp LLVM.IntPred.ugt (LLVM.shl (LLVM.select (LLVM.icmp LLVM.IntPred.ugt (i139786_a2n_arg0 V) (LLVM.const? 8 1)) (i139786_a2n_arg0 V) (LLVM.const? 8 1)) (LLVM.const? 8 1) (LLVM.NoWrapFlags.mk false true)) (LLVM.const? 8 16)) (LLVM.shl (LLVM.select (LLVM.icmp LLVM.IntPred.ugt (i139786_a2n_arg0 V) (LLVM.const? 8 1)) (i139786_a2n_arg0 V) (LLVM.const? 8 1)) (LLVM.const? 8 1) (LLVM.NoWrapFlags.mk false true)) (LLVM.const? 8 16))
def i139786_a2n_tgt_sem (V : InstCombine.InputValuation i139786_a2n_ctx) : LLVM.IntW 8 :=
  (LLVM.select (LLVM.icmp LLVM.IntPred.ugt (LLVM.shl (i139786_a2n_arg0 V) (LLVM.const? 8 1) (LLVM.NoWrapFlags.mk false true)) (LLVM.const? 8 16)) (LLVM.shl (i139786_a2n_arg0 V) (LLVM.const? 8 1) (LLVM.NoWrapFlags.mk false true)) (LLVM.const? 8 16))
def i139786_a2n_ret (x : LLVM.IntW 8) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 8)) ::ₕ HVector.nil

theorem i139786_a2n_value (arg0 : LLVM.IntW 8) :
    (LLVM.select (LLVM.icmp LLVM.IntPred.ugt (LLVM.shl (LLVM.select (LLVM.icmp LLVM.IntPred.ugt arg0 (LLVM.const? 8 1)) arg0 (LLVM.const? 8 1)) (LLVM.const? 8 1) (LLVM.NoWrapFlags.mk false true)) (LLVM.const? 8 16)) (LLVM.shl (LLVM.select (LLVM.icmp LLVM.IntPred.ugt arg0 (LLVM.const? 8 1)) arg0 (LLVM.const? 8 1)) (LLVM.const? 8 1) (LLVM.NoWrapFlags.mk false true)) (LLVM.const? 8 16))
      ⊑ (LLVM.select (LLVM.icmp LLVM.IntPred.ugt (LLVM.shl arg0 (LLVM.const? 8 1) (LLVM.NoWrapFlags.mk false true)) (LLVM.const? 8 16)) (LLVM.shl arg0 (LLVM.const? 8 1) (LLVM.NoWrapFlags.mk false true)) (LLVM.const? 8 16)) := by
  cases arg0 <;>
    simp [LLVM.select, LLVM.icmp, LLVM.shl, LLVM.const?, LLVM.icmp?, LLVM.icmp', LLVM.shl?]
  repeat' split <;> simp_all [BitVec.ofBool]
  · exfalso
    rename_i a hle _ hgt
    have ha_le : a.toNat ≤ 1 := by
      by_contra hle_nat
      have hlt : 1 < a.toNat := by omega
      exact hle (by simp [BitVec.ult, hlt])
    have hgt_mod : 16 < a.toNat <<< 1 % 256 := by
      by_cases h : 16 < a.toNat <<< 1 % 256
      · exact h
      · exfalso
        simp [BitVec.ult, BitVec.toNat_shiftLeft, h] at hgt
    rw [Nat.shiftLeft_eq] at hgt_mod
    have hmod : a.toNat * 2 < 256 := by omega
    have hsmall : a.toNat * 2 % 256 ≤ 2 := by
      rw [Nat.mod_eq_of_lt hmod]
      omega
    omega
  · exfalso
    rename_i a hle hover
    have ha_le : a.toNat ≤ 1 := by
      by_contra hle_nat
      have hlt : 1 < a.toNat := by omega
      exact hle (by simp [BitVec.ult, hlt])
    have hshift : a <<< 1 >>> 1 = a := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
        Nat.shiftLeft_eq]
      omega
    exact hover hshift

theorem i139786_a2n_correct : i139786_a2n_src ⊑ i139786_a2n_tgt := by
  unfold i139786_a2n_src i139786_a2n_tgt
  intro V
  change
    (some (i139786_a2n_ret (i139786_a2n_src_sem V)) ⊑ some (i139786_a2n_ret (i139786_a2n_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i139786_a2n_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i139786_a2n_src_sem, i139786_a2n_tgt_sem] using
        i139786_a2n_value (i139786_a2n_arg0 V)
  · exact True.intro
