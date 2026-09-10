import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i143636_a2n_src :=
  [llvm()| {
  llvm.func @i143636_a2n_src(%arg0 : i32) -> i1 {
  ^bb0(%arg0 : i32):
    %c_32_1 = llvm.mlir.constant(1 : i32) : i32
    %1 = llvm.add %arg0, %c_32_1 : i32
    %c_32_4 = llvm.mlir.constant(4 : i32) : i32
    %2 = llvm.lshr %1, %c_32_4 : i32
    %c_32_15 = llvm.mlir.constant(15 : i32) : i32
    %3 = llvm.and %1, %c_32_15 : i32
    %c_32_0 = llvm.mlir.constant(0 : i32) : i32
    %4 = llvm.icmp "ne" %3, %c_32_0 : i32
    %5 = llvm.zext %4 : i1 to i32
    %6 = llvm.add %2, %5 overflow<nsw,nuw> : i32
    %7 = llvm.icmp "eq" %6, %c_32_0 : i32
    llvm.return %7 : i1
  }
  }]

def i143636_a2n_tgt :=
  [llvm()| {
  llvm.func @i143636_a2n_tgt(%arg0 : i32) -> i1 {
  ^bb0(%arg0 : i32):
    %c_32_m1 = llvm.mlir.constant(-1 : i32) : i32
    %5 = llvm.icmp "eq" %arg0, %c_32_m1 : i32
    llvm.return %5 : i1
  }
  }]

abbrev i143636_a2n_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32]
def i143636_a2n_arg0 (V : InstCombine.InputValuation i143636_a2n_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := i143636_a2n_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 0 (by simp [i143636_a2n_ctx]))
def i143636_a2n_src_sem (V : InstCombine.InputValuation i143636_a2n_ctx) : LLVM.IntW 1 :=
  (LLVM.icmp LLVM.IntPred.eq (LLVM.add (LLVM.lshr (LLVM.add (i143636_a2n_arg0 V) (LLVM.const? 32 1)) (LLVM.const? 32 4)) (LLVM.zext 32 (LLVM.icmp LLVM.IntPred.ne (LLVM.and (LLVM.add (i143636_a2n_arg0 V) (LLVM.const? 32 1)) (LLVM.const? 32 15)) (LLVM.const? 32 0))) (LLVM.NoWrapFlags.mk true true)) (LLVM.const? 32 0))
def i143636_a2n_tgt_sem (V : InstCombine.InputValuation i143636_a2n_ctx) : LLVM.IntW 1 :=
  (LLVM.icmp LLVM.IntPred.eq (i143636_a2n_arg0 V) (LLVM.const? 32 (-1)))
def i143636_a2n_ret (x : LLVM.IntW 1) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) ::ₕ HVector.nil

theorem i143636_a2n_value (arg0 : LLVM.IntW 32) :
    (LLVM.icmp LLVM.IntPred.eq (LLVM.add (LLVM.lshr (LLVM.add arg0 (LLVM.const? 32 1)) (LLVM.const? 32 4)) (LLVM.zext 32 (LLVM.icmp LLVM.IntPred.ne (LLVM.and (LLVM.add arg0 (LLVM.const? 32 1)) (LLVM.const? 32 15)) (LLVM.const? 32 0))) (LLVM.NoWrapFlags.mk true true)) (LLVM.const? 32 0))
      ⊑ (LLVM.icmp LLVM.IntPred.eq arg0 (LLVM.const? 32 (-1))) := by
  cases arg0 with
  | poison =>
      simp [LLVM.icmp, LLVM.add, LLVM.lshr, LLVM.and, LLVM.zext, LLVM.const?, LLVM.add?,
        LLVM.lshr?, LLVM.and?, LLVM.icmp?, LLVM.icmp', LLVM.zext?]
  | value x =>
      have land_15_eq_mod_16 (n : Nat) : n &&& 15 = n % 16 := by
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_and]
        change (n.testBit i && (2 ^ 4 - 1).testBit i) = (n % 2 ^ 4).testBit i
        rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
        cases h : decide (i < 4) <;> cases n.testBit i <;> rfl
      have rounded_zero_iff (y : BitVec 32) :
          (y >>> 4 + setWidth 32 (ofBool (y &&& 15#32 != 0#32)) = 0#32) ↔
            y = 0#32 := by
        constructor
        · intro h
          apply BitVec.eq_of_toNat_eq
          have hsum := congrArg BitVec.toNat h
          simp [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
            BitVec.toNat_ofBool, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at hsum
          simp [BitVec.toNat_ofNat]
          have hltY : y.toNat < 4294967296 := by simpa using y.isLt
          have hb : (y &&& 15#32 != 0#32).toNat ≤ 1 := by
            cases y &&& 15#32 != 0#32 <;> simp
          have hltSum :
              y.toNat / 16 + (y &&& 15#32 != 0#32).toNat < 4294967296 := by
            have hdiv := Nat.div_le_self y.toNat 16
            omega
          have hsum0 : y.toNat / 16 + (y &&& 15#32 != 0#32).toNat = 0 := by
            rw [Nat.mod_eq_of_lt hltSum] at hsum
            exact hsum
          have hdiv0 : y.toNat / 16 = 0 := by omega
          have hbool0 : (y &&& 15#32 != 0#32).toNat = 0 := by omega
          have hmask0 : y &&& 15#32 = 0#32 := by
            have hf : (y &&& 15#32 != 0#32) = false := Bool.toNat_eq_zero.mp hbool0
            simpa using hf
          have hmod0 : y.toNat % 16 = 0 := by
            have ht := congrArg BitVec.toNat hmask0
            simp [BitVec.toNat_and, BitVec.toNat_ofNat, land_15_eq_mod_16] at ht
            exact ht
          have hrecon := Nat.mod_add_div y.toNat 16
          omega
        · intro h
          subst h
          simp
      have add_one_zero_iff (y : BitVec 32) :
          y + 1#32 = 0#32 ↔ y = 4294967295#32 := by
        constructor
        · intro h
          apply BitVec.eq_of_toNat_eq
          have ht := congrArg BitVec.toNat h
          simp [BitVec.toNat_add, BitVec.toNat_ofNat] at ht
          simp [BitVec.toNat_ofNat]
          have hlt : y.toNat < 4294967296 := by simpa using y.isLt
          have hmod := Nat.mod_eq_iff.mp ht
          rcases hmod with hzero | hcase
          · omega
          · rcases hcase with ⟨_, k, hk⟩
            omega
        · intro h
          apply BitVec.eq_of_toNat_eq
          subst h
          simp [BitVec.toNat_ofNat]
      simp [LLVM.icmp, LLVM.add, LLVM.lshr, LLVM.and, LLVM.zext, LLVM.const?, LLVM.add?,
        LLVM.lshr?, LLVM.and?, LLVM.icmp?, LLVM.icmp', LLVM.zext?]
      split_ifs
      · simp
      · simp
      · simp
        apply congrArg BitVec.ofBool
        rw [Bool.eq_iff_iff]
        constructor
        · intro h
          have hzero :
              (x + 1#32) >>> 4 + setWidth 32 (ofBool (x + 1#32 &&& 15#32 != 0#32)) =
                0#32 := beq_iff_eq.mp h
          have hx1 : x + 1#32 = 0#32 := (rounded_zero_iff (x + 1#32)).mp hzero
          exact beq_iff_eq.mpr ((add_one_zero_iff x).mp hx1)
        · intro h
          have hxmax : x = 4294967295#32 := beq_iff_eq.mp h
          have hx1 : x + 1#32 = 0#32 := (add_one_zero_iff x).mpr hxmax
          have hzero := (rounded_zero_iff (x + 1#32)).mpr hx1
          exact beq_iff_eq.mpr hzero

theorem i143636_a2n_correct : i143636_a2n_src ⊑ i143636_a2n_tgt := by
  unfold i143636_a2n_src i143636_a2n_tgt
  intro V
  change
    (some (i143636_a2n_ret (i143636_a2n_src_sem V)) ⊑ some (i143636_a2n_ret (i143636_a2n_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i143636_a2n_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i143636_a2n_src_sem, i143636_a2n_tgt_sem] using
        i143636_a2n_value (i143636_a2n_arg0 V)
  · exact True.intro
