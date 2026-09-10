import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def B_shift_mul__corpus3_src :=
  [llvm()| {
  llvm.func @B_shift_mul__corpus3_src(%v0 : i32, %v1 : i32) -> i32 {
  ^bb0(%v0 : i32, %v1 : i32):
    %c_i32_1 = llvm.mlir.constant(1 : i32) : i32
    %v2 = llvm.shl %v0, %c_i32_1 overflow<nsw> : i32
    %v3 = llvm.mul %v1, %v2 overflow<nsw> : i32
    %v4 = llvm.or %c_i32_1, %v3 : i32
    %v5 = llvm.icmp "slt" %v4, %c_i32_1 : i32
    %v6 = llvm.select %v5, %v1, %c_i32_1 : i32
    %v7 = llvm.mul %v0, %v6 overflow<nsw> : i32
    llvm.return %v7 : i32
  }
  }]

def B_shift_mul__corpus3_tgt :=
  [llvm()| {
  llvm.func @B_shift_mul__corpus3_tgt(%v0 : i32, %v1 : i32) -> i32 {
  ^bb0(%v0 : i32, %v1 : i32):
    %v2 = llvm.mul %v0, %v1 overflow<nsw> : i32
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %v3 = llvm.icmp "slt" %v2, %c_i32_0 : i32
    %v5 = llvm.select %v3, %v2, %v0 : i32
    llvm.return %v5 : i32
  }
  }]

abbrev B_shift_mul__corpus3_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]
def B_shift_mul__corpus3_v0 (V : InstCombine.InputValuation B_shift_mul__corpus3_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := B_shift_mul__corpus3_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 1 (by simp [B_shift_mul__corpus3_ctx]))
def B_shift_mul__corpus3_v1 (V : InstCombine.InputValuation B_shift_mul__corpus3_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := B_shift_mul__corpus3_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 0 (by simp [B_shift_mul__corpus3_ctx]))
def B_shift_mul__corpus3_src_sem (V : InstCombine.InputValuation B_shift_mul__corpus3_ctx) : LLVM.IntW 32 :=
  (LLVM.mul (B_shift_mul__corpus3_v0 V) (LLVM.select (LLVM.icmp LLVM.IntPred.slt (LLVM.or (LLVM.const? 32 1) (LLVM.mul (B_shift_mul__corpus3_v1 V) (LLVM.shl (B_shift_mul__corpus3_v0 V) (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false)) (LLVM.NoWrapFlags.mk true false))) (LLVM.const? 32 1)) (B_shift_mul__corpus3_v1 V) (LLVM.const? 32 1)) (LLVM.NoWrapFlags.mk true false))
def B_shift_mul__corpus3_tgt_sem (V : InstCombine.InputValuation B_shift_mul__corpus3_ctx) : LLVM.IntW 32 :=
  (LLVM.select (LLVM.icmp LLVM.IntPred.slt (LLVM.mul (B_shift_mul__corpus3_v0 V) (B_shift_mul__corpus3_v1 V) (LLVM.NoWrapFlags.mk true false)) (LLVM.const? 32 0)) (LLVM.mul (B_shift_mul__corpus3_v0 V) (B_shift_mul__corpus3_v1 V) (LLVM.NoWrapFlags.mk true false)) (B_shift_mul__corpus3_v0 V))
def B_shift_mul__corpus3_ret (x : LLVM.IntW 32) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 32] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 32)) ::ₕ HVector.nil

theorem B_shift_mul__corpus3_value (v0 : LLVM.IntW 32) (v1 : LLVM.IntW 32) :
    (LLVM.mul v0 (LLVM.select (LLVM.icmp LLVM.IntPred.slt (LLVM.or (LLVM.const? 32 1) (LLVM.mul v1 (LLVM.shl v0 (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false)) (LLVM.NoWrapFlags.mk true false))) (LLVM.const? 32 1)) v1 (LLVM.const? 32 1)) (LLVM.NoWrapFlags.mk true false))
      ⊑ (LLVM.select (LLVM.icmp LLVM.IntPred.slt (LLVM.mul v0 v1 (LLVM.NoWrapFlags.mk true false)) (LLVM.const? 32 0)) (LLVM.mul v0 v1 (LLVM.NoWrapFlags.mk true false)) v0) := by
  cases v0 with
  | poison =>
      cases v1 <;>
        simp [LLVM.mul, LLVM.mul?, LLVM.select, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or,
          LLVM.or?, LLVM.shl, LLVM.shl?, LLVM.const?]
  | value x =>
      cases v1 with
      | poison =>
          simp [LLVM.mul, LLVM.mul?, LLVM.select, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or,
            LLVM.or?, LLVM.shl, LLVM.shl?, LLVM.const?]
      | value y =>
          have shiftExact (h : (x <<< 1).sshiftRight 1 = x) :
              ((↑(x.toNat <<< 1) : Int).bmod (2 ^ 32)) = 2 * x.toInt := by
            have hto := congrArg BitVec.toInt h
            simp [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, BitVec.toInt_shiftLeft,
              Nat.shiftLeft_eq] at hto
            simp [Nat.shiftLeft_eq] at hto ⊢
            have hbmod2 : (((x.toNat : Int) * 2).bmod 4294967296).bmod 2 = 0 := by
              have hdvdM : (2 : Nat) ∣ 4294967296 := ⟨2147483648, by decide⟩
              have hbm := Int.bmod_bmod_of_dvd (a := ((x.toNat : Int) * 2)) (n := 2)
                (m := 4294967296) hdvdM
              have ha : ((x.toNat : Int) * 2).bmod 2 = 0 := by
                apply Int.bmod_eq_zero_of_dvd
                refine ⟨(x.toNat : Int), ?_⟩
                omega
              rw [hbm, ha]
            have hemod2 : (((x.toNat : Int) * 2).bmod 4294967296) % 2 = 0 := by
              have hiff := (Int.bmod_eq_iff
                (a := (((x.toNat : Int) * 2).bmod 4294967296)) (b := 2) (c := 0)
                (by decide)).1 hbmod2
              rcases hiff with ⟨_, _, hdvd⟩
              have hdvd' : (2 : Int) ∣ (((x.toNat : Int) * 2).bmod 4294967296) := by
                rcases hdvd with ⟨k, hk⟩
                refine ⟨-k, ?_⟩
                omega
              exact Int.emod_eq_zero_of_dvd hdvd'
            omega
          have noTargetOverflow (hshl : (x <<< 1).sshiftRight 1 = x)
              (hmul2 : y.smulOverflow (x <<< 1) = false) :
              x.smulOverflow y = false := by
            have hs : (((x.toNat : Int) * 2).bmod 4294967296) = 2 * x.toInt := by
              simpa [Nat.shiftLeft_eq] using shiftExact hshl
            have halg : y.toInt * (2 * x.toInt) = 2 * (x.toInt * y.toInt) := by
              calc
                y.toInt * (2 * x.toInt) = (y.toInt * 2) * x.toInt := by rw [mul_assoc]
                _ = (2 * y.toInt) * x.toInt := by rw [mul_comm y.toInt 2]
                _ = 2 * (y.toInt * x.toInt) := by rw [← mul_assoc]
                _ = 2 * (x.toInt * y.toInt) := by rw [mul_comm y.toInt x.toInt]
            simp [BitVec.smulOverflow, BitVec.toInt_shiftLeft, Nat.shiftLeft_eq] at hmul2 ⊢
            rw [hs, halg] at hmul2
            omega
          have sourceTest (hshl : (x <<< 1).sshiftRight 1 = x)
              (hmul2 : y.smulOverflow (x <<< 1) = false) (hxy : x.smulOverflow y = false) :
              ((1#32 ||| y * (x <<< 1)) <ₛ 1#32) = (x * y <ₛ 0#32) := by
            let t : BitVec 32 := y * (x <<< 1)
            let p : Int := x.toInt * y.toInt
            have hs : (((x.toNat : Int) * 2).bmod 4294967296) = 2 * x.toInt := by
              simpa [Nat.shiftLeft_eq] using shiftExact hshl
            have halg : y.toInt * (2 * x.toInt) = 2 * p := by
              dsimp [p]
              calc
                y.toInt * (2 * x.toInt) = (y.toInt * 2) * x.toInt := by rw [mul_assoc]
                _ = (2 * y.toInt) * x.toInt := by rw [mul_comm y.toInt 2]
                _ = 2 * (y.toInt * x.toInt) := by rw [← mul_assoc]
                _ = 2 * (x.toInt * y.toInt) := by rw [mul_comm y.toInt x.toInt]
            have ht : t.toInt = 2 * p := by
              calc
                t.toInt = (y * (x <<< 1)).toInt := rfl
                _ = y.toInt * (x <<< 1).toInt :=
                  BitVec.toInt_mul_of_not_smulOverflow (x := y) (y := x <<< 1)
                    (by simpa using hmul2)
                _ = 2 * p := by
                  simp [BitVec.toInt_shiftLeft, Nat.shiftLeft_eq, hs, halg]
            have hp : (x * y).toInt = p := by
              dsimp [p]
              exact BitVec.toInt_mul_of_not_smulOverflow (x := x) (y := y) (by simpa using hxy)
            have htEven : t.toNat % 2 = 0 := by
              have hti := ht
              rw [BitVec.toInt_eq_msb_cond] at hti
              split at hti <;> omega
            have horNat : 1 ||| t.toNat = t.toNat + 1 := by
              apply Nat.eq_of_testBit_eq
              intro i
              rw [Nat.testBit_or]
              cases i with
              | zero =>
                  simp [Nat.testBit_zero, htEven]
                  omega
              | succ j =>
                  have hdiv : (t.toNat + 1) / 2 = t.toNat / 2 := by omega
                  simp [Nat.testBit_succ, hdiv]
            have horNat' : (1#32).toNat ||| t.toNat = t.toNat + 1 := by
              simpa using horNat
            have hmsb : (1#32 ||| t).msb = t.msb := by
              rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_or, BitVec.msb_eq_getLsbD_last]
              simp
            have horInt : (1#32 ||| t).toInt = t.toInt + 1 := by
              rw [BitVec.toInt_eq_msb_cond (1#32 ||| t), BitVec.toInt_eq_msb_cond t, hmsb]
              rw [BitVec.toNat_or, horNat']
              by_cases hm : t.msb = true
              · simp [hm]
                try omega
              · simp [hm]
                try omega
            rw [show ((1#32 ||| y * (x <<< 1)) <ₛ 1#32) =
              decide ((1#32 ||| t).toInt < (1#32 : BitVec 32).toInt) by rfl]
            rw [show (x * y <ₛ 0#32) =
              decide ((x * y).toInt < (0#32 : BitVec 32).toInt) by rfl]
            rw [horInt, ht, hp]
            simp [p]
            by_cases hpneg : x.toInt * y.toInt < 0
            · simp [hpneg]
              omega
            · simp [hpneg]
              omega
          have xMulOne : x.smulOverflow 1#32 = false := by
            simp [BitVec.smulOverflow]
            have hlo := BitVec.le_toInt (x := x)
            have hhi := BitVec.toInt_lt (x := x)
            omega
          by_cases hshl : (x <<< 1).sshiftRight 1 = x
          · cases hmul2 : y.smulOverflow (x <<< 1)
            · have hxy := noTargetOverflow hshl hmul2
              have htest := sourceTest hshl hmul2 hxy
              simp [LLVM.mul, LLVM.mul?, LLVM.select, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or,
                LLVM.or?, LLVM.shl, LLVM.shl?, LLVM.const?]
              simp_all
              by_cases hcond : ofBool (x * y <ₛ 0#32) = 1#1
              · simp [hcond, hxy]
              · simp [hcond, xMulOne]
            · simp [LLVM.mul, LLVM.mul?, LLVM.select, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or,
                LLVM.or?, LLVM.shl, LLVM.shl?, LLVM.const?]
              simp_all
          · simp [LLVM.mul, LLVM.mul?, LLVM.select, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or,
              LLVM.or?, LLVM.shl, LLVM.shl?, LLVM.const?]
            simp_all

theorem B_shift_mul__corpus3_correct : B_shift_mul__corpus3_src ⊑ B_shift_mul__corpus3_tgt := by
  unfold B_shift_mul__corpus3_src B_shift_mul__corpus3_tgt
  intro V
  change
    (some (B_shift_mul__corpus3_ret (B_shift_mul__corpus3_src_sem V)) ⊑ some (B_shift_mul__corpus3_ret (B_shift_mul__corpus3_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold B_shift_mul__corpus3_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [B_shift_mul__corpus3_src_sem, B_shift_mul__corpus3_tgt_sem] using
        B_shift_mul__corpus3_value (B_shift_mul__corpus3_v0 V) (B_shift_mul__corpus3_v1 V)
  · exact True.intro
