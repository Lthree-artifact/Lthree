import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i163084_src :=
  [llvm()| {
  llvm.func @i163084_src(%arg0 : i64) -> i1 {
  ^bb0(%arg0 : i64):
    %c_64_12 = llvm.mlir.constant(12 : i64) : i64
    %v0 = llvm.sdiv exact %arg0, %c_64_12 : i64
    %v1 = llvm.icmp "ugt" %v0, %c_64_12 : i64
    llvm.return %v1 : i1
  }
  }]

def i163084_tgt :=
  [llvm()| {
  llvm.func @i163084_tgt(%arg0 : i64) -> i1 {
  ^bb0(%arg0 : i64):
    %c_64_144 = llvm.mlir.constant(144 : i64) : i64
    %v0 = llvm.icmp "ugt" %arg0, %c_64_144 : i64
    llvm.return %v0 : i1
  }
  }]

abbrev i163084_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 64]
def i163084_arg0 (V : InstCombine.InputValuation i163084_ctx) : LLVM.IntW 64 :=
  V (Ctxt.Var.mk (Γ := i163084_ctx) (t := InstCombine.LLVM.Ty.bitvec 64) 0 (by simp [i163084_ctx]))
def i163084_src_sem (V : InstCombine.InputValuation i163084_ctx) : LLVM.IntWUB 1 :=
  (InstCombine.lift2 (fun x y => LLVM.icmp LLVM.IntPred.ugt x y) (InstCombine.lift2UB (fun x y => LLVM.sdiv x y (LLVM.ExactFlag.mk true)) (some (i163084_arg0 V)) (some (LLVM.const? 64 12))) (some (LLVM.const? 64 12)))
def i163084_tgt_sem (V : InstCombine.InputValuation i163084_ctx) : LLVM.IntWUB 1 :=
  (InstCombine.lift2 (fun x y => LLVM.icmp LLVM.IntPred.ugt x y) (some (i163084_arg0 V)) (some (LLVM.const? 64 144)))
def i163084_ret (x : LLVM.IntWUB 1) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1] :=
  (x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) ::ₕ HVector.nil

theorem i163084_value (arg0 : LLVM.IntW 64) :
    (InstCombine.lift2 (fun x y => LLVM.icmp LLVM.IntPred.ugt x y) (InstCombine.lift2UB (fun x y => LLVM.sdiv x y (LLVM.ExactFlag.mk true)) (some arg0) (some (LLVM.const? 64 12))) (some (LLVM.const? 64 12)))
      ⊑ (InstCombine.lift2 (fun x y => LLVM.icmp LLVM.IntPred.ugt x y) (some arg0) (some (LLVM.const? 64 144))) := by
  cases arg0 with
  | poison =>
      exact ImmediateUBOr.IsRefinedBy.bothValues (LLVM.SemVal.poison_isRefinedBy _)
  | value x =>
      simp [InstCombine.lift2UB, InstCombine.lift2, LLVM.sdiv, LLVM.icmp, LLVM.icmp?,
        LLVM.const?]
      split
      · rename_i hmod
        apply ImmediateUBOr.IsRefinedBy.bothValues
        simp [LLVM.icmp']
        have h12msb : (12#64).msb = false := rfl
        by_cases hx : x.msb
        · have hxcopy : x.msb = true := by simpa using hx
          have hxneg : x.toInt < 0 := BitVec.toInt_neg_of_msb_true hxcopy
          have hmodInt : x.toInt.fmod 12 = 0 := by
            have hI := congrArg BitVec.toInt hmod
            simpa [BitVec.toInt_smod] using hI
          have hemod : x.toInt % 12 = 0 := by
            simpa [Int.fmod_eq_emod] using hmodInt
          have hdvd : (12 : Int) ∣ x.toInt := (Int.dvd_iff_emod_eq_zero).2 hemod
          have hmul : x.toInt.tdiv 12 * 12 = x.toInt := Int.tdiv_mul_cancel hdvd
          have hqneg : x.toInt.tdiv 12 < 0 := by omega
          have hsdivInt : (x.sdiv 12#64).toInt = x.toInt.tdiv 12 := by
            simpa using
              (BitVec.toInt_sdiv_of_ne_or_ne x (12#64)
                (Or.inr (by decide : (12#64 : BitVec 64) ≠ -1#64)))
          have hqtoIntNeg : (x.sdiv 12#64).toInt < 0 := by omega
          have hqNatBound : 2 ^ 64 ≤ 2 * (x.sdiv 12#64).toNat :=
            (BitVec.toInt_neg_iff).1 hqtoIntNeg
          have hqNatGt : 12 < (x.sdiv 12#64).toNat := by omega
          have hxNatBound : 2 ^ (64 - 1) ≤ x.toNat := BitVec.le_toNat_of_msb_true hxcopy
          have hxNatGt : 144 < x.toNat := by omega
          simp [BitVec.ult, hqNatGt, hxNatGt]
        · have hxcopy : x.msb = false := by simpa using hx
          simp [BitVec.sdiv_eq, BitVec.smod_eq, hxcopy, h12msb, BitVec.ult,
            BitVec.toNat_udiv] at hmod ⊢
          have hmodNat : x.toNat % 12 = 0 := by
            have hI := congrArg BitVec.toNat hmod
            simpa [BitVec.toNat_umod] using hI
          have hdiv : x.toNat = 12 * (x.toNat / 12) := by
            have hdm := Nat.div_add_mod x.toNat 12
            omega
          apply congrArg BitVec.ofBool
          apply decide_eq_decide.mpr
          constructor <;> omega
      · exact ImmediateUBOr.IsRefinedBy.bothValues (LLVM.SemVal.poison_isRefinedBy _)

theorem i163084_correct : i163084_src ⊑ i163084_tgt := by
  unfold i163084_src i163084_tgt
  intro V
  change
    (some (i163084_ret (i163084_src_sem V)) ⊑ some (i163084_ret (i163084_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i163084_ret
  constructor
  · exact (by
      simpa [i163084_src_sem, i163084_tgt_sem] using
        i163084_value (i163084_arg0 V))
  · exact True.intro
