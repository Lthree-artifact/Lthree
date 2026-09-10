import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i144020_a2n_src :=
  [llvm()| {
  llvm.func @i144020_a2n_src(%arg0 : i40) -> i40 {
  ^bb0(%arg0 : i40):
    %1 = llvm.trunc %arg0 : i40 to i8
    %c_8_2 = llvm.mlir.constant(2 : i8) : i8
    %2 = llvm.icmp "eq" %1, %c_8_2 : i8
    %c_40_m256 = llvm.mlir.constant(-256 : i40) : i40
    %3 = llvm.and %arg0, %c_40_m256 : i40
    %c_8_0 = llvm.mlir.constant(0 : i8) : i8
    %4 = llvm.select %2, %c_8_0, %1 : i8
    %c_40_0 = llvm.mlir.constant(0 : i40) : i40
    %5 = llvm.select %2, %c_40_0, %3 : i40
    %6 = llvm.zext %4 : i8 to i40
    %7 = llvm.or disjoint %5, %6 : i40
    llvm.return %7 : i40
  }
  }]

def i144020_a2n_tgt :=
  [llvm()| {
  llvm.func @i144020_a2n_tgt(%arg0 : i40) -> i40 {
  ^bb0(%arg0 : i40):
    %1 = llvm.trunc %arg0 : i40 to i8
    %c_8_2 = llvm.mlir.constant(2 : i8) : i8
    %2 = llvm.icmp "eq" %1, %c_8_2 : i8
    %c_40_0 = llvm.mlir.constant(0 : i40) : i40
    %3 = llvm.select %2, %c_40_0, %arg0 : i40
    llvm.return %3 : i40
  }
  }]

abbrev i144020_a2n_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 40]
def i144020_a2n_arg0 (V : InstCombine.InputValuation i144020_a2n_ctx) : LLVM.IntW 40 :=
  V (Ctxt.Var.mk (Γ := i144020_a2n_ctx) (t := InstCombine.LLVM.Ty.bitvec 40) 0 (by simp [i144020_a2n_ctx]))
def i144020_a2n_src_sem (V : InstCombine.InputValuation i144020_a2n_ctx) : LLVM.IntW 40 :=
  (LLVM.or (LLVM.select (LLVM.icmp LLVM.IntPred.eq (LLVM.trunc 8 (i144020_a2n_arg0 V)) (LLVM.const? 8 2)) (LLVM.const? 40 0) (LLVM.and (i144020_a2n_arg0 V) (LLVM.const? 40 (-256)))) (LLVM.zext 40 (LLVM.select (LLVM.icmp LLVM.IntPred.eq (LLVM.trunc 8 (i144020_a2n_arg0 V)) (LLVM.const? 8 2)) (LLVM.const? 8 0) (LLVM.trunc 8 (i144020_a2n_arg0 V)))) (LLVM.DisjointFlag.mk true))
def i144020_a2n_tgt_sem (V : InstCombine.InputValuation i144020_a2n_ctx) : LLVM.IntW 40 :=
  (LLVM.select (LLVM.icmp LLVM.IntPred.eq (LLVM.trunc 8 (i144020_a2n_arg0 V)) (LLVM.const? 8 2)) (LLVM.const? 40 0) (i144020_a2n_arg0 V))
def i144020_a2n_ret (x : LLVM.IntW 40) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 40] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 40)) ::ₕ HVector.nil

theorem i144020_a2n_value (arg0 : LLVM.IntW 40) :
    (LLVM.or (LLVM.select (LLVM.icmp LLVM.IntPred.eq (LLVM.trunc 8 arg0) (LLVM.const? 8 2)) (LLVM.const? 40 0) (LLVM.and arg0 (LLVM.const? 40 (-256)))) (LLVM.zext 40 (LLVM.select (LLVM.icmp LLVM.IntPred.eq (LLVM.trunc 8 arg0) (LLVM.const? 8 2)) (LLVM.const? 8 0) (LLVM.trunc 8 arg0))) (LLVM.DisjointFlag.mk true))
      ⊑ (LLVM.select (LLVM.icmp LLVM.IntPred.eq (LLVM.trunc 8 arg0) (LLVM.const? 8 2)) (LLVM.const? 40 0) arg0) := by
  cases arg0 with
  | poison =>
      simp [LLVM.trunc, LLVM.trunc?, LLVM.icmp, LLVM.icmp?, LLVM.select, LLVM.and,
        LLVM.or, LLVM.zext]
  | value x =>
      by_cases h : BitVec.ofBool (BitVec.setWidth 8 x == 2#8) = 1#1
      · simp [LLVM.trunc, LLVM.trunc?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.const?,
          LLVM.select, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.zext, LLVM.zext?, h]
      · simp [LLVM.trunc, LLVM.trunc?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.const?,
          LLVM.select, LLVM.and, LLVM.and?, LLVM.or, LLVM.or?, LLVM.zext, LLVM.zext?, h]
        split
        · simp
          have hc : (1099511627520#40 : BitVec 40) = ~~~ (255#40) := by decide
          rw [hc]
          apply BitVec.eq_of_getLsbD_eq
          intro i hi
          simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_setWidth,
            BitVec.getLsbD_ofNat]
          have h255 : Nat.testBit 255 i = decide (i < 8) := by
            have h : (255 : Nat) = 2 ^ 8 - 1 := by decide
            rw [h, Nat.testBit_two_pow_sub_one]
          rw [h255]
          by_cases h8 : i < 8
          · simp [h8, hi]
          · simp [h8, hi]
        · simp

theorem i144020_a2n_correct : i144020_a2n_src ⊑ i144020_a2n_tgt := by
  unfold i144020_a2n_src i144020_a2n_tgt
  intro V
  change
    (some (i144020_a2n_ret (i144020_a2n_src_sem V)) ⊑ some (i144020_a2n_ret (i144020_a2n_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i144020_a2n_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i144020_a2n_src_sem, i144020_a2n_tgt_sem] using
        i144020_a2n_value (i144020_a2n_arg0 V)
  · exact True.intro
