import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i143957_src :=
  [llvm()| {
  llvm.func @i143957_src(%arg0 : i64) -> i1 {
  ^bb0(%arg0 : i64):
    %c_64_32 = llvm.mlir.constant(32 : i64) : i64
    %1 = llvm.lshr %arg0, %c_64_32 : i64
    %2 = llvm.trunc %1 overflow<nuw> : i64 to i32
    %c_32_55296 = llvm.mlir.constant(55296 : i32) : i32
    %3 = llvm.xor %2, %c_32_55296 : i32
    %c_32_m1114112 = llvm.mlir.constant(-1114112 : i32) : i32
    %4 = llvm.add %3, %c_32_m1114112 : i32
    %c_32_m1112064 = llvm.mlir.constant(-1112064 : i32) : i32
    %5 = llvm.icmp "ult" %4, %c_32_m1112064 : i32
    %c_64_1114112 = llvm.mlir.constant(1114112 : i64) : i64
    %6 = llvm.icmp "eq" %1, %c_64_1114112 : i64
    %7 = llvm.or %6, %5 : i1
    llvm.return %7 : i1
  }
  }]

def i143957_tgt :=
  [llvm()| {
  llvm.func @i143957_tgt(%arg0 : i64) -> i1 {
  ^bb0(%arg0 : i64):
    %c_64_32 = llvm.mlir.constant(32 : i64) : i64
    %1 = llvm.lshr %arg0, %c_64_32 : i64
    %2 = llvm.trunc %1 overflow<nuw> : i64 to i32
    %c_32_55296 = llvm.mlir.constant(55296 : i32) : i32
    %3 = llvm.xor %2, %c_32_55296 : i32
    %c_32_m1114112 = llvm.mlir.constant(-1114112 : i32) : i32
    %4 = llvm.add %3, %c_32_m1114112 : i32
    %c_32_m1112064 = llvm.mlir.constant(-1112064 : i32) : i32
    %5 = llvm.icmp "ult" %4, %c_32_m1112064 : i32
    llvm.return %5 : i1
  }
  }]

abbrev i143957_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 64]
def i143957_arg0 (V : InstCombine.InputValuation i143957_ctx) : LLVM.IntW 64 :=
  V (Ctxt.Var.mk (Γ := i143957_ctx) (t := InstCombine.LLVM.Ty.bitvec 64) 0 (by simp [i143957_ctx]))
def i143957_src_sem (V : InstCombine.InputValuation i143957_ctx) : LLVM.IntW 1 :=
  (LLVM.or (LLVM.icmp LLVM.IntPred.eq (LLVM.lshr (i143957_arg0 V) (LLVM.const? 64 32)) (LLVM.const? 64 1114112)) (LLVM.icmp LLVM.IntPred.ult (LLVM.add (LLVM.xor (LLVM.trunc 32 (LLVM.lshr (i143957_arg0 V) (LLVM.const? 64 32)) (LLVM.NoWrapFlags.mk false true)) (LLVM.const? 32 55296)) (LLVM.const? 32 (-1114112))) (LLVM.const? 32 (-1112064))))
def i143957_tgt_sem (V : InstCombine.InputValuation i143957_ctx) : LLVM.IntW 1 :=
  (LLVM.icmp LLVM.IntPred.ult (LLVM.add (LLVM.xor (LLVM.trunc 32 (LLVM.lshr (i143957_arg0 V) (LLVM.const? 64 32)) (LLVM.NoWrapFlags.mk false true)) (LLVM.const? 32 55296)) (LLVM.const? 32 (-1114112))) (LLVM.const? 32 (-1112064)))
def i143957_ret (x : LLVM.IntW 1) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) ::ₕ HVector.nil

theorem i143957_value (arg0 : LLVM.IntW 64) :
    (LLVM.or (LLVM.icmp LLVM.IntPred.eq (LLVM.lshr arg0 (LLVM.const? 64 32)) (LLVM.const? 64 1114112)) (LLVM.icmp LLVM.IntPred.ult (LLVM.add (LLVM.xor (LLVM.trunc 32 (LLVM.lshr arg0 (LLVM.const? 64 32)) (LLVM.NoWrapFlags.mk false true)) (LLVM.const? 32 55296)) (LLVM.const? 32 (-1114112))) (LLVM.const? 32 (-1112064))))
      ⊑ (LLVM.icmp LLVM.IntPred.ult (LLVM.add (LLVM.xor (LLVM.trunc 32 (LLVM.lshr arg0 (LLVM.const? 64 32)) (LLVM.NoWrapFlags.mk false true)) (LLVM.const? 32 55296)) (LLVM.const? 32 (-1114112))) (LLVM.const? 32 (-1112064))) := by
  cases arg0 with
  | poison =>
      simp [LLVM.or, LLVM.or?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.lshr, LLVM.lshr?,
        LLVM.trunc, LLVM.trunc?, LLVM.xor, LLVM.xor?, LLVM.add, LLVM.add?, LLVM.const?]
  | value x =>
      simp [LLVM.or, LLVM.or?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.lshr, LLVM.lshr?,
        LLVM.trunc, LLVM.trunc?, LLVM.xor, LLVM.xor?, LLVM.add, LLVM.add?, LLVM.const?]
      split <;> simp_all
      by_cases hA : x >>> (32 : Nat) = 1114112#64
      · rw [hA]
        decide
      · rw [beq_eq_false_iff_ne.mpr hA, Bool.false_or]

theorem i143957_correct : i143957_src ⊑ i143957_tgt := by
  unfold i143957_src i143957_tgt
  intro V
  change
    (some (i143957_ret (i143957_src_sem V)) ⊑ some (i143957_ret (i143957_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i143957_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i143957_src_sem, i143957_tgt_sem] using
        i143957_value (i143957_arg0 V)
  · exact True.intro
