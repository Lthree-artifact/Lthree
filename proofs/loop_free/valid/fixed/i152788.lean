import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i152788_src :=
  [llvm()| {
  llvm.func @i152788_src(%0 : i32) -> i64 {
  ^bb0(%0 : i32):
    %c_32_1 = llvm.mlir.constant(1 : i32) : i32
    %v0 = llvm.add %0, %c_32_1 overflow<nsw> : i32
    %v1 = llvm.shl %0, %c_32_1 overflow<nsw> : i32
    %v2_smax_cmp = llvm.icmp "sgt" %v1, %v0 : i32
    %v2 = llvm.select %v2_smax_cmp, %v1, %v0 : i32
    %c_32_4 = llvm.mlir.constant(4 : i32) : i32
    %v3_smax_cmp = llvm.icmp "sgt" %v2, %c_32_4 : i32
    %v3 = llvm.select %v3_smax_cmp, %v2, %c_32_4 : i32
    %v4 = llvm.zext nneg %v3 : i32 to i64
    %c_64_3 = llvm.mlir.constant(3 : i64) : i64
    %v5 = llvm.shl %v4, %c_64_3 overflow<nsw,nuw> : i64
    llvm.return %v5 : i64
  }
  }]

def i152788_tgt :=
  [llvm()| {
  llvm.func @i152788_tgt(%0 : i32) -> i64 {
  ^bb0(%0 : i32):
    %c_32_1 = llvm.mlir.constant(1 : i32) : i32
    %v1 = llvm.shl %0, %c_32_1 overflow<nsw> : i32
    %c_32_4 = llvm.mlir.constant(4 : i32) : i32
    %v2_smax_cmp = llvm.icmp "sgt" %v1, %c_32_4 : i32
    %v2 = llvm.select %v2_smax_cmp, %v1, %c_32_4 : i32
    %v3 = llvm.zext nneg %v2 : i32 to i64
    %c_64_3 = llvm.mlir.constant(3 : i64) : i64
    %v4 = llvm.shl %v3, %c_64_3 overflow<nsw,nuw> : i64
    llvm.return %v4 : i64
  }
  }]

abbrev i152788_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32]
def i152788_v0 (V : InstCombine.InputValuation i152788_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := i152788_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 0 (by simp [i152788_ctx]))
def i152788_src_sem (V : InstCombine.InputValuation i152788_ctx) : LLVM.IntW 64 :=
  (LLVM.shl (LLVM.zext 64 (LLVM.select (LLVM.icmp LLVM.IntPred.sgt (LLVM.select (LLVM.icmp LLVM.IntPred.sgt (LLVM.shl (i152788_v0 V) (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false)) (LLVM.add (i152788_v0 V) (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false))) (LLVM.shl (i152788_v0 V) (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false)) (LLVM.add (i152788_v0 V) (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false))) (LLVM.const? 32 4)) (LLVM.select (LLVM.icmp LLVM.IntPred.sgt (LLVM.shl (i152788_v0 V) (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false)) (LLVM.add (i152788_v0 V) (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false))) (LLVM.shl (i152788_v0 V) (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false)) (LLVM.add (i152788_v0 V) (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false))) (LLVM.const? 32 4)) (LLVM.NonNegFlag.mk true)) (LLVM.const? 64 3) (LLVM.NoWrapFlags.mk true true))
def i152788_tgt_sem (V : InstCombine.InputValuation i152788_ctx) : LLVM.IntW 64 :=
  (LLVM.shl (LLVM.zext 64 (LLVM.select (LLVM.icmp LLVM.IntPred.sgt (LLVM.shl (i152788_v0 V) (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false)) (LLVM.const? 32 4)) (LLVM.shl (i152788_v0 V) (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false)) (LLVM.const? 32 4)) (LLVM.NonNegFlag.mk true)) (LLVM.const? 64 3) (LLVM.NoWrapFlags.mk true true))
def i152788_ret (x : LLVM.IntW 64) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 64] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 64)) ::ₕ HVector.nil

theorem i152788_ofBool_eq_one_iff {b : Bool} : BitVec.ofBool b = 1#1 ↔ b = true := by
  cases b <;> decide

theorem i152788_contra_shl (a : BitVec 32) (h1 : (a <<< 1).sshiftRight 1 = a)
    (h3 : ¬ BitVec.ofBool (a + 1#32 <ₛ a <<< 1) = 1#1)
    (h4 : BitVec.ofBool (4#32 <ₛ a <<< 1) = 1#1) : False := by
  have h1' := congrArg BitVec.toInt h1
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow] at h1'
  rw [i152788_ofBool_eq_one_iff] at h3 h4
  simp only [BitVec.slt, decide_eq_true_eq] at h3 h4
  simp only [BitVec.toInt_eq_toNat_cond] at h1' h3 h4
  have hn : a.toNat < 4294967296 := a.isLt
  bv_omega

theorem i152788_contra_add (a : BitVec 32) (h1 : (a <<< 1).sshiftRight 1 = a)
    (h3 : ¬ BitVec.ofBool (a + 1#32 <ₛ a <<< 1) = 1#1)
    (h4 : BitVec.ofBool (4#32 <ₛ a + 1#32) = 1#1) : False := by
  have h1' := congrArg BitVec.toInt h1
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow] at h1'
  rw [i152788_ofBool_eq_one_iff] at h3 h4
  simp only [BitVec.slt, decide_eq_true_eq] at h3 h4
  simp only [BitVec.toInt_eq_toNat_cond] at h1' h3 h4
  have hn : a.toNat < 4294967296 := a.isLt
  bv_omega

theorem i152788_value (v0 : LLVM.IntW 32) :
    (LLVM.shl (LLVM.zext 64 (LLVM.select (LLVM.icmp LLVM.IntPred.sgt (LLVM.select (LLVM.icmp LLVM.IntPred.sgt (LLVM.shl v0 (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false)) (LLVM.add v0 (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false))) (LLVM.shl v0 (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false)) (LLVM.add v0 (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false))) (LLVM.const? 32 4)) (LLVM.select (LLVM.icmp LLVM.IntPred.sgt (LLVM.shl v0 (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false)) (LLVM.add v0 (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false))) (LLVM.shl v0 (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false)) (LLVM.add v0 (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false))) (LLVM.const? 32 4)) (LLVM.NonNegFlag.mk true)) (LLVM.const? 64 3) (LLVM.NoWrapFlags.mk true true))
      ⊑ (LLVM.shl (LLVM.zext 64 (LLVM.select (LLVM.icmp LLVM.IntPred.sgt (LLVM.shl v0 (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false)) (LLVM.const? 32 4)) (LLVM.shl v0 (LLVM.const? 32 1) (LLVM.NoWrapFlags.mk true false)) (LLVM.const? 32 4)) (LLVM.NonNegFlag.mk true)) (LLVM.const? 64 3) (LLVM.NoWrapFlags.mk true true)) := by
  cases v0 with
  | poison =>
      simp [LLVM.shl, LLVM.shl?, LLVM.add, LLVM.add?, LLVM.icmp, LLVM.icmp?, LLVM.icmp',
        LLVM.select, LLVM.zext, LLVM.zext?, LLVM.const?]
  | value a =>
      simp [LLVM.shl, LLVM.shl?, LLVM.add, LLVM.add?, LLVM.icmp, LLVM.icmp?, LLVM.icmp',
        LLVM.select, LLVM.zext, LLVM.zext?, LLVM.const?]
      split_ifs
      all_goals simp_all
      all_goals try split_ifs
      all_goals simp_all
      all_goals try split_ifs
      all_goals simp_all
      all_goals try split_ifs
      all_goals simp_all
      all_goals (exfalso; first
        | exact i152788_contra_shl a ‹_› ‹_› ‹_›
        | exact i152788_contra_add a ‹_› ‹_› ‹_›)

theorem i152788_correct : i152788_src ⊑ i152788_tgt := by
  unfold i152788_src i152788_tgt
  intro V
  change
    (some (i152788_ret (i152788_src_sem V)) ⊑ some (i152788_ret (i152788_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i152788_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i152788_src_sem, i152788_tgt_sem] using
        i152788_value (i152788_v0 V)
  · exact True.intro
