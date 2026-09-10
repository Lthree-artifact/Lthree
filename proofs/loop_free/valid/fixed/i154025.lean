import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i154025_src :=
  [llvm()| {
  llvm.func @i154025_src(%arg0 : i32, %arg1 : i32, %arg2 : i32, %arg3 : i32) -> i32 {
  ^bb0(%arg0 : i32, %arg1 : i32, %arg2 : i32, %arg3 : i32):
    %v0 = llvm.or %arg3, %arg2 : i32
    %c_32_0 = llvm.mlir.constant(0 : i32) : i32
    %v1 = llvm.icmp "ne" %arg1, %c_32_0 : i32
    %v2 = llvm.or %v0, %arg0 : i32
    %v3 = llvm.icmp "ne" %v2, %c_32_0 : i32
    %c_1_true = llvm.mlir.constant(true) : i1
    %v4 = llvm.select %v3, %c_1_true, %v1 : i1
    %v5 = llvm.select %v4, %arg0, %c_32_0 : i32
    llvm.return %v5 : i32
  }
  }]

def i154025_tgt :=
  [llvm()| {
  llvm.func @i154025_tgt(%arg0 : i32, %arg1 : i32, %arg2 : i32, %arg3 : i32) -> i32 {
  ^bb0(%arg0 : i32, %arg1 : i32, %arg2 : i32, %arg3 : i32):
    llvm.return %arg0 : i32
  }
  }]

abbrev i154025_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]
def i154025_arg0 (V : InstCombine.InputValuation i154025_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := i154025_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 3 (by simp [i154025_ctx]))
def i154025_arg1 (V : InstCombine.InputValuation i154025_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := i154025_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 2 (by simp [i154025_ctx]))
def i154025_arg2 (V : InstCombine.InputValuation i154025_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := i154025_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 1 (by simp [i154025_ctx]))
def i154025_arg3 (V : InstCombine.InputValuation i154025_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := i154025_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 0 (by simp [i154025_ctx]))
def i154025_src_sem (V : InstCombine.InputValuation i154025_ctx) : LLVM.IntW 32 :=
  (LLVM.select (LLVM.select (LLVM.icmp LLVM.IntPred.ne (LLVM.or (LLVM.or (i154025_arg3 V) (i154025_arg2 V)) (i154025_arg0 V)) (LLVM.const? 32 0)) (LLVM.const? 1 1) (LLVM.icmp LLVM.IntPred.ne (i154025_arg1 V) (LLVM.const? 32 0))) (i154025_arg0 V) (LLVM.const? 32 0))
def i154025_tgt_sem (V : InstCombine.InputValuation i154025_ctx) : LLVM.IntW 32 :=
  (i154025_arg0 V)
def i154025_ret (x : LLVM.IntW 32) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 32] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 32)) ::ₕ HVector.nil

theorem i154025_value (arg0 : LLVM.IntW 32) (arg1 : LLVM.IntW 32) (arg2 : LLVM.IntW 32) (arg3 : LLVM.IntW 32) :
    (LLVM.select (LLVM.select (LLVM.icmp LLVM.IntPred.ne (LLVM.or (LLVM.or arg3 arg2) arg0) (LLVM.const? 32 0)) (LLVM.const? 1 1) (LLVM.icmp LLVM.IntPred.ne arg1 (LLVM.const? 32 0))) arg0 (LLVM.const? 32 0))
      ⊑ arg0 := by
  cases arg0 <;> cases arg1 <;> cases arg2 <;> cases arg3 <;>
    simp [LLVM.select, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.or, LLVM.or?, LLVM.const?]
  · split <;> simp
  · rename_i a0 a1 a2 a3
    by_cases hOr : a3 ||| a2 ||| a0 = 0#32
    · have ha0 : a0 = 0#32 := (BitVec.or_eq_zero_iff.mp hOr).2
      subst a0
      simp
      split <;> simp
    · have hNe : (a3 ||| a2 ||| a0 != 0#32) = true := bne_iff_ne.mpr hOr
      have hCondOr : BitVec.ofBool (a3 ||| a2 ||| a0 != 0#32) = 1#1 := by
        simp [hNe]
      simp [hCondOr]

theorem i154025_correct : i154025_src ⊑ i154025_tgt := by
  unfold i154025_src i154025_tgt
  intro V
  change
    (some (i154025_ret (i154025_src_sem V)) ⊑ some (i154025_ret (i154025_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i154025_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i154025_src_sem, i154025_tgt_sem] using
        i154025_value (i154025_arg0 V) (i154025_arg1 V) (i154025_arg2 V) (i154025_arg3 V)
  · exact True.intro
