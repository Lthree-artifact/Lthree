import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i167199_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167199_src(%C1 : _, %C2 : _, %newvar_v0 : _, %v1 : _) -> i1 {
  ^bb0(%C1 : _, %C2 : _, %newvar_v0 : _, %v1 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %v2 = llvm.shl %C1, %v1 : _
    %v4 = llvm.and %newvar_v0, %v2 : _
    %v5 = llvm.shl %C2, %v1 : _
    %v7 = llvm.and %newvar_v0, %v5 : _
    %v8 = llvm.icmp "ne" %v4, %zero : _
    %v9 = llvm.icmp "ne" %v7, %zero : _
    %v10 = llvm.or %v8, %v9 : i1
    llvm.return %v10 : i1
  }
  }]

def i167199_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167199_tgt(%C1 : _, %C2 : _, %newvar_v0 : _, %v1 : _) -> i1 {
  ^bb0(%C1 : _, %C2 : _, %newvar_v0 : _, %v1 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %C3 = llvm.or %C1, %C2 : _
    %x1 = llvm.shl %C3, %v1 : _
    %x2 = llvm.and %newvar_v0, %x1 : _
    %v8 = llvm.icmp "ne" %x2, %zero : _
    llvm.return %v8 : i1
  }
  }]

abbrev i167199_ctx (w : Nat) : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]
def i167199_C1 (w : Nat) (V : InstCombine.InputValuation (i167199_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i167199_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 3 (by simp [i167199_ctx]))
def i167199_C2 (w : Nat) (V : InstCombine.InputValuation (i167199_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i167199_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 2 (by simp [i167199_ctx]))
def i167199_newvar_v0 (w : Nat) (V : InstCombine.InputValuation (i167199_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i167199_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 1 (by simp [i167199_ctx]))
def i167199_v1 (w : Nat) (V : InstCombine.InputValuation (i167199_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i167199_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 0 (by simp [i167199_ctx]))
def i167199_src_sem (w : Nat) (V : InstCombine.InputValuation (i167199_ctx w)) : LLVM.IntW 1 :=
  (LLVM.or (LLVM.icmp LLVM.IntPred.ne (LLVM.and (i167199_newvar_v0 w V) (LLVM.shl (i167199_C1 w V) (i167199_v1 w V))) (LLVM.const? w 0)) (LLVM.icmp LLVM.IntPred.ne (LLVM.and (i167199_newvar_v0 w V) (LLVM.shl (i167199_C2 w V) (i167199_v1 w V))) (LLVM.const? w 0)))
def i167199_tgt_sem (w : Nat) (V : InstCombine.InputValuation (i167199_ctx w)) : LLVM.IntW 1 :=
  (LLVM.icmp LLVM.IntPred.ne (LLVM.and (i167199_newvar_v0 w V) (LLVM.shl (LLVM.or (i167199_C1 w V) (i167199_C2 w V)) (i167199_v1 w V))) (LLVM.const? w 0))
def i167199_ret (x : LLVM.IntW 1) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) ::ₕ HVector.nil

theorem i167199_value (w : Nat) (C1 : LLVM.IntW w) (C2 : LLVM.IntW w) (newvar_v0 : LLVM.IntW w) (v1 : LLVM.IntW w) :
    (LLVM.or (LLVM.icmp LLVM.IntPred.ne (LLVM.and newvar_v0 (LLVM.shl C1 v1)) (LLVM.const? w 0)) (LLVM.icmp LLVM.IntPred.ne (LLVM.and newvar_v0 (LLVM.shl C2 v1)) (LLVM.const? w 0)))
      ⊑ (LLVM.icmp LLVM.IntPred.ne (LLVM.and newvar_v0 (LLVM.shl (LLVM.or C1 C2) v1)) (LLVM.const? w 0)) := by
  cases C1 <;> cases C2 <;> cases newvar_v0 <;> cases v1 <;>
    simp [LLVM.or, LLVM.icmp, LLVM.and, LLVM.shl, LLVM.const?, LLVM.or?, LLVM.and?,
      LLVM.shl?, LLVM.icmp?]
  · split <;> simp
  · split <;> simp [LLVM.icmp']
    rw [BitVec.shiftLeft_or_distrib, BitVec.and_or_distrib_left]
    simp [bne, Bool.beq_eq_decide_eq, BitVec.or_eq_zero_iff]

theorem i167199_correct (w : Nat) : i167199_src w ⊑ i167199_tgt w := by
  unfold i167199_src i167199_tgt
  intro V
  change
    (some (i167199_ret (i167199_src_sem w V)) ⊑ some (i167199_ret (i167199_tgt_sem w V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i167199_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i167199_src_sem, i167199_tgt_sem] using
        i167199_value w (i167199_C1 w V) (i167199_C2 w V) (i167199_newvar_v0 w V) (i167199_v1 w V)
  · exact True.intro
