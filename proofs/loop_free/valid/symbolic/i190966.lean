import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i190966_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i190966_src(%x0 : _, %x1 : _, %C1 : _) -> i1 {
  ^bb0(%x0 : _, %x1 : _, %C1 : _):
    %a = llvm.add %x0, %C1 : _
    %b = llvm.sub %a, %x1 : _
    %r = llvm.icmp "eq" %b, %C1 : _
    llvm.return %r : i1
  }
  }]

def i190966_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i190966_tgt(%x0 : _, %x1 : _, %C1 : _) -> i1 {
  ^bb0(%x0 : _, %x1 : _, %C1 : _):
    %r = llvm.icmp "eq" %x0, %x1 : _
    llvm.return %r : i1
  }
  }]

abbrev i190966_ctx (w : Nat) : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]
def i190966_x0 (w : Nat) (V : InstCombine.InputValuation (i190966_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i190966_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 2 (by simp [i190966_ctx]))
def i190966_x1 (w : Nat) (V : InstCombine.InputValuation (i190966_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i190966_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 1 (by simp [i190966_ctx]))
def i190966_C1 (w : Nat) (V : InstCombine.InputValuation (i190966_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i190966_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 0 (by simp [i190966_ctx]))
def i190966_src_sem (w : Nat) (V : InstCombine.InputValuation (i190966_ctx w)) : LLVM.IntW 1 :=
  (LLVM.icmp LLVM.IntPred.eq (LLVM.sub (LLVM.add (i190966_x0 w V) (i190966_C1 w V)) (i190966_x1 w V)) (i190966_C1 w V))
def i190966_tgt_sem (w : Nat) (V : InstCombine.InputValuation (i190966_ctx w)) : LLVM.IntW 1 :=
  (LLVM.icmp LLVM.IntPred.eq (i190966_x0 w V) (i190966_x1 w V))
def i190966_ret (x : LLVM.IntW 1) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) ::ₕ HVector.nil

theorem i190966_value (w : Nat) (x0 : LLVM.IntW w) (x1 : LLVM.IntW w) (C1 : LLVM.IntW w) :
    (LLVM.icmp LLVM.IntPred.eq (LLVM.sub (LLVM.add x0 C1) x1) C1)
      ⊑ (LLVM.icmp LLVM.IntPred.eq x0 x1) := by
  cases x0 <;> cases x1 <;> cases C1 <;>
    simp [LLVM.icmp, LLVM.sub, LLVM.add, LLVM.icmp?, LLVM.sub?, LLVM.add?, LLVM.icmp']
  rename_i a b c
  apply congrArg BitVec.ofBool
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hEq : a + c - b = c := beq_iff_eq.mp h
    have h1 : a + c = c + b := (BitVec.sub_eq_iff_eq_add).mp hEq
    have h2 : a + c = b + c := by simpa [BitVec.add_comm] using h1
    have h3 := congrArg (fun t : BitVec w => t - c) h2
    exact beq_iff_eq.mpr (by simpa [BitVec.add_sub_cancel] using h3)
  · intro h
    have hEq : a = b := beq_iff_eq.mp h
    subst hEq
    exact beq_iff_eq.mpr (by simpa [BitVec.add_comm] using BitVec.add_sub_cancel c a)

theorem i190966_correct (w : Nat) : i190966_src w ⊑ i190966_tgt w := by
  unfold i190966_src i190966_tgt
  intro V
  change
    (some (i190966_ret (i190966_src_sem w V)) ⊑ some (i190966_ret (i190966_tgt_sem w V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i190966_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i190966_src_sem, i190966_tgt_sem] using
        i190966_value w (i190966_x0 w V) (i190966_x1 w V) (i190966_C1 w V)
  · exact True.intro
