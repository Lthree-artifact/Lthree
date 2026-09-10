import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i167190_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167190_src(%arg0 : _, %arg1 : _, %C1 : _, %C2 : _) -> _ {
  ^bb0(%arg0 : _, %arg1 : _, %C1 : _, %C2 : _):
    %C1_f = llvm.freeze %C1 : _
    %C2_f = llvm.freeze %C2 : _
    %v0 = llvm.add %arg1, %arg0 : _
    %v1 = llvm.mul %arg0, %C1_f : _
    %v2 = llvm.mul %v0, %C2_f : _
    %v3 = llvm.sub %v1, %v2 : _
    llvm.return %v3 : _
  }
  }]

def i167190_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167190_tgt(%arg0 : _, %arg1 : _, %C1 : _, %C2 : _) -> _ {
  ^bb0(%arg0 : _, %arg1 : _, %C1 : _, %C2 : _):
    %C1_f = llvm.freeze %C1 : _
    %C2_f = llvm.freeze %C2 : _
    %subC = llvm.sub %C1_f, %C2_f : _
    %v0 = llvm.mul %arg0, %subC : _
    %v1 = llvm.mul %arg1, %C2_f : _
    %v2 = llvm.sub %v0, %v1 : _
    llvm.return %v2 : _
  }
  }]

abbrev i167190_ctx (w : Nat) : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]
def i167190_arg0 (w : Nat) (V : InstCombine.InputValuation (i167190_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i167190_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 3 (by simp [i167190_ctx]))
def i167190_arg1 (w : Nat) (V : InstCombine.InputValuation (i167190_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i167190_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 2 (by simp [i167190_ctx]))
def i167190_C1 (w : Nat) (V : InstCombine.InputValuation (i167190_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i167190_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 1 (by simp [i167190_ctx]))
def i167190_C2 (w : Nat) (V : InstCombine.InputValuation (i167190_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i167190_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 0 (by simp [i167190_ctx]))
def i167190_src_sem (w : Nat) (V : InstCombine.InputValuation (i167190_ctx w)) : LLVM.IntW w :=
  (LLVM.sub (LLVM.mul (i167190_arg0 w V) (LLVM.freeze (i167190_C1 w V))) (LLVM.mul (LLVM.add (i167190_arg1 w V) (i167190_arg0 w V)) (LLVM.freeze (i167190_C2 w V))))
def i167190_tgt_sem (w : Nat) (V : InstCombine.InputValuation (i167190_ctx w)) : LLVM.IntW w :=
  (LLVM.sub (LLVM.mul (i167190_arg0 w V) (LLVM.sub (LLVM.freeze (i167190_C1 w V)) (LLVM.freeze (i167190_C2 w V)))) (LLVM.mul (i167190_arg1 w V) (LLVM.freeze (i167190_C2 w V))))
def i167190_ret (x : LLVM.IntW w) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec w] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec w)) ::ₕ HVector.nil

theorem i167190_value (w : Nat) (arg0 : LLVM.IntW w) (arg1 : LLVM.IntW w) (C1 : LLVM.IntW w) (C2 : LLVM.IntW w) :
    (LLVM.sub (LLVM.mul arg0 (LLVM.freeze C1)) (LLVM.mul (LLVM.add arg1 arg0) (LLVM.freeze C2)))
      ⊑ (LLVM.sub (LLVM.mul arg0 (LLVM.sub (LLVM.freeze C1) (LLVM.freeze C2))) (LLVM.mul arg1 (LLVM.freeze C2))) := by
  cases arg0 <;> cases arg1 <;> cases C1 <;> cases C2 <;>
    simp [LLVM.add, LLVM.sub, LLVM.mul, LLVM.freeze, LLVM.add?, LLVM.sub?, LLVM.mul?,
      BitVec.mul_add, BitVec.sub_eq_add_neg, BitVec.neg_add,
      BitVec.add_assoc, BitVec.add_comm, BitVec.mul_comm]

theorem i167190_correct (w : Nat) : i167190_src w ⊑ i167190_tgt w := by
  unfold i167190_src i167190_tgt
  intro V
  change
    (some (i167190_ret (i167190_src_sem w V)) ⊑ some (i167190_ret (i167190_tgt_sem w V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i167190_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i167190_src_sem, i167190_tgt_sem] using
        i167190_value w (i167190_arg0 w V) (i167190_arg1 w V) (i167190_C1 w V) (i167190_C2 w V)
  · exact True.intro
