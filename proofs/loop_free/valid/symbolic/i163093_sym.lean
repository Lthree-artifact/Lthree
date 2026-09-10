import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i163093_sym_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i163093_sym_src(%arg0 : _, %arg1 : _, %arg2 : _, %C : _) -> i1 {
  ^bb0(%arg0 : _, %arg1 : _, %arg2 : _, %C : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %v4 = llvm.sub %arg2, %arg1 : _
    %v5 = llvm.icmp "slt" %arg2, %C : _
    %v6 = llvm.select %v5, %C, %v4 : _
    %v7 = llvm.sub %arg1, %arg0 : _
    %v8 = llvm.add %v7, %v6 : _
    %v9 = llvm.icmp "eq" %v8, %zero : _
    llvm.return %v9 : i1
  }
  }]

def i163093_sym_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i163093_sym_tgt(%arg0 : _, %arg1 : _, %arg2 : _, %C : _) -> i1 {
  ^bb0(%arg0 : _, %arg1 : _, %arg2 : _, %C : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %v4 = llvm.icmp "slt" %arg2, %C : _
    %v5sub = llvm.add %arg1, %C : _
    %v5 = llvm.select %v4, %v5sub, %arg2 : _
    %v6 = llvm.sub %v5, %arg0 : _
    %v7 = llvm.icmp "eq" %v6, %zero : _
    llvm.return %v7 : i1
  }
  }]

abbrev i163093_sym_ctx (w : Nat) : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]
def i163093_sym_arg0 (w : Nat) (V : InstCombine.InputValuation (i163093_sym_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i163093_sym_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 3 (by simp [i163093_sym_ctx]))
def i163093_sym_arg1 (w : Nat) (V : InstCombine.InputValuation (i163093_sym_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i163093_sym_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 2 (by simp [i163093_sym_ctx]))
def i163093_sym_arg2 (w : Nat) (V : InstCombine.InputValuation (i163093_sym_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i163093_sym_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 1 (by simp [i163093_sym_ctx]))
def i163093_sym_C (w : Nat) (V : InstCombine.InputValuation (i163093_sym_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i163093_sym_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 0 (by simp [i163093_sym_ctx]))
def i163093_sym_src_sem (w : Nat) (V : InstCombine.InputValuation (i163093_sym_ctx w)) : LLVM.IntW 1 :=
  (LLVM.icmp LLVM.IntPred.eq (LLVM.add (LLVM.sub (i163093_sym_arg1 w V) (i163093_sym_arg0 w V)) (LLVM.select (LLVM.icmp LLVM.IntPred.slt (i163093_sym_arg2 w V) (i163093_sym_C w V)) (i163093_sym_C w V) (LLVM.sub (i163093_sym_arg2 w V) (i163093_sym_arg1 w V)))) (LLVM.const? w 0))
def i163093_sym_tgt_sem (w : Nat) (V : InstCombine.InputValuation (i163093_sym_ctx w)) : LLVM.IntW 1 :=
  (LLVM.icmp LLVM.IntPred.eq (LLVM.sub (LLVM.select (LLVM.icmp LLVM.IntPred.slt (i163093_sym_arg2 w V) (i163093_sym_C w V)) (LLVM.add (i163093_sym_arg1 w V) (i163093_sym_C w V)) (i163093_sym_arg2 w V)) (i163093_sym_arg0 w V)) (LLVM.const? w 0))
def i163093_sym_ret (x : LLVM.IntW 1) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) ::ₕ HVector.nil

theorem i163093_sym_value (w : Nat) (arg0 : LLVM.IntW w) (arg1 : LLVM.IntW w) (arg2 : LLVM.IntW w) (C : LLVM.IntW w) :
    (LLVM.icmp LLVM.IntPred.eq (LLVM.add (LLVM.sub arg1 arg0) (LLVM.select (LLVM.icmp LLVM.IntPred.slt arg2 C) C (LLVM.sub arg2 arg1))) (LLVM.const? w 0))
      ⊑ (LLVM.icmp LLVM.IntPred.eq (LLVM.sub (LLVM.select (LLVM.icmp LLVM.IntPred.slt arg2 C) (LLVM.add arg1 C) arg2) arg0) (LLVM.const? w 0)) := by
  cases arg0 <;> cases arg1 <;> cases arg2 <;> cases C <;>
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.sub, LLVM.sub?,
      LLVM.select, LLVM.const?]
  split <;> simp [LLVM.SemVal.value_isRefinedBy_value]
  all_goals grind

theorem i163093_sym_correct (w : Nat) : i163093_sym_src w ⊑ i163093_sym_tgt w := by
  unfold i163093_sym_src i163093_sym_tgt
  intro V
  change
    (some (i163093_sym_ret (i163093_sym_src_sem w V)) ⊑ some (i163093_sym_ret (i163093_sym_tgt_sem w V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i163093_sym_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i163093_sym_src_sem, i163093_sym_tgt_sem] using
        i163093_sym_value w (i163093_sym_arg0 w V) (i163093_sym_arg1 w V) (i163093_sym_arg2 w V) (i163093_sym_C w V)
  · exact True.intro
