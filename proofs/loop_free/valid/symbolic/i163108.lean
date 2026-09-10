import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i163108_src (w : Nat) (_h : 2 ≤ w) :=
  [llvm(w)| {
  llvm.func @i163108_src(%arg0 : i1, %C1 : _, %C2 : _, %C3 : _) -> _ {
  ^bb0(%arg0 : i1, %C1 : _, %C2 : _, %C3 : _):
    %v0 = llvm.zext %arg0 : i1 to _
    %v1 = llvm.select %arg0, %C1, %C2 : _
    %v2 = llvm.or disjoint %v1, %v0 : _
    %v3 = llvm.or disjoint %v2, %C3 : _
    llvm.return %v3 : _
  }
  }]

def i163108_tgt (w : Nat) (_h : 2 ≤ w) :=
  [llvm(w)| {
  llvm.func @i163108_tgt(%arg0 : i1, %C1 : _, %C2 : _, %C3 : _) -> _ {
  ^bb0(%arg0 : i1, %C1 : _, %C2 : _, %C3 : _):
    %one = llvm.mlir.constant(1 : _) : _
    %t = llvm.or disjoint %C1, %one : _
    %t2 = llvm.or disjoint %t, %C3 : _
    %f = llvm.or disjoint %C2, %C3 : _
    %res = llvm.select %arg0, %t2, %f : _
    llvm.return %res : _
  }
  }]

abbrev i163108_ctx (w : Nat) : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec 1]
def i163108_arg0 (w : Nat) (V : InstCombine.InputValuation (i163108_ctx w)) : LLVM.IntW 1 :=
  V (Ctxt.Var.mk (Γ := i163108_ctx w) (t := InstCombine.LLVM.Ty.bitvec 1) 3 (by simp [i163108_ctx]))
def i163108_C1 (w : Nat) (V : InstCombine.InputValuation (i163108_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i163108_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 2 (by simp [i163108_ctx]))
def i163108_C2 (w : Nat) (V : InstCombine.InputValuation (i163108_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i163108_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 1 (by simp [i163108_ctx]))
def i163108_C3 (w : Nat) (V : InstCombine.InputValuation (i163108_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i163108_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 0 (by simp [i163108_ctx]))
def i163108_src_sem (w : Nat) (V : InstCombine.InputValuation (i163108_ctx w)) : LLVM.IntW w :=
  (LLVM.or (LLVM.or (LLVM.select (i163108_arg0 w V) (i163108_C1 w V) (i163108_C2 w V)) (LLVM.zext w (i163108_arg0 w V)) (LLVM.DisjointFlag.mk true)) (i163108_C3 w V) (LLVM.DisjointFlag.mk true))
def i163108_tgt_sem (w : Nat) (V : InstCombine.InputValuation (i163108_ctx w)) : LLVM.IntW w :=
  (LLVM.select (i163108_arg0 w V) (LLVM.or (LLVM.or (i163108_C1 w V) (LLVM.const? w 1) (LLVM.DisjointFlag.mk true)) (i163108_C3 w V) (LLVM.DisjointFlag.mk true)) (LLVM.or (i163108_C2 w V) (i163108_C3 w V) (LLVM.DisjointFlag.mk true)))
def i163108_ret (x : LLVM.IntW w) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec w] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec w)) ::ₕ HVector.nil

theorem i163108_value (w : Nat) (_h : 2 ≤ w) (arg0 : LLVM.IntW 1) (C1 : LLVM.IntW w) (C2 : LLVM.IntW w) (C3 : LLVM.IntW w) :
    (LLVM.or (LLVM.or (LLVM.select arg0 C1 C2) (LLVM.zext w arg0) (LLVM.DisjointFlag.mk true)) C3 (LLVM.DisjointFlag.mk true))
      ⊑ (LLVM.select arg0 (LLVM.or (LLVM.or C1 (LLVM.const? w 1) (LLVM.DisjointFlag.mk true)) C3 (LLVM.DisjointFlag.mk true)) (LLVM.or C2 C3 (LLVM.DisjointFlag.mk true))) := by
  have hset_one : setWidth w (1#1) = (1#w) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth]
  cases arg0 with
  | poison =>
      simp [LLVM.or, LLVM.select, LLVM.zext, LLVM.const?, LLVM.or?, LLVM.zext?,
        LLVM.SemVal.instMonad]
  | value a =>
      have ha : a = 0#1 ∨ a = 1#1 := by
        revert a
        decide
      rcases ha with rfl | rfl
      · cases C1 <;> cases C2 <;> cases C3 <;>
          simp [LLVM.or, LLVM.select, LLVM.zext, LLVM.const?, LLVM.or?, LLVM.zext?,
            LLVM.SemVal.instMonad]
      · cases C1 <;> cases C2 <;> cases C3 <;>
          simp [LLVM.or, LLVM.select, LLVM.zext, LLVM.const?, LLVM.or?, LLVM.zext?,
            LLVM.SemVal.instMonad, hset_one]

theorem i163108_correct (w : Nat) (_h : 2 ≤ w) : i163108_src w _h ⊑ i163108_tgt w _h := by
  unfold i163108_src i163108_tgt
  intro V
  change
    (some (i163108_ret (i163108_src_sem w V)) ⊑ some (i163108_ret (i163108_tgt_sem w V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i163108_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i163108_src_sem, i163108_tgt_sem] using
        i163108_value w _h (i163108_arg0 w V) (i163108_C1 w V) (i163108_C2 w V) (i163108_C3 w V)
  · exact True.intro
