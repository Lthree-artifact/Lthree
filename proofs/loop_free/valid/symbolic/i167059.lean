import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i167059_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167059_src(%arg0 : _, %arg1 : _, %C : _) -> i1 {
  ^bb0(%arg0 : _, %arg1 : _, %C : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %v0 = llvm.sub %arg1, %arg0 overflow<nsw> : _
    %v1 = llvm.sub %C, %arg0 overflow<nsw> : _
    %c = llvm.icmp "slt" %v1, %v0 : _
    %v2 = llvm.select %c, %v1, %v0 : _
    %v3 = llvm.icmp "sgt" %v2, %zero : _
    llvm.return %v3 : i1
  }
  }]

def i167059_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167059_tgt(%arg0 : _, %arg1 : _, %C : _) -> i1 {
  ^bb0(%arg0 : _, %arg1 : _, %C : _):
    %v0 = llvm.icmp "slt" %arg0, %C : _
    %v1 = llvm.icmp "slt" %arg0, %arg1 : _
    %v2 = llvm.and %v0, %v1 : i1
    llvm.return %v2 : i1
  }
  }]

abbrev i167059_ctx (w : Nat) : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]
def i167059_arg0 (w : Nat) (V : InstCombine.InputValuation (i167059_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i167059_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 2 (by simp [i167059_ctx]))
def i167059_arg1 (w : Nat) (V : InstCombine.InputValuation (i167059_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i167059_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 1 (by simp [i167059_ctx]))
def i167059_C (w : Nat) (V : InstCombine.InputValuation (i167059_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i167059_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 0 (by simp [i167059_ctx]))
def i167059_src_sem (w : Nat) (V : InstCombine.InputValuation (i167059_ctx w)) : LLVM.IntW 1 :=
  (LLVM.icmp LLVM.IntPred.sgt (LLVM.select (LLVM.icmp LLVM.IntPred.slt (LLVM.sub (i167059_C w V) (i167059_arg0 w V) (LLVM.NoWrapFlags.mk true false)) (LLVM.sub (i167059_arg1 w V) (i167059_arg0 w V) (LLVM.NoWrapFlags.mk true false))) (LLVM.sub (i167059_C w V) (i167059_arg0 w V) (LLVM.NoWrapFlags.mk true false)) (LLVM.sub (i167059_arg1 w V) (i167059_arg0 w V) (LLVM.NoWrapFlags.mk true false))) (LLVM.const? w 0))
def i167059_tgt_sem (w : Nat) (V : InstCombine.InputValuation (i167059_ctx w)) : LLVM.IntW 1 :=
  (LLVM.and (LLVM.icmp LLVM.IntPred.slt (i167059_arg0 w V) (i167059_C w V)) (LLVM.icmp LLVM.IntPred.slt (i167059_arg0 w V) (i167059_arg1 w V)))
def i167059_ret (x : LLVM.IntW 1) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) ::ₕ HVector.nil

theorem i167059_value (w : Nat) (arg0 : LLVM.IntW w) (arg1 : LLVM.IntW w) (C : LLVM.IntW w) :
    (LLVM.icmp LLVM.IntPred.sgt (LLVM.select (LLVM.icmp LLVM.IntPred.slt (LLVM.sub C arg0 (LLVM.NoWrapFlags.mk true false)) (LLVM.sub arg1 arg0 (LLVM.NoWrapFlags.mk true false))) (LLVM.sub C arg0 (LLVM.NoWrapFlags.mk true false)) (LLVM.sub arg1 arg0 (LLVM.NoWrapFlags.mk true false))) (LLVM.const? w 0))
      ⊑ (LLVM.and (LLVM.icmp LLVM.IntPred.slt arg0 C) (LLVM.icmp LLVM.IntPred.slt arg0 arg1)) := by
  cases arg0 with
  | poison =>
      cases arg1 <;> cases C <;>
        simp [LLVM.icmp, LLVM.select, LLVM.sub, LLVM.and, LLVM.const?, LLVM.icmp?,
          LLVM.sub?, LLVM.and?, LLVM.SemVal.instMonad]
  | value a =>
      cases arg1 with
      | poison =>
          cases C with
          | poison =>
              simp [LLVM.icmp, LLVM.select, LLVM.sub, LLVM.and, LLVM.const?, LLVM.icmp?,
                LLVM.sub?, LLVM.and?, LLVM.SemVal.instMonad]
          | value c =>
              simp [LLVM.icmp, LLVM.select, LLVM.sub, LLVM.and, LLVM.const?, LLVM.icmp?,
                LLVM.sub?, LLVM.and?, LLVM.SemVal.instMonad]
              repeat' split at *
              all_goals simp_all
      | value b =>
          cases C with
          | poison =>
              simp [LLVM.icmp, LLVM.select, LLVM.sub, LLVM.and, LLVM.const?, LLVM.icmp?,
                LLVM.sub?, LLVM.and?, LLVM.SemVal.instMonad]
          | value c =>
              by_cases hc : c.ssubOverflow a = true
              · simp [LLVM.icmp, LLVM.select, LLVM.sub, LLVM.and, LLVM.const?, LLVM.icmp?,
                  LLVM.sub?, LLVM.and?, LLVM.SemVal.instMonad, hc]
              · by_cases hb : b.ssubOverflow a = true
                · simp [LLVM.icmp, LLVM.select, LLVM.sub, LLVM.and, LLVM.const?, LLVM.icmp?,
                    LLVM.sub?, LLVM.and?, LLVM.SemVal.instMonad, hc, hb]
                · have hcint : (c - a).toInt = c.toInt - a.toInt :=
                    BitVec.toInt_sub_of_not_ssubOverflow hc
                  have hbint : (b - a).toInt = b.toInt - a.toInt :=
                    BitVec.toInt_sub_of_not_ssubOverflow hb
                  by_cases hcb : c.toInt < b.toInt
                  · simp [LLVM.icmp, LLVM.select, LLVM.sub, LLVM.and, LLVM.const?, LLVM.icmp?,
                      LLVM.sub?, LLVM.and?, LLVM.SemVal.instMonad, LLVM.icmp',
                      BitVec.slt_eq_decide, hc, hb, hcint, hbint, hcb]
                    by_cases hac : a.toInt < c.toInt
                    · have hab : a.toInt < b.toInt := by omega
                      simp [hac, hab]
                    · simp [hac]
                  · simp [LLVM.icmp, LLVM.select, LLVM.sub, LLVM.and, LLVM.const?, LLVM.icmp?,
                      LLVM.sub?, LLVM.and?, LLVM.SemVal.instMonad, LLVM.icmp',
                      BitVec.slt_eq_decide, hc, hb, hcint, hbint, hcb]
                    by_cases hab : a.toInt < b.toInt
                    · have hac : a.toInt < c.toInt := by omega
                      simp [hab, hac]
                    · simp [hab]

theorem i167059_correct (w : Nat) : i167059_src w ⊑ i167059_tgt w := by
  unfold i167059_src i167059_tgt
  intro V
  change
    (some (i167059_ret (i167059_src_sem w V)) ⊑ some (i167059_ret (i167059_tgt_sem w V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i167059_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i167059_src_sem, i167059_tgt_sem] using
        i167059_value w (i167059_arg0 w V) (i167059_arg1 w V) (i167059_C w V)
  · exact True.intro
