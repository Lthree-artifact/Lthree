import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i167003_sym_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167003_sym_src(%C : _, %arg1 : _, %newvar_v1 : _) -> _ {
  ^bb0(%C : _, %arg1 : _, %newvar_v1 : _):
    %v0 = llvm.sub %C, %arg1 overflow<nsw> : _
    %v2 = llvm.sub %newvar_v1, %arg1 overflow<nsw> : _
    %c3 = llvm.icmp "slt" %v0, %v2 : _
    %v3 = llvm.select %c3, %v0, %v2 : _
    %v4 = llvm.add %v3, %arg1 : _
    llvm.return %v4 : _
  }
  }]

def i167003_sym_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167003_sym_tgt(%C : _, %arg1 : _, %newvar_v1 : _) -> _ {
  ^bb0(%C : _, %arg1 : _, %newvar_v1 : _):
    %c3 = llvm.icmp "slt" %newvar_v1, %C : _
    %v3 = llvm.select %c3, %newvar_v1, %C : _
    llvm.return %v3 : _
  }
  }]

abbrev i167003_sym_ctx (w : Nat) : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]
def i167003_sym_C (w : Nat) (V : InstCombine.InputValuation (i167003_sym_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i167003_sym_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 2 (by simp [i167003_sym_ctx]))
def i167003_sym_arg1 (w : Nat) (V : InstCombine.InputValuation (i167003_sym_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i167003_sym_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 1 (by simp [i167003_sym_ctx]))
def i167003_sym_newvar_v1 (w : Nat) (V : InstCombine.InputValuation (i167003_sym_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i167003_sym_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 0 (by simp [i167003_sym_ctx]))
def i167003_sym_src_sem (w : Nat) (V : InstCombine.InputValuation (i167003_sym_ctx w)) : LLVM.IntW w :=
  (LLVM.add (LLVM.select (LLVM.icmp LLVM.IntPred.slt (LLVM.sub (i167003_sym_C w V) (i167003_sym_arg1 w V) (LLVM.NoWrapFlags.mk true false)) (LLVM.sub (i167003_sym_newvar_v1 w V) (i167003_sym_arg1 w V) (LLVM.NoWrapFlags.mk true false))) (LLVM.sub (i167003_sym_C w V) (i167003_sym_arg1 w V) (LLVM.NoWrapFlags.mk true false)) (LLVM.sub (i167003_sym_newvar_v1 w V) (i167003_sym_arg1 w V) (LLVM.NoWrapFlags.mk true false))) (i167003_sym_arg1 w V))
def i167003_sym_tgt_sem (w : Nat) (V : InstCombine.InputValuation (i167003_sym_ctx w)) : LLVM.IntW w :=
  (LLVM.select (LLVM.icmp LLVM.IntPred.slt (i167003_sym_newvar_v1 w V) (i167003_sym_C w V)) (i167003_sym_newvar_v1 w V) (i167003_sym_C w V))
def i167003_sym_ret (x : LLVM.IntW w) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec w] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec w)) ::ₕ HVector.nil

theorem i167003_sym_value (w : Nat) (C : LLVM.IntW w) (arg1 : LLVM.IntW w) (newvar_v1 : LLVM.IntW w) :
    (LLVM.add (LLVM.select (LLVM.icmp LLVM.IntPred.slt (LLVM.sub C arg1 (LLVM.NoWrapFlags.mk true false)) (LLVM.sub newvar_v1 arg1 (LLVM.NoWrapFlags.mk true false))) (LLVM.sub C arg1 (LLVM.NoWrapFlags.mk true false)) (LLVM.sub newvar_v1 arg1 (LLVM.NoWrapFlags.mk true false))) arg1)
      ⊑ (LLVM.select (LLVM.icmp LLVM.IntPred.slt newvar_v1 C) newvar_v1 C) := by
  cases C <;> cases arg1 <;> cases newvar_v1 <;>
    simp [LLVM.add, LLVM.sub, LLVM.add?, LLVM.sub?, LLVM.select, LLVM.icmp, BitVec.slt]
  all_goals split_ifs <;> simp_all
  · rename_i C arg v hC hv hsel
    have hC' : ¬ C.ssubOverflow arg = true := by simp [hC]
    have hv' : ¬ v.ssubOverflow arg = true := by simp [hv]
    have hCbmod : (C.toInt - arg.toInt).bmod (2 ^ w) = C.toInt - arg.toInt := by
      simpa [BitVec.toInt_sub] using BitVec.toInt_sub_of_not_ssubOverflow hC'
    have hvbmod : (v.toInt - arg.toInt).bmod (2 ^ w) = v.toInt - arg.toInt := by
      simpa [BitVec.toInt_sub] using BitVec.toInt_sub_of_not_ssubOverflow hv'
    have hvltC : v.toInt < C.toInt := by
      have hb : decide (v.toInt < C.toInt) = true :=
        BitVec.ofBool_eq_iff_eq.mp (by simpa using hsel)
      exact of_decide_eq_true hb
    have hCnotltv : ¬ C.toInt < v.toInt := by omega
    simp [hCbmod, hvbmod, hCnotltv, BitVec.sub_add_cancel]
  · rename_i C arg v hC hv hsel
    have hC' : ¬ C.ssubOverflow arg = true := by simp [hC]
    have hv' : ¬ v.ssubOverflow arg = true := by simp [hv]
    have hCbmod : (C.toInt - arg.toInt).bmod (2 ^ w) = C.toInt - arg.toInt := by
      simpa [BitVec.toInt_sub] using BitVec.toInt_sub_of_not_ssubOverflow hC'
    have hvbmod : (v.toInt - arg.toInt).bmod (2 ^ w) = v.toInt - arg.toInt := by
      simpa [BitVec.toInt_sub] using BitVec.toInt_sub_of_not_ssubOverflow hv'
    have hnlt : ¬ v.toInt < C.toInt := by
      intro hvltC
      apply hsel
      simp [hvltC]
    by_cases hCltv : C.toInt < v.toInt
    · simp [hCbmod, hvbmod, hCltv, BitVec.sub_add_cancel]
    · have hEqInt : C.toInt = v.toInt := by omega
      have hEq : C = v := BitVec.toInt_inj.mp hEqInt
      simp [hvbmod, hEq, BitVec.sub_add_cancel]

theorem i167003_sym_correct (w : Nat) : i167003_sym_src w ⊑ i167003_sym_tgt w := by
  unfold i167003_sym_src i167003_sym_tgt
  intro V
  change
    (some (i167003_sym_ret (i167003_sym_src_sem w V)) ⊑ some (i167003_sym_ret (i167003_sym_tgt_sem w V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i167003_sym_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i167003_sym_src_sem, i167003_sym_tgt_sem] using
        i167003_sym_value w (i167003_sym_C w V) (i167003_sym_arg1 w V) (i167003_sym_newvar_v1 w V)
  · exact True.intro
