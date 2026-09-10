import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i143211_a2n_src :=
  [llvm()| {
  llvm.func @i143211_a2n_src(%0 : i8, %1 : i8) -> i1 {
  ^bb0(%0 : i8, %1 : i8):
    %3 = llvm.sub %1, %0 overflow<nsw> : i8
    %4 = llvm.add %1, %0 overflow<nsw> : i8
    %5 = llvm.icmp "sgt" %3, %4 : i8
    llvm.return %5 : i1
  }
  }]

def i143211_a2n_tgt :=
  [llvm()| {
  llvm.func @i143211_a2n_tgt(%0 : i8, %1 : i8) -> i1 {
  ^bb0(%0 : i8, %1 : i8):
    %c_8_0 = llvm.mlir.constant(0 : i8) : i8
    %3 = llvm.icmp "slt" %0, %c_8_0 : i8
    llvm.return %3 : i1
  }
  }]

abbrev i143211_a2n_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 8, InstCombine.LLVM.Ty.bitvec 8]
def i143211_a2n_v0 (V : InstCombine.InputValuation i143211_a2n_ctx) : LLVM.IntW 8 :=
  V (Ctxt.Var.mk (Γ := i143211_a2n_ctx) (t := InstCombine.LLVM.Ty.bitvec 8) 1 (by simp [i143211_a2n_ctx]))
def i143211_a2n_v1 (V : InstCombine.InputValuation i143211_a2n_ctx) : LLVM.IntW 8 :=
  V (Ctxt.Var.mk (Γ := i143211_a2n_ctx) (t := InstCombine.LLVM.Ty.bitvec 8) 0 (by simp [i143211_a2n_ctx]))
def i143211_a2n_src_sem (V : InstCombine.InputValuation i143211_a2n_ctx) : LLVM.IntW 1 :=
  (LLVM.icmp LLVM.IntPred.sgt (LLVM.sub (i143211_a2n_v1 V) (i143211_a2n_v0 V) (LLVM.NoWrapFlags.mk true false)) (LLVM.add (i143211_a2n_v1 V) (i143211_a2n_v0 V) (LLVM.NoWrapFlags.mk true false)))
def i143211_a2n_tgt_sem (V : InstCombine.InputValuation i143211_a2n_ctx) : LLVM.IntW 1 :=
  (LLVM.icmp LLVM.IntPred.slt (i143211_a2n_v0 V) (LLVM.const? 8 0))
def i143211_a2n_ret (x : LLVM.IntW 1) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) ::ₕ HVector.nil

theorem i143211_a2n_value (v0 : LLVM.IntW 8) (v1 : LLVM.IntW 8) :
    (LLVM.icmp LLVM.IntPred.sgt (LLVM.sub v1 v0 (LLVM.NoWrapFlags.mk true false)) (LLVM.add v1 v0 (LLVM.NoWrapFlags.mk true false)))
      ⊑ (LLVM.icmp LLVM.IntPred.slt v0 (LLVM.const? 8 0)) := by
  rcases v0 with _ | x <;> rcases v1 with _ | y <;>
    simp [LLVM.icmp, LLVM.add, LLVM.sub, LLVM.const?, LLVM.icmp?, LLVM.icmp', LLVM.add?, LLVM.sub?]
  by_cases hsub : y.ssubOverflow x = true
  · simp [hsub]
  · by_cases hadd : y.saddOverflow x = true
    · simp [hsub, hadd]
    · simp [hsub, hadd]
      apply congrArg BitVec.ofBool
      simp only [BitVec.slt_eq_decide]
      rw [BitVec.toInt_add_of_not_saddOverflow hadd,
          BitVec.toInt_sub_of_not_ssubOverflow hsub,
          BitVec.toInt_zero]
      by_cases hx : x.toInt < 0
      · simp [hx]
        omega
      · simp [hx]
        omega

theorem i143211_a2n_correct : i143211_a2n_src ⊑ i143211_a2n_tgt := by
  unfold i143211_a2n_src i143211_a2n_tgt
  intro V
  change
    (some (i143211_a2n_ret (i143211_a2n_src_sem V)) ⊑ some (i143211_a2n_ret (i143211_a2n_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i143211_a2n_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i143211_a2n_src_sem, i143211_a2n_tgt_sem] using
        i143211_a2n_value (i143211_a2n_v0 V) (i143211_a2n_v1 V)
  · exact True.intro
