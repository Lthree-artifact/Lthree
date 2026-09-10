import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i163093_a2n_src :=
  [llvm()| {
  llvm.func @i163093_a2n_src(%arg0 : i64, %load_v1 : i64, %load_v3 : i64) -> i1 {
  ^bb0(%arg0 : i64, %load_v1 : i64, %load_v3 : i64):
    %v4 = llvm.sub %load_v1, %load_v3 : i64
    %c_64_0 = llvm.mlir.constant(0 : i64) : i64
    %v5 = llvm.icmp "slt" %load_v1, %c_64_0 : i64
    %v6 = llvm.select %v5, %c_64_0, %v4 : i64
    %v7 = llvm.sub %load_v3, %arg0 : i64
    %v8 = llvm.add %v7, %v6 : i64
    %v9 = llvm.icmp "eq" %v8, %c_64_0 : i64
    llvm.return %v9 : i1
  }
  }]

def i163093_a2n_tgt :=
  [llvm()| {
  llvm.func @i163093_a2n_tgt(%arg0 : i64, %load_v1 : i64, %load_v3 : i64) -> i1 {
  ^bb0(%arg0 : i64, %load_v1 : i64, %load_v3 : i64):
    %c_64_0 = llvm.mlir.constant(0 : i64) : i64
    %v4 = llvm.icmp "slt" %load_v1, %c_64_0 : i64
    %v5 = llvm.select %v4, %load_v3, %load_v1 : i64
    %v6 = llvm.sub %v5, %arg0 : i64
    %v7 = llvm.icmp "eq" %v6, %c_64_0 : i64
    llvm.return %v7 : i1
  }
  }]

abbrev i163093_a2n_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64, InstCombine.LLVM.Ty.bitvec 64]
def i163093_a2n_arg0 (V : InstCombine.InputValuation i163093_a2n_ctx) : LLVM.IntW 64 :=
  V (Ctxt.Var.mk (Γ := i163093_a2n_ctx) (t := InstCombine.LLVM.Ty.bitvec 64) 2 (by simp [i163093_a2n_ctx]))
def i163093_a2n_load_v1 (V : InstCombine.InputValuation i163093_a2n_ctx) : LLVM.IntW 64 :=
  V (Ctxt.Var.mk (Γ := i163093_a2n_ctx) (t := InstCombine.LLVM.Ty.bitvec 64) 1 (by simp [i163093_a2n_ctx]))
def i163093_a2n_load_v3 (V : InstCombine.InputValuation i163093_a2n_ctx) : LLVM.IntW 64 :=
  V (Ctxt.Var.mk (Γ := i163093_a2n_ctx) (t := InstCombine.LLVM.Ty.bitvec 64) 0 (by simp [i163093_a2n_ctx]))
def i163093_a2n_src_sem (V : InstCombine.InputValuation i163093_a2n_ctx) : LLVM.IntW 1 :=
  (LLVM.icmp LLVM.IntPred.eq (LLVM.add (LLVM.sub (i163093_a2n_load_v3 V) (i163093_a2n_arg0 V)) (LLVM.select (LLVM.icmp LLVM.IntPred.slt (i163093_a2n_load_v1 V) (LLVM.const? 64 0)) (LLVM.const? 64 0) (LLVM.sub (i163093_a2n_load_v1 V) (i163093_a2n_load_v3 V)))) (LLVM.const? 64 0))
def i163093_a2n_tgt_sem (V : InstCombine.InputValuation i163093_a2n_ctx) : LLVM.IntW 1 :=
  (LLVM.icmp LLVM.IntPred.eq (LLVM.sub (LLVM.select (LLVM.icmp LLVM.IntPred.slt (i163093_a2n_load_v1 V) (LLVM.const? 64 0)) (i163093_a2n_load_v3 V) (i163093_a2n_load_v1 V)) (i163093_a2n_arg0 V)) (LLVM.const? 64 0))
def i163093_a2n_ret (x : LLVM.IntW 1) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) ::ₕ HVector.nil

theorem i163093_a2n_value (arg0 : LLVM.IntW 64) (load_v1 : LLVM.IntW 64) (load_v3 : LLVM.IntW 64) :
    (LLVM.icmp LLVM.IntPred.eq (LLVM.add (LLVM.sub load_v3 arg0) (LLVM.select (LLVM.icmp LLVM.IntPred.slt load_v1 (LLVM.const? 64 0)) (LLVM.const? 64 0) (LLVM.sub load_v1 load_v3))) (LLVM.const? 64 0))
      ⊑ (LLVM.icmp LLVM.IntPred.eq (LLVM.sub (LLVM.select (LLVM.icmp LLVM.IntPred.slt load_v1 (LLVM.const? 64 0)) load_v3 load_v1) arg0) (LLVM.const? 64 0)) := by
  cases arg0 <;> cases load_v1 <;> cases load_v3 <;>
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.sub, LLVM.sub?,
      LLVM.select, LLVM.const?]
  rename_i arg0 load_v1 load_v3
  split
  · simp_all
  · simp_all
    have h : load_v3 - arg0 + (load_v1 - load_v3) = load_v1 - arg0 := by
      calc
        load_v3 - arg0 + (load_v1 - load_v3)
            = (load_v1 - load_v3) + (load_v3 - arg0) := by rw [BitVec.add_comm]
        _ = (load_v1 - load_v3 + load_v3) - arg0 := by
          simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        _ = load_v1 - arg0 := by rw [BitVec.sub_add_cancel]
    rw [h]

theorem i163093_a2n_correct : i163093_a2n_src ⊑ i163093_a2n_tgt := by
  unfold i163093_a2n_src i163093_a2n_tgt
  intro V
  change
    (some (i163093_a2n_ret (i163093_a2n_src_sem V)) ⊑ some (i163093_a2n_ret (i163093_a2n_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i163093_a2n_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i163093_a2n_src_sem, i163093_a2n_tgt_sem] using
        i163093_a2n_value (i163093_a2n_arg0 V) (i163093_a2n_load_v1 V) (i163093_a2n_load_v3 V)
  · exact True.intro
