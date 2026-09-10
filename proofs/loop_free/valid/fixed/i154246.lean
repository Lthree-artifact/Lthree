import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i154246_src :=
  [llvm()| {
  llvm.func @i154246_src(%arg0 : i8, %arg1 : i8) -> i8 {
  ^bb0(%arg0 : i8, %arg1 : i8):
    %c_8_m1 = llvm.mlir.constant(-1 : i8) : i8
    %v0 = llvm.icmp "eq" %arg1, %c_8_m1 : i8
    %c_8_4 = llvm.mlir.constant(4 : i8) : i8
    %v1 = llvm.or %arg0, %c_8_4 : i8
    %v2 = llvm.select %v0, %v1, %arg0 : i8
    %c_8_1 = llvm.mlir.constant(1 : i8) : i8
    %v3 = llvm.or %v2, %c_8_1 : i8
    llvm.return %v3 : i8
  }
  }]

def i154246_tgt :=
  [llvm()| {
  llvm.func @i154246_tgt(%arg0 : i8, %arg1 : i8) -> i8 {
  ^bb0(%arg0 : i8, %arg1 : i8):
    %c_8_m1 = llvm.mlir.constant(-1 : i8) : i8
    %v0 = llvm.icmp "eq" %arg1, %c_8_m1 : i8
    %c_8_5 = llvm.mlir.constant(5 : i8) : i8
    %c_8_1 = llvm.mlir.constant(1 : i8) : i8
    %v1 = llvm.select %v0, %c_8_5, %c_8_1 : i8
    %v2 = llvm.or %arg0, %v1 : i8
    llvm.return %v2 : i8
  }
  }]

abbrev i154246_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 8, InstCombine.LLVM.Ty.bitvec 8]
def i154246_arg0 (V : InstCombine.InputValuation i154246_ctx) : LLVM.IntW 8 :=
  V (Ctxt.Var.mk (Γ := i154246_ctx) (t := InstCombine.LLVM.Ty.bitvec 8) 1 (by simp [i154246_ctx]))
def i154246_arg1 (V : InstCombine.InputValuation i154246_ctx) : LLVM.IntW 8 :=
  V (Ctxt.Var.mk (Γ := i154246_ctx) (t := InstCombine.LLVM.Ty.bitvec 8) 0 (by simp [i154246_ctx]))
def i154246_src_sem (V : InstCombine.InputValuation i154246_ctx) : LLVM.IntW 8 :=
  (LLVM.or (LLVM.select (LLVM.icmp LLVM.IntPred.eq (i154246_arg1 V) (LLVM.const? 8 (-1))) (LLVM.or (i154246_arg0 V) (LLVM.const? 8 4)) (i154246_arg0 V)) (LLVM.const? 8 1))
def i154246_tgt_sem (V : InstCombine.InputValuation i154246_ctx) : LLVM.IntW 8 :=
  (LLVM.or (i154246_arg0 V) (LLVM.select (LLVM.icmp LLVM.IntPred.eq (i154246_arg1 V) (LLVM.const? 8 (-1))) (LLVM.const? 8 5) (LLVM.const? 8 1)))
def i154246_ret (x : LLVM.IntW 8) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 8)) ::ₕ HVector.nil

theorem i154246_value (arg0 : LLVM.IntW 8) (arg1 : LLVM.IntW 8) :
    (LLVM.or (LLVM.select (LLVM.icmp LLVM.IntPred.eq arg1 (LLVM.const? 8 (-1))) (LLVM.or arg0 (LLVM.const? 8 4)) arg0) (LLVM.const? 8 1))
      ⊑ (LLVM.or arg0 (LLVM.select (LLVM.icmp LLVM.IntPred.eq arg1 (LLVM.const? 8 (-1))) (LLVM.const? 8 5) (LLVM.const? 8 1))) := by
  cases arg0 with
  | poison =>
      cases arg1 <;>
        simp [LLVM.or, LLVM.select, LLVM.icmp, LLVM.const?, LLVM.or?, LLVM.icmp', LLVM.icmp?,
          LLVM.SemVal.instMonad, HRefinement.IsRefinedBy, Refinement.ofEq,
          InstCombine.instRefinementBitVec]
      · exact LLVM.SemVal.IsRefinedBy.poisonLeft (α := BitVec 8) (β := BitVec 8)
      · exact LLVM.SemVal.IsRefinedBy.poisonLeft (α := BitVec 8) (β := BitVec 8)
  | value x =>
      cases arg1 with
      | poison =>
          simp [LLVM.or, LLVM.select, LLVM.icmp, LLVM.const?, LLVM.or?, LLVM.icmp',
            LLVM.icmp?, LLVM.SemVal.instMonad, HRefinement.IsRefinedBy, Refinement.ofEq,
            InstCombine.instRefinementBitVec]
          exact LLVM.SemVal.IsRefinedBy.poisonLeft (α := BitVec 8) (β := BitVec 8)
      | value y =>
          simp [LLVM.or, LLVM.select, LLVM.icmp, LLVM.const?, LLVM.or?, LLVM.icmp',
            LLVM.icmp?, LLVM.SemVal.instMonad, HRefinement.IsRefinedBy, Refinement.ofEq,
            InstCombine.instRefinementBitVec]
          by_cases h : ofBool (y == 255#8) = 1#1
          · simp [h]
            apply LLVM.SemVal.IsRefinedBy.bothValues
            change (x ||| 4#8) ||| 1#8 = x ||| 5#8
            rw [BitVec.or_assoc]
            simp [← BitVec.ofNat_or]
          · simp [h]
            apply LLVM.SemVal.IsRefinedBy.bothValues
            rfl

theorem i154246_correct : i154246_src ⊑ i154246_tgt := by
  unfold i154246_src i154246_tgt
  intro V
  change
    (some (i154246_ret (i154246_src_sem V)) ⊑ some (i154246_ret (i154246_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i154246_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i154246_src_sem, i154246_tgt_sem] using
        i154246_value (i154246_arg0 V) (i154246_arg1 V)
  · exact True.intro
