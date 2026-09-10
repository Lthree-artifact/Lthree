import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i152237_a2n_src :=
  [llvm()| {
  llvm.func @i152237_a2n_src(%0 : i8) -> i8 {
  ^bb0(%0 : i8):
    %c_8_40 = llvm.mlir.constant(40 : i8) : i8
    %2 = llvm.mul %0, %c_8_40 overflow<nsw> : i8
    %c_8_m40 = llvm.mlir.constant(-40 : i8) : i8
    %3 = llvm.add %2, %c_8_m40 overflow<nsw> : i8
    %4 = llvm.udiv exact %3, %c_8_40 : i8
    llvm.return %4 : i8
  }
  }]

def i152237_a2n_tgt :=
  [llvm()| {
  llvm.func @i152237_a2n_tgt(%0 : i8) -> i8 {
  ^bb0(%0 : i8):
    %c_8_1 = llvm.mlir.constant(1 : i8) : i8
    %2 = llvm.sub %0, %c_8_1 overflow<nsw> : i8
    llvm.return %2 : i8
  }
  }]

abbrev i152237_a2n_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 8]
def i152237_a2n_v0 (V : InstCombine.InputValuation i152237_a2n_ctx) : LLVM.IntW 8 :=
  V (Ctxt.Var.mk (Γ := i152237_a2n_ctx) (t := InstCombine.LLVM.Ty.bitvec 8) 0 (by simp [i152237_a2n_ctx]))
def i152237_a2n_src_sem (V : InstCombine.InputValuation i152237_a2n_ctx) : LLVM.IntWUB 8 :=
  (InstCombine.lift2UB (fun x y => LLVM.udiv x y (LLVM.ExactFlag.mk true)) (InstCombine.lift2 (fun x y => LLVM.add x y (LLVM.NoWrapFlags.mk true false)) (InstCombine.lift2 (fun x y => LLVM.mul x y (LLVM.NoWrapFlags.mk true false)) (some (i152237_a2n_v0 V)) (some (LLVM.const? 8 40))) (some (LLVM.const? 8 (-40)))) (some (LLVM.const? 8 40)))
def i152237_a2n_tgt_sem (V : InstCombine.InputValuation i152237_a2n_ctx) : LLVM.IntWUB 8 :=
  (InstCombine.lift2 (fun x y => LLVM.sub x y (LLVM.NoWrapFlags.mk true false)) (some (i152237_a2n_v0 V)) (some (LLVM.const? 8 1)))
def i152237_a2n_ret (x : LLVM.IntWUB 8) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 8] :=
  (x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 8)) ::ₕ HVector.nil

theorem i152237_a2n_value (v0 : LLVM.IntW 8) :
    (InstCombine.lift2UB (fun x y => LLVM.udiv x y (LLVM.ExactFlag.mk true)) (InstCombine.lift2 (fun x y => LLVM.add x y (LLVM.NoWrapFlags.mk true false)) (InstCombine.lift2 (fun x y => LLVM.mul x y (LLVM.NoWrapFlags.mk true false)) (some v0) (some (LLVM.const? 8 40))) (some (LLVM.const? 8 (-40)))) (some (LLVM.const? 8 40)))
      ⊑ (InstCombine.lift2 (fun x y => LLVM.sub x y (LLVM.NoWrapFlags.mk true false)) (some v0) (some (LLVM.const? 8 1))) := by
  cases v0 with
  | poison =>
      simp [InstCombine.lift2UB, InstCombine.lift2, LLVM.const?, LLVM.mul, LLVM.add,
        LLVM.sub, LLVM.udiv, LLVM.mul?, LLVM.add?, LLVM.sub?]
      exact ImmediateUBOr.IsRefinedBy.bothValues (LLVM.SemVal.IsRefinedBy.poisonLeft)
  | value x =>
      by_cases hmul : x.smulOverflow 40#8 = true
      · simp [InstCombine.lift2UB, InstCombine.lift2, LLVM.const?, LLVM.mul, LLVM.add,
          LLVM.sub, LLVM.udiv, LLVM.mul?, LLVM.add?, LLVM.sub?, hmul]
        split <;> exact ImmediateUBOr.IsRefinedBy.bothValues
          (LLVM.SemVal.IsRefinedBy.poisonLeft)
      · by_cases hadd : (x * 40#8).saddOverflow 216#8 = true
        · simp [InstCombine.lift2UB, InstCombine.lift2, LLVM.const?, LLVM.mul, LLVM.add,
            LLVM.sub, LLVM.udiv, LLVM.mul?, LLVM.add?, LLVM.sub?, hmul, hadd]
          split <;> exact ImmediateUBOr.IsRefinedBy.bothValues
            (LLVM.SemVal.IsRefinedBy.poisonLeft)
        · by_cases hrem : (x * 40#8 + 216#8) % 40#8 = 0#8
          · have hmul' : x.smulOverflow 40#8 = false := by
              cases h : x.smulOverflow 40#8 <;> simp [h] at hmul ⊢
            have hadd' : (x * 40#8).saddOverflow 216#8 = false := by
              cases h : (x * 40#8).saddOverflow 216#8 <;> simp [h] at hadd ⊢
            by_cases hsub : x.ssubOverflow 1#8 = true
            · have hbad : ∀ x : BitVec 8,
                  x.smulOverflow 40#8 = false →
                  (x * 40#8).saddOverflow 216#8 = false →
                  (x * 40#8 + 216#8) % 40#8 = 0#8 →
                  x.ssubOverflow 1#8 = true → False := by
                decide
              exact False.elim (hbad x hmul' hadd' hrem hsub)
            · have hsub' : x.ssubOverflow 1#8 = false := by
                cases h : x.ssubOverflow 1#8 <;> simp [h] at hsub ⊢
              simp [InstCombine.lift2UB, InstCombine.lift2, LLVM.const?, LLVM.mul, LLVM.add,
                LLVM.sub, LLVM.udiv, LLVM.mul?, LLVM.add?, LLVM.sub?, hmul, hadd, hrem, hsub]
              apply ImmediateUBOr.IsRefinedBy.bothValues
              apply LLVM.SemVal.IsRefinedBy.bothValues
              simp
              have hsame : ∀ x : BitVec 8,
                  x.smulOverflow 40#8 = false →
                  (x * 40#8).saddOverflow 216#8 = false →
                  (x * 40#8 + 216#8) % 40#8 = 0#8 →
                  x.ssubOverflow 1#8 = false →
                  (x * 40#8 + 216#8) / 40#8 = x - 1#8 := by
                decide
              exact hsame x hmul' hadd' hrem hsub'
          · simp [InstCombine.lift2UB, InstCombine.lift2, LLVM.const?, LLVM.mul, LLVM.add,
              LLVM.sub, LLVM.udiv, LLVM.mul?, LLVM.add?, LLVM.sub?, hmul, hadd, hrem]
            split <;> exact ImmediateUBOr.IsRefinedBy.bothValues
              (LLVM.SemVal.IsRefinedBy.poisonLeft)

theorem i152237_a2n_correct : i152237_a2n_src ⊑ i152237_a2n_tgt := by
  unfold i152237_a2n_src i152237_a2n_tgt
  intro V
  change
    (some (i152237_a2n_ret (i152237_a2n_src_sem V)) ⊑ some (i152237_a2n_ret (i152237_a2n_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i152237_a2n_ret
  constructor
  · exact (by
      simpa [i152237_a2n_src_sem, i152237_a2n_tgt_sem] using
        i152237_a2n_value (i152237_a2n_v0 V))
  · exact True.intro
