import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace InstCombine
namespace TestLoop

def lsr_postinc_exitvalue_safe_src :=
  [llvm()| {
  llvm.func @lsr_postinc_exitvalue_safe_src(%step : i32) -> i32 {
  ^entry(%step : i32):
    %e_zero = llvm.mlir.constant 0 : i32
    llvm.br ^loop(%e_zero : i32, %e_zero : i32)
  ^loop(%k : i32, %iv : i32):
    %iv_next = llvm.add %iv, %step : i32
    %l_one = llvm.mlir.constant 1 : i32
    %k1 = llvm.add %k, %l_one : i32
    %l_two = llvm.mlir.constant 1 : i32
    %cond = llvm.icmp "eq" %k1, %l_two : i32
    llvm.cond_br %cond : i1, ^out(%iv : i32), ^loop(%k1 : i32, %iv_next : i32)
  ^out(%res : i32):
    llvm.return %res : i32
  }
  }]

def lsr_postinc_exitvalue_safe_tgt :=
  [llvm()| {
  llvm.func @lsr_postinc_exitvalue_safe_tgt(%step : i32) -> i32 {
  ^entry(%step : i32):
    %r = llvm.mlir.constant 0 : i32
    llvm.return %r : i32
  }
  }]

private abbrev lsr_postinc_exitvalue_safe_ity : LLVM.Ty := LLVM.Ty.bitvec 32

private abbrev lsr_postinc_exitvalue_safe_ctx : Ctxt LLVM.Ty := Ctxt.ofList [lsr_postinc_exitvalue_safe_ity]

private def lsr_postinc_exitvalue_safe_srcBlocks : CFGBlocks LLVM lsr_postinc_exitvalue_safe_ctx .impure [lsr_postinc_exitvalue_safe_ity] :=
  match lsr_postinc_exitvalue_safe_src with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private theorem lsr_postinc_exitvalue_safe_entry_ne_loop : ¬ ("entry" = "loop") := by
  decide

private theorem lsr_postinc_exitvalue_safe_out_ne_loop : ¬ ("out" = "loop") := by
  decide

private def lsr_postinc_exitvalue_safe_srcLoopTarget : CFGTarget LLVM (Ctxt.ofList [lsr_postinc_exitvalue_safe_ity, lsr_postinc_exitvalue_safe_ity]) where
  name := "loop"
  argTys := [lsr_postinc_exitvalue_safe_ity, lsr_postinc_exitvalue_safe_ity]
  args := (⟨0, by decide⟩ : (Ctxt.ofList [lsr_postinc_exitvalue_safe_ity, lsr_postinc_exitvalue_safe_ity]).Var lsr_postinc_exitvalue_safe_ity) ::ₕ (⟨1, by decide⟩ : (Ctxt.ofList [lsr_postinc_exitvalue_safe_ity, lsr_postinc_exitvalue_safe_ity]).Var lsr_postinc_exitvalue_safe_ity) ::ₕ HVector.nil

private def lsr_postinc_exitvalue_safe_srcLoopVal (j1 j2 : TyDenote.toType lsr_postinc_exitvalue_safe_ity) :
    Ctxt.Valuation (Ctxt.ofList [lsr_postinc_exitvalue_safe_ity, lsr_postinc_exitvalue_safe_ity]) :=
  Ctxt.Valuation.ofHVector (j1 ::ₕ j2 ::ₕ HVector.nil)

private theorem lsr_postinc_exitvalue_safe_src_loop_dispatch
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation lsr_postinc_exitvalue_safe_ctx) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a1 a2 : Γcur.Var lsr_postinc_exitvalue_safe_ity) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel lsr_postinc_exitvalue_safe_srcBlocks V W
            ({ name := "loop", argTys := [lsr_postinc_exitvalue_safe_ity, lsr_postinc_exitvalue_safe_ity], args := a1 ::ₕ a2 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel lsr_postinc_exitvalue_safe_srcBlocks V
            (lsr_postinc_exitvalue_safe_srcLoopVal (W a1) (W a2)) lsr_postinc_exitvalue_safe_srcLoopTarget)
          ∅)
        s := by
  cases fuel <;>
    simp [lsr_postinc_exitvalue_safe_src, lsr_postinc_exitvalue_safe_srcBlocks, lsr_postinc_exitvalue_safe_srcLoopTarget, lsr_postinc_exitvalue_safe_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

private def lsr_postinc_exitvalue_safe_tgtResult (V : Ctxt.Valuation lsr_postinc_exitvalue_safe_ctx) : TyDenote.toType lsr_postinc_exitvalue_safe_ity :=
  (pure (LLVM.const? 32 0))

private def lsr_postinc_exitvalue_safe_inv (j1 j2 : TyDenote.toType lsr_postinc_exitvalue_safe_ity)
    (V : Ctxt.Valuation lsr_postinc_exitvalue_safe_ctx) : Prop :=
  j1 = lsr_postinc_exitvalue_safe_tgtResult V ∧ j2 = lsr_postinc_exitvalue_safe_tgtResult V

private theorem lsr_postinc_exitvalue_safe_step (V : Ctxt.Valuation lsr_postinc_exitvalue_safe_ctx) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType lsr_postinc_exitvalue_safe_ity),
      lsr_postinc_exitvalue_safe_inv j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel lsr_postinc_exitvalue_safe_srcBlocks V
              (lsr_postinc_exitvalue_safe_srcLoopVal j1 j2) lsr_postinc_exitvalue_safe_srcLoopTarget)
            ∅)
          s
        ⊑
        (some (lsr_postinc_exitvalue_safe_tgtResult V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [lsr_postinc_exitvalue_safe_ity] × LLVMMemory.State))) :
    ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType lsr_postinc_exitvalue_safe_ity),
      lsr_postinc_exitvalue_safe_inv j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) lsr_postinc_exitvalue_safe_srcBlocks V
              (lsr_postinc_exitvalue_safe_srcLoopVal j1 j2) lsr_postinc_exitvalue_safe_srcLoopTarget)
            ∅)
          s
        ⊑
        (some (lsr_postinc_exitvalue_safe_tgtResult V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [lsr_postinc_exitvalue_safe_ity] × LLVMMemory.State)) :=
  by
    intro s j1 j2 hinv
    rcases hinv with ⟨rfl, rfl⟩
    cases fuel with
    | zero =>
        simp [lsr_postinc_exitvalue_safe_src, lsr_postinc_exitvalue_safe_srcBlocks, lsr_postinc_exitvalue_safe_srcLoopTarget, lsr_postinc_exitvalue_safe_srcLoopVal,
          lsr_postinc_exitvalue_safe_tgtResult, lsr_postinc_exitvalue_safe_inv, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
          LLVMMemory.CFGBlocks.findMemoryBlock?,
          LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
          LLVMMemory.Op.denoteVec, DialectDenote.denote, LLVM.add, LLVM.add?, LLVM.icmp,
          LLVM.icmp?, LLVM.icmp', LLVM.const?] at *
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    | succ fuel =>
        simp [lsr_postinc_exitvalue_safe_src, lsr_postinc_exitvalue_safe_srcBlocks, lsr_postinc_exitvalue_safe_srcLoopTarget, lsr_postinc_exitvalue_safe_srcLoopVal,
          lsr_postinc_exitvalue_safe_tgtResult, lsr_postinc_exitvalue_safe_inv, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
          LLVMMemory.CFGBlocks.findMemoryBlock?,
          LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
          LLVMMemory.Op.denoteVec, DialectDenote.denote, LLVM.add, LLVM.add?, LLVM.icmp,
          LLVM.icmp?, LLVM.icmp', LLVM.const?] at *
        exact ImmediateUBOr.IsRefinedBy.bothValues (by
          constructor
          · constructor
            · exact IntWUB_le_self _
            · trivial
          · rfl)

private theorem lsr_postinc_exitvalue_safe_loop_refine (V : Ctxt.Valuation lsr_postinc_exitvalue_safe_ctx) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) (j1 j2 : TyDenote.toType lsr_postinc_exitvalue_safe_ity),
      lsr_postinc_exitvalue_safe_inv j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel lsr_postinc_exitvalue_safe_srcBlocks V
              (lsr_postinc_exitvalue_safe_srcLoopVal j1 j2) lsr_postinc_exitvalue_safe_srcLoopTarget)
            ∅)
          s
        ⊑
        (some (lsr_postinc_exitvalue_safe_tgtResult V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [lsr_postinc_exitvalue_safe_ity] × LLVMMemory.State)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s j1 j2 _hinv
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact lsr_postinc_exitvalue_safe_step V fuel ih

theorem lsr_postinc_exitvalue_safe_correct :
    IsRefinedByOnIntWInputsWithMemory lsr_postinc_exitvalue_safe_src (lsr_postinc_exitvalue_safe_tgt.castPureToEff .impure) := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>

      simp [lsr_postinc_exitvalue_safe_src, lsr_postinc_exitvalue_safe_tgt,
        LLVMMemory.Com.denoteWithMemoryFuel, LLVMMemory.Com.denoteWithMemoryFuelIn,
        LLVMMemory.Com.denoteWithMemoryCore, Com.castPureToEff, Com.changeEffect,
        Expr.changeEffect,
        LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
        LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
        LLVMMemory.Op.denoteVec, DialectDenote.denote, LLVM.const?]
      have h := lsr_postinc_exitvalue_safe_loop_refine (InputValuation.lift V) fuel s
        (lsr_postinc_exitvalue_safe_tgtResult (InputValuation.lift V))
        (lsr_postinc_exitvalue_safe_tgtResult (InputValuation.lift V))
        (by simp [lsr_postinc_exitvalue_safe_inv])
      simp [lsr_postinc_exitvalue_safe_srcLoopVal, lsr_postinc_exitvalue_safe_tgtResult, LLVM.const?] at h
      have hdispatch := lsr_postinc_exitvalue_safe_src_loop_dispatch
        (V := InputValuation.lift V)
        (W := (lsr_postinc_exitvalue_safe_tgtResult (InputValuation.lift V)) ::ᵥ (InputValuation.lift V))
        (fuel := fuel)
        (s := s)
        (a1 := Ctxt.Var.last (↑[lsr_postinc_exitvalue_safe_ity]) lsr_postinc_exitvalue_safe_ity)
        (a2 := Ctxt.Var.last (↑[lsr_postinc_exitvalue_safe_ity]) lsr_postinc_exitvalue_safe_ity)
      simp [lsr_postinc_exitvalue_safe_srcLoopVal, lsr_postinc_exitvalue_safe_tgtResult, LLVM.const?] at hdispatch
      rw [← hdispatch] at h
      simpa [lsr_postinc_exitvalue_safe_src, lsr_postinc_exitvalue_safe_tgt, lsr_postinc_exitvalue_safe_srcBlocks, lsr_postinc_exitvalue_safe_srcLoopTarget,
        lsr_postinc_exitvalue_safe_srcLoopVal, lsr_postinc_exitvalue_safe_tgtResult, lsr_postinc_exitvalue_safe_inv,
        LLVMMemory.Com.denoteWithMemoryFuel, LLVMMemory.Com.denoteWithMemoryFuelIn,
        LLVMMemory.Com.denoteWithMemoryCore, Com.castPureToEff, Expr.castPureToEff,
        Com.changeEffect, Expr.changeEffect,
        LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
        LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
        LLVMMemory.Op.denoteVec, DialectDenote.denote, LLVM.const?] using h

end TestLoop
end InstCombine
