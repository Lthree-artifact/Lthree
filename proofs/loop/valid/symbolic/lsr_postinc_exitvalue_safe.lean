import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace InstCombine
namespace TestLoop

def lsr_postinc_exitvalue_safe_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @lsr_postinc_exitvalue_safe_src(%step : _) -> _ {
  ^entry(%step : _):
    %e_zero = llvm.mlir.constant 0 : _
    llvm.br ^loop(%e_zero : _, %e_zero : _)
  ^loop(%k : _, %iv : _):
    %iv_next = llvm.add %iv, %step : _
    %l_one = llvm.mlir.constant 1 : _
    %k1 = llvm.add %k, %l_one : _
    %l_two = llvm.mlir.constant 1 : _
    %cond = llvm.icmp "eq" %k1, %l_two : _
    llvm.cond_br %cond : i1, ^out(%iv : _), ^loop(%k1 : _, %iv_next : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

def lsr_postinc_exitvalue_safe_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @lsr_postinc_exitvalue_safe_tgt(%step : _) -> _ {
  ^entry(%step : _):
    %r = llvm.mlir.constant 0 : _
    llvm.return %r : _
  }
  }]

private abbrev lsr_postinc_exitvalue_safe_ity (w : Nat) : LLVM.Ty := LLVM.Ty.bitvec w

private abbrev lsr_postinc_exitvalue_safe_ctx (w : Nat) : Ctxt LLVM.Ty := Ctxt.ofList [(lsr_postinc_exitvalue_safe_ity w)]

private def lsr_postinc_exitvalue_safe_srcBlocks (w : Nat) : CFGBlocks LLVM (lsr_postinc_exitvalue_safe_ctx w) .impure [(lsr_postinc_exitvalue_safe_ity w)] :=
  match (lsr_postinc_exitvalue_safe_src w) with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private theorem lsr_postinc_exitvalue_safe_entry_ne_loop (w : Nat) : ¬ ("entry" = "loop") := by
  decide

private theorem lsr_postinc_exitvalue_safe_out_ne_loop (w : Nat) : ¬ ("out" = "loop") := by
  decide

private def lsr_postinc_exitvalue_safe_srcLoopTarget (w : Nat) : CFGTarget LLVM (Ctxt.ofList [(lsr_postinc_exitvalue_safe_ity w), (lsr_postinc_exitvalue_safe_ity w)]) where
  name := "loop"
  argTys := [(lsr_postinc_exitvalue_safe_ity w), (lsr_postinc_exitvalue_safe_ity w)]
  args := (⟨0, by rfl⟩ : (Ctxt.ofList [(lsr_postinc_exitvalue_safe_ity w), (lsr_postinc_exitvalue_safe_ity w)]).Var (lsr_postinc_exitvalue_safe_ity w)) ::ₕ (⟨1, by rfl⟩ : (Ctxt.ofList [(lsr_postinc_exitvalue_safe_ity w), (lsr_postinc_exitvalue_safe_ity w)]).Var (lsr_postinc_exitvalue_safe_ity w)) ::ₕ HVector.nil

private def lsr_postinc_exitvalue_safe_srcLoopVal (w : Nat) (j1 j2 : TyDenote.toType (lsr_postinc_exitvalue_safe_ity w)) :
    Ctxt.Valuation (Ctxt.ofList [(lsr_postinc_exitvalue_safe_ity w), (lsr_postinc_exitvalue_safe_ity w)]) :=
  Ctxt.Valuation.ofHVector (j1 ::ₕ j2 ::ₕ HVector.nil)

private theorem lsr_postinc_exitvalue_safe_src_loop_dispatch (w : Nat)
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation (lsr_postinc_exitvalue_safe_ctx w)) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a1 a2 : Γcur.Var (lsr_postinc_exitvalue_safe_ity w)) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (lsr_postinc_exitvalue_safe_srcBlocks w) V W
            ({ name := "loop", argTys := [(lsr_postinc_exitvalue_safe_ity w), (lsr_postinc_exitvalue_safe_ity w)], args := a1 ::ₕ a2 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (lsr_postinc_exitvalue_safe_srcBlocks w) V
            ((lsr_postinc_exitvalue_safe_srcLoopVal w) (W a1) (W a2)) (lsr_postinc_exitvalue_safe_srcLoopTarget w))
          ∅)
        s := by
  cases fuel <;>
    simp [lsr_postinc_exitvalue_safe_src, lsr_postinc_exitvalue_safe_srcBlocks, lsr_postinc_exitvalue_safe_srcLoopTarget, lsr_postinc_exitvalue_safe_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

private def lsr_postinc_exitvalue_safe_tgtResult (w : Nat) (V : Ctxt.Valuation (lsr_postinc_exitvalue_safe_ctx w)) : TyDenote.toType (lsr_postinc_exitvalue_safe_ity w) :=
  (pure (LLVM.const? w 0))

private def lsr_postinc_exitvalue_safe_inv (w : Nat) (j1 j2 : TyDenote.toType (lsr_postinc_exitvalue_safe_ity w))
    (V : Ctxt.Valuation (lsr_postinc_exitvalue_safe_ctx w)) : Prop :=
  j1 = (pure (LLVM.const? w 0)) ∧ j2 = (lsr_postinc_exitvalue_safe_tgtResult w V)

private theorem lsr_postinc_exitvalue_safe_step (w : Nat) (V : Ctxt.Valuation (lsr_postinc_exitvalue_safe_ctx w)) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (lsr_postinc_exitvalue_safe_ity w)),
      (lsr_postinc_exitvalue_safe_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (lsr_postinc_exitvalue_safe_srcBlocks w) V
              ((lsr_postinc_exitvalue_safe_srcLoopVal w) j1 j2) (lsr_postinc_exitvalue_safe_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((lsr_postinc_exitvalue_safe_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(lsr_postinc_exitvalue_safe_ity w)] × LLVMMemory.State))) :
    ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (lsr_postinc_exitvalue_safe_ity w)),
      (lsr_postinc_exitvalue_safe_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) (lsr_postinc_exitvalue_safe_srcBlocks w) V
              ((lsr_postinc_exitvalue_safe_srcLoopVal w) j1 j2) (lsr_postinc_exitvalue_safe_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((lsr_postinc_exitvalue_safe_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(lsr_postinc_exitvalue_safe_ity w)] × LLVMMemory.State)) :=
  by
    intro s j1 j2 hinv
    rcases hinv with ⟨hj1, hj2⟩
    subst j1
    subst j2
    cases fuel with
    | zero =>
        simp [simp_memory, lsr_postinc_exitvalue_safe_tgtResult, lsr_postinc_exitvalue_safe_src, lsr_postinc_exitvalue_safe_srcBlocks,
          lsr_postinc_exitvalue_safe_srcLoopTarget, lsr_postinc_exitvalue_safe_srcLoopVal, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
          LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, DialectDenote.denote,
          LLVMMemory.Op.denoteVec, Op.denote, lift2, LLVM.const?, LLVM.add, LLVM.add?,
          LLVM.icmp, LLVM.icmp?, LLVM.icmp']
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    | succ fuel =>
        simp [simp_memory, lsr_postinc_exitvalue_safe_tgtResult, lsr_postinc_exitvalue_safe_src, lsr_postinc_exitvalue_safe_srcBlocks,
          lsr_postinc_exitvalue_safe_srcLoopTarget, lsr_postinc_exitvalue_safe_srcLoopVal, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
          LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, DialectDenote.denote,
          LLVMMemory.Op.denoteVec, Op.denote, lift2, LLVM.const?, LLVM.add, LLVM.add?,
          LLVM.icmp, LLVM.icmp?, LLVM.icmp']
        exact mem_result_le_self _

private theorem lsr_postinc_exitvalue_safe_loop_refine (w : Nat) (V : Ctxt.Valuation (lsr_postinc_exitvalue_safe_ctx w)) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (lsr_postinc_exitvalue_safe_ity w)),
      (lsr_postinc_exitvalue_safe_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (lsr_postinc_exitvalue_safe_srcBlocks w) V
              ((lsr_postinc_exitvalue_safe_srcLoopVal w) j1 j2) (lsr_postinc_exitvalue_safe_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((lsr_postinc_exitvalue_safe_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(lsr_postinc_exitvalue_safe_ity w)] × LLVMMemory.State)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s j1 j2 _hinv
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact (lsr_postinc_exitvalue_safe_step w) V fuel ih

theorem lsr_postinc_exitvalue_safe_correct (w : Nat) :
    IsRefinedByOnIntWInputsWithMemory (lsr_postinc_exitvalue_safe_src w) ((lsr_postinc_exitvalue_safe_tgt w).castPureToEff .impure) := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>

      simp [simp_memory, lsr_postinc_exitvalue_safe_src, lsr_postinc_exitvalue_safe_tgt,
        LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
        LLVMMemory.CFGBody.denoteWithMemoryFuelCore, LLVMMemory.CFGTerm.denoteWithMemoryFuelCore,
        DialectDenote.denote, LLVMMemory.Op.denoteVec, Op.denote, LLVM.const?,
        Expr.changeEffect, Com.castPureToEff, Com.changeEffect]
      have hdispatch :=
        lsr_postinc_exitvalue_safe_src_loop_dispatch w V.lift ((pure (LLVM.const? w 0)) ::ᵥ V.lift) fuel s
          (Ctxt.Var.last (lsr_postinc_exitvalue_safe_ctx w) (lsr_postinc_exitvalue_safe_ity w))
          (Ctxt.Var.last (lsr_postinc_exitvalue_safe_ctx w) (lsr_postinc_exitvalue_safe_ity w))
      simp [lsr_postinc_exitvalue_safe_src, lsr_postinc_exitvalue_safe_srcBlocks, lsr_postinc_exitvalue_safe_ity, lsr_postinc_exitvalue_safe_ctx, LLVM.const?] at hdispatch
      rw [hdispatch]
      simpa [lsr_postinc_exitvalue_safe_inv, lsr_postinc_exitvalue_safe_tgtResult, lsr_postinc_exitvalue_safe_srcLoopVal,
        lsr_postinc_exitvalue_safe_srcLoopTarget, lsr_postinc_exitvalue_safe_src, lsr_postinc_exitvalue_safe_srcBlocks, lsr_postinc_exitvalue_safe_ity,
        lsr_postinc_exitvalue_safe_ctx, LLVM.const?] using
        (lsr_postinc_exitvalue_safe_loop_refine w V.lift fuel s (pure (LLVM.const? w 0))
          (lsr_postinc_exitvalue_safe_tgtResult w V.lift) ⟨rfl, rfl⟩)

end TestLoop
end InstCombine
