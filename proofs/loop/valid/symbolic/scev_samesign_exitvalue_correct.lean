import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace InstCombine
namespace TestLoop

def scev_samesign_exitvalue_correct_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @scev_samesign_exitvalue_correct_src(%unused : _) -> _ {
  ^entry(%unused : _):
    %e_a = llvm.mlir.constant 1 : _
    %e_b = llvm.mlir.constant 0 : _
    %e_xor = llvm.xor %e_a, %e_b : _
    %e_lim = llvm.mlir.constant 100 : _
    %e_guard = llvm.icmp "ult" %e_xor, %e_lim : _
    %e_zero = llvm.mlir.constant 0 : _
    llvm.cond_br %e_guard : i1, ^loop(%e_zero : _), ^out(%e_zero : _)
  ^loop(%f : _):
    %l_one = llvm.mlir.constant 1 : _
    %cmp = llvm.icmp "slt" %f, %l_one : _
    %l_zero = llvm.mlir.constant 0 : _
    llvm.cond_br %cmp : i1, ^loop(%l_one : _), ^out(%l_zero : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

def scev_samesign_exitvalue_correct_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @scev_samesign_exitvalue_correct_tgt(%unused : _) -> _ {
  ^entry(%unused : _):
    %r = llvm.mlir.constant 0 : _
    llvm.return %r : _
  }
  }]

private abbrev scev_samesign_exitvalue_correct_ity (w : Nat) : LLVM.Ty := LLVM.Ty.bitvec w

private abbrev scev_samesign_exitvalue_correct_ctx (w : Nat) : Ctxt LLVM.Ty := Ctxt.ofList [(scev_samesign_exitvalue_correct_ity w)]

private def scev_samesign_exitvalue_correct_srcBlocks (w : Nat) : CFGBlocks LLVM (scev_samesign_exitvalue_correct_ctx w) .impure [(scev_samesign_exitvalue_correct_ity w)] :=
  match (scev_samesign_exitvalue_correct_src w) with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private theorem scev_samesign_exitvalue_correct_entry_ne_loop (w : Nat) : ¬ ("entry" = "loop") := by
  decide

private theorem scev_samesign_exitvalue_correct_out_ne_loop (w : Nat) : ¬ ("out" = "loop") := by
  decide

private def scev_samesign_exitvalue_correct_srcLoopTarget (w : Nat) : CFGTarget LLVM (Ctxt.ofList [(scev_samesign_exitvalue_correct_ity w)]) where
  name := "loop"
  argTys := [(scev_samesign_exitvalue_correct_ity w)]
  args := (⟨0, by rfl⟩ : (Ctxt.ofList [(scev_samesign_exitvalue_correct_ity w)]).Var (scev_samesign_exitvalue_correct_ity w)) ::ₕ HVector.nil

private def scev_samesign_exitvalue_correct_srcLoopVal (w : Nat) (j1 : TyDenote.toType (scev_samesign_exitvalue_correct_ity w)) :
    Ctxt.Valuation (Ctxt.ofList [(scev_samesign_exitvalue_correct_ity w)]) :=
  Ctxt.Valuation.ofHVector (j1 ::ₕ HVector.nil)

private theorem scev_samesign_exitvalue_correct_src_loop_dispatch (w : Nat)
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation (scev_samesign_exitvalue_correct_ctx w)) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a1 : Γcur.Var (scev_samesign_exitvalue_correct_ity w)) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (scev_samesign_exitvalue_correct_srcBlocks w) V W
            ({ name := "loop", argTys := [(scev_samesign_exitvalue_correct_ity w)], args := a1 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (scev_samesign_exitvalue_correct_srcBlocks w) V
            ((scev_samesign_exitvalue_correct_srcLoopVal w) (W a1)) (scev_samesign_exitvalue_correct_srcLoopTarget w))
          ∅)
        s := by
  cases fuel <;>
    simp [scev_samesign_exitvalue_correct_src, scev_samesign_exitvalue_correct_srcBlocks, scev_samesign_exitvalue_correct_srcLoopTarget, scev_samesign_exitvalue_correct_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

private def scev_samesign_exitvalue_correct_tgtResult (w : Nat) (V : Ctxt.Valuation (scev_samesign_exitvalue_correct_ctx w)) : TyDenote.toType (scev_samesign_exitvalue_correct_ity w) :=
  (pure (LLVM.const? w 0))

private def scev_samesign_exitvalue_correct_inv (w : Nat) (j1 : TyDenote.toType (scev_samesign_exitvalue_correct_ity w))
    (V : Ctxt.Valuation (scev_samesign_exitvalue_correct_ctx w)) : Prop :=
  True

private theorem scev_samesign_exitvalue_correct_step (w : Nat) (V : Ctxt.Valuation (scev_samesign_exitvalue_correct_ctx w)) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) (j1 : TyDenote.toType (scev_samesign_exitvalue_correct_ity w)),
      (scev_samesign_exitvalue_correct_inv w) j1 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (scev_samesign_exitvalue_correct_srcBlocks w) V
              ((scev_samesign_exitvalue_correct_srcLoopVal w) j1) (scev_samesign_exitvalue_correct_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((scev_samesign_exitvalue_correct_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(scev_samesign_exitvalue_correct_ity w)] × LLVMMemory.State))) :
    ∀ (s : LLVMMemory.State) (j1 : TyDenote.toType (scev_samesign_exitvalue_correct_ity w)),
      (scev_samesign_exitvalue_correct_inv w) j1 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) (scev_samesign_exitvalue_correct_srcBlocks w) V
              ((scev_samesign_exitvalue_correct_srcLoopVal w) j1) (scev_samesign_exitvalue_correct_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((scev_samesign_exitvalue_correct_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(scev_samesign_exitvalue_correct_ity w)] × LLVMMemory.State)) :=
  by
    intro s j1 _hinv
    cases j1 with
    | none =>
        simp [scev_samesign_exitvalue_correct_src, scev_samesign_exitvalue_correct_srcBlocks, scev_samesign_exitvalue_correct_srcLoopTarget,
          scev_samesign_exitvalue_correct_srcLoopVal, scev_samesign_exitvalue_correct_tgtResult,
          LLVMMemory.CFGTarget.denoteWithMemoryFuel,
          LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
          LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
          Ctxt.Valuation.cons, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp',
          LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.throwUB]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    | some j1v =>
        cases j1v with
        | poison =>
            simp [scev_samesign_exitvalue_correct_src, scev_samesign_exitvalue_correct_srcBlocks, scev_samesign_exitvalue_correct_srcLoopTarget,
              scev_samesign_exitvalue_correct_srcLoopVal, scev_samesign_exitvalue_correct_tgtResult,
              LLVMMemory.CFGTarget.denoteWithMemoryFuel,
              LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
              LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
              LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
              Ctxt.Valuation.cons, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp',
              LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.throwUB]
            exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        | value x =>
            simp [scev_samesign_exitvalue_correct_src, scev_samesign_exitvalue_correct_srcBlocks, scev_samesign_exitvalue_correct_srcLoopTarget,
              scev_samesign_exitvalue_correct_srcLoopVal, scev_samesign_exitvalue_correct_tgtResult,
              LLVMMemory.CFGTarget.denoteWithMemoryFuel,
              LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
              LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
              LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
              Ctxt.Valuation.cons, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp',
              LLVMMemory.CFGBlocks.findMemoryBlock?]
            split
            all_goals try exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
            · split
              · change
                  (ReaderT.run
                        (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (scev_samesign_exitvalue_correct_srcBlocks w) V _ _)
                        ∅).run
                    s
                    ⊑
                    (some ((scev_samesign_exitvalue_correct_tgtResult w) V ::ₕ HVector.nil, s) :
                      ImmediateUBOr
                        (HVector TyDenote.toType [(scev_samesign_exitvalue_correct_ity w)] × LLVMMemory.State))
                rw [scev_samesign_exitvalue_correct_src_loop_dispatch]
                exact ih s (some (LLVM.const? w 1)) True.intro
              · cases fuel <;>
                  simp [LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                    LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                    LLVMMemory.CFGTerm.denoteWithMemoryFuelCore,
                    Ctxt.Valuation.cons,
                    LLVMMemory.CFGBlocks.findMemoryBlock?]
                · exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                · exact mem_result_le_self _

private theorem scev_samesign_exitvalue_correct_loop_refine (w : Nat) (V : Ctxt.Valuation (scev_samesign_exitvalue_correct_ctx w)) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) (j1 : TyDenote.toType (scev_samesign_exitvalue_correct_ity w)),
      (scev_samesign_exitvalue_correct_inv w) j1 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (scev_samesign_exitvalue_correct_srcBlocks w) V
              ((scev_samesign_exitvalue_correct_srcLoopVal w) j1) (scev_samesign_exitvalue_correct_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((scev_samesign_exitvalue_correct_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(scev_samesign_exitvalue_correct_ity w)] × LLVMMemory.State)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s j1 _hinv
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact (scev_samesign_exitvalue_correct_step w) V fuel ih

theorem scev_samesign_exitvalue_correct_correct (w : Nat) :
    IsRefinedByOnIntWInputsWithMemory (scev_samesign_exitvalue_correct_src w) ((scev_samesign_exitvalue_correct_tgt w).castPureToEff .impure) := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>

      simp [scev_samesign_exitvalue_correct_src, scev_samesign_exitvalue_correct_tgt, LLVMMemory.Com.denoteWithMemoryFuel,
        LLVMMemory.Com.denoteWithMemoryFuelIn, LLVMMemory.Com.denoteWithMemoryCore,
        Com.castPureToEff, Com.changeEffect, Expr.changeEffect,
        LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
        LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
        Ctxt.Valuation.cons, LLVM.const?, LLVM.xor, LLVM.xor?, LLVM.icmp, LLVM.icmp?, LLVM.icmp',
        LLVMMemory.CFGBlocks.findMemoryBlock?]
      split
      all_goals try exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      · split
        · change
            StateT.run
                (ReaderT.run
                  (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (scev_samesign_exitvalue_correct_srcBlocks w) V.lift _ _)
                  ∅)
                s
              ⊑
              (some ((scev_samesign_exitvalue_correct_tgtResult w) V.lift ::ₕ HVector.nil, s) :
                ImmediateUBOr (HVector TyDenote.toType [(scev_samesign_exitvalue_correct_ity w)] × LLVMMemory.State))
          rw [scev_samesign_exitvalue_correct_src_loop_dispatch]
          exact (scev_samesign_exitvalue_correct_loop_refine w) V.lift fuel s (some (LLVM.const? w 0)) True.intro
        · cases fuel <;>
            simp [LLVMMemory.CFGTarget.denoteWithMemoryFuel,
              LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
              LLVMMemory.CFGTerm.denoteWithMemoryFuelCore,
              Ctxt.Valuation.cons,
              LLVMMemory.CFGBlocks.findMemoryBlock?]
          · exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
          · exact mem_result_le_self _

end TestLoop
end InstCombine
