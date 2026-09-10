import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace InstCombine
namespace TestLoop

def scev_nuw_exitvalue_correct_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @scev_nuw_exitvalue_correct_src(%unused : _) -> _ {
  ^entry(%unused : _):
    %e_index = llvm.mlir.constant 0 : _
    %e_vec = llvm.mlir.constant -8 : _
    llvm.br ^loop(%e_index : _, %e_vec : _)
  ^loop(%index : _, %vec : _):
    %l_four = llvm.mlir.constant 4 : _
    %index_next = llvm.add %index, %l_four : _
    %vec_next = llvm.add %vec, %l_four overflow<nuw> : _
    %l_twelve = llvm.mlir.constant 12 : _
    %cmp = llvm.icmp "eq" %index_next, %l_twelve : _
    %l_zero = llvm.mlir.constant 0 : _
    llvm.cond_br %cmp : i1, ^out(%l_zero : _), ^loop(%index_next : _, %vec_next : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

def scev_nuw_exitvalue_correct_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @scev_nuw_exitvalue_correct_tgt(%unused : _) -> _ {
  ^entry(%unused : _):
    %r = llvm.mlir.constant 0 : _
    llvm.return %r : _
  }
  }]

private abbrev scev_nuw_exitvalue_correct_ity (w : Nat) : LLVM.Ty := LLVM.Ty.bitvec w

private abbrev scev_nuw_exitvalue_correct_ctx (w : Nat) : Ctxt LLVM.Ty := Ctxt.ofList [(scev_nuw_exitvalue_correct_ity w)]

private def scev_nuw_exitvalue_correct_srcBlocks (w : Nat) : CFGBlocks LLVM (scev_nuw_exitvalue_correct_ctx w) .impure [(scev_nuw_exitvalue_correct_ity w)] :=
  match (scev_nuw_exitvalue_correct_src w) with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private theorem scev_nuw_exitvalue_correct_entry_ne_loop (w : Nat) : ¬ ("entry" = "loop") := by
  decide

private theorem scev_nuw_exitvalue_correct_out_ne_loop (w : Nat) : ¬ ("out" = "loop") := by
  decide

private def scev_nuw_exitvalue_correct_srcLoopTarget (w : Nat) : CFGTarget LLVM (Ctxt.ofList [(scev_nuw_exitvalue_correct_ity w), (scev_nuw_exitvalue_correct_ity w)]) where
  name := "loop"
  argTys := [(scev_nuw_exitvalue_correct_ity w), (scev_nuw_exitvalue_correct_ity w)]
  args := (⟨0, by rfl⟩ : (Ctxt.ofList [(scev_nuw_exitvalue_correct_ity w), (scev_nuw_exitvalue_correct_ity w)]).Var (scev_nuw_exitvalue_correct_ity w)) ::ₕ (⟨1, by rfl⟩ : (Ctxt.ofList [(scev_nuw_exitvalue_correct_ity w), (scev_nuw_exitvalue_correct_ity w)]).Var (scev_nuw_exitvalue_correct_ity w)) ::ₕ HVector.nil

private def scev_nuw_exitvalue_correct_srcLoopVal (w : Nat) (j1 j2 : TyDenote.toType (scev_nuw_exitvalue_correct_ity w)) :
    Ctxt.Valuation (Ctxt.ofList [(scev_nuw_exitvalue_correct_ity w), (scev_nuw_exitvalue_correct_ity w)]) :=
  Ctxt.Valuation.ofHVector (j1 ::ₕ j2 ::ₕ HVector.nil)

private theorem scev_nuw_exitvalue_correct_src_loop_dispatch (w : Nat)
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation (scev_nuw_exitvalue_correct_ctx w)) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a1 a2 : Γcur.Var (scev_nuw_exitvalue_correct_ity w)) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (scev_nuw_exitvalue_correct_srcBlocks w) V W
            ({ name := "loop", argTys := [(scev_nuw_exitvalue_correct_ity w), (scev_nuw_exitvalue_correct_ity w)], args := a1 ::ₕ a2 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (scev_nuw_exitvalue_correct_srcBlocks w) V
            ((scev_nuw_exitvalue_correct_srcLoopVal w) (W a1) (W a2)) (scev_nuw_exitvalue_correct_srcLoopTarget w))
          ∅)
        s := by
  cases fuel <;>
    simp [scev_nuw_exitvalue_correct_src, scev_nuw_exitvalue_correct_srcBlocks, scev_nuw_exitvalue_correct_srcLoopTarget, scev_nuw_exitvalue_correct_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

private def scev_nuw_exitvalue_correct_tgtResult (w : Nat) (V : Ctxt.Valuation (scev_nuw_exitvalue_correct_ctx w)) : TyDenote.toType (scev_nuw_exitvalue_correct_ity w) :=
  (pure (LLVM.const? w 0))

private def scev_nuw_exitvalue_correct_inv (w : Nat) (j1 j2 : TyDenote.toType (scev_nuw_exitvalue_correct_ity w))
    (V : Ctxt.Valuation (scev_nuw_exitvalue_correct_ctx w)) : Prop :=
  True

private theorem scev_nuw_exitvalue_correct_step (w : Nat) (V : Ctxt.Valuation (scev_nuw_exitvalue_correct_ctx w)) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (scev_nuw_exitvalue_correct_ity w)),
      (scev_nuw_exitvalue_correct_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (scev_nuw_exitvalue_correct_srcBlocks w) V
              ((scev_nuw_exitvalue_correct_srcLoopVal w) j1 j2) (scev_nuw_exitvalue_correct_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((scev_nuw_exitvalue_correct_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(scev_nuw_exitvalue_correct_ity w)] × LLVMMemory.State))) :
    ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (scev_nuw_exitvalue_correct_ity w)),
      (scev_nuw_exitvalue_correct_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) (scev_nuw_exitvalue_correct_srcBlocks w) V
              ((scev_nuw_exitvalue_correct_srcLoopVal w) j1 j2) (scev_nuw_exitvalue_correct_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((scev_nuw_exitvalue_correct_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(scev_nuw_exitvalue_correct_ity w)] × LLVMMemory.State)) :=
  by
    intro s j1 j2 _hinv
    cases j1 with
    | none =>
        simp [-Ctxt.Var.zero_eq_last, scev_nuw_exitvalue_correct_src, scev_nuw_exitvalue_correct_srcBlocks, scev_nuw_exitvalue_correct_srcLoopTarget,
          scev_nuw_exitvalue_correct_srcLoopVal, scev_nuw_exitvalue_correct_tgtResult,
          LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
          LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
          DialectDenote.denote, LLVMMemory.Op.denoteVec, InstCombine.Op.denote,
          LLVMMemory.throwUB,
          ImmediateUBOr.immediateUB]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    | some j1v =>
        cases j1v with
        | poison =>
            simp [-Ctxt.Var.zero_eq_last, scev_nuw_exitvalue_correct_src, scev_nuw_exitvalue_correct_srcBlocks, scev_nuw_exitvalue_correct_srcLoopTarget,
              scev_nuw_exitvalue_correct_srcLoopVal, scev_nuw_exitvalue_correct_tgtResult,
              LLVMMemory.CFGTarget.denoteWithMemoryFuel,
              LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
              LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
              DialectDenote.denote, LLVMMemory.Op.denoteVec, InstCombine.Op.denote,
              LLVM.const?, LLVM.add, LLVM.add?,
              LLVM.icmp, LLVM.icmp?, LLVMMemory.throwUB, ImmediateUBOr.immediateUB]
            exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        | value x =>
            by_cases hcmp :
                BitVec.ofBool (LLVM.icmp' LLVM.IntPred.eq (x + 4#w) 12#w) = 1#1
            · simp [-Ctxt.Var.zero_eq_last, scev_nuw_exitvalue_correct_src, scev_nuw_exitvalue_correct_srcBlocks, scev_nuw_exitvalue_correct_srcLoopTarget,
                scev_nuw_exitvalue_correct_srcLoopVal, scev_nuw_exitvalue_correct_tgtResult, hcmp,
                LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                LLVMMemory.CFGBlocks.findMemoryBlock?,
                LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
                DialectDenote.denote, LLVMMemory.Op.denoteVec, InstCombine.Op.denote,
                LLVM.const?, LLVM.add,
                LLVM.add?, LLVM.icmp, LLVM.icmp?]
              cases fuel with
              | zero =>
                  simp [LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.throwUB,
                    ImmediateUBOr.immediateUB]
                  exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
              | succ fuel =>
                  simp [LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                    LLVMMemory.CFGBlocks.findMemoryBlock?,
                    LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                    LLVMMemory.CFGTerm.denoteWithMemoryFuelCore]
                  exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    constructor
                    · constructor
                      · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                          simp [LLVM.IntW.instRefinement])
                      · trivial
                    · rfl)
            · simp [-Ctxt.Var.zero_eq_last, scev_nuw_exitvalue_correct_src, scev_nuw_exitvalue_correct_srcBlocks, scev_nuw_exitvalue_correct_srcLoopTarget,
                scev_nuw_exitvalue_correct_srcLoopVal, scev_nuw_exitvalue_correct_tgtResult, hcmp,
                LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                LLVMMemory.CFGBlocks.findMemoryBlock?,
                LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
                DialectDenote.denote, LLVMMemory.Op.denoteVec, InstCombine.Op.denote,
                LLVM.const?, LLVM.add,
                LLVM.add?, LLVM.icmp, LLVM.icmp?]
              change
                StateT.run
                    (ReaderT.run
                      (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (scev_nuw_exitvalue_correct_srcBlocks w) V
                        _
                        ({ name := "loop", argTys := [(scev_nuw_exitvalue_correct_ity w), (scev_nuw_exitvalue_correct_ity w)],
                           args := _ ::ₕ _ ::ₕ HVector.nil } : CFGTarget LLVM _))
                      ∅)
                    s
                  ⊑
                  (some ((scev_nuw_exitvalue_correct_tgtResult w) V ::ₕ HVector.nil, s) :
                    ImmediateUBOr (HVector TyDenote.toType [(scev_nuw_exitvalue_correct_ity w)] × LLVMMemory.State))
              rw [scev_nuw_exitvalue_correct_src_loop_dispatch w]
              exact ih _ _ _ trivial

private theorem scev_nuw_exitvalue_correct_loop_refine (w : Nat) (V : Ctxt.Valuation (scev_nuw_exitvalue_correct_ctx w)) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (scev_nuw_exitvalue_correct_ity w)),
      (scev_nuw_exitvalue_correct_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (scev_nuw_exitvalue_correct_srcBlocks w) V
              ((scev_nuw_exitvalue_correct_srcLoopVal w) j1 j2) (scev_nuw_exitvalue_correct_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((scev_nuw_exitvalue_correct_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(scev_nuw_exitvalue_correct_ity w)] × LLVMMemory.State)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s j1 j2 _hinv
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact (scev_nuw_exitvalue_correct_step w) V fuel ih

theorem scev_nuw_exitvalue_correct_correct (w : Nat) :
    IsRefinedByOnIntWInputsWithMemory (scev_nuw_exitvalue_correct_src w) ((scev_nuw_exitvalue_correct_tgt w).castPureToEff .impure) := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>

      simp [scev_nuw_exitvalue_correct_src, scev_nuw_exitvalue_correct_tgt,
        LLVMMemory.Com.denoteWithMemoryFuel, LLVMMemory.Com.denoteWithMemoryFuelIn,
        LLVMMemory.Com.denoteWithMemoryCore,
        LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
        LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
        DialectDenote.denote, LLVMMemory.Op.denoteVec, InstCombine.Op.denote, LLVM.const?,
        LLVM.add, LLVM.add?, LLVM.icmp, LLVM.icmp?]
      change
        StateT.run
            (ReaderT.run
              (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (scev_nuw_exitvalue_correct_srcBlocks w)
                (InputValuation.lift V)
                _
                ({ name := "loop", argTys := [(scev_nuw_exitvalue_correct_ity w), (scev_nuw_exitvalue_correct_ity w)],
                   args := _ ::ₕ _ ::ₕ HVector.nil } : CFGTarget LLVM _))
              ∅)
            s
          ⊑
          (some ((scev_nuw_exitvalue_correct_tgtResult w) (InputValuation.lift V) ::ₕ HVector.nil, s) :
            ImmediateUBOr (HVector TyDenote.toType [(scev_nuw_exitvalue_correct_ity w)] × LLVMMemory.State))
      rw [scev_nuw_exitvalue_correct_src_loop_dispatch w]
      exact scev_nuw_exitvalue_correct_loop_refine w (InputValuation.lift V) fuel s _ _ trivial

end TestLoop
end InstCombine
