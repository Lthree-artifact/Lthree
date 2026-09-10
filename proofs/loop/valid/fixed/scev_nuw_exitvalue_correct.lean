import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace InstCombine
namespace TestLoop

def scev_nuw_exitvalue_correct_src :=
  [llvm()| {
  llvm.func @scev_nuw_exitvalue_correct_src(%unused : i32) -> i32 {
  ^entry(%unused : i32):
    %e_index = llvm.mlir.constant 0 : i32
    %e_vec = llvm.mlir.constant -8 : i32
    llvm.br ^loop(%e_index : i32, %e_vec : i32)
  ^loop(%index : i32, %vec : i32):
    %l_four = llvm.mlir.constant 4 : i32
    %index_next = llvm.add %index, %l_four : i32
    %vec_next = llvm.add %vec, %l_four overflow<nuw> : i32
    %l_twelve = llvm.mlir.constant 12 : i32
    %cmp = llvm.icmp "eq" %index_next, %l_twelve : i32
    %l_zero = llvm.mlir.constant 0 : i32
    llvm.cond_br %cmp : i1, ^out(%l_zero : i32), ^loop(%index_next : i32, %vec_next : i32)
  ^out(%res : i32):
    llvm.return %res : i32
  }
  }]

def scev_nuw_exitvalue_correct_tgt :=
  [llvm()| {
  llvm.func @scev_nuw_exitvalue_correct_tgt(%unused : i32) -> i32 {
  ^entry(%unused : i32):
    %r = llvm.mlir.constant 0 : i32
    llvm.return %r : i32
  }
  }]

private abbrev scev_nuw_exitvalue_correct_ity : LLVM.Ty := LLVM.Ty.bitvec 32

private abbrev scev_nuw_exitvalue_correct_ctx : Ctxt LLVM.Ty := Ctxt.ofList [scev_nuw_exitvalue_correct_ity]

private def scev_nuw_exitvalue_correct_srcBlocks : CFGBlocks LLVM scev_nuw_exitvalue_correct_ctx .impure [scev_nuw_exitvalue_correct_ity] :=
  match scev_nuw_exitvalue_correct_src with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private theorem scev_nuw_exitvalue_correct_entry_ne_loop : ¬ ("entry" = "loop") := by
  decide

private theorem scev_nuw_exitvalue_correct_out_ne_loop : ¬ ("out" = "loop") := by
  decide

private def scev_nuw_exitvalue_correct_srcLoopTarget : CFGTarget LLVM (Ctxt.ofList [scev_nuw_exitvalue_correct_ity, scev_nuw_exitvalue_correct_ity]) where
  name := "loop"
  argTys := [scev_nuw_exitvalue_correct_ity, scev_nuw_exitvalue_correct_ity]
  args := (⟨0, by decide⟩ : (Ctxt.ofList [scev_nuw_exitvalue_correct_ity, scev_nuw_exitvalue_correct_ity]).Var scev_nuw_exitvalue_correct_ity) ::ₕ (⟨1, by decide⟩ : (Ctxt.ofList [scev_nuw_exitvalue_correct_ity, scev_nuw_exitvalue_correct_ity]).Var scev_nuw_exitvalue_correct_ity) ::ₕ HVector.nil

private def scev_nuw_exitvalue_correct_srcLoopVal (j1 j2 : TyDenote.toType scev_nuw_exitvalue_correct_ity) :
    Ctxt.Valuation (Ctxt.ofList [scev_nuw_exitvalue_correct_ity, scev_nuw_exitvalue_correct_ity]) :=
  Ctxt.Valuation.ofHVector (j1 ::ₕ j2 ::ₕ HVector.nil)

private theorem scev_nuw_exitvalue_correct_src_loop_dispatch
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation scev_nuw_exitvalue_correct_ctx) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a1 a2 : Γcur.Var scev_nuw_exitvalue_correct_ity) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel scev_nuw_exitvalue_correct_srcBlocks V W
            ({ name := "loop", argTys := [scev_nuw_exitvalue_correct_ity, scev_nuw_exitvalue_correct_ity], args := a1 ::ₕ a2 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel scev_nuw_exitvalue_correct_srcBlocks V
            (scev_nuw_exitvalue_correct_srcLoopVal (W a1) (W a2)) scev_nuw_exitvalue_correct_srcLoopTarget)
          ∅)
        s := by
  cases fuel <;>
    simp [scev_nuw_exitvalue_correct_src, scev_nuw_exitvalue_correct_srcBlocks, scev_nuw_exitvalue_correct_srcLoopTarget, scev_nuw_exitvalue_correct_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

private def scev_nuw_exitvalue_correct_tgtResult (V : Ctxt.Valuation scev_nuw_exitvalue_correct_ctx) : TyDenote.toType scev_nuw_exitvalue_correct_ity :=
  (pure (LLVM.const? 32 0))

private def scev_nuw_exitvalue_correct_inv (j1 j2 : TyDenote.toType scev_nuw_exitvalue_correct_ity)
    (V : Ctxt.Valuation scev_nuw_exitvalue_correct_ctx) : Prop :=
  (j1 = some (LLVM.const? 32 0) ∧ j2 = some (LLVM.const? 32 (-8))) ∨
  (j1 = some (LLVM.const? 32 4) ∧ j2 = some (LLVM.const? 32 (-4))) ∨
  (j1 = some (LLVM.const? 32 8) ∧ j2 = some LLVM.SemVal.poison)

private theorem scev_nuw_exitvalue_correct_step (V : Ctxt.Valuation scev_nuw_exitvalue_correct_ctx) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType scev_nuw_exitvalue_correct_ity),
      scev_nuw_exitvalue_correct_inv j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel scev_nuw_exitvalue_correct_srcBlocks V
              (scev_nuw_exitvalue_correct_srcLoopVal j1 j2) scev_nuw_exitvalue_correct_srcLoopTarget)
            ∅)
          s
        ⊑
        (some (scev_nuw_exitvalue_correct_tgtResult V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [scev_nuw_exitvalue_correct_ity] × LLVMMemory.State))) :
    ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType scev_nuw_exitvalue_correct_ity),
      scev_nuw_exitvalue_correct_inv j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) scev_nuw_exitvalue_correct_srcBlocks V
              (scev_nuw_exitvalue_correct_srcLoopVal j1 j2) scev_nuw_exitvalue_correct_srcLoopTarget)
            ∅)
          s
        ⊑
        (some (scev_nuw_exitvalue_correct_tgtResult V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [scev_nuw_exitvalue_correct_ity] × LLVMMemory.State)) :=
  by
    intro s j1 j2 hinv
    rcases hinv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hfour :
        ((some (LLVM.SemVal.value 4#32) ::ᵥ some (LLVM.SemVal.value 0#32) ::ᵥ
              some (LLVM.SemVal.value 4294967288#32) ::ᵥ V)
            (Ctxt.Var.last
              (Ctxt.ofList [LLVM.Ty.bitvec 32, LLVM.Ty.bitvec 32, LLVM.Ty.bitvec 32])
              (LLVM.Ty.bitvec 32))) =
          some (LLVM.SemVal.value 4#32) := rfl
      simp [scev_nuw_exitvalue_correct_ity, scev_nuw_exitvalue_correct_tgtResult, scev_nuw_exitvalue_correct_src, scev_nuw_exitvalue_correct_srcBlocks,
        scev_nuw_exitvalue_correct_srcLoopTarget, scev_nuw_exitvalue_correct_srcLoopVal, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
        LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
        DialectDenote.denote, LLVMMemory.Op.denoteVec,
        Op.denote, lift2, LLVM.add, LLVM.add?, LLVM.icmp, LLVM.icmp?,
        LLVM.icmp', LLVM.const?, LLVMMemory.throwUB, ImmediateUBOr.immediateUB,
        hfour]
      change
        (StateT.run
            (ReaderT.run
              (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel scev_nuw_exitvalue_correct_srcBlocks V _ _)
              ∅)
            s)
          ⊑ _
      rw [scev_nuw_exitvalue_correct_src_loop_dispatch]
      exact ih s (some (LLVM.const? 32 4)) (some (LLVM.const? 32 (-4))) (by
        simp [scev_nuw_exitvalue_correct_inv])
    · have hfour :
        ((some (LLVM.SemVal.value 4#32) ::ᵥ some (LLVM.SemVal.value 4#32) ::ᵥ
              some (LLVM.SemVal.value 4294967292#32) ::ᵥ V)
            (Ctxt.Var.last
              (Ctxt.ofList [LLVM.Ty.bitvec 32, LLVM.Ty.bitvec 32, LLVM.Ty.bitvec 32])
              (LLVM.Ty.bitvec 32))) =
          some (LLVM.SemVal.value 4#32) := rfl
      simp [scev_nuw_exitvalue_correct_ity, scev_nuw_exitvalue_correct_tgtResult, scev_nuw_exitvalue_correct_src, scev_nuw_exitvalue_correct_srcBlocks,
        scev_nuw_exitvalue_correct_srcLoopTarget, scev_nuw_exitvalue_correct_srcLoopVal, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
        LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
        DialectDenote.denote, LLVMMemory.Op.denoteVec,
        Op.denote, lift2, LLVM.add, LLVM.add?, LLVM.icmp, LLVM.icmp?,
        LLVM.icmp', LLVM.const?, LLVMMemory.throwUB, ImmediateUBOr.immediateUB,
        hfour]
      change
        (StateT.run
            (ReaderT.run
              (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel scev_nuw_exitvalue_correct_srcBlocks V _ _)
              ∅)
            s)
          ⊑ _
      rw [scev_nuw_exitvalue_correct_src_loop_dispatch]
      exact ih s (some (LLVM.const? 32 8)) (some LLVM.SemVal.poison) (by
        simp [scev_nuw_exitvalue_correct_inv])
    · have hfour :
        ((some (LLVM.SemVal.value 4#32) ::ᵥ some (LLVM.SemVal.value 8#32) ::ᵥ
              some LLVM.SemVal.poison ::ᵥ V)
            (Ctxt.Var.last
              (Ctxt.ofList [LLVM.Ty.bitvec 32, LLVM.Ty.bitvec 32, LLVM.Ty.bitvec 32])
              (LLVM.Ty.bitvec 32))) =
          some (LLVM.SemVal.value 4#32) := rfl
      simp [scev_nuw_exitvalue_correct_ity, scev_nuw_exitvalue_correct_tgtResult, scev_nuw_exitvalue_correct_src, scev_nuw_exitvalue_correct_srcBlocks,
        scev_nuw_exitvalue_correct_srcLoopTarget, scev_nuw_exitvalue_correct_srcLoopVal, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
        LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
        DialectDenote.denote, LLVMMemory.Op.denoteVec,
        Op.denote, lift2, LLVM.add, LLVM.add?, LLVM.icmp, LLVM.icmp?,
        LLVM.icmp', LLVM.const?,
        LLVMMemory.throwUB, ImmediateUBOr.immediateUB, hfour]
      cases fuel <;>
        simp [scev_nuw_exitvalue_correct_ity,
          LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
          LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.throwUB,
          ImmediateUBOr.immediateUB]
      · exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      · exact mem_result_le_self _

private theorem scev_nuw_exitvalue_correct_loop_refine (V : Ctxt.Valuation scev_nuw_exitvalue_correct_ctx) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) (j1 j2 : TyDenote.toType scev_nuw_exitvalue_correct_ity),
      scev_nuw_exitvalue_correct_inv j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel scev_nuw_exitvalue_correct_srcBlocks V
              (scev_nuw_exitvalue_correct_srcLoopVal j1 j2) scev_nuw_exitvalue_correct_srcLoopTarget)
            ∅)
          s
        ⊑
        (some (scev_nuw_exitvalue_correct_tgtResult V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [scev_nuw_exitvalue_correct_ity] × LLVMMemory.State)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s j1 j2 _hinv
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact scev_nuw_exitvalue_correct_step V fuel ih

theorem scev_nuw_exitvalue_correct_correct :
    IsRefinedByOnIntWInputsWithMemory scev_nuw_exitvalue_correct_src (scev_nuw_exitvalue_correct_tgt.castPureToEff .impure) := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>

      simp [scev_nuw_exitvalue_correct_src, scev_nuw_exitvalue_correct_tgt,
        LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
        LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
        DialectDenote.denote, LLVMMemory.Op.denoteVec, Op.denote, LLVM.const?]
      change
        (StateT.run
            (ReaderT.run
              (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel scev_nuw_exitvalue_correct_srcBlocks V.lift _ _)
              ∅)
            s)
          ⊑ _
      rw [scev_nuw_exitvalue_correct_src_loop_dispatch]
      simpa [scev_nuw_exitvalue_correct_inv, scev_nuw_exitvalue_correct_srcLoopVal, scev_nuw_exitvalue_correct_tgtResult, scev_nuw_exitvalue_correct_tgt,
        LLVMMemory.Com.denoteWithMemoryCore, LLVMMemory.Expr.denoteWithMemory,
        DialectDenote.denote, LLVMMemory.Op.denoteVec, Op.denote, LLVM.const?]
        using scev_nuw_exitvalue_correct_loop_refine V.lift fuel s (some (LLVM.const? 32 0))
          (some (LLVM.const? 32 (-8))) (by simp [scev_nuw_exitvalue_correct_inv])

end TestLoop
end InstCombine
