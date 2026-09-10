import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace InstCombine
namespace TestLoop

def scev_samesign_exitvalue_correct_src :=
  [llvm()| {
  llvm.func @scev_samesign_exitvalue_correct_src(%unused : i8) -> i8 {
  ^entry(%unused : i8):
    %e_a = llvm.mlir.constant 1 : i8
    %e_b = llvm.mlir.constant 0 : i8
    %e_xor = llvm.xor %e_a, %e_b : i8
    %e_lim = llvm.mlir.constant 100 : i8
    %e_guard = llvm.icmp "ult" %e_xor, %e_lim : i8
    %e_zero = llvm.mlir.constant 0 : i8
    llvm.cond_br %e_guard : i1, ^loop(%e_zero : i8), ^out(%e_zero : i8)
  ^loop(%f : i8):
    %l_one = llvm.mlir.constant 1 : i8
    %cmp = llvm.icmp "slt" %f, %l_one : i8
    %l_zero = llvm.mlir.constant 0 : i8
    llvm.cond_br %cmp : i1, ^loop(%l_one : i8), ^out(%l_zero : i8)
  ^out(%res : i8):
    llvm.return %res : i8
  }
  }]

def scev_samesign_exitvalue_correct_tgt :=
  [llvm()| {
  llvm.func @scev_samesign_exitvalue_correct_tgt(%unused : i8) -> i8 {
  ^entry(%unused : i8):
    %r = llvm.mlir.constant 0 : i8
    llvm.return %r : i8
  }
  }]

private abbrev scev_samesign_exitvalue_correct_ity : LLVM.Ty := LLVM.Ty.bitvec 8

private abbrev scev_samesign_exitvalue_correct_ctx : Ctxt LLVM.Ty := Ctxt.ofList [scev_samesign_exitvalue_correct_ity]

private def scev_samesign_exitvalue_correct_srcBlocks : CFGBlocks LLVM scev_samesign_exitvalue_correct_ctx .impure [scev_samesign_exitvalue_correct_ity] :=
  match scev_samesign_exitvalue_correct_src with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private theorem scev_samesign_exitvalue_correct_entry_ne_loop : ¬ ("entry" = "loop") := by
  decide

private theorem scev_samesign_exitvalue_correct_out_ne_loop : ¬ ("out" = "loop") := by
  decide

private def scev_samesign_exitvalue_correct_srcLoopTarget : CFGTarget LLVM (Ctxt.ofList [scev_samesign_exitvalue_correct_ity]) where
  name := "loop"
  argTys := [scev_samesign_exitvalue_correct_ity]
  args := (⟨0, by decide⟩ : (Ctxt.ofList [scev_samesign_exitvalue_correct_ity]).Var scev_samesign_exitvalue_correct_ity) ::ₕ HVector.nil

private def scev_samesign_exitvalue_correct_srcLoopVal (j1 : TyDenote.toType scev_samesign_exitvalue_correct_ity) :
    Ctxt.Valuation (Ctxt.ofList [scev_samesign_exitvalue_correct_ity]) :=
  Ctxt.Valuation.ofHVector (j1 ::ₕ HVector.nil)

private theorem scev_samesign_exitvalue_correct_src_loop_dispatch
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation scev_samesign_exitvalue_correct_ctx) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a1 : Γcur.Var scev_samesign_exitvalue_correct_ity) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel scev_samesign_exitvalue_correct_srcBlocks V W
            ({ name := "loop", argTys := [scev_samesign_exitvalue_correct_ity], args := a1 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel scev_samesign_exitvalue_correct_srcBlocks V
            (scev_samesign_exitvalue_correct_srcLoopVal (W a1)) scev_samesign_exitvalue_correct_srcLoopTarget)
          ∅)
        s := by
  cases fuel <;>
    simp [scev_samesign_exitvalue_correct_src, scev_samesign_exitvalue_correct_srcBlocks, scev_samesign_exitvalue_correct_srcLoopTarget, scev_samesign_exitvalue_correct_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

private def scev_samesign_exitvalue_correct_tgtResult (V : Ctxt.Valuation scev_samesign_exitvalue_correct_ctx) : TyDenote.toType scev_samesign_exitvalue_correct_ity :=
  (pure (LLVM.const? 8 0))

private def scev_samesign_exitvalue_correct_inv (j1 : TyDenote.toType scev_samesign_exitvalue_correct_ity)
    (V : Ctxt.Valuation scev_samesign_exitvalue_correct_ctx) : Prop :=
  j1 = LLVM.IntWUB.value (0#8) ∨ j1 = LLVM.IntWUB.value (1#8)

private theorem scev_samesign_exitvalue_correct_step (V : Ctxt.Valuation scev_samesign_exitvalue_correct_ctx) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) (j1 : TyDenote.toType scev_samesign_exitvalue_correct_ity),
      scev_samesign_exitvalue_correct_inv j1 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel scev_samesign_exitvalue_correct_srcBlocks V
              (scev_samesign_exitvalue_correct_srcLoopVal j1) scev_samesign_exitvalue_correct_srcLoopTarget)
            ∅)
          s
        ⊑
        (some (scev_samesign_exitvalue_correct_tgtResult V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [scev_samesign_exitvalue_correct_ity] × LLVMMemory.State))) :
    ∀ (s : LLVMMemory.State) (j1 : TyDenote.toType scev_samesign_exitvalue_correct_ity),
      scev_samesign_exitvalue_correct_inv j1 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) scev_samesign_exitvalue_correct_srcBlocks V
              (scev_samesign_exitvalue_correct_srcLoopVal j1) scev_samesign_exitvalue_correct_srcLoopTarget)
            ∅)
          s
        ⊑
        (some (scev_samesign_exitvalue_correct_tgtResult V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [scev_samesign_exitvalue_correct_ity] × LLVMMemory.State)) :=
  by
    intro s j1 hinv
    rcases hinv with rfl | rfl
    · simp (config := { failIfUnchanged := false })
        [scev_samesign_exitvalue_correct_src, scev_samesign_exitvalue_correct_srcBlocks, scev_samesign_exitvalue_correct_srcLoopTarget, scev_samesign_exitvalue_correct_srcLoopVal,
          scev_samesign_exitvalue_correct_tgtResult, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
          LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.CFGBlocks.findMemoryBlock?,
          LLVMMemory.Expr.denoteWithMemory, LLVMMemory.Op.denoteVec, DialectDenote.denote,
          InstCombine.Op.denote, simp_denote, simp_llvm, simp_llvm_option,
          LLVMMemory.throwUB, ImmediateUBOr.immediateUB, Ctxt.Valuation.cons,
          Ctxt.Var.zero_eq_last, Ctxt.Var.casesOn]
      exact
        show
          StateT.run
            (ReaderT.run
              (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel scev_samesign_exitvalue_correct_srcBlocks V
                ((LLVM.IntWUB.value (0#8) ::ᵥ LLVM.IntWUB.value (1#1) ::ᵥ
                  LLVM.IntWUB.value (1#8) ::ᵥ LLVM.IntWUB.value (0#8) ::ᵥ V) :
                  Ctxt.Valuation (Ctxt.ofList [LLVM.Ty.bitvec 8, LLVM.Ty.bitvec 1,
                    LLVM.Ty.bitvec 8, LLVM.Ty.bitvec 8, scev_samesign_exitvalue_correct_ity]))
                { name := "loop"
                  argTys := [LLVM.Ty.bitvec 8]
                  args := (⟨2, scev_samesign_exitvalue_correct_src._proof_2⟩ : _) ::ₕ HVector.nil })
              ∅)
            s ⊑
            (some (scev_samesign_exitvalue_correct_tgtResult V ::ₕ HVector.nil, s) :
              ImmediateUBOr (HVector TyDenote.toType [scev_samesign_exitvalue_correct_ity] × LLVMMemory.State))
        from by
          rw [scev_samesign_exitvalue_correct_src_loop_dispatch]
          simpa (config := { failIfUnchanged := false })
            [scev_samesign_exitvalue_correct_srcLoopVal, scev_samesign_exitvalue_correct_tgtResult, Ctxt.Valuation.cons, Ctxt.Var.casesOn]
            using ih s (LLVM.IntWUB.value (1#8)) (Or.inr rfl)
    · simp (config := { failIfUnchanged := false })
        [scev_samesign_exitvalue_correct_src, scev_samesign_exitvalue_correct_srcBlocks, scev_samesign_exitvalue_correct_srcLoopTarget, scev_samesign_exitvalue_correct_srcLoopVal,
          scev_samesign_exitvalue_correct_tgtResult, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
          LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.CFGBlocks.findMemoryBlock?,
          LLVMMemory.Expr.denoteWithMemory, LLVMMemory.Op.denoteVec, DialectDenote.denote,
          InstCombine.Op.denote, simp_denote, simp_llvm, simp_llvm_option,
          LLVMMemory.throwUB, ImmediateUBOr.immediateUB, Ctxt.Valuation.cons,
          Ctxt.Var.zero_eq_last, Ctxt.Var.casesOn]
      cases fuel with
      | zero =>
          simpa [LLVMMemory.lift_apply, ImmediateUBOr.immediateUB]
            using (ImmediateUBOr.IsRefinedBy.immediateUBLeft :
              (ImmediateUBOr.immediateUB :
                ImmediateUBOr (HVector TyDenote.toType [scev_samesign_exitvalue_correct_ity] × LLVMMemory.State)) ⊑
              (some (scev_samesign_exitvalue_correct_tgtResult V ::ₕ HVector.nil, s) :
                ImmediateUBOr (HVector TyDenote.toType [scev_samesign_exitvalue_correct_ity] × LLVMMemory.State)))
      | succ fuel =>
          simpa [scev_samesign_exitvalue_correct_tgtResult]
            using (mem_result_le_self
              (some (scev_samesign_exitvalue_correct_tgtResult V ::ₕ HVector.nil, s) :
                ImmediateUBOr (HVector TyDenote.toType [scev_samesign_exitvalue_correct_ity] × LLVMMemory.State)))

private theorem scev_samesign_exitvalue_correct_loop_refine (V : Ctxt.Valuation scev_samesign_exitvalue_correct_ctx) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) (j1 : TyDenote.toType scev_samesign_exitvalue_correct_ity),
      scev_samesign_exitvalue_correct_inv j1 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel scev_samesign_exitvalue_correct_srcBlocks V
              (scev_samesign_exitvalue_correct_srcLoopVal j1) scev_samesign_exitvalue_correct_srcLoopTarget)
            ∅)
          s
        ⊑
        (some (scev_samesign_exitvalue_correct_tgtResult V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [scev_samesign_exitvalue_correct_ity] × LLVMMemory.State)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s j1 _hinv
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact scev_samesign_exitvalue_correct_step V fuel ih

theorem scev_samesign_exitvalue_correct_correct :
    IsRefinedByOnIntWInputsWithMemory scev_samesign_exitvalue_correct_src (scev_samesign_exitvalue_correct_tgt.castPureToEff .impure) := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>

      simp (config := { failIfUnchanged := false }) only [simp_denote, simp_memory]
      simp (config := { failIfUnchanged := false })
        [scev_samesign_exitvalue_correct_src, scev_samesign_exitvalue_correct_tgt, LLVMMemory.Com.denoteWithMemoryCore,
          LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.CFGBlocks.findMemoryBlock?,
          LLVMMemory.Expr.denoteWithMemory, LLVMMemory.Op.denoteVec, DialectDenote.denote,
          InstCombine.Op.denote, simp_llvm, simp_llvm_option, LLVM.const?, Ctxt.Valuation.cons,
          Ctxt.Var.zero_eq_last, Ctxt.Var.casesOn]
      exact
        show
          StateT.run
            (ReaderT.run
              (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel scev_samesign_exitvalue_correct_srcBlocks V.lift
                ((LLVM.IntWUB.value (0#8) ::ᵥ LLVM.IntWUB.value (1#1) ::ᵥ
                  LLVM.IntWUB.value (100#8) ::ᵥ LLVM.IntWUB.value (1#8) ::ᵥ
                  LLVM.IntWUB.value (0#8) ::ᵥ LLVM.IntWUB.value (1#8) ::ᵥ V.lift) :
                  Ctxt.Valuation (Ctxt.ofList [LLVM.Ty.bitvec 8, LLVM.Ty.bitvec 1,
                    LLVM.Ty.bitvec 8, LLVM.Ty.bitvec 8, LLVM.Ty.bitvec 8,
                    LLVM.Ty.bitvec 8, scev_samesign_exitvalue_correct_ity]))
                { name := "loop"
                  argTys := [LLVM.Ty.bitvec 8]
                  args := (Ctxt.Var.last
                    (Ctxt.ofList [LLVM.Ty.bitvec 1, LLVM.Ty.bitvec 8,
                      LLVM.Ty.bitvec 8, LLVM.Ty.bitvec 8, LLVM.Ty.bitvec 8,
                      scev_samesign_exitvalue_correct_ity])
                    (LLVM.Ty.bitvec 8)) ::ₕ HVector.nil })
              ∅)
            s ⊑
          (some (scev_samesign_exitvalue_correct_tgtResult V.lift ::ₕ HVector.nil, s) :
            ImmediateUBOr (HVector TyDenote.toType [scev_samesign_exitvalue_correct_ity] × LLVMMemory.State))
        from by
          rw [scev_samesign_exitvalue_correct_src_loop_dispatch]
          simpa (config := { failIfUnchanged := false })
            [scev_samesign_exitvalue_correct_srcLoopVal, scev_samesign_exitvalue_correct_tgtResult, Ctxt.Valuation.cons,
              Ctxt.Var.casesOn]
            using scev_samesign_exitvalue_correct_loop_refine V.lift fuel s (LLVM.IntWUB.value (0#8)) (Or.inl rfl)

end TestLoop
end InstCombine
