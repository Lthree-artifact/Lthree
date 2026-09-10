import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace InstCombine
namespace TestLoop

def loopunroll_full_xor_cancel_src :=
  [llvm()| {
  llvm.func @loopunroll_full_xor_cancel_src(%m : i32, %x : i32) -> i32 {
  ^entry(%m : i32, %x : i32):
    %e_zero = llvm.mlir.constant 0 : i32
    llvm.br ^loop(%e_zero : i32, %x : i32)
  ^loop(%i : i32, %v : i32):
    %v1 = llvm.xor %v, %m : i32
    %l_one = llvm.mlir.constant 1 : i32
    %i1 = llvm.add %i, %l_one : i32
    %l_two = llvm.mlir.constant 2 : i32
    %cond = llvm.icmp "eq" %i1, %l_two : i32
    llvm.cond_br %cond : i1, ^out(%v1 : i32), ^loop(%i1 : i32, %v1 : i32)
  ^out(%res : i32):
    llvm.return %res : i32
  }
  }]

def loopunroll_full_xor_cancel_tgt :=
  [llvm()| {
  llvm.func @loopunroll_full_xor_cancel_tgt(%m : i32, %x : i32) -> i32 {
  ^entry(%m : i32, %x : i32):
    llvm.return %x : i32
  }
  }]

private abbrev loopunroll_full_xor_cancel_ity : LLVM.Ty := LLVM.Ty.bitvec 32

private abbrev loopunroll_full_xor_cancel_ctx : Ctxt LLVM.Ty := Ctxt.ofList [loopunroll_full_xor_cancel_ity, loopunroll_full_xor_cancel_ity]

private def loopunroll_full_xor_cancel_srcBlocks : CFGBlocks LLVM loopunroll_full_xor_cancel_ctx .impure [loopunroll_full_xor_cancel_ity] :=
  match loopunroll_full_xor_cancel_src with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private theorem loopunroll_full_xor_cancel_entry_ne_loop : ¬ ("entry" = "loop") := by
  decide

private theorem loopunroll_full_xor_cancel_out_ne_loop : ¬ ("out" = "loop") := by
  decide

private def loopunroll_full_xor_cancel_srcLoopTarget : CFGTarget LLVM (Ctxt.ofList [loopunroll_full_xor_cancel_ity, loopunroll_full_xor_cancel_ity]) where
  name := "loop"
  argTys := [loopunroll_full_xor_cancel_ity, loopunroll_full_xor_cancel_ity]
  args := (⟨0, by decide⟩ : (Ctxt.ofList [loopunroll_full_xor_cancel_ity, loopunroll_full_xor_cancel_ity]).Var loopunroll_full_xor_cancel_ity) ::ₕ (⟨1, by decide⟩ : (Ctxt.ofList [loopunroll_full_xor_cancel_ity, loopunroll_full_xor_cancel_ity]).Var loopunroll_full_xor_cancel_ity) ::ₕ HVector.nil

private def loopunroll_full_xor_cancel_srcLoopVal (j1 j2 : TyDenote.toType loopunroll_full_xor_cancel_ity) :
    Ctxt.Valuation (Ctxt.ofList [loopunroll_full_xor_cancel_ity, loopunroll_full_xor_cancel_ity]) :=
  Ctxt.Valuation.ofHVector (j1 ::ₕ j2 ::ₕ HVector.nil)

private theorem loopunroll_full_xor_cancel_src_loop_dispatch
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation loopunroll_full_xor_cancel_ctx) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a1 a2 : Γcur.Var loopunroll_full_xor_cancel_ity) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loopunroll_full_xor_cancel_srcBlocks V W
            ({ name := "loop", argTys := [loopunroll_full_xor_cancel_ity, loopunroll_full_xor_cancel_ity], args := a1 ::ₕ a2 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loopunroll_full_xor_cancel_srcBlocks V
            (loopunroll_full_xor_cancel_srcLoopVal (W a1) (W a2)) loopunroll_full_xor_cancel_srcLoopTarget)
          ∅)
        s := by
  cases fuel <;>
    simp [loopunroll_full_xor_cancel_src, loopunroll_full_xor_cancel_srcBlocks, loopunroll_full_xor_cancel_srcLoopTarget, loopunroll_full_xor_cancel_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

private def loopunroll_full_xor_cancel_tgtResult (V : Ctxt.Valuation loopunroll_full_xor_cancel_ctx) : TyDenote.toType loopunroll_full_xor_cancel_ity :=
  (V (Ctxt.Var.last (Ctxt.ofList [loopunroll_full_xor_cancel_ity]) loopunroll_full_xor_cancel_ity))

private def loopunroll_full_xor_cancel_inv (j1 j2 : TyDenote.toType loopunroll_full_xor_cancel_ity)
    (V : Ctxt.Valuation loopunroll_full_xor_cancel_ctx) : Prop :=
  j1 = some (LLVM.SemVal.value 0#32) ∧
    j2 = V (Ctxt.Var.last (Ctxt.ofList [loopunroll_full_xor_cancel_ity]) loopunroll_full_xor_cancel_ity)

private theorem loopunroll_full_xor_cancel_step (V : Ctxt.Valuation loopunroll_full_xor_cancel_ctx) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType loopunroll_full_xor_cancel_ity),
      loopunroll_full_xor_cancel_inv j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loopunroll_full_xor_cancel_srcBlocks V
              (loopunroll_full_xor_cancel_srcLoopVal j1 j2) loopunroll_full_xor_cancel_srcLoopTarget)
            ∅)
          s
        ⊑
        (some (loopunroll_full_xor_cancel_tgtResult V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [loopunroll_full_xor_cancel_ity] × LLVMMemory.State))) :
    ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType loopunroll_full_xor_cancel_ity),
      loopunroll_full_xor_cancel_inv j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) loopunroll_full_xor_cancel_srcBlocks V
              (loopunroll_full_xor_cancel_srcLoopVal j1 j2) loopunroll_full_xor_cancel_srcLoopTarget)
            ∅)
          s
        ⊑
        (some (loopunroll_full_xor_cancel_tgtResult V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [loopunroll_full_xor_cancel_ity] × LLVMMemory.State)) :=
  by
    intro s j1 j2 hinv
    rcases hinv with ⟨hj1, hj2⟩
    subst hj1
    subst hj2
    cases fuel with
    | zero =>
        simp [loopunroll_full_xor_cancel_src, loopunroll_full_xor_cancel_srcBlocks, loopunroll_full_xor_cancel_srcLoopTarget,
            loopunroll_full_xor_cancel_srcLoopVal, loopunroll_full_xor_cancel_tgtResult, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
            LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
            LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
            LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
            DialectSignature.effectKind, DialectSignature.signature, EffectKind.toMonad,
            EffectKind.liftEffect, LLVMMemory.throwUB, LLVM.xor, LLVM.xor?, LLVM.add, LLVM.add?, LLVM.icmp,
            LLVM.icmp?, LLVM.icmp', LLVM.const?]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    | succ fuel =>
        cases fuel with
        | zero =>
            simp [loopunroll_full_xor_cancel_src, loopunroll_full_xor_cancel_srcBlocks, loopunroll_full_xor_cancel_srcLoopTarget,
            loopunroll_full_xor_cancel_srcLoopVal, loopunroll_full_xor_cancel_tgtResult, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
            LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
            LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
            LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
            DialectSignature.effectKind, DialectSignature.signature, EffectKind.toMonad,
            EffectKind.liftEffect, LLVMMemory.throwUB, LLVM.xor, LLVM.xor?, LLVM.add, LLVM.add?, LLVM.icmp,
            LLVM.icmp?, LLVM.icmp', LLVM.const?]
            exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        | succ fuel =>
            simp [loopunroll_full_xor_cancel_src, loopunroll_full_xor_cancel_srcBlocks, loopunroll_full_xor_cancel_srcLoopTarget,
            loopunroll_full_xor_cancel_srcLoopVal, loopunroll_full_xor_cancel_tgtResult, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
            LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
            LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
            LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
            DialectSignature.effectKind, DialectSignature.signature, EffectKind.toMonad,
            EffectKind.liftEffect, LLVMMemory.throwUB, LLVM.xor, LLVM.xor?, LLVM.add, LLVM.add?, LLVM.icmp,
            LLVM.icmp?, LLVM.icmp', LLVM.const?]
            change (some ((InstCombine.lift2 (fun a b => LLVM.xor a b)
                (InstCombine.lift2 (fun a b => LLVM.xor a b)
                  (V (Ctxt.Var.last (Ctxt.ofList [loopunroll_full_xor_cancel_ity]) loopunroll_full_xor_cancel_ity))
                  (V (((Ctxt.Var.last (Ctxt.ofList []) loopunroll_full_xor_cancel_ity).toCons : loopunroll_full_xor_cancel_ctx.Var loopunroll_full_xor_cancel_ity))))
                (V (((Ctxt.Var.last (Ctxt.ofList []) loopunroll_full_xor_cancel_ity).toCons : loopunroll_full_xor_cancel_ctx.Var loopunroll_full_xor_cancel_ity))))
                ::ₕ HVector.nil, s) :
                ImmediateUBOr (HVector TyDenote.toType [loopunroll_full_xor_cancel_ity] × LLVMMemory.State)) ⊑
              some (V (Ctxt.Var.last (Ctxt.ofList [loopunroll_full_xor_cancel_ity]) loopunroll_full_xor_cancel_ity) ::ₕ HVector.nil, s)
            rcases hx : V (Ctxt.Var.last (Ctxt.ofList [loopunroll_full_xor_cancel_ity]) loopunroll_full_xor_cancel_ity) with _ | (_ | x)
            <;> rcases hm : V (((Ctxt.Var.last (Ctxt.ofList []) loopunroll_full_xor_cancel_ity).toCons :
                  loopunroll_full_xor_cancel_ctx.Var loopunroll_full_xor_cancel_ity)) with _ | (_ | m)
            <;> simp [InstCombine.lift2, LLVM.xor, LLVM.xor?]
            all_goals first
              | exact ImmediateUBOr.IsRefinedBy.bothValues
                  ⟨⟨ImmediateUBOr.IsRefinedBy.immediateUBLeft, trivial⟩, rfl⟩
              | exact ImmediateUBOr.IsRefinedBy.bothValues ⟨⟨IntWUB_le_self _, trivial⟩, rfl⟩
              | exact ImmediateUBOr.IsRefinedBy.bothValues
                  ⟨⟨ImmediateUBOr.IsRefinedBy.bothValues (LLVM.SemVal.poison_isRefinedBy _), trivial⟩, rfl⟩
              | (rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
                 exact ImmediateUBOr.IsRefinedBy.bothValues ⟨⟨IntWUB_le_self _, trivial⟩, rfl⟩)

private theorem loopunroll_full_xor_cancel_loop_refine (V : Ctxt.Valuation loopunroll_full_xor_cancel_ctx) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) (j1 j2 : TyDenote.toType loopunroll_full_xor_cancel_ity),
      loopunroll_full_xor_cancel_inv j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loopunroll_full_xor_cancel_srcBlocks V
              (loopunroll_full_xor_cancel_srcLoopVal j1 j2) loopunroll_full_xor_cancel_srcLoopTarget)
            ∅)
          s
        ⊑
        (some (loopunroll_full_xor_cancel_tgtResult V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [loopunroll_full_xor_cancel_ity] × LLVMMemory.State)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s j1 j2 _hinv
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact loopunroll_full_xor_cancel_step V fuel ih

theorem loopunroll_full_xor_cancel_correct :
    IsRefinedByOnIntWInputsWithMemory loopunroll_full_xor_cancel_src (loopunroll_full_xor_cancel_tgt.castPureToEff .impure) := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>

      simp [loopunroll_full_xor_cancel_src, loopunroll_full_xor_cancel_tgt,
        LLVMMemory.Com.denoteWithMemoryFuel, LLVMMemory.Com.denoteWithMemoryFuelIn,
        LLVMMemory.Com.denoteWithMemoryCore, Com.castPureToEff, Com.changeEffect,
        Expr.changeEffect,
        LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
        LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
        LLVMMemory.Op.denoteVec, DialectDenote.denote, LLVM.const?]
      have h := loopunroll_full_xor_cancel_loop_refine (InputValuation.lift V) fuel s
        (some (LLVM.SemVal.value 0#32))
        ((InputValuation.lift V) (Ctxt.Var.last (Ctxt.ofList [loopunroll_full_xor_cancel_ity]) loopunroll_full_xor_cancel_ity))
        (by simp [loopunroll_full_xor_cancel_inv])
      simp [loopunroll_full_xor_cancel_srcLoopVal, loopunroll_full_xor_cancel_tgtResult, LLVM.const?] at h
      have hdispatch := loopunroll_full_xor_cancel_src_loop_dispatch
        (V := InputValuation.lift V)
        (W := (some (LLVM.SemVal.value 0#32)) ::ᵥ (InputValuation.lift V))
        (fuel := fuel)
        (s := s)
        (a1 := Ctxt.Var.last (Ctxt.ofList [loopunroll_full_xor_cancel_ity, loopunroll_full_xor_cancel_ity]) loopunroll_full_xor_cancel_ity)
        (a2 := (⟨1, by decide⟩ : (Ctxt.ofList [loopunroll_full_xor_cancel_ity, loopunroll_full_xor_cancel_ity, loopunroll_full_xor_cancel_ity]).Var loopunroll_full_xor_cancel_ity))
      simp [loopunroll_full_xor_cancel_srcLoopVal, loopunroll_full_xor_cancel_tgtResult, LLVM.const?] at hdispatch
      rw [← hdispatch] at h
      simpa [loopunroll_full_xor_cancel_src, loopunroll_full_xor_cancel_tgt, loopunroll_full_xor_cancel_srcBlocks, loopunroll_full_xor_cancel_srcLoopTarget,
        loopunroll_full_xor_cancel_srcLoopVal, loopunroll_full_xor_cancel_tgtResult, loopunroll_full_xor_cancel_inv,
        LLVMMemory.Com.denoteWithMemoryFuel, LLVMMemory.Com.denoteWithMemoryFuelIn,
        LLVMMemory.Com.denoteWithMemoryCore, Com.castPureToEff, Expr.castPureToEff,
        Com.changeEffect, Expr.changeEffect,
        LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
        LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
        LLVMMemory.Op.denoteVec, DialectDenote.denote, LLVM.const?] using h

end TestLoop
end InstCombine
