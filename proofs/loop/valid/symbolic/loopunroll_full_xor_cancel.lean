import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace InstCombine
namespace TestLoop

def loopunroll_full_xor_cancel_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @loopunroll_full_xor_cancel_src(%m : _, %x : _) -> _ {
  ^entry(%m : _, %x : _):
    %e_zero = llvm.mlir.constant 0 : _
    llvm.br ^loop(%e_zero : _, %x : _)
  ^loop(%i : _, %v : _):
    %v1 = llvm.xor %v, %m : _
    %l_one = llvm.mlir.constant 1 : _
    %i1 = llvm.add %i, %l_one : _
    %l_two = llvm.mlir.constant 2 : _
    %cond = llvm.icmp "eq" %i1, %l_two : _
    llvm.cond_br %cond : i1, ^out(%v1 : _), ^loop(%i1 : _, %v1 : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

def loopunroll_full_xor_cancel_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @loopunroll_full_xor_cancel_tgt(%m : _, %x : _) -> _ {
  ^entry(%m : _, %x : _):
    llvm.return %x : _
  }
  }]

private abbrev loopunroll_full_xor_cancel_ity (w : Nat) : LLVM.Ty := LLVM.Ty.bitvec w

private abbrev loopunroll_full_xor_cancel_ctx (w : Nat) : Ctxt LLVM.Ty := Ctxt.ofList [(loopunroll_full_xor_cancel_ity w), (loopunroll_full_xor_cancel_ity w)]

private def loopunroll_full_xor_cancel_srcBlocks (w : Nat) : CFGBlocks LLVM (loopunroll_full_xor_cancel_ctx w) .impure [(loopunroll_full_xor_cancel_ity w)] :=
  match (loopunroll_full_xor_cancel_src w) with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private theorem loopunroll_full_xor_cancel_entry_ne_loop (w : Nat) : ¬ ("entry" = "loop") := by
  decide

private theorem loopunroll_full_xor_cancel_out_ne_loop (w : Nat) : ¬ ("out" = "loop") := by
  decide

private def loopunroll_full_xor_cancel_srcLoopTarget (w : Nat) : CFGTarget LLVM (Ctxt.ofList [(loopunroll_full_xor_cancel_ity w), (loopunroll_full_xor_cancel_ity w)]) where
  name := "loop"
  argTys := [(loopunroll_full_xor_cancel_ity w), (loopunroll_full_xor_cancel_ity w)]
  args := (⟨0, by rfl⟩ : (Ctxt.ofList [(loopunroll_full_xor_cancel_ity w), (loopunroll_full_xor_cancel_ity w)]).Var (loopunroll_full_xor_cancel_ity w)) ::ₕ (⟨1, by rfl⟩ : (Ctxt.ofList [(loopunroll_full_xor_cancel_ity w), (loopunroll_full_xor_cancel_ity w)]).Var (loopunroll_full_xor_cancel_ity w)) ::ₕ HVector.nil

private def loopunroll_full_xor_cancel_srcLoopVal (w : Nat) (j1 j2 : TyDenote.toType (loopunroll_full_xor_cancel_ity w)) :
    Ctxt.Valuation (Ctxt.ofList [(loopunroll_full_xor_cancel_ity w), (loopunroll_full_xor_cancel_ity w)]) :=
  Ctxt.Valuation.ofHVector (j1 ::ₕ j2 ::ₕ HVector.nil)

private theorem loopunroll_full_xor_cancel_src_loop_dispatch (w : Nat)
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation (loopunroll_full_xor_cancel_ctx w)) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a1 a2 : Γcur.Var (loopunroll_full_xor_cancel_ity w)) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (loopunroll_full_xor_cancel_srcBlocks w) V W
            ({ name := "loop", argTys := [(loopunroll_full_xor_cancel_ity w), (loopunroll_full_xor_cancel_ity w)], args := a1 ::ₕ a2 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (loopunroll_full_xor_cancel_srcBlocks w) V
            ((loopunroll_full_xor_cancel_srcLoopVal w) (W a1) (W a2)) (loopunroll_full_xor_cancel_srcLoopTarget w))
          ∅)
        s := by
  cases fuel <;>
    simp [loopunroll_full_xor_cancel_src, loopunroll_full_xor_cancel_srcBlocks, loopunroll_full_xor_cancel_srcLoopTarget, loopunroll_full_xor_cancel_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

private def loopunroll_full_xor_cancel_tgtResult (w : Nat) (V : Ctxt.Valuation (loopunroll_full_xor_cancel_ctx w)) : TyDenote.toType (loopunroll_full_xor_cancel_ity w) :=
  (V (Ctxt.Var.last (Ctxt.ofList [(loopunroll_full_xor_cancel_ity w)]) (loopunroll_full_xor_cancel_ity w)))

private def loopunroll_full_xor_cancel_inv (w : Nat) (j1 j2 : TyDenote.toType (loopunroll_full_xor_cancel_ity w))
    (V : Ctxt.Valuation (loopunroll_full_xor_cancel_ctx w)) : Prop :=
  j1 = some (LLVM.SemVal.value 0#w) ∧
    j2 = V (Ctxt.Var.last (Ctxt.ofList [(loopunroll_full_xor_cancel_ity w)]) (loopunroll_full_xor_cancel_ity w))

private theorem loopunroll_full_xor_cancel_one_ne_two (w : Nat) (hw : w ≠ 0) : (1#w : BitVec w) ≠ 2#w := by
  intro h
  rcases w with _ | _ | w
  · exact hw rfl
  · exact absurd h (by decide)
  · have hlt : 2 < 2 ^ (w + 2) := by
      have := Nat.one_le_two_pow (n := w)
      rw [Nat.pow_succ, Nat.pow_succ]
      omega
    rw [BitVec.toNat_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hlt] at h
    omega

private theorem loopunroll_full_xor_cancel_step (w : Nat) (V : Ctxt.Valuation (loopunroll_full_xor_cancel_ctx w)) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (loopunroll_full_xor_cancel_ity w)),
      (loopunroll_full_xor_cancel_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (loopunroll_full_xor_cancel_srcBlocks w) V
              ((loopunroll_full_xor_cancel_srcLoopVal w) j1 j2) (loopunroll_full_xor_cancel_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((loopunroll_full_xor_cancel_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(loopunroll_full_xor_cancel_ity w)] × LLVMMemory.State))) :
    ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (loopunroll_full_xor_cancel_ity w)),
      (loopunroll_full_xor_cancel_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) (loopunroll_full_xor_cancel_srcBlocks w) V
              ((loopunroll_full_xor_cancel_srcLoopVal w) j1 j2) (loopunroll_full_xor_cancel_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((loopunroll_full_xor_cancel_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(loopunroll_full_xor_cancel_ity w)] × LLVMMemory.State)) :=
  by
    intro s j1 j2 hinv
    rcases hinv with ⟨hj1, hj2⟩
    subst hj1
    subst hj2
    have h2 : (1#w : BitVec w) + 1#w = 2#w := by
      rw [← BitVec.ofNat_add]
    cases fuel with
    | zero =>
        simp [loopunroll_full_xor_cancel_src, loopunroll_full_xor_cancel_srcBlocks, loopunroll_full_xor_cancel_srcLoopTarget,
          loopunroll_full_xor_cancel_srcLoopVal, loopunroll_full_xor_cancel_tgtResult, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
          LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
          LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
          DialectSignature.effectKind, DialectSignature.signature, EffectKind.toMonad,
          EffectKind.liftEffect, LLVMMemory.throwUB, LLVM.xor, LLVM.xor?, LLVM.add, LLVM.add?,
          LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.const?]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    | succ fuel =>
        simp [loopunroll_full_xor_cancel_src, loopunroll_full_xor_cancel_srcBlocks, loopunroll_full_xor_cancel_srcLoopTarget,
          loopunroll_full_xor_cancel_srcLoopVal, loopunroll_full_xor_cancel_tgtResult, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
          LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
          LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
          DialectSignature.effectKind, DialectSignature.signature, EffectKind.toMonad,
          EffectKind.liftEffect, LLVMMemory.throwUB, LLVM.xor, LLVM.xor?, LLVM.add, LLVM.add?,
          LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.const?]
        by_cases h1 : (1#w : BitVec w) = 2#w
        · have hw : w = 0 := by
            by_contra hw
            exact loopunroll_full_xor_cancel_one_ne_two w hw h1
          subst hw
          simp [h1]
          change (some ((InstCombine.lift2 (fun a b => LLVM.xor a b) (V (Ctxt.Var.last (Ctxt.ofList [(loopunroll_full_xor_cancel_ity 0)]) (loopunroll_full_xor_cancel_ity 0))) (V (((Ctxt.Var.last (Ctxt.ofList []) (loopunroll_full_xor_cancel_ity 0)).toCons : (loopunroll_full_xor_cancel_ctx 0).Var (loopunroll_full_xor_cancel_ity 0)))))
              ::ₕ HVector.nil, s) :
              ImmediateUBOr (HVector TyDenote.toType [(loopunroll_full_xor_cancel_ity 0)] × LLVMMemory.State)) ⊑
            some ((V (Ctxt.Var.last (Ctxt.ofList [(loopunroll_full_xor_cancel_ity 0)]) (loopunroll_full_xor_cancel_ity 0))) ::ₕ HVector.nil, s)
          rcases hx : (V (Ctxt.Var.last (Ctxt.ofList [(loopunroll_full_xor_cancel_ity 0)]) (loopunroll_full_xor_cancel_ity 0))) with _ | (_ | x)
          <;> rcases hm : (V (((Ctxt.Var.last (Ctxt.ofList []) (loopunroll_full_xor_cancel_ity 0)).toCons : (loopunroll_full_xor_cancel_ctx 0).Var (loopunroll_full_xor_cancel_ity 0)))) with _ | (_ | m)
          <;> simp [InstCombine.lift2, LLVM.xor, LLVM.xor?]
          all_goals first
            | exact ImmediateUBOr.IsRefinedBy.bothValues
                ⟨⟨ImmediateUBOr.IsRefinedBy.immediateUBLeft, trivial⟩, rfl⟩
            | exact ImmediateUBOr.IsRefinedBy.bothValues ⟨⟨IntWUB_le_self _, trivial⟩, rfl⟩
            | exact ImmediateUBOr.IsRefinedBy.bothValues
                ⟨⟨ImmediateUBOr.IsRefinedBy.bothValues (LLVM.SemVal.poison_isRefinedBy _), trivial⟩, rfl⟩
            | exact ImmediateUBOr.IsRefinedBy.bothValues
                ⟨⟨ImmediateUBOr.IsRefinedBy.bothValues
                  ((LLVM.IntW.isRefinedBy_iff _ _).mpr (LLVM.SemVal.poison_isRefinedBy _)), trivial⟩, rfl⟩
            | (rw [BitVec.eq_nil (_ ^^^ _), BitVec.eq_nil x]
               exact ImmediateUBOr.IsRefinedBy.bothValues ⟨⟨IntWUB_le_self _, trivial⟩, rfl⟩)
        · have hb1 : ((1#w : BitVec w) == 2#w) = false := by
            simpa using h1
          have hb2 : ((1#w : BitVec w) + 1#w == 2#w) = true := by
            simp [h2]
          simp only [hb1, hb2, BitVec.ofBool_false, BitVec.ofBool_true]
          simp
          cases fuel with
          | zero =>
              simp [loopunroll_full_xor_cancel_src, loopunroll_full_xor_cancel_srcBlocks, loopunroll_full_xor_cancel_srcLoopTarget,
                loopunroll_full_xor_cancel_srcLoopVal, loopunroll_full_xor_cancel_tgtResult, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
                LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
                DialectSignature.effectKind, DialectSignature.signature, EffectKind.toMonad,
                EffectKind.liftEffect, LLVMMemory.throwUB, LLVM.xor, LLVM.xor?, LLVM.add, LLVM.add?,
                LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.const?]
              exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
          | succ fuel =>
              simp [loopunroll_full_xor_cancel_src, loopunroll_full_xor_cancel_srcBlocks, loopunroll_full_xor_cancel_srcLoopTarget,
                loopunroll_full_xor_cancel_srcLoopVal, loopunroll_full_xor_cancel_tgtResult, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
                LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
                DialectSignature.effectKind, DialectSignature.signature, EffectKind.toMonad,
                EffectKind.liftEffect, LLVMMemory.throwUB, LLVM.xor, LLVM.xor?, LLVM.add, LLVM.add?,
                LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.const?]
              change (some ((InstCombine.lift2 (fun a b => LLVM.xor a b) (InstCombine.lift2 (fun a b => LLVM.xor a b) (V (Ctxt.Var.last (Ctxt.ofList [(loopunroll_full_xor_cancel_ity w)]) (loopunroll_full_xor_cancel_ity w))) (V (((Ctxt.Var.last (Ctxt.ofList []) (loopunroll_full_xor_cancel_ity w)).toCons : (loopunroll_full_xor_cancel_ctx w).Var (loopunroll_full_xor_cancel_ity w))))) (V (((Ctxt.Var.last (Ctxt.ofList []) (loopunroll_full_xor_cancel_ity w)).toCons : (loopunroll_full_xor_cancel_ctx w).Var (loopunroll_full_xor_cancel_ity w)))))
                  ::ₕ HVector.nil, s) :
                  ImmediateUBOr (HVector TyDenote.toType [(loopunroll_full_xor_cancel_ity w)] × LLVMMemory.State)) ⊑
                some ((V (Ctxt.Var.last (Ctxt.ofList [(loopunroll_full_xor_cancel_ity w)]) (loopunroll_full_xor_cancel_ity w))) ::ₕ HVector.nil, s)
              rcases hx : (V (Ctxt.Var.last (Ctxt.ofList [(loopunroll_full_xor_cancel_ity w)]) (loopunroll_full_xor_cancel_ity w))) with _ | (_ | x)
              <;> rcases hm : (V (((Ctxt.Var.last (Ctxt.ofList []) (loopunroll_full_xor_cancel_ity w)).toCons : (loopunroll_full_xor_cancel_ctx w).Var (loopunroll_full_xor_cancel_ity w)))) with _ | (_ | m)
              <;> simp [InstCombine.lift2, LLVM.xor, LLVM.xor?]
              all_goals first
                | exact ImmediateUBOr.IsRefinedBy.bothValues
                    ⟨⟨ImmediateUBOr.IsRefinedBy.immediateUBLeft, trivial⟩, rfl⟩
                | exact ImmediateUBOr.IsRefinedBy.bothValues ⟨⟨IntWUB_le_self _, trivial⟩, rfl⟩
                | exact ImmediateUBOr.IsRefinedBy.bothValues
                    ⟨⟨ImmediateUBOr.IsRefinedBy.bothValues (LLVM.SemVal.poison_isRefinedBy _), trivial⟩, rfl⟩
                | exact ImmediateUBOr.IsRefinedBy.bothValues
                    ⟨⟨ImmediateUBOr.IsRefinedBy.bothValues
                      ((LLVM.IntW.isRefinedBy_iff _ _).mpr (LLVM.SemVal.poison_isRefinedBy _)), trivial⟩, rfl⟩
                | (rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
                   exact ImmediateUBOr.IsRefinedBy.bothValues ⟨⟨IntWUB_le_self _, trivial⟩, rfl⟩)

private theorem loopunroll_full_xor_cancel_loop_refine (w : Nat) (V : Ctxt.Valuation (loopunroll_full_xor_cancel_ctx w)) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (loopunroll_full_xor_cancel_ity w)),
      (loopunroll_full_xor_cancel_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (loopunroll_full_xor_cancel_srcBlocks w) V
              ((loopunroll_full_xor_cancel_srcLoopVal w) j1 j2) (loopunroll_full_xor_cancel_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((loopunroll_full_xor_cancel_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(loopunroll_full_xor_cancel_ity w)] × LLVMMemory.State)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s j1 j2 _hinv
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact (loopunroll_full_xor_cancel_step w) V fuel ih

theorem loopunroll_full_xor_cancel_correct (w : Nat) :
    IsRefinedByOnIntWInputsWithMemory (loopunroll_full_xor_cancel_src w) ((loopunroll_full_xor_cancel_tgt w).castPureToEff .impure) := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>

      simp [loopunroll_full_xor_cancel_src, loopunroll_full_xor_cancel_tgt,
        LLVMMemory.Com.denoteWithMemoryFuel, LLVMMemory.Com.denoteWithMemoryFuelIn,
        LLVMMemory.Com.denoteWithMemoryCore, Com.castPureToEff, Com.changeEffect,
        LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
        LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
        LLVMMemory.Op.denoteVec, DialectDenote.denote, LLVM.const?]
      have h := loopunroll_full_xor_cancel_loop_refine w (InputValuation.lift V) fuel s
        (some (LLVM.SemVal.value 0#w))
        ((InputValuation.lift V) (Ctxt.Var.last (Ctxt.ofList [(loopunroll_full_xor_cancel_ity w)]) (loopunroll_full_xor_cancel_ity w)))
        (by simp [loopunroll_full_xor_cancel_inv])
      simp [loopunroll_full_xor_cancel_srcLoopVal, loopunroll_full_xor_cancel_tgtResult] at h
      have hdispatch := loopunroll_full_xor_cancel_src_loop_dispatch w
        (V := InputValuation.lift V)
        (W := (some (LLVM.SemVal.value 0#w)) ::ᵥ (InputValuation.lift V))
        (fuel := fuel)
        (s := s)
        (a1 := Ctxt.Var.last (Ctxt.ofList [(loopunroll_full_xor_cancel_ity w), (loopunroll_full_xor_cancel_ity w)]) (loopunroll_full_xor_cancel_ity w))
        (a2 := (⟨1, by rfl⟩ : (Ctxt.ofList [(loopunroll_full_xor_cancel_ity w), (loopunroll_full_xor_cancel_ity w), (loopunroll_full_xor_cancel_ity w)]).Var (loopunroll_full_xor_cancel_ity w)))
      simp [loopunroll_full_xor_cancel_srcLoopVal] at hdispatch
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
