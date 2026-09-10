import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace InstCombine
namespace TestLoop

def licm_exitvalue_add_nuw_dropped_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @licm_exitvalue_add_nuw_dropped_src(%c1 : _, %c2 : _) -> _ {
  ^entry(%c1 : _, %c2 : _):
    %e_zero = llvm.mlir.constant 0 : _
    %e_start = llvm.mlir.constant 0 : _
    llvm.br ^loop(%e_zero : _, %e_start : _)
  ^loop(%k : _, %index : _):
    %step_add = llvm.add %index, %c1 : _
    %index_next = llvm.add %step_add, %c2 overflow<nuw> : _
    %l_one = llvm.mlir.constant 1 : _
    %k1 = llvm.add %k, %l_one : _
    %l_three = llvm.mlir.constant 3 : _
    %cond = llvm.icmp "eq" %k1, %l_three : _
    llvm.cond_br %cond : i1, ^out(%index_next : _), ^loop(%k1 : _, %index_next : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

def licm_exitvalue_add_nuw_dropped_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @licm_exitvalue_add_nuw_dropped_tgt(%c1 : _, %c2 : _) -> _ {
  ^entry(%c1 : _, %c2 : _):
    %invariant_op = llvm.add %c1, %c2 : _
    %s2 = llvm.add %invariant_op, %invariant_op : _
    %s3 = llvm.add %s2, %invariant_op : _
    llvm.return %s3 : _
  }
  }]

private abbrev licm_exitvalue_add_nuw_dropped_ity (w : Nat) : LLVM.Ty := LLVM.Ty.bitvec w

private abbrev licm_exitvalue_add_nuw_dropped_ctx (w : Nat) : Ctxt LLVM.Ty := Ctxt.ofList [(licm_exitvalue_add_nuw_dropped_ity w), (licm_exitvalue_add_nuw_dropped_ity w)]

private def licm_exitvalue_add_nuw_dropped_srcBlocks (w : Nat) : CFGBlocks LLVM (licm_exitvalue_add_nuw_dropped_ctx w) .impure [(licm_exitvalue_add_nuw_dropped_ity w)] :=
  match (licm_exitvalue_add_nuw_dropped_src w) with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private theorem licm_exitvalue_add_nuw_dropped_entry_ne_loop (w : Nat) : ¬ ("entry" = "loop") := by
  decide

private theorem licm_exitvalue_add_nuw_dropped_out_ne_loop (w : Nat) : ¬ ("out" = "loop") := by
  decide

private def licm_exitvalue_add_nuw_dropped_srcLoopTarget (w : Nat) : CFGTarget LLVM (Ctxt.ofList [(licm_exitvalue_add_nuw_dropped_ity w), (licm_exitvalue_add_nuw_dropped_ity w)]) where
  name := "loop"
  argTys := [(licm_exitvalue_add_nuw_dropped_ity w), (licm_exitvalue_add_nuw_dropped_ity w)]
  args := (⟨0, by rfl⟩ : (Ctxt.ofList [(licm_exitvalue_add_nuw_dropped_ity w), (licm_exitvalue_add_nuw_dropped_ity w)]).Var (licm_exitvalue_add_nuw_dropped_ity w)) ::ₕ (⟨1, by rfl⟩ : (Ctxt.ofList [(licm_exitvalue_add_nuw_dropped_ity w), (licm_exitvalue_add_nuw_dropped_ity w)]).Var (licm_exitvalue_add_nuw_dropped_ity w)) ::ₕ HVector.nil

private def licm_exitvalue_add_nuw_dropped_srcLoopVal (w : Nat) (j1 j2 : TyDenote.toType (licm_exitvalue_add_nuw_dropped_ity w)) :
    Ctxt.Valuation (Ctxt.ofList [(licm_exitvalue_add_nuw_dropped_ity w), (licm_exitvalue_add_nuw_dropped_ity w)]) :=
  Ctxt.Valuation.ofHVector (j1 ::ₕ j2 ::ₕ HVector.nil)

private theorem licm_exitvalue_add_nuw_dropped_src_loop_dispatch (w : Nat)
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation (licm_exitvalue_add_nuw_dropped_ctx w)) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a1 a2 : Γcur.Var (licm_exitvalue_add_nuw_dropped_ity w)) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (licm_exitvalue_add_nuw_dropped_srcBlocks w) V W
            ({ name := "loop", argTys := [(licm_exitvalue_add_nuw_dropped_ity w), (licm_exitvalue_add_nuw_dropped_ity w)], args := a1 ::ₕ a2 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (licm_exitvalue_add_nuw_dropped_srcBlocks w) V
            ((licm_exitvalue_add_nuw_dropped_srcLoopVal w) (W a1) (W a2)) (licm_exitvalue_add_nuw_dropped_srcLoopTarget w))
          ∅)
        s := by
  cases fuel <;>
    simp [licm_exitvalue_add_nuw_dropped_src, licm_exitvalue_add_nuw_dropped_srcBlocks, licm_exitvalue_add_nuw_dropped_srcLoopTarget, licm_exitvalue_add_nuw_dropped_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

private def licm_exitvalue_add_nuw_dropped_tgtResult (w : Nat) (V : Ctxt.Valuation (licm_exitvalue_add_nuw_dropped_ctx w)) : TyDenote.toType (licm_exitvalue_add_nuw_dropped_ity w) :=
  (InstCombine.lift2 (fun x y => LLVM.add x y) (InstCombine.lift2 (fun x y => LLVM.add x y) (InstCombine.lift2 (fun x y => LLVM.add x y) (V ((⟨1, by rfl⟩ : (licm_exitvalue_add_nuw_dropped_ctx w).Var (licm_exitvalue_add_nuw_dropped_ity w)))) (V (Ctxt.Var.last (Ctxt.ofList [(licm_exitvalue_add_nuw_dropped_ity w)]) (licm_exitvalue_add_nuw_dropped_ity w)))) (InstCombine.lift2 (fun x y => LLVM.add x y) (V ((⟨1, by rfl⟩ : (licm_exitvalue_add_nuw_dropped_ctx w).Var (licm_exitvalue_add_nuw_dropped_ity w)))) (V (Ctxt.Var.last (Ctxt.ofList [(licm_exitvalue_add_nuw_dropped_ity w)]) (licm_exitvalue_add_nuw_dropped_ity w))))) (InstCombine.lift2 (fun x y => LLVM.add x y) (V ((⟨1, by rfl⟩ : (licm_exitvalue_add_nuw_dropped_ctx w).Var (licm_exitvalue_add_nuw_dropped_ity w)))) (V (Ctxt.Var.last (Ctxt.ofList [(licm_exitvalue_add_nuw_dropped_ity w)]) (licm_exitvalue_add_nuw_dropped_ity w)))))

private def licm_exitvalue_add_nuw_dropped_inv (w : Nat) (j1 j2 : TyDenote.toType (licm_exitvalue_add_nuw_dropped_ity w))
    (V : Ctxt.Valuation (licm_exitvalue_add_nuw_dropped_ctx w)) : Prop :=
  ∀ (c1 c2 k index : BitVec w),
    V (((Ctxt.Var.last (Ctxt.ofList []) (licm_exitvalue_add_nuw_dropped_ity w)).toCons :
        (licm_exitvalue_add_nuw_dropped_ctx w).Var (licm_exitvalue_add_nuw_dropped_ity w))) =
        some (LLVM.SemVal.value c1) →
    V (Ctxt.Var.last (Ctxt.ofList [(licm_exitvalue_add_nuw_dropped_ity w)]) (licm_exitvalue_add_nuw_dropped_ity w)) =
        some (LLVM.SemVal.value c2) →
    j1 = some (LLVM.SemVal.value k) →
    j2 = some (LLVM.SemVal.value index) →
    index = k * (c1 + c2)

private theorem licm_exitvalue_add_nuw_dropped_step (w : Nat) (V : Ctxt.Valuation (licm_exitvalue_add_nuw_dropped_ctx w)) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (licm_exitvalue_add_nuw_dropped_ity w)),
      (licm_exitvalue_add_nuw_dropped_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (licm_exitvalue_add_nuw_dropped_srcBlocks w) V
              ((licm_exitvalue_add_nuw_dropped_srcLoopVal w) j1 j2) (licm_exitvalue_add_nuw_dropped_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((licm_exitvalue_add_nuw_dropped_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(licm_exitvalue_add_nuw_dropped_ity w)] × LLVMMemory.State))) :
    ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (licm_exitvalue_add_nuw_dropped_ity w)),
      (licm_exitvalue_add_nuw_dropped_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) (licm_exitvalue_add_nuw_dropped_srcBlocks w) V
              ((licm_exitvalue_add_nuw_dropped_srcLoopVal w) j1 j2) (licm_exitvalue_add_nuw_dropped_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((licm_exitvalue_add_nuw_dropped_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(licm_exitvalue_add_nuw_dropped_ity w)] × LLVMMemory.State)) :=
  by
    intro s j1 j2 hinv
    rcases hj1 : j1 with _ | (_ | k)
    · simp [licm_exitvalue_add_nuw_dropped_src, licm_exitvalue_add_nuw_dropped_srcBlocks, licm_exitvalue_add_nuw_dropped_srcLoopTarget,
        licm_exitvalue_add_nuw_dropped_srcLoopVal, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
        LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
        LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
        DialectSignature.effectKind, DialectSignature.signature, EffectKind.toMonad,
        EffectKind.liftEffect, LLVMMemory.throwUB]
      change (none : ImmediateUBOr (HVector TyDenote.toType [(licm_exitvalue_add_nuw_dropped_ity w)] ×
        LLVMMemory.State)) ⊑ some ((licm_exitvalue_add_nuw_dropped_tgtResult w) V ::ₕ HVector.nil, s)
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    · simp [licm_exitvalue_add_nuw_dropped_src, licm_exitvalue_add_nuw_dropped_srcBlocks, licm_exitvalue_add_nuw_dropped_srcLoopTarget,
        licm_exitvalue_add_nuw_dropped_srcLoopVal, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
        LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
        LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
        DialectSignature.effectKind, DialectSignature.signature, EffectKind.toMonad,
        EffectKind.liftEffect, LLVMMemory.throwUB, LLVM.add, LLVM.add?, LLVM.icmp,
        LLVM.icmp?, LLVM.icmp', LLVM.const?]
      change (none : ImmediateUBOr (HVector TyDenote.toType [(licm_exitvalue_add_nuw_dropped_ity w)] ×
        LLVMMemory.State)) ⊑ some ((licm_exitvalue_add_nuw_dropped_tgtResult w) V ::ₕ HVector.nil, s)
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    · let indexNext : TyDenote.toType (licm_exitvalue_add_nuw_dropped_ity w) :=
        InstCombine.lift2 (fun x y => LLVM.add x y { «nuw» := true })
          (InstCombine.lift2 (fun x y => LLVM.add x y) j2
            (V (((Ctxt.Var.last (Ctxt.ofList []) (licm_exitvalue_add_nuw_dropped_ity w)).toCons :
              (licm_exitvalue_add_nuw_dropped_ctx w).Var (licm_exitvalue_add_nuw_dropped_ity w)))))
          (V (Ctxt.Var.last (Ctxt.ofList [(licm_exitvalue_add_nuw_dropped_ity w)]) (licm_exitvalue_add_nuw_dropped_ity w)))
      have hExit : k + 1#w = 3#w → indexNext ⊑ (licm_exitvalue_add_nuw_dropped_tgtResult w) V := by
        intro hcondExit
        rcases hc1 :
            V (((Ctxt.Var.last (Ctxt.ofList []) (licm_exitvalue_add_nuw_dropped_ity w)).toCons :
              (licm_exitvalue_add_nuw_dropped_ctx w).Var (licm_exitvalue_add_nuw_dropped_ity w))) with
            _ | (_ | c1)
        <;> rcases hc2 :
            V (Ctxt.Var.last (Ctxt.ofList [(licm_exitvalue_add_nuw_dropped_ity w)]) (licm_exitvalue_add_nuw_dropped_ity w)) with
            _ | (_ | c2)
        <;> rcases hj2 : j2 with _ | (_ | index)
        <;> simp [indexNext, licm_exitvalue_add_nuw_dropped_tgtResult, LLVM.add, LLVM.add?, hc1, hc2, hj2]
        case some.value.some.value.some.value =>
          by_cases hov : BitVec.uaddOverflow (index + c1) c2
          · simp [hov]
            apply ImmediateUBOr.IsRefinedBy.bothValues
            simp
          · simp [hov]
            have hold := hinv c1 c2 k index hc1 hc2 hj1 hj2
            rw [hold]
            have hstep : k * (c1 + c2) + c1 + c2 = (k + 1#w) * (c1 + c2) := by
              rw [BitVec.add_assoc]
              rw [BitVec.mul_comm (k + 1#w) (c1 + c2), BitVec.mul_succ]
              rw [BitVec.mul_comm (c1 + c2) k]
            rw [hstep]
            rw [hcondExit]
            have h3 : (3#w : BitVec w) * (c1 + c2) =
                (c1 + c2) + (c1 + c2) + (c1 + c2) := by
              have h3c : (3#w : BitVec w) = (2#w : BitVec w) + 1#w := by
                rw [← BitVec.ofNat_add]
              rw [h3c, BitVec.mul_comm ((2#w : BitVec w) + 1#w) (c1 + c2),
                BitVec.mul_succ]
              rw [BitVec.mul_two]
            rw [h3]
            apply ImmediateUBOr.IsRefinedBy.bothValues
            simp
        all_goals
          first
          | exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
          | apply ImmediateUBOr.IsRefinedBy.bothValues; simp
      have hBack :
          (licm_exitvalue_add_nuw_dropped_inv w) (some (LLVM.SemVal.value (k + 1#w))) indexNext V := by
        intro c1 c2 k' index' hc1 hc2 hk' hidx'
        cases hk'
        rcases hj2 : j2 with _ | (_ | index)
        · simp [indexNext, LLVM.add, LLVM.add?, hc1, hc2, hj2] at hidx'
        · simp [indexNext, LLVM.add, LLVM.add?, hc1, hc2, hj2] at hidx'
          cases hidx'
        · by_cases hov : BitVec.uaddOverflow (index + c1) c2
          · simp [indexNext, LLVM.add, LLVM.add?, hc1, hc2, hj2, hov] at hidx'
            cases hidx'
          · simp [indexNext, LLVM.add, LLVM.add?, hc1, hc2, hj2, hov] at hidx'
            cases hidx'
            have hold := hinv c1 c2 k index hc1 hc2 hj1 hj2
            rw [hold]
            rw [BitVec.add_assoc]
            rw [BitVec.mul_comm (k + 1#w) (c1 + c2), BitVec.mul_succ]
            rw [BitVec.mul_comm (c1 + c2) k]
      by_cases hcond : k + 1#w = 3#w
      · cases fuel with
        | zero =>
            simp [licm_exitvalue_add_nuw_dropped_src, licm_exitvalue_add_nuw_dropped_srcBlocks, licm_exitvalue_add_nuw_dropped_srcLoopTarget,
              licm_exitvalue_add_nuw_dropped_srcLoopVal, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
              LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
              LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
              LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
              DialectSignature.effectKind, DialectSignature.signature, EffectKind.toMonad,
              EffectKind.liftEffect, LLVMMemory.throwUB, LLVM.add, LLVM.add?, LLVM.icmp,
              LLVM.icmp?, LLVM.icmp', LLVM.const?, hcond]
            change (none : ImmediateUBOr (HVector TyDenote.toType [(licm_exitvalue_add_nuw_dropped_ity w)] ×
              LLVMMemory.State)) ⊑ some ((licm_exitvalue_add_nuw_dropped_tgtResult w) V ::ₕ HVector.nil, s)
            exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        | succ fuel =>
            simp [licm_exitvalue_add_nuw_dropped_src, licm_exitvalue_add_nuw_dropped_srcBlocks, licm_exitvalue_add_nuw_dropped_srcLoopTarget,
              licm_exitvalue_add_nuw_dropped_srcLoopVal, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
              LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
              LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
              LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
              DialectSignature.effectKind, DialectSignature.signature, EffectKind.toMonad,
              EffectKind.liftEffect, LLVMMemory.throwUB, LLVM.add, LLVM.add?, LLVM.icmp,
              LLVM.icmp?, LLVM.icmp', LLVM.const?, hcond]
            apply ImmediateUBOr.IsRefinedBy.bothValues
            constructor
            · constructor
              · simpa [indexNext, LLVM.add, LLVM.add?, Ctxt.Valuation.cons_last,
                  Ctxt.Valuation.cons_toCons, Ctxt.Valuation.cons_eval] using hExit hcond
              · trivial
            · rfl
      · have hb : (k + 1#w == 3#w) = false := by
          simpa [Bool.not_eq_true] using (show ¬ (k + 1#w == 3#w) = true by
            simpa [BEq.beq] using hcond)
        simp [licm_exitvalue_add_nuw_dropped_src, licm_exitvalue_add_nuw_dropped_srcBlocks, licm_exitvalue_add_nuw_dropped_srcLoopTarget,
          licm_exitvalue_add_nuw_dropped_srcLoopVal, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
          LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
          LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
          DialectSignature.effectKind, DialectSignature.signature, EffectKind.toMonad,
          EffectKind.liftEffect, LLVMMemory.throwUB, LLVM.add, LLVM.add?, LLVM.icmp,
          LLVM.icmp?, LLVM.icmp', LLVM.const?, hb]
        change (StateT.run
            (ReaderT.run
              (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (licm_exitvalue_add_nuw_dropped_srcBlocks w) V _
                ({ name := "loop", argTys := [(licm_exitvalue_add_nuw_dropped_ity w), (licm_exitvalue_add_nuw_dropped_ity w)], args := _ ::ₕ _ ::ₕ HVector.nil } : CFGTarget LLVM _))
              ∅)
            s ⊑
          some ((licm_exitvalue_add_nuw_dropped_tgtResult w) V ::ₕ HVector.nil, s)
        )
        rw [licm_exitvalue_add_nuw_dropped_src_loop_dispatch]
        simpa [indexNext, licm_exitvalue_add_nuw_dropped_srcLoopVal, LLVM.add, LLVM.add?,
          Ctxt.Valuation.cons_last, Ctxt.Valuation.cons_toCons, Ctxt.Valuation.cons_eval] using
          ih s (some (LLVM.SemVal.value (k + 1#w))) indexNext hBack

private theorem licm_exitvalue_add_nuw_dropped_loop_refine (w : Nat) (V : Ctxt.Valuation (licm_exitvalue_add_nuw_dropped_ctx w)) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (licm_exitvalue_add_nuw_dropped_ity w)),
      (licm_exitvalue_add_nuw_dropped_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (licm_exitvalue_add_nuw_dropped_srcBlocks w) V
              ((licm_exitvalue_add_nuw_dropped_srcLoopVal w) j1 j2) (licm_exitvalue_add_nuw_dropped_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((licm_exitvalue_add_nuw_dropped_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(licm_exitvalue_add_nuw_dropped_ity w)] × LLVMMemory.State)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s j1 j2 _hinv
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact (licm_exitvalue_add_nuw_dropped_step w) V fuel ih

theorem licm_exitvalue_add_nuw_dropped_correct (w : Nat) :
    IsRefinedByOnIntWInputsWithMemory (licm_exitvalue_add_nuw_dropped_src w) ((licm_exitvalue_add_nuw_dropped_tgt w).castPureToEff .impure) := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>

      have hInit :
          (licm_exitvalue_add_nuw_dropped_inv w) (some (LLVM.SemVal.value (0#w)))
            (some (LLVM.SemVal.value (0#w))) V.lift := by
        intro c1 c2 k index _hc1 _hc2 hk hindex
        cases hk
        cases hindex
        simp
      simp [simp_memory, simp_llvm, licm_exitvalue_add_nuw_dropped_src, licm_exitvalue_add_nuw_dropped_tgt,
        LLVMMemory.Com.denoteWithMemoryFuel, LLVMMemory.Com.denoteWithMemoryFuelIn,
        LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
        LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
        LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
        DialectSignature.effectKind, DialectSignature.signature, EffectKind.toMonad,
        EffectKind.liftEffect, Expr.changeEffect, Com.castPureToEff, Com.changeEffect]
      change (StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (licm_exitvalue_add_nuw_dropped_srcBlocks w) V.lift _
              ({ name := "loop", argTys := [(licm_exitvalue_add_nuw_dropped_ity w), (licm_exitvalue_add_nuw_dropped_ity w)], args := _ ::ₕ _ ::ₕ HVector.nil } : CFGTarget LLVM _))
            ∅)
          s ⊑
        some ((licm_exitvalue_add_nuw_dropped_tgtResult w) V.lift ::ₕ HVector.nil, s)
      )
      rw [licm_exitvalue_add_nuw_dropped_src_loop_dispatch]
      simpa [licm_exitvalue_add_nuw_dropped_tgtResult] using
        (licm_exitvalue_add_nuw_dropped_loop_refine w V.lift fuel s (some (LLVM.SemVal.value (0#w)))
          (some (LLVM.SemVal.value (0#w))) hInit)

end TestLoop
end InstCombine
