import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace InstCombine
namespace TestLoop

def licm_exitvalue_add_nuw_dropped_src :=
  [llvm()| {
  llvm.func @licm_exitvalue_add_nuw_dropped_src(%c1 : i64, %c2 : i64) -> i64 {
  ^entry(%c1 : i64, %c2 : i64):
    %e_zero = llvm.mlir.constant 0 : i64
    %e_start = llvm.mlir.constant 0 : i64
    llvm.br ^loop(%e_zero : i64, %e_start : i64)
  ^loop(%k : i64, %index : i64):
    %step_add = llvm.add %index, %c1 : i64
    %index_next = llvm.add %step_add, %c2 overflow<nuw> : i64
    %l_one = llvm.mlir.constant 1 : i64
    %k1 = llvm.add %k, %l_one : i64
    %l_three = llvm.mlir.constant 3 : i64
    %cond = llvm.icmp "eq" %k1, %l_three : i64
    llvm.cond_br %cond : i1, ^out(%index_next : i64), ^loop(%k1 : i64, %index_next : i64)
  ^out(%res : i64):
    llvm.return %res : i64
  }
  }]

def licm_exitvalue_add_nuw_dropped_tgt :=
  [llvm()| {
  llvm.func @licm_exitvalue_add_nuw_dropped_tgt(%c1 : i64, %c2 : i64) -> i64 {
  ^entry(%c1 : i64, %c2 : i64):
    %invariant_op = llvm.add %c1, %c2 : i64
    %s2 = llvm.add %invariant_op, %invariant_op : i64
    %s3 = llvm.add %s2, %invariant_op : i64
    llvm.return %s3 : i64
  }
  }]

private abbrev licm_exitvalue_add_nuw_dropped_ity : LLVM.Ty := LLVM.Ty.bitvec 64

private abbrev licm_exitvalue_add_nuw_dropped_ctx : Ctxt LLVM.Ty := Ctxt.ofList [licm_exitvalue_add_nuw_dropped_ity, licm_exitvalue_add_nuw_dropped_ity]

private def licm_exitvalue_add_nuw_dropped_srcBlocks : CFGBlocks LLVM licm_exitvalue_add_nuw_dropped_ctx .impure [licm_exitvalue_add_nuw_dropped_ity] :=
  match licm_exitvalue_add_nuw_dropped_src with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private theorem licm_exitvalue_add_nuw_dropped_entry_ne_loop : ¬ ("entry" = "loop") := by
  decide

private theorem licm_exitvalue_add_nuw_dropped_out_ne_loop : ¬ ("out" = "loop") := by
  decide

private def licm_exitvalue_add_nuw_dropped_srcLoopTarget : CFGTarget LLVM (Ctxt.ofList [licm_exitvalue_add_nuw_dropped_ity, licm_exitvalue_add_nuw_dropped_ity]) where
  name := "loop"
  argTys := [licm_exitvalue_add_nuw_dropped_ity, licm_exitvalue_add_nuw_dropped_ity]
  args := (⟨0, by decide⟩ : (Ctxt.ofList [licm_exitvalue_add_nuw_dropped_ity, licm_exitvalue_add_nuw_dropped_ity]).Var licm_exitvalue_add_nuw_dropped_ity) ::ₕ (⟨1, by decide⟩ : (Ctxt.ofList [licm_exitvalue_add_nuw_dropped_ity, licm_exitvalue_add_nuw_dropped_ity]).Var licm_exitvalue_add_nuw_dropped_ity) ::ₕ HVector.nil

private def licm_exitvalue_add_nuw_dropped_srcLoopVal (j1 j2 : TyDenote.toType licm_exitvalue_add_nuw_dropped_ity) :
    Ctxt.Valuation (Ctxt.ofList [licm_exitvalue_add_nuw_dropped_ity, licm_exitvalue_add_nuw_dropped_ity]) :=
  Ctxt.Valuation.ofHVector (j1 ::ₕ j2 ::ₕ HVector.nil)

private theorem licm_exitvalue_add_nuw_dropped_src_loop_dispatch
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation licm_exitvalue_add_nuw_dropped_ctx) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a1 a2 : Γcur.Var licm_exitvalue_add_nuw_dropped_ity) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel licm_exitvalue_add_nuw_dropped_srcBlocks V W
            ({ name := "loop", argTys := [licm_exitvalue_add_nuw_dropped_ity, licm_exitvalue_add_nuw_dropped_ity], args := a1 ::ₕ a2 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel licm_exitvalue_add_nuw_dropped_srcBlocks V
            (licm_exitvalue_add_nuw_dropped_srcLoopVal (W a1) (W a2)) licm_exitvalue_add_nuw_dropped_srcLoopTarget)
          ∅)
        s := by
  cases fuel <;>
    simp [licm_exitvalue_add_nuw_dropped_src, licm_exitvalue_add_nuw_dropped_srcBlocks, licm_exitvalue_add_nuw_dropped_srcLoopTarget, licm_exitvalue_add_nuw_dropped_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

private def licm_exitvalue_add_nuw_dropped_tgtResult (V : Ctxt.Valuation licm_exitvalue_add_nuw_dropped_ctx) : TyDenote.toType licm_exitvalue_add_nuw_dropped_ity :=
  (InstCombine.lift2 (fun x y => LLVM.add x y) (InstCombine.lift2 (fun x y => LLVM.add x y) (InstCombine.lift2 (fun x y => LLVM.add x y) (V ((⟨1, by rfl⟩ : licm_exitvalue_add_nuw_dropped_ctx.Var licm_exitvalue_add_nuw_dropped_ity))) (V (Ctxt.Var.last (Ctxt.ofList [licm_exitvalue_add_nuw_dropped_ity]) licm_exitvalue_add_nuw_dropped_ity))) (InstCombine.lift2 (fun x y => LLVM.add x y) (V ((⟨1, by rfl⟩ : licm_exitvalue_add_nuw_dropped_ctx.Var licm_exitvalue_add_nuw_dropped_ity))) (V (Ctxt.Var.last (Ctxt.ofList [licm_exitvalue_add_nuw_dropped_ity]) licm_exitvalue_add_nuw_dropped_ity)))) (InstCombine.lift2 (fun x y => LLVM.add x y) (V ((⟨1, by rfl⟩ : licm_exitvalue_add_nuw_dropped_ctx.Var licm_exitvalue_add_nuw_dropped_ity))) (V (Ctxt.Var.last (Ctxt.ofList [licm_exitvalue_add_nuw_dropped_ity]) licm_exitvalue_add_nuw_dropped_ity))))

private def licm_exitvalue_add_nuw_dropped_inv (j1 j2 : TyDenote.toType licm_exitvalue_add_nuw_dropped_ity)
    (V : Ctxt.Valuation licm_exitvalue_add_nuw_dropped_ctx) : Prop :=
  ∀ (c1 c2 k index : BitVec 64),
    V (((Ctxt.Var.last (Ctxt.ofList []) licm_exitvalue_add_nuw_dropped_ity).toCons :
        licm_exitvalue_add_nuw_dropped_ctx.Var licm_exitvalue_add_nuw_dropped_ity)) =
        some (LLVM.SemVal.value c1) →
    V (Ctxt.Var.last (Ctxt.ofList [licm_exitvalue_add_nuw_dropped_ity]) licm_exitvalue_add_nuw_dropped_ity) =
        some (LLVM.SemVal.value c2) →
    j1 = some (LLVM.SemVal.value k) →
    j2 = some (LLVM.SemVal.value index) →
    index = k * (c1 + c2)

private theorem licm_exitvalue_add_nuw_dropped_step (V : Ctxt.Valuation licm_exitvalue_add_nuw_dropped_ctx) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType licm_exitvalue_add_nuw_dropped_ity),
      licm_exitvalue_add_nuw_dropped_inv j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel licm_exitvalue_add_nuw_dropped_srcBlocks V
              (licm_exitvalue_add_nuw_dropped_srcLoopVal j1 j2) licm_exitvalue_add_nuw_dropped_srcLoopTarget)
            ∅)
          s
        ⊑
        (some (licm_exitvalue_add_nuw_dropped_tgtResult V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [licm_exitvalue_add_nuw_dropped_ity] × LLVMMemory.State))) :
    ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType licm_exitvalue_add_nuw_dropped_ity),
      licm_exitvalue_add_nuw_dropped_inv j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) licm_exitvalue_add_nuw_dropped_srcBlocks V
              (licm_exitvalue_add_nuw_dropped_srcLoopVal j1 j2) licm_exitvalue_add_nuw_dropped_srcLoopTarget)
            ∅)
          s
        ⊑
        (some (licm_exitvalue_add_nuw_dropped_tgtResult V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [licm_exitvalue_add_nuw_dropped_ity] × LLVMMemory.State)) :=
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
      change (none : ImmediateUBOr (HVector TyDenote.toType [licm_exitvalue_add_nuw_dropped_ity] ×
        LLVMMemory.State)) ⊑ some (licm_exitvalue_add_nuw_dropped_tgtResult V ::ₕ HVector.nil, s)
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    · simp [licm_exitvalue_add_nuw_dropped_src, licm_exitvalue_add_nuw_dropped_srcBlocks, licm_exitvalue_add_nuw_dropped_srcLoopTarget,
        licm_exitvalue_add_nuw_dropped_srcLoopVal, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
        LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
        LLVMMemory.Op.denoteVec, InstCombine.Op.denote, DialectDenote.denote,
        DialectSignature.effectKind, DialectSignature.signature, EffectKind.toMonad,
        EffectKind.liftEffect, LLVMMemory.throwUB, LLVM.add, LLVM.add?, LLVM.icmp,
        LLVM.icmp?, LLVM.icmp', LLVM.const?]
      change (none : ImmediateUBOr (HVector TyDenote.toType [licm_exitvalue_add_nuw_dropped_ity] ×
        LLVMMemory.State)) ⊑ some (licm_exitvalue_add_nuw_dropped_tgtResult V ::ₕ HVector.nil, s)
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    · let indexNext : TyDenote.toType licm_exitvalue_add_nuw_dropped_ity :=
        InstCombine.lift2 (fun x y => LLVM.add x y { «nuw» := true })
          (InstCombine.lift2 (fun x y => LLVM.add x y) j2
            (V (((Ctxt.Var.last (Ctxt.ofList []) licm_exitvalue_add_nuw_dropped_ity).toCons :
              licm_exitvalue_add_nuw_dropped_ctx.Var licm_exitvalue_add_nuw_dropped_ity))))
          (V (Ctxt.Var.last (Ctxt.ofList [licm_exitvalue_add_nuw_dropped_ity]) licm_exitvalue_add_nuw_dropped_ity))
      have hExit : k + 1#64 = 3#64 → indexNext ⊑ licm_exitvalue_add_nuw_dropped_tgtResult V := by
        intro hcondExit
        rcases hc1 :
            V (((Ctxt.Var.last (Ctxt.ofList []) licm_exitvalue_add_nuw_dropped_ity).toCons :
              licm_exitvalue_add_nuw_dropped_ctx.Var licm_exitvalue_add_nuw_dropped_ity)) with
            _ | (_ | c1)
        <;> rcases hc2 :
            V (Ctxt.Var.last (Ctxt.ofList [licm_exitvalue_add_nuw_dropped_ity]) licm_exitvalue_add_nuw_dropped_ity) with
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
            have hstep : k * (c1 + c2) + c1 + c2 = (k + 1#64) * (c1 + c2) := by
              rw [BitVec.add_assoc]
              rw [BitVec.mul_comm (k + 1#64) (c1 + c2), BitVec.mul_succ]
              rw [BitVec.mul_comm (c1 + c2) k]
            rw [hstep]
            rw [hcondExit]
            have h3 : (3#64 : BitVec 64) * (c1 + c2) =
                (c1 + c2) + (c1 + c2) + (c1 + c2) := by
              have h3c : (3#64 : BitVec 64) = (2#64 : BitVec 64) + 1#64 := by
                rw [← BitVec.ofNat_add]
              rw [h3c, BitVec.mul_comm ((2#64 : BitVec 64) + 1#64) (c1 + c2),
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
          licm_exitvalue_add_nuw_dropped_inv (some (LLVM.SemVal.value (k + 1#64))) indexNext V := by
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
            rw [BitVec.mul_comm (k + 1#64) (c1 + c2), BitVec.mul_succ]
            rw [BitVec.mul_comm (c1 + c2) k]
      by_cases hcond : k + 1#64 = 3#64
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
            change (none : ImmediateUBOr (HVector TyDenote.toType [licm_exitvalue_add_nuw_dropped_ity] ×
              LLVMMemory.State)) ⊑ some (licm_exitvalue_add_nuw_dropped_tgtResult V ::ₕ HVector.nil, s)
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
      · have hb : (k + 1#64 == 3#64) = false := by
          simpa [Bool.not_eq_true] using (show ¬ (k + 1#64 == 3#64) = true by
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
              (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel licm_exitvalue_add_nuw_dropped_srcBlocks V _
                ({ name := "loop", argTys := [licm_exitvalue_add_nuw_dropped_ity, licm_exitvalue_add_nuw_dropped_ity], args := _ ::ₕ _ ::ₕ HVector.nil } : CFGTarget LLVM _))
              ∅)
            s ⊑
          some (licm_exitvalue_add_nuw_dropped_tgtResult V ::ₕ HVector.nil, s)
        )
        rw [licm_exitvalue_add_nuw_dropped_src_loop_dispatch]
        simpa [indexNext, licm_exitvalue_add_nuw_dropped_srcLoopVal, LLVM.add, LLVM.add?,
          Ctxt.Valuation.cons_last, Ctxt.Valuation.cons_toCons, Ctxt.Valuation.cons_eval] using
          ih s (some (LLVM.SemVal.value (k + 1#64))) indexNext hBack

private theorem licm_exitvalue_add_nuw_dropped_loop_refine (V : Ctxt.Valuation licm_exitvalue_add_nuw_dropped_ctx) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) (j1 j2 : TyDenote.toType licm_exitvalue_add_nuw_dropped_ity),
      licm_exitvalue_add_nuw_dropped_inv j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel licm_exitvalue_add_nuw_dropped_srcBlocks V
              (licm_exitvalue_add_nuw_dropped_srcLoopVal j1 j2) licm_exitvalue_add_nuw_dropped_srcLoopTarget)
            ∅)
          s
        ⊑
        (some (licm_exitvalue_add_nuw_dropped_tgtResult V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [licm_exitvalue_add_nuw_dropped_ity] × LLVMMemory.State)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s j1 j2 _hinv
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact licm_exitvalue_add_nuw_dropped_step V fuel ih

theorem licm_exitvalue_add_nuw_dropped_correct :
    IsRefinedByOnIntWInputsWithMemory licm_exitvalue_add_nuw_dropped_src (licm_exitvalue_add_nuw_dropped_tgt.castPureToEff .impure) := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>

      have hInit :
          licm_exitvalue_add_nuw_dropped_inv (some (LLVM.SemVal.value (0#64)))
            (some (LLVM.SemVal.value (0#64))) V.lift := by
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
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel licm_exitvalue_add_nuw_dropped_srcBlocks V.lift _
              ({ name := "loop", argTys := [licm_exitvalue_add_nuw_dropped_ity, licm_exitvalue_add_nuw_dropped_ity], args := _ ::ₕ _ ::ₕ HVector.nil } : CFGTarget LLVM _))
            ∅)
          s ⊑
        some (licm_exitvalue_add_nuw_dropped_tgtResult V.lift ::ₕ HVector.nil, s)
      )
      rw [licm_exitvalue_add_nuw_dropped_src_loop_dispatch]
      simpa [licm_exitvalue_add_nuw_dropped_tgtResult] using
        (licm_exitvalue_add_nuw_dropped_loop_refine V.lift fuel s (some (LLVM.SemVal.value (0#64)))
          (some (LLVM.SemVal.value (0#64))) hInit)

end TestLoop
end InstCombine
