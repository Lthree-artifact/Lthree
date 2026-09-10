/-
  Row C1W (C1W-widening-v1) multi-hole fuel-induction scaffold, variant `loop`,
  emitted deterministically by shape_cfg.py (widened from the kernel-verified
  Row C1 prototype llvmtestloop_licm_hoist_invariant_mul_shapeD.lean).

  IMPORT PINNING (soundness-critical): the 3-import header below INCLUDES
  SSA.Projects.InstCombine.MemoryRefinement.  The corpus contains a
  kernel-accepted proof AND a kernel-accepted refutation of "the same"
  refinement statement differing only in this import (import-dependent ⊑).
  Under these pinned imports the theorem below is the fuel/memory-aware
  refinement, not the CFG-opaque collapse.

  Holes (exactly 4 sorries):
    H1.1   coupling def for tgt carried arg 1
    H1.2   coupling def for tgt carried arg 2
    H2     inductive step of the fuel induction
    H3     final assembly: entry-block reduction to the core lemma
-/
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace InstCombine
namespace TestLoop

def loop_15_src :=
  [llvm()| {
  llvm.func @loop_15_src(%a : i32) -> i32 {
  ^entry(%a : i32):
    %e_zero = llvm.mlir.constant 0 : i32
    llvm.br ^loop(%e_zero : i32, %e_zero : i32)
  ^loop(%k : i32, %val : i32):
    %o = llvm.or %val, %a : i32
    %l_65536 = llvm.mlir.constant 65536 : i32
    %m1 = llvm.mul %o, %l_65536 overflow<nuw> : i32
    %l_m9 = llvm.mlir.constant -9 : i32
    %sext = llvm.mul %m1, %l_m9 overflow<nsw> : i32
    %l_one = llvm.mlir.constant 1 : i32
    %k1 = llvm.add %k, %l_one : i32
    %l_two = llvm.mlir.constant 2 : i32
    %cond = llvm.icmp "eq" %k1, %l_two : i32
    llvm.cond_br %cond : i1, ^out(%sext : i32), ^loop(%k1 : i32, %l_one : i32)
  ^out(%res : i32):
    llvm.return %res : i32
  }
  }]

def loop_15_tgt :=
  [llvm()| {
  llvm.func @loop_15_tgt(%a : i32) -> i32 {
  ^entry(%a : i32):
    %e_zero = llvm.mlir.constant 0 : i32
    llvm.br ^loop(%e_zero : i32, %e_zero : i32)
  ^loop(%k : i32, %val : i32):
    %o = llvm.or %val, %a : i32
    %l_c = llvm.mlir.constant -589824 : i32
    %sext = llvm.mul %o, %l_c : i32
    %l_one = llvm.mlir.constant 1 : i32
    %k1 = llvm.add %k, %l_one : i32
    %l_two = llvm.mlir.constant 2 : i32
    %cond = llvm.icmp "eq" %k1, %l_two : i32
    llvm.cond_br %cond : i1, ^out(%sext : i32), ^loop(%k1 : i32, %l_one : i32)
  ^out(%res : i32):
    llvm.return %res : i32
  }
  }]

-- [IR-DERIVED: scalar type abbrev from the signature]
private abbrev loop_15_ity : LLVM.Ty := LLVM.Ty.bitvec 32

-- [IR-DERIVED: function context (1 param(s))]
private abbrev loop_15_ctx : Ctxt LLVM.Ty := Ctxt.ofList [loop_15_ity]

-- [IR-DERIVED: fixed blocks-extractor template, src side]
private def loop_15_srcBlocks : CFGBlocks LLVM loop_15_ctx .impure [loop_15_ity] :=
  match loop_15_src with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private def loop_15_tgtBlocks : CFGBlocks LLVM loop_15_ctx .impure [loop_15_ity] :=
  match loop_15_tgt with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

-- [IR-DERIVED: block-name inequality helpers for the hole fillers]
private theorem loop_15_entry_ne_loop : ¬ ("entry" = "loop") := by
  decide

private theorem loop_15_out_ne_loop : ¬ ("out" = "loop") := by
  decide

-- [IR-DERIVED: src loop continuation target (2 carried arg(s))]
private def loop_15_srcLoopTarget : CFGTarget LLVM (Ctxt.ofList [loop_15_ity, loop_15_ity]) where
  name := "loop"
  argTys := [loop_15_ity, loop_15_ity]
  args := (⟨0, by decide⟩ : (Ctxt.ofList [loop_15_ity, loop_15_ity]).Var loop_15_ity) ::ₕ (⟨1, by decide⟩ : (Ctxt.ofList [loop_15_ity, loop_15_ity]).Var loop_15_ity) ::ₕ HVector.nil

private def loop_15_srcLoopVal (j1 j2 : TyDenote.toType loop_15_ity) :
    Ctxt.Valuation (Ctxt.ofList [loop_15_ity, loop_15_ity]) :=
  Ctxt.Valuation.ofHVector (j1 ::ₕ j2 ::ₕ HVector.nil)

/- [IR-DERIVED: emitter-OWNED adequacy lemma (machine-closes with the fixed
   script or the emitter declines): loop re-entry dispatch, src side.] -/
private theorem loop_15_src_loop_dispatch
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation loop_15_ctx) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a1 a2 : Γcur.Var loop_15_ity) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_15_srcBlocks V W
            ({ name := "loop", argTys := [loop_15_ity, loop_15_ity], args := a1 ::ₕ a2 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_15_srcBlocks V
            (loop_15_srcLoopVal (W a1) (W a2)) loop_15_srcLoopTarget)
          ∅)
        s := by
  cases fuel <;>
    simp [loop_15_src, loop_15_srcBlocks, loop_15_srcLoopTarget, loop_15_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

-- [IR-DERIVED: tgt loop continuation target (2 carried arg(s))]
private def loop_15_tgtLoopTarget : CFGTarget LLVM (Ctxt.ofList [loop_15_ity, loop_15_ity]) where
  name := "loop"
  argTys := [loop_15_ity, loop_15_ity]
  args := (⟨0, by decide⟩ : (Ctxt.ofList [loop_15_ity, loop_15_ity]).Var loop_15_ity) ::ₕ (⟨1, by decide⟩ : (Ctxt.ofList [loop_15_ity, loop_15_ity]).Var loop_15_ity) ::ₕ HVector.nil

private def loop_15_tgtLoopVal (i1 i2 : TyDenote.toType loop_15_ity) :
    Ctxt.Valuation (Ctxt.ofList [loop_15_ity, loop_15_ity]) :=
  Ctxt.Valuation.ofHVector (i1 ::ₕ i2 ::ₕ HVector.nil)

private theorem loop_15_tgt_loop_dispatch
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation loop_15_ctx) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (b1 b2 : Γcur.Var loop_15_ity) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_15_tgtBlocks V W
            ({ name := "loop", argTys := [loop_15_ity, loop_15_ity], args := b1 ::ₕ b2 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_15_tgtBlocks V
            (loop_15_tgtLoopVal (W b1) (W b2)) loop_15_tgtLoopTarget)
          ∅)
        s := by
  cases fuel <;>
    simp [loop_15_tgt, loop_15_tgtBlocks, loop_15_tgtLoopTarget, loop_15_tgtLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

/- [IR-DERIVED: emitter-OWNED exit-block refinement lemma (bare-return exit
   blocks on both sides); helper for the succ-case filler.] -/
private theorem loop_15_out_refine
    {Γsrc Γtgt : Ctxt LLVM.Ty} (V : Ctxt.Valuation loop_15_ctx)
    (Wsrc : Ctxt.Valuation Γsrc) (Wtgt : Ctxt.Valuation Γtgt)
    (fuel : Nat) (s : LLVMMemory.State) (a : Γsrc.Var loop_15_ity) (b : Γtgt.Var loop_15_ity)
    (h : Wsrc a = Wtgt b) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_15_srcBlocks V Wsrc
            ({ name := "out", argTys := [loop_15_ity], args := a ::ₕ HVector.nil } :
              CFGTarget LLVM Γsrc))
          ∅)
        s
      ⊑
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_15_tgtBlocks V Wtgt
            ({ name := "out", argTys := [loop_15_ity], args := b ::ₕ HVector.nil } :
              CFGTarget LLVM Γtgt))
          ∅)
        s := by
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>
      simp [loop_15_src, loop_15_tgt,
        loop_15_srcBlocks, loop_15_tgtBlocks, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
        LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, h]
      exact mem_result_le_self _

/- [HOLE H1.1: the coupling — the value of tgt loop-carried argument 1
   as a function of the src loop-carried state (j1 j2) and the function
   inputs (V).  One-liner expected.  The LLM fills this.] -/
private def loop_15_coupling1 (j1 j2 : TyDenote.toType loop_15_ity)
    (V : Ctxt.Valuation loop_15_ctx) : TyDenote.toType loop_15_ity :=
  j1

/- [HOLE H1.2: the coupling — the value of tgt loop-carried argument 2
   as a function of the src loop-carried state (j1 j2) and the function
   inputs (V).  One-liner expected.  The LLM fills this.] -/
private def loop_15_coupling2 (j1 j2 : TyDenote.toType loop_15_ity)
    (V : Ctxt.Valuation loop_15_ctx) : TyDenote.toType loop_15_ity :=
  j2

/- [HOLE H2: the inductive step of the fuel induction, as a STANDALONE
   typed lemma — the induction hypothesis is the explicit `ih` binder, so the
   obligation kernel-checks, audits and retries on its own, exactly like the
   single-block row's holes and the paper figure's `value_hole`.
   Framework-free IntW/BitVec math in the model style: case on
   poison of the carried values/inputs and on the branch
   condition; exit path closes via loop_15_out_refine, backedge path
   re-enters via loop_15_src_loop_dispatch / loop_15_tgt_loop_dispatch
   + ih.
   NOTE — input(s) `%a` are NOT discharged by the emitter: their
   poison never reaches a branch condition, so the source is not
   immediately UB and no one-step discharge exists.  Their poison
   has to be CARRIED by this induction to the exit, where
   `LLVM.SemVal.poison_isRefinedBy` closes it (poison refines
   anything).  Case on them here alongside the carried values.] -/
private theorem loop_15_step (V : Ctxt.Valuation loop_15_ctx) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType loop_15_ity),
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_15_srcBlocks V
              (loop_15_srcLoopVal j1 j2) loop_15_srcLoopTarget)
            ∅)
          s
        ⊑
        StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_15_tgtBlocks V
              (loop_15_tgtLoopVal (loop_15_coupling1 j1 j2 V) (loop_15_coupling2 j1 j2 V)) loop_15_tgtLoopTarget)
            ∅)
          s) :
    ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType loop_15_ity),
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) loop_15_srcBlocks V
              (loop_15_srcLoopVal j1 j2) loop_15_srcLoopTarget)
            ∅)
          s
        ⊑
        StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) loop_15_tgtBlocks V
              (loop_15_tgtLoopVal (loop_15_coupling1 j1 j2 V) (loop_15_coupling2 j1 j2 V)) loop_15_tgtLoopTarget)
            ∅)
          s :=
  by
    have hmul : ∀ x : LLVM.IntWUB 32,
        ((x.bind fun a =>
              some (LLVM.mul a (LLVM.const? 32 65536)
                ({ «nuw» := true } : LLVM.NoWrapFlags))).bind fun a =>
            some (LLVM.mul a (LLVM.const? 32 (-9))
              ({ «nsw» := true } : LLVM.NoWrapFlags)))
          ⊑
          (x.bind fun a => some (LLVM.mul a (LLVM.const? 32 (-589824)))) := by
      intro x
      cases x with
      | none =>
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      | some xv =>
          cases xv with
          | poison =>
              simp [LLVM.mul, LLVM.const?]
          | value bv =>
              simp [LLVM.mul, LLVM.mul?, LLVM.const?]
              split_ifs with h₁
              · exact ImmediateUBOr.IsRefinedBy.bothValues (LLVM.SemVal.poison_isRefinedBy _)
              · simp [LLVM.SemVal.bind_value]
                split_ifs with h₂
                · exact ImmediateUBOr.IsRefinedBy.bothValues (LLVM.SemVal.poison_isRefinedBy _)
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by
                    simp [LLVM.IntW.isRefinedBy_iff]
                    bv_decide)
    intro s j1 j2
    let a : loop_15_ctx.Var loop_15_ity := ⟨0, by decide⟩
    cases j1 with
    | none =>
        simp [a, loop_15_src, loop_15_tgt, loop_15_srcBlocks, loop_15_tgtBlocks,
          loop_15_srcLoopTarget, loop_15_tgtLoopTarget, loop_15_srcLoopVal, loop_15_tgtLoopVal,
          loop_15_coupling1, loop_15_coupling2, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
          LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
          InstCombine.LLVMMemory.instDialectDenoteLLVMM, LLVMMemory.Op.denoteVec,
          InstCombine.Op.denote]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    | some j1v =>
        cases j1v with
        | poison =>
            simp [a, loop_15_src, loop_15_tgt, loop_15_srcBlocks, loop_15_tgtBlocks,
              loop_15_srcLoopTarget, loop_15_tgtLoopTarget, loop_15_srcLoopVal,
              loop_15_tgtLoopVal, loop_15_coupling1, loop_15_coupling2,
              LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
              LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
              LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
              InstCombine.LLVMMemory.instDialectDenoteLLVMM, LLVMMemory.Op.denoteVec,
              InstCombine.Op.denote, LLVM.add, LLVM.icmp, LLVM.const?]
            exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        | value k =>
            by_cases hc : k + 1#32 = 2#32
            · simp only [a, hc, loop_15_src, loop_15_tgt, loop_15_srcBlocks,
                loop_15_tgtBlocks,
                loop_15_srcLoopTarget, loop_15_tgtLoopTarget, loop_15_srcLoopVal,
                loop_15_tgtLoopVal, loop_15_coupling1, loop_15_coupling2,
                LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                LLVMMemory.CFGBlocks.findMemoryBlock?,
                LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
                InstCombine.LLVMMemory.instDialectDenoteLLVMM, LLVMMemory.Op.denoteVec,
                InstCombine.Op.denote, LLVM.add, LLVM.add?, LLVM.icmp, LLVM.icmp?, LLVM.icmp',
                LLVM.const?, Bool.beq_eq_decide_eq, decide_eq_true_eq, loop_15_entry_ne_loop,
                loop_15_out_ne_loop, ite_true, ite_false]
            · simp only [a, hc, loop_15_src, loop_15_tgt, loop_15_srcBlocks,
                loop_15_tgtBlocks,
                loop_15_srcLoopTarget, loop_15_tgtLoopTarget, loop_15_srcLoopVal,
                loop_15_tgtLoopVal, loop_15_coupling1, loop_15_coupling2,
                LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                LLVMMemory.CFGBlocks.findMemoryBlock?,
                LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
                InstCombine.LLVMMemory.instDialectDenoteLLVMM, LLVMMemory.Op.denoteVec,
                InstCombine.Op.denote, LLVM.add, LLVM.add?, LLVM.icmp, LLVM.icmp?, LLVM.icmp',
                LLVM.const?, Bool.beq_eq_decide_eq, decide_eq_true_eq, loop_15_entry_ne_loop,
                loop_15_out_ne_loop, ite_true, ite_false, loop_15_src_loop_dispatch,
                loop_15_tgt_loop_dispatch]

/- [IR-DERIVED: core fuel-induction lemma — BOTH cases are emitted: the zero
   case by the fixed out-of-fuel closer, the succ case by the step lemma
   above.  No hole is left inside this proof.] -/
private theorem loop_15_loop_refine (V : Ctxt.Valuation loop_15_ctx) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) (j1 j2 : TyDenote.toType loop_15_ity),
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_15_srcBlocks V
              (loop_15_srcLoopVal j1 j2) loop_15_srcLoopTarget)
            ∅)
          s
        ⊑
        StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_15_tgtBlocks V
              (loop_15_tgtLoopVal (loop_15_coupling1 j1 j2 V) (loop_15_coupling2 j1 j2 V)) loop_15_tgtLoopTarget)
            ∅)
          s := by
  intro fuel
  induction fuel with
  | zero =>
      intro s j1 j2
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact loop_15_step V fuel ih

theorem loop_15_correct : loop_15_src ⊑ loop_15_tgt := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>
      /- [HOLE H3: final assembly — unfold both entry blocks (simp with the two block sets
         + LLVMMemory.Com.denoteWithMemoryFuel/denoteWithMemoryFuelIn +
         CFGTarget/CFGBody/CFGTerm denote lemmas), dispatch both loop
         entries via loop_15_src_loop_dispatch / loop_15_tgt_loop_dispatch, then
         apply loop_15_loop_refine; the coupling holes fix the tgt init values.] -/
      sorry

end TestLoop
end InstCombine
