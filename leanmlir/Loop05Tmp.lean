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

  Holes (exactly 5 sorries):
    H1.1   coupling def for tgt carried arg 1
    H1.2   coupling def for tgt carried arg 2
    H1.3   coupling def for tgt carried arg 3
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

def loop_05_src :=
  [llvm()| {
  llvm.func @loop_05_src(%c1 : i64, %c2 : i64) -> i64 {
  ^entry(%c1 : i64, %c2 : i64):
    %e_zero = llvm.mlir.constant 0 : i64
    llvm.br ^loop(%e_zero : i64, %e_zero : i64)
  ^loop(%k : i64, %index : i64):
    %step_add = llvm.or %index, %c1 : i64
    %index_next = llvm.or disjoint %c2, %step_add : i64
    %l_one = llvm.mlir.constant 1 : i64
    %k1 = llvm.add %k, %l_one : i64
    %l_three = llvm.mlir.constant 3 : i64
    %cond = llvm.icmp "eq" %k1, %l_three : i64
    llvm.cond_br %cond : i1, ^out(%index_next : i64), ^loop(%k1 : i64, %index_next : i64)
  ^out(%res : i64):
    llvm.return %res : i64
  }
  }]

def loop_05_tgt :=
  [llvm()| {
  llvm.func @loop_05_tgt(%c1 : i64, %c2 : i64) -> i64 {
  ^entry(%c1 : i64, %c2 : i64):
    %e_zero = llvm.mlir.constant 0 : i64
    %invariant_op = llvm.or %c1, %c2 : i64
    llvm.br ^loop(%e_zero : i64, %e_zero : i64, %invariant_op : i64)
  ^loop(%k : i64, %index : i64, %inv : i64):
    %index_next = llvm.or %index, %inv : i64
    %l_one = llvm.mlir.constant 1 : i64
    %k1 = llvm.add %k, %l_one : i64
    %l_three = llvm.mlir.constant 3 : i64
    %cond = llvm.icmp "eq" %k1, %l_three : i64
    llvm.cond_br %cond : i1, ^out(%index_next : i64), ^loop(%k1 : i64, %index_next : i64, %inv : i64)
  ^out(%res : i64):
    llvm.return %res : i64
  }
  }]

-- [IR-DERIVED: scalar type abbrev from the signature]
private abbrev loop_05_ity : LLVM.Ty := LLVM.Ty.bitvec 64

-- [IR-DERIVED: function context (2 param(s))]
private abbrev loop_05_ctx : Ctxt LLVM.Ty := Ctxt.ofList [loop_05_ity, loop_05_ity]

-- [IR-DERIVED: fixed blocks-extractor template, src side]
private def loop_05_srcBlocks : CFGBlocks LLVM loop_05_ctx .impure [loop_05_ity] :=
  match loop_05_src with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private def loop_05_tgtBlocks : CFGBlocks LLVM loop_05_ctx .impure [loop_05_ity] :=
  match loop_05_tgt with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

-- [IR-DERIVED: block-name inequality helpers for the hole fillers]
private theorem loop_05_entry_ne_loop : ¬ ("entry" = "loop") := by
  decide

private theorem loop_05_out_ne_loop : ¬ ("out" = "loop") := by
  decide

-- [IR-DERIVED: src loop continuation target (2 carried arg(s))]
private def loop_05_srcLoopTarget : CFGTarget LLVM (Ctxt.ofList [loop_05_ity, loop_05_ity]) where
  name := "loop"
  argTys := [loop_05_ity, loop_05_ity]
  args := (⟨0, by decide⟩ : (Ctxt.ofList [loop_05_ity, loop_05_ity]).Var loop_05_ity) ::ₕ (⟨1, by decide⟩ : (Ctxt.ofList [loop_05_ity, loop_05_ity]).Var loop_05_ity) ::ₕ HVector.nil

private def loop_05_srcLoopVal (j1 j2 : TyDenote.toType loop_05_ity) :
    Ctxt.Valuation (Ctxt.ofList [loop_05_ity, loop_05_ity]) :=
  Ctxt.Valuation.ofHVector (j1 ::ₕ j2 ::ₕ HVector.nil)

/- [IR-DERIVED: emitter-OWNED adequacy lemma (machine-closes with the fixed
   script or the emitter declines): loop re-entry dispatch, src side.] -/
private theorem loop_05_src_loop_dispatch
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation loop_05_ctx) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a1 a2 : Γcur.Var loop_05_ity) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_05_srcBlocks V W
            ({ name := "loop", argTys := [loop_05_ity, loop_05_ity], args := a1 ::ₕ a2 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_05_srcBlocks V
            (loop_05_srcLoopVal (W a1) (W a2)) loop_05_srcLoopTarget)
          ∅)
        s := by
  cases fuel <;>
    simp [loop_05_src, loop_05_srcBlocks, loop_05_srcLoopTarget, loop_05_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

-- [IR-DERIVED: tgt loop continuation target (3 carried arg(s))]
private def loop_05_tgtLoopTarget : CFGTarget LLVM (Ctxt.ofList [loop_05_ity, loop_05_ity, loop_05_ity]) where
  name := "loop"
  argTys := [loop_05_ity, loop_05_ity, loop_05_ity]
  args := (⟨0, by decide⟩ : (Ctxt.ofList [loop_05_ity, loop_05_ity, loop_05_ity]).Var loop_05_ity) ::ₕ (⟨1, by decide⟩ : (Ctxt.ofList [loop_05_ity, loop_05_ity, loop_05_ity]).Var loop_05_ity) ::ₕ (⟨2, by decide⟩ : (Ctxt.ofList [loop_05_ity, loop_05_ity, loop_05_ity]).Var loop_05_ity) ::ₕ HVector.nil

private def loop_05_tgtLoopVal (i1 i2 i3 : TyDenote.toType loop_05_ity) :
    Ctxt.Valuation (Ctxt.ofList [loop_05_ity, loop_05_ity, loop_05_ity]) :=
  Ctxt.Valuation.ofHVector (i1 ::ₕ i2 ::ₕ i3 ::ₕ HVector.nil)

private theorem loop_05_tgt_loop_dispatch
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation loop_05_ctx) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (b1 b2 b3 : Γcur.Var loop_05_ity) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_05_tgtBlocks V W
            ({ name := "loop", argTys := [loop_05_ity, loop_05_ity, loop_05_ity], args := b1 ::ₕ b2 ::ₕ b3 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_05_tgtBlocks V
            (loop_05_tgtLoopVal (W b1) (W b2) (W b3)) loop_05_tgtLoopTarget)
          ∅)
        s := by
  cases fuel <;>
    simp [loop_05_tgt, loop_05_tgtBlocks, loop_05_tgtLoopTarget, loop_05_tgtLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

/- [IR-DERIVED: emitter-OWNED exit-block refinement lemma (bare-return exit
   blocks on both sides); helper for the succ-case filler.] -/
private theorem loop_05_out_refine
    {Γsrc Γtgt : Ctxt LLVM.Ty} (V : Ctxt.Valuation loop_05_ctx)
    (Wsrc : Ctxt.Valuation Γsrc) (Wtgt : Ctxt.Valuation Γtgt)
    (fuel : Nat) (s : LLVMMemory.State) (a : Γsrc.Var loop_05_ity) (b : Γtgt.Var loop_05_ity)
    (h : Wsrc a = Wtgt b) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_05_srcBlocks V Wsrc
            ({ name := "out", argTys := [loop_05_ity], args := a ::ₕ HVector.nil } :
              CFGTarget LLVM Γsrc))
          ∅)
        s
      ⊑
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_05_tgtBlocks V Wtgt
            ({ name := "out", argTys := [loop_05_ity], args := b ::ₕ HVector.nil } :
              CFGTarget LLVM Γtgt))
          ∅)
        s := by
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>
      simp [loop_05_src, loop_05_tgt,
        loop_05_srcBlocks, loop_05_tgtBlocks, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
        LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, h]
      exact mem_result_le_self _

/- [HOLE H1.1: the coupling — the value of tgt loop-carried argument 1
   as a function of the src loop-carried state (j1 j2) and the function
   inputs (V).  One-liner expected.  The LLM fills this.] -/
private def loop_05_coupling1 (j1 j2 : TyDenote.toType loop_05_ity)
    (V : Ctxt.Valuation loop_05_ctx) : TyDenote.toType loop_05_ity :=
  j1

/- [HOLE H1.2: the coupling — the value of tgt loop-carried argument 2
   as a function of the src loop-carried state (j1 j2) and the function
   inputs (V).  One-liner expected.  The LLM fills this.] -/
private def loop_05_coupling2 (j1 j2 : TyDenote.toType loop_05_ity)
    (V : Ctxt.Valuation loop_05_ctx) : TyDenote.toType loop_05_ity :=
  j2

/- [HOLE H1.3: the coupling — the value of tgt loop-carried argument 3
   as a function of the src loop-carried state (j1 j2) and the function
   inputs (V).  One-liner expected.  The LLM fills this.] -/
private def loop_05_coupling3 (j1 j2 : TyDenote.toType loop_05_ity)
    (V : Ctxt.Valuation loop_05_ctx) : TyDenote.toType loop_05_ity :=
  lift2 (fun x y => LLVM.or x y) (V (⟨0, by decide⟩ : loop_05_ctx.Var loop_05_ity))
    (V (⟨1, by decide⟩ : loop_05_ctx.Var loop_05_ity))

/- [HOLE H2: the inductive step of the fuel induction, as a STANDALONE
   typed lemma — the induction hypothesis is the explicit `ih` binder, so the
   obligation kernel-checks, audits and retries on its own, exactly like the
   single-block row's holes and the paper figure's `value_hole`.
   Framework-free IntW/BitVec math in the model style: case on
   poison of the carried values/inputs and on the branch
   condition; exit path closes via loop_05_out_refine, backedge path
   re-enters via loop_05_src_loop_dispatch / loop_05_tgt_loop_dispatch
   + ih.
   NOTE — input(s) `%c1`, `%c2` are NOT discharged by the emitter: their
   poison never reaches a branch condition, so the source is not
   immediately UB and no one-step discharge exists.  Their poison
   has to be CARRIED by this induction to the exit, where
   `LLVM.SemVal.poison_isRefinedBy` closes it (poison refines
   anything).  Case on them here alongside the carried values.] -/
private theorem loop_05_step (V : Ctxt.Valuation loop_05_ctx) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType loop_05_ity),
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_05_srcBlocks V
              (loop_05_srcLoopVal j1 j2) loop_05_srcLoopTarget)
            ∅)
          s
        ⊑
        StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_05_tgtBlocks V
              (loop_05_tgtLoopVal (loop_05_coupling1 j1 j2 V) (loop_05_coupling2 j1 j2 V) (loop_05_coupling3 j1 j2 V)) loop_05_tgtLoopTarget)
            ∅)
          s) :
    ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType loop_05_ity),
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) loop_05_srcBlocks V
              (loop_05_srcLoopVal j1 j2) loop_05_srcLoopTarget)
            ∅)
          s
        ⊑
        StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) loop_05_tgtBlocks V
              (loop_05_tgtLoopVal (loop_05_coupling1 j1 j2 V) (loop_05_coupling2 j1 j2 V) (loop_05_coupling3 j1 j2 V)) loop_05_tgtLoopTarget)
            ∅)
          s :=
  by
    intro s j1 j2
    rcases j1 with _ | (_ | k)
    · simp (config := { failIfUnchanged := false }) [loop_05_src, loop_05_tgt,
        loop_05_srcBlocks, loop_05_tgtBlocks, loop_05_srcLoopTarget, loop_05_tgtLoopTarget,
        loop_05_srcLoopVal, loop_05_tgtLoopVal,
        loop_05_coupling1, loop_05_coupling2, loop_05_coupling3,
        LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
        LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore,
        LLVMMemory.Expr.denoteWithMemory, LLVMMemory.Op.denoteVec, Op.denote,
        DialectDenote.denote, lift2, LLVM.or, LLVM.or?, LLVM.add, LLVM.add?, LLVM.icmp,
        LLVM.icmp?, LLVM.icmp', LLVM.const?, Ctxt.Var.zero_eq_last]
    · simp (config := { failIfUnchanged := false }) [loop_05_src, loop_05_tgt,
        loop_05_srcBlocks, loop_05_tgtBlocks, loop_05_srcLoopTarget, loop_05_tgtLoopTarget,
        loop_05_srcLoopVal, loop_05_tgtLoopVal,
        loop_05_coupling1, loop_05_coupling2, loop_05_coupling3,
        LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
        LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore,
        LLVMMemory.Expr.denoteWithMemory, LLVMMemory.Op.denoteVec, Op.denote,
        DialectDenote.denote, lift2, LLVM.or, LLVM.or?, LLVM.add, LLVM.add?, LLVM.icmp,
        LLVM.icmp?, LLVM.icmp', LLVM.const?, Ctxt.Var.zero_eq_last]
    · rcases j2 with _ | (_ | index)
      · simp (config := { failIfUnchanged := false }) [loop_05_src, loop_05_tgt,
          loop_05_srcBlocks, loop_05_tgtBlocks, loop_05_srcLoopTarget, loop_05_tgtLoopTarget,
          loop_05_srcLoopVal, loop_05_tgtLoopVal,
          loop_05_coupling1, loop_05_coupling2, loop_05_coupling3,
          LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
          LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore,
          LLVMMemory.Expr.denoteWithMemory, LLVMMemory.Op.denoteVec, Op.denote,
          DialectDenote.denote, lift2, LLVM.or, LLVM.or?, LLVM.add, LLVM.add?, LLVM.icmp,
          LLVM.icmp?, LLVM.icmp', LLVM.const?, Ctxt.Var.zero_eq_last]
      · simp (config := { failIfUnchanged := false }) [loop_05_src, loop_05_tgt,
          loop_05_srcBlocks, loop_05_tgtBlocks, loop_05_srcLoopTarget, loop_05_tgtLoopTarget,
          loop_05_srcLoopVal, loop_05_tgtLoopVal,
          loop_05_coupling1, loop_05_coupling2, loop_05_coupling3,
          LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
          LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore,
          LLVMMemory.Expr.denoteWithMemory, LLVMMemory.Op.denoteVec, Op.denote,
          DialectDenote.denote, lift2, LLVM.or, LLVM.or?, LLVM.add, LLVM.add?, LLVM.icmp,
          LLVM.icmp?, LLVM.icmp', LLVM.const?, Ctxt.Var.zero_eq_last]
      · generalize hV0 : V (⟨0, by decide⟩ : loop_05_ctx.Var loop_05_ity) = v0
        generalize hV1 : V (⟨1, by decide⟩ : loop_05_ctx.Var loop_05_ity) = v1
        rcases v0 with _ | (_ | c1) <;>
        rcases v1 with _ | (_ | c2) <;>
          simp (config := { failIfUnchanged := false }) [loop_05_src, loop_05_tgt,
            loop_05_srcBlocks, loop_05_tgtBlocks, loop_05_srcLoopTarget,
            loop_05_tgtLoopTarget, loop_05_srcLoopVal, loop_05_tgtLoopVal,
            loop_05_coupling1, loop_05_coupling2, loop_05_coupling3,
            LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
            LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
            LLVMMemory.CFGTerm.denoteWithMemoryFuelCore,
            LLVMMemory.Expr.denoteWithMemory, LLVMMemory.Op.denoteVec, Op.denote,
            DialectDenote.denote, lift2, LLVM.or, LLVM.or?, LLVM.add, LLVM.add?,
            LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.const?, hV0, hV1,
            Ctxt.Var.zero_eq_last, BitVec.or_assoc, BitVec.or_comm]

/- [IR-DERIVED: core fuel-induction lemma — BOTH cases are emitted: the zero
   case by the fixed out-of-fuel closer, the succ case by the step lemma
   above.  No hole is left inside this proof.] -/
private theorem loop_05_loop_refine (V : Ctxt.Valuation loop_05_ctx) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) (j1 j2 : TyDenote.toType loop_05_ity),
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_05_srcBlocks V
              (loop_05_srcLoopVal j1 j2) loop_05_srcLoopTarget)
            ∅)
          s
        ⊑
        StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel loop_05_tgtBlocks V
              (loop_05_tgtLoopVal (loop_05_coupling1 j1 j2 V) (loop_05_coupling2 j1 j2 V) (loop_05_coupling3 j1 j2 V)) loop_05_tgtLoopTarget)
            ∅)
          s := by
  intro fuel
  induction fuel with
  | zero =>
      intro s j1 j2
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact loop_05_step V fuel ih

theorem loop_05_correct : loop_05_src ⊑ loop_05_tgt := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>
      /- [HOLE H3: final assembly — unfold both entry blocks (simp with the two block sets
         + LLVMMemory.Com.denoteWithMemoryFuel/denoteWithMemoryFuelIn +
         CFGTarget/CFGBody/CFGTerm denote lemmas), dispatch both loop
         entries via loop_05_src_loop_dispatch / loop_05_tgt_loop_dispatch, then
         apply loop_05_loop_refine; the coupling holes fix the tgt init values.] -/
      sorry

end TestLoop
end InstCombine
