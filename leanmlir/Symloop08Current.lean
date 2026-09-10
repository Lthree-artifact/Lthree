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
    H1     relational loop invariant (src state × tgt state × inputs)
    HU1    target-specific UB (nuw)
    HL1    target-specific UB in the tgt LOOP BODY (nuw)
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

def symloop_08_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @symloop_08_src(%c1 : _, %c2 : _) -> _ {
  ^entry(%c1 : _, %c2 : _):
    %e_zero = llvm.mlir.constant 0 : _
    llvm.br ^loop(%e_zero : _, %e_zero : _)
  ^loop(%k : _, %index : _):
    %step_add = llvm.add %index, %c1 overflow<nuw> : _
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

def symloop_08_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @symloop_08_tgt(%c1 : _, %c2 : _) -> _ {
  ^entry(%c1 : _, %c2 : _):
    %e_zero = llvm.mlir.constant 0 : _
    %invariant_op = llvm.add %c1, %c2 overflow<nuw> : _
    llvm.br ^loop(%e_zero : _, %e_zero : _, %invariant_op : _)
  ^loop(%k : _, %index : _, %inv : _):
    %index_next = llvm.add %index, %inv overflow<nuw> : _
    %l_one = llvm.mlir.constant 1 : _
    %k1 = llvm.add %k, %l_one : _
    %l_three = llvm.mlir.constant 3 : _
    %cond = llvm.icmp "eq" %k1, %l_three : _
    llvm.cond_br %cond : i1, ^out(%index_next : _), ^loop(%k1 : _, %index_next : _, %inv : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

-- [IR-DERIVED: scalar type abbrev from the signature]
private abbrev symloop_08_ity (w : Nat) : LLVM.Ty := LLVM.Ty.bitvec w

-- [IR-DERIVED: function context (2 param(s))]
private abbrev symloop_08_ctx (w : Nat) : Ctxt LLVM.Ty := Ctxt.ofList [(symloop_08_ity w), (symloop_08_ity w)]

-- [IR-DERIVED: fixed blocks-extractor template, src side]
private def symloop_08_srcBlocks (w : Nat) : CFGBlocks LLVM (symloop_08_ctx w) .impure [(symloop_08_ity w)] :=
  match (symloop_08_src w) with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private def symloop_08_tgtBlocks (w : Nat) : CFGBlocks LLVM (symloop_08_ctx w) .impure [(symloop_08_ity w)] :=
  match (symloop_08_tgt w) with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

-- [IR-DERIVED: block-name inequality helpers for the hole fillers]
private theorem symloop_08_entry_ne_loop (w : Nat) : ¬ ("entry" = "loop") := by
  decide

private theorem symloop_08_out_ne_loop (w : Nat) : ¬ ("out" = "loop") := by
  decide

-- [IR-DERIVED: src loop continuation target (2 carried arg(s))]
private def symloop_08_srcLoopTarget (w : Nat) : CFGTarget LLVM (Ctxt.ofList [(symloop_08_ity w), (symloop_08_ity w)]) where
  name := "loop"
  argTys := [(symloop_08_ity w), (symloop_08_ity w)]
  args := (⟨0, by rfl⟩ : (Ctxt.ofList [(symloop_08_ity w), (symloop_08_ity w)]).Var (symloop_08_ity w)) ::ₕ (⟨1, by rfl⟩ : (Ctxt.ofList [(symloop_08_ity w), (symloop_08_ity w)]).Var (symloop_08_ity w)) ::ₕ HVector.nil

private def symloop_08_srcLoopVal (w : Nat) (j1 j2 : TyDenote.toType (symloop_08_ity w)) :
    Ctxt.Valuation (Ctxt.ofList [(symloop_08_ity w), (symloop_08_ity w)]) :=
  Ctxt.Valuation.ofHVector (j1 ::ₕ j2 ::ₕ HVector.nil)

/- [IR-DERIVED: emitter-OWNED adequacy lemma (machine-closes with the fixed
   script or the emitter declines): loop re-entry dispatch, src side.] -/
private theorem symloop_08_src_loop_dispatch (w : Nat)
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation (symloop_08_ctx w)) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a1 a2 : Γcur.Var (symloop_08_ity w)) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (symloop_08_srcBlocks w) V W
            ({ name := "loop", argTys := [(symloop_08_ity w), (symloop_08_ity w)], args := a1 ::ₕ a2 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (symloop_08_srcBlocks w) V
            ((symloop_08_srcLoopVal w) (W a1) (W a2)) (symloop_08_srcLoopTarget w))
          ∅)
        s := by
  cases fuel <;>
    simp [symloop_08_src, symloop_08_srcBlocks, symloop_08_srcLoopTarget, symloop_08_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

-- [IR-DERIVED: tgt loop continuation target (3 carried arg(s))]
private def symloop_08_tgtLoopTarget (w : Nat) : CFGTarget LLVM (Ctxt.ofList [(symloop_08_ity w), (symloop_08_ity w), (symloop_08_ity w)]) where
  name := "loop"
  argTys := [(symloop_08_ity w), (symloop_08_ity w), (symloop_08_ity w)]
  args := (⟨0, by rfl⟩ : (Ctxt.ofList [(symloop_08_ity w), (symloop_08_ity w), (symloop_08_ity w)]).Var (symloop_08_ity w)) ::ₕ (⟨1, by rfl⟩ : (Ctxt.ofList [(symloop_08_ity w), (symloop_08_ity w), (symloop_08_ity w)]).Var (symloop_08_ity w)) ::ₕ (⟨2, by rfl⟩ : (Ctxt.ofList [(symloop_08_ity w), (symloop_08_ity w), (symloop_08_ity w)]).Var (symloop_08_ity w)) ::ₕ HVector.nil

private def symloop_08_tgtLoopVal (w : Nat) (i1 i2 i3 : TyDenote.toType (symloop_08_ity w)) :
    Ctxt.Valuation (Ctxt.ofList [(symloop_08_ity w), (symloop_08_ity w), (symloop_08_ity w)]) :=
  Ctxt.Valuation.ofHVector (i1 ::ₕ i2 ::ₕ i3 ::ₕ HVector.nil)

private theorem symloop_08_tgt_loop_dispatch (w : Nat)
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation (symloop_08_ctx w)) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (b1 b2 b3 : Γcur.Var (symloop_08_ity w)) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (symloop_08_tgtBlocks w) V W
            ({ name := "loop", argTys := [(symloop_08_ity w), (symloop_08_ity w), (symloop_08_ity w)], args := b1 ::ₕ b2 ::ₕ b3 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (symloop_08_tgtBlocks w) V
            ((symloop_08_tgtLoopVal w) (W b1) (W b2) (W b3)) (symloop_08_tgtLoopTarget w))
          ∅)
        s := by
  cases fuel <;>
    simp [symloop_08_tgt, symloop_08_tgtBlocks, symloop_08_tgtLoopTarget, symloop_08_tgtLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

/- [IR-DERIVED: emitter-OWNED exit-block refinement lemma (bare-return exit
   blocks on both sides); helper for the succ-case filler.] -/
private theorem symloop_08_out_refine (w : Nat)
    {Γsrc Γtgt : Ctxt LLVM.Ty} (V : Ctxt.Valuation (symloop_08_ctx w))
    (Wsrc : Ctxt.Valuation Γsrc) (Wtgt : Ctxt.Valuation Γtgt)
    (fuel : Nat) (s : LLVMMemory.State) (a : Γsrc.Var (symloop_08_ity w)) (b : Γtgt.Var (symloop_08_ity w))
    (h : Wsrc a = Wtgt b) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (symloop_08_srcBlocks w) V Wsrc
            ({ name := "out", argTys := [(symloop_08_ity w)], args := a ::ₕ HVector.nil } :
              CFGTarget LLVM Γsrc))
          ∅)
        s
      ⊑
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (symloop_08_tgtBlocks w) V Wtgt
            ({ name := "out", argTys := [(symloop_08_ity w)], args := b ::ₕ HVector.nil } :
              CFGTarget LLVM Γtgt))
          ∅)
        s := by
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>
      simp [symloop_08_src, symloop_08_tgt,
        symloop_08_srcBlocks, symloop_08_tgtBlocks, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
        LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, h]
      exact mem_result_le_self _

/- [HOLE H1: the RELATIONAL loop invariant — a predicate relating the src
   loop-carried state (j1 j2) to the tgt loop-carried state (b1 b2 b3) and the
   function inputs (V).  It must be (a) established by the two entry blocks,
   (b) preserved across the backedge, and (c) strong enough to prove the step
   below and every HL obligation.  The LLM fills this.] -/
private def symloop_08_inv (w : Nat) (j1 j2 : TyDenote.toType (symloop_08_ity w))
    (b1 b2 b3 : TyDenote.toType (symloop_08_ity w))
    (V : Ctxt.Valuation (symloop_08_ctx w)) : Prop :=
  j1 = b1 ∧
  j2 = b2 ∧
  b3 =
    (do
      let a1 ← V ((⟨1, by rfl⟩ : (symloop_08_ctx w).Var (symloop_08_ity w)))
      let a2 ← V (Ctxt.Var.last (Ctxt.ofList [(symloop_08_ity w)]) (symloop_08_ity w))
      pure (LLVM.add a1 a2 (LLVM.NoWrapFlags.mk false true))) ∧
  (∀ (x2 x3 : BitVec w),
    b2 = pure (LLVM.SemVal.value x2) →
    b3 = pure (LLVM.SemVal.value x3) →
    ¬ BitVec.uaddOverflow x2 x3)

/- [HOLE HU1: TARGET-SPECIFIC UB — the paper figure's `target_ub_hole`.
   llvm.add overflow<nuw> poisons on unsigned overflow.
   Target op: `%invariant_op = llvm.add %c1, %c2 overflow<nuw> : _`
   If it fires the TARGET is poison / immediately UB where the source was
   neither, so `src ⊑ tgt` fails.  Proving this is the obligation the
   transformation silently assumes.  The LLM proves it.
   PREMISES `hs1`..`hs2` are the SOURCE's OWN conditions on its FIRST
   iteration -- the source loop body evaluated at the entry block's initial
   carried values.  A target entry op that was HOISTED out of the source loop
   (the LICM shape) is not UB-free outright: it is UB-free BECAUSE the source
   already required the same thing.  Stated with no premise the obligation
   quantifies over all inputs and is simply FALSE, which is why it carries
   them.  Where a premise FAILS the source itself is poison on its first
   iteration and a poison source refines anything, so discharging `hs*` is the
   final-assembly hole's job, not this one's.] -/
private theorem symloop_08_tgt_ub1 (w : Nat) (a1 a2 : BitVec w) (hs1 : ¬ BitVec.uaddOverflow (0#w) a1) (hs2 : ¬ BitVec.uaddOverflow ((0#w) + a1) a2) :
    ¬ BitVec.uaddOverflow a1 a2 :=
  by
    simpa using hs2

/- [HOLE HL1: TARGET-SPECIFIC UB inside the tgt LOOP BODY — a
   PER-ITERATION obligation.  llvm.add overflow<nuw> poisons on unsigned overflow.
   Target op: `%index_next = llvm.add %index, %inv overflow<nuw> : _`
   Unlike the HU series (which is about the entry block and holds outright),
   this one only has to hold on the states the loop actually REACHES, so it is
   stated UNDER THE INVARIANT.  That premise is exactly what a relational
   invariant provides and a functional coupling cannot: quantified over all
   source states the same claim would simply be false.  The LLM proves it.] -/
private theorem symloop_08_tgt_loop_ub1 (w : Nat)
    (V : Ctxt.Valuation (symloop_08_ctx w)) (j1 j2 b1 b2 b3 : TyDenote.toType (symloop_08_ity w))
    (hinv : (symloop_08_inv w) j1 j2 b1 b2 b3 V)
    (x1 x2 x3 : BitVec w) (hx1 : b1 = pure (LLVM.SemVal.value x1)) (hx2 : b2 = pure (LLVM.SemVal.value x2)) (hx3 : b3 = pure (LLVM.SemVal.value x3))
    (a1 a2 : BitVec w) (ha1 : V ((⟨1, by rfl⟩ : (symloop_08_ctx w).Var (symloop_08_ity w))) = pure (LLVM.SemVal.value a1)) (ha2 : V (Ctxt.Var.last (Ctxt.ofList [(symloop_08_ity w)]) (symloop_08_ity w)) = pure (LLVM.SemVal.value a2)) :
    ¬ BitVec.uaddOverflow x2 x3 :=
  by
    exact hinv.2.2.2 x2 x3 hx2 hx3

/- [HOLE H2: the inductive step of the fuel induction, as a STANDALONE
   typed lemma — the induction hypothesis is the explicit `ih` binder, so the
   obligation kernel-checks, audits and retries on its own, exactly like the
   single-block row's holes and the paper figure's `value_hole`.
   Framework-free IntW/BitVec math in the model style: case on
   poison of the carried values/inputs and on the branch
   condition; exit path closes via (symloop_08_out_refine w), backedge path
   re-enters via (symloop_08_src_loop_dispatch w) / (symloop_08_tgt_loop_dispatch w)
   + ih, RE-ESTABLISHING the invariant at the next state.
   The tgt loop body's UB obligations are the HL lemma(s) above —
   apply them rather than re-deriving them.
   NOTE — input(s) `%c1`, `%c2` are NOT discharged by the emitter: their
   poison never reaches a branch condition, so the source is not
   immediately UB and no one-step discharge exists.  Their poison
   has to be CARRIED by this induction to the exit, where
   `LLVM.SemVal.poison_isRefinedBy` closes it (poison refines
   anything).  Case on them here alongside the carried values.] -/
private theorem symloop_08_step (w : Nat) (V : Ctxt.Valuation (symloop_08_ctx w)) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) (j1 j2 b1 b2 b3 : TyDenote.toType (symloop_08_ity w)),
      (symloop_08_inv w) j1 j2 b1 b2 b3 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (symloop_08_srcBlocks w) V
              ((symloop_08_srcLoopVal w) j1 j2) (symloop_08_srcLoopTarget w))
            ∅)
          s
        ⊑
        StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (symloop_08_tgtBlocks w) V
              ((symloop_08_tgtLoopVal w) b1 b2 b3) (symloop_08_tgtLoopTarget w))
            ∅)
          s) :
    ∀ (s : LLVMMemory.State) (j1 j2 b1 b2 b3 : TyDenote.toType (symloop_08_ity w)),
      (symloop_08_inv w) j1 j2 b1 b2 b3 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) (symloop_08_srcBlocks w) V
              ((symloop_08_srcLoopVal w) j1 j2) (symloop_08_srcLoopTarget w))
            ∅)
          s
        ⊑
        StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) (symloop_08_tgtBlocks w) V
              ((symloop_08_tgtLoopVal w) b1 b2 b3) (symloop_08_tgtLoopTarget w))
            ∅)
          s :=
  by
    have hadd_assoc_nuw :
        ∀ (a b c : LLVM.IntW w),
          LLVM.add (LLVM.add a b (LLVM.NoWrapFlags.mk false true)) c
              (LLVM.NoWrapFlags.mk false true) =
            LLVM.add a (LLVM.add b c (LLVM.NoWrapFlags.mk false true))
              (LLVM.NoWrapFlags.mk false true) := by
      intro a b c
      cases a <;> cases b <;> cases c <;>
        simp [LLVM.add, LLVM.add?, LLVM.SemVal.bind_poison, LLVM.SemVal.bind_value]
      case value.value.poison a b =>
        by_cases hab : a.uaddOverflow b = true <;> simp [hab]
      case value.value.value a b c =>
        have ha := BitVec.isLt a
        have hb := BitVec.isLt b
        have hc := BitVec.isLt c
        by_cases hab : a.uaddOverflow b = true
        · simp [hab]
          by_cases hbc : b.uaddOverflow c = true
          · simp [hbc]
          · have hbclt : b.toNat + c.toNat < 2 ^ w := by
              simp [BitVec.uaddOverflow] at hbc
              omega
            have hright : a.uaddOverflow (b + c) = true := by
              simp [BitVec.uaddOverflow, BitVec.toNat_add_of_lt hbclt]
              simp [BitVec.uaddOverflow] at hab
              omega
            simp [hbc, hright]
        · simp [hab]
          have hablt : a.toNat + b.toNat < 2 ^ w := by
            simp [BitVec.uaddOverflow] at hab
            omega
          by_cases habc : (a + b).uaddOverflow c = true
          · simp [habc]
            have hsum : a.toNat + b.toNat + c.toNat ≥ 2 ^ w := by
              have habcNat : (a + b).toNat + c.toNat ≥ 2 ^ w := by
                simpa [BitVec.uaddOverflow] using habc
              rw [BitVec.toNat_add_of_lt hablt] at habcNat
              omega
            by_cases hbc : b.uaddOverflow c = true
            · simp [hbc]
            · have hbclt : b.toNat + c.toNat < 2 ^ w := by
                simp [BitVec.uaddOverflow] at hbc
                omega
              have hright : a.uaddOverflow (b + c) = true := by
                simp [BitVec.uaddOverflow, BitVec.toNat_add_of_lt hbclt]
                omega
              simp [hbc, hright]
          · simp [habc]
            have hsumlt : a.toNat + b.toNat + c.toNat < 2 ^ w := by
              have habcNat : (a + b).toNat + c.toNat < 2 ^ w := by
                have habcNot : ¬(a + b).toNat + c.toNat ≥ 2 ^ w := by
                  simpa [BitVec.uaddOverflow] using habc
                omega
              rw [BitVec.toNat_add_of_lt hablt] at habcNat
              omega
            have hbc : b.uaddOverflow c = false := by
              simp [BitVec.uaddOverflow]
              omega
            have hbclt : b.toNat + c.toNat < 2 ^ w := by
              simp [BitVec.uaddOverflow] at hbc
              omega
            have hright : a.uaddOverflow (b + c) = false := by
              simp [BitVec.uaddOverflow, BitVec.toNat_add_of_lt hbclt]
              omega
            simp [hbc, hright, BitVec.add_assoc]
    have hidx :
        ∀ (idx c1 c2 : TyDenote.toType (symloop_08_ity w)),
          (do
              let step ← (do
                let x ← idx
                let y ← c1
                pure (LLVM.add x y (LLVM.NoWrapFlags.mk false true)))
              let z ← c2
              pure (LLVM.add step z (LLVM.NoWrapFlags.mk false true))) =
            (do
              let x ← idx
              let inv ← (do
                let y ← c1
                let z ← c2
                pure (LLVM.add y z (LLVM.NoWrapFlags.mk false true)))
              pure (LLVM.add x inv (LLVM.NoWrapFlags.mk false true))) := by
      intro idx c1 c2
      cases idx <;> cases c1 <;> cases c2 <;> simp [hadd_assoc_nuw]
    have hloop :
        ∀ (n : Nat) (s : LLVMMemory.State) (j1 j2 b3 : TyDenote.toType (symloop_08_ity w)),
          b3 =
            (do
              let a1 ← V ((⟨1, by rfl⟩ : (symloop_08_ctx w).Var (symloop_08_ity w)))
              let a2 ← V (Ctxt.Var.last (Ctxt.ofList [(symloop_08_ity w)]) (symloop_08_ity w))
              pure (LLVM.add a1 a2 (LLVM.NoWrapFlags.mk false true))) →
          StateT.run
              (ReaderT.run
                (LLVMMemory.CFGTarget.denoteWithMemoryFuel n (symloop_08_srcBlocks w) V
                  ((symloop_08_srcLoopVal w) j1 j2) (symloop_08_srcLoopTarget w))
                ∅)
              s
            ⊑
            StateT.run
              (ReaderT.run
                (LLVMMemory.CFGTarget.denoteWithMemoryFuel n (symloop_08_tgtBlocks w) V
                  ((symloop_08_tgtLoopVal w) j1 j2 b3) (symloop_08_tgtLoopTarget w))
                ∅)
              s := by
      intro n
      induction n with
      | zero =>
          intro s j1 j2 b3 hb3
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      | succ n ihn =>
          intro s j1 j2 b3 hb3
          simp [simp_denote, simp_memory, simp_llvm, symloop_08_src, symloop_08_tgt,
            symloop_08_srcBlocks, symloop_08_tgtBlocks,
            symloop_08_srcLoopTarget, symloop_08_tgtLoopTarget, symloop_08_srcLoopVal,
            symloop_08_tgtLoopVal, symloop_08_src_loop_dispatch, symloop_08_tgt_loop_dispatch,
            LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
            LLVMMemory.CFGBody.denoteWithMemoryFuelCore, LLVMMemory.CFGTerm.denoteWithMemoryFuelCore,
            DialectDenote.denote, Op.denote, LLVMMemory.Op.denoteVec, hb3, hidx]
          split <;>
            simp_all [simp_denote, simp_memory, simp_llvm, symloop_08_src, symloop_08_tgt,
              symloop_08_srcBlocks, symloop_08_tgtBlocks,
              symloop_08_srcLoopTarget, symloop_08_tgtLoopTarget, symloop_08_srcLoopVal,
              symloop_08_tgtLoopVal, symloop_08_src_loop_dispatch, symloop_08_tgt_loop_dispatch,
              LLVMMemory.CFGTarget.denoteWithMemoryFuel,
              LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
              LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, DialectDenote.denote, Op.denote,
              LLVMMemory.Op.denoteVec, hidx]
          all_goals first
            | exact mem_result_le_self _
            | exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
            | rename_i _ c _
              by_cases hc : c = 1#1
              · cases n <;>
                simp_all [hc, simp_denote, simp_memory, simp_llvm, symloop_08_src, symloop_08_tgt,
                  symloop_08_srcBlocks, symloop_08_tgtBlocks,
                  symloop_08_srcLoopTarget, symloop_08_tgtLoopTarget, symloop_08_srcLoopVal,
                  symloop_08_tgtLoopVal, symloop_08_src_loop_dispatch, symloop_08_tgt_loop_dispatch,
                  LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                  LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                  LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, DialectDenote.denote, Op.denote,
                  LLVMMemory.Op.denoteVec, hidx]
                all_goals
                  have hV1 :
                      V ((Ctxt.Var.toCons (t' := symloop_08_ity w)
                          (Ctxt.Var.last (Ctxt.ofList []) (symloop_08_ity w))) :
                          (symloop_08_ctx w).Var (symloop_08_ity w)) =
                        V ((⟨1, by rfl⟩ : (symloop_08_ctx w).Var (symloop_08_ity w))) := by
                    rfl
                  simpa [hV1, hidx, hadd_assoc_nuw] using mem_result_le_self _
              ·
                simp_all [hc, simp_denote, simp_memory, simp_llvm, symloop_08_src, symloop_08_tgt,
                  symloop_08_srcBlocks, symloop_08_tgtBlocks,
                  symloop_08_srcLoopTarget, symloop_08_tgtLoopTarget, symloop_08_srcLoopVal,
                  symloop_08_tgtLoopVal, symloop_08_src_loop_dispatch, symloop_08_tgt_loop_dispatch,
                  LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                  LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                  LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, DialectDenote.denote, Op.denote,
                  LLVMMemory.Op.denoteVec, hidx]
                all_goals first
                  | exact mem_result_le_self _
                  | exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                  | rw [symloop_08_src_loop_dispatch, symloop_08_tgt_loop_dispatch]
                    have hV1 :
                        V ((Ctxt.Var.toCons (t' := symloop_08_ity w)
                            (Ctxt.Var.last (Ctxt.ofList []) (symloop_08_ity w))) :
                            (symloop_08_ctx w).Var (symloop_08_ity w)) =
                          V ((⟨1, by rfl⟩ : (symloop_08_ctx w).Var (symloop_08_ity w))) := by
                      rfl
                    simpa [hV1, hidx, hadd_assoc_nuw] using
                      ihn s
                        (Option.bind j1 fun a =>
                          some (LLVM.add a (LLVM.SemVal.value 1#w)))
                        (Option.bind j2 fun x' =>
                          Option.bind
                            (V ((⟨1, by rfl⟩ :
                              (symloop_08_ctx w).Var (symloop_08_ity w)))) fun y' =>
                            some (LLVM.add x' y' (LLVM.NoWrapFlags.mk false true)))
    intro s j1 j2 b1 b2 b3 hinv
    rcases hinv with ⟨rfl, rfl, hb3, hno⟩
    exact hloop (fuel + 1) s j1 j2 b3 hb3

/- [IR-DERIVED: core fuel-induction lemma — BOTH cases are emitted: the zero
   case by the fixed out-of-fuel closer, the succ case by the step lemma
   above.  No hole is left inside this proof.] -/
private theorem symloop_08_loop_refine (w : Nat) (V : Ctxt.Valuation (symloop_08_ctx w)) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) (j1 j2 b1 b2 b3 : TyDenote.toType (symloop_08_ity w)),
      (symloop_08_inv w) j1 j2 b1 b2 b3 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (symloop_08_srcBlocks w) V
              ((symloop_08_srcLoopVal w) j1 j2) (symloop_08_srcLoopTarget w))
            ∅)
          s
        ⊑
        StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (symloop_08_tgtBlocks w) V
              ((symloop_08_tgtLoopVal w) b1 b2 b3) (symloop_08_tgtLoopTarget w))
            ∅)
          s := by
  intro fuel
  induction fuel with
  | zero =>
      intro s j1 j2 b1 b2 b3 _hinv
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact (symloop_08_step w) V fuel ih

theorem symloop_08_correct (w : Nat) : (symloop_08_src w) ⊑ (symloop_08_tgt w) := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>
      /- [HOLE H3: final assembly — unfold both entry blocks (simp with the two block sets
         + LLVMMemory.Com.denoteWithMemoryFuel/denoteWithMemoryFuelIn +
         CFGTarget/CFGBody/CFGTerm denote lemmas), dispatch both loop
         entries via (symloop_08_src_loop_dispatch w) / (symloop_08_tgt_loop_dispatch w), then
         apply (symloop_08_loop_refine w) — which now requires ESTABLISHING
         (symloop_08_inv w) at the two entry-block initial states.
         The 1 TARGET-SPECIFIC UB obligation(s) HU1..HU1 above are
         proved separately, so the tgt entry block yields plain values
         on this path.
         Each HU takes premises hs1..hs2 — the SOURCE's conditions on its
         FIRST iteration. Supply them HERE: case-split on them, and in the
         failing branch the src loop body poisons on iteration 1, so the
         src side is poison and refines anything (¬ BitVec.uaddOverflow (0#w) a1; ¬ BitVec.uaddOverflow ((0#w) + a1) a2).] -/
      sorry

end TestLoop
end InstCombine
