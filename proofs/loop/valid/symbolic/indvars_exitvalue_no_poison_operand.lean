import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace InstCombine
namespace TestLoop

def indvars_exitvalue_no_poison_operand_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @indvars_exitvalue_no_poison_operand_src(%x : _, %n : _) -> _ {
  ^entry(%x : _, %n : _):
    %e_zero = llvm.mlir.constant 0 : _
    llvm.br ^loop(%e_zero : _, %e_zero : _)
  ^loop(%acc : _, %i : _):
    %l_one = llvm.mlir.constant 1 : _
    %acc_next = llvm.add %acc, %l_one : _
    %i_next = llvm.add %i, %l_one : _
    %cond = llvm.icmp "eq" %i, %n : _
    llvm.cond_br %cond : i1, ^out(%acc : _), ^loop(%acc_next : _, %i_next : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

def indvars_exitvalue_no_poison_operand_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @indvars_exitvalue_no_poison_operand_tgt(%x : _, %n : _) -> _ {
  ^entry(%x : _, %n : _):
    llvm.return %n : _
  }
  }]

private abbrev indvars_exitvalue_no_poison_operand_ity (w : Nat) : LLVM.Ty := LLVM.Ty.bitvec w

private abbrev indvars_exitvalue_no_poison_operand_ctx (w : Nat) : Ctxt LLVM.Ty := Ctxt.ofList [(indvars_exitvalue_no_poison_operand_ity w), (indvars_exitvalue_no_poison_operand_ity w)]

private def indvars_exitvalue_no_poison_operand_srcBlocks (w : Nat) : CFGBlocks LLVM (indvars_exitvalue_no_poison_operand_ctx w) .impure [(indvars_exitvalue_no_poison_operand_ity w)] :=
  match (indvars_exitvalue_no_poison_operand_src w) with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private theorem indvars_exitvalue_no_poison_operand_entry_ne_loop (w : Nat) : ¬ ("entry" = "loop") := by
  decide

private theorem indvars_exitvalue_no_poison_operand_out_ne_loop (w : Nat) : ¬ ("out" = "loop") := by
  decide

private def indvars_exitvalue_no_poison_operand_srcLoopTarget (w : Nat) : CFGTarget LLVM (Ctxt.ofList [(indvars_exitvalue_no_poison_operand_ity w), (indvars_exitvalue_no_poison_operand_ity w)]) where
  name := "loop"
  argTys := [(indvars_exitvalue_no_poison_operand_ity w), (indvars_exitvalue_no_poison_operand_ity w)]
  args := (⟨0, by rfl⟩ : (Ctxt.ofList [(indvars_exitvalue_no_poison_operand_ity w), (indvars_exitvalue_no_poison_operand_ity w)]).Var (indvars_exitvalue_no_poison_operand_ity w)) ::ₕ (⟨1, by rfl⟩ : (Ctxt.ofList [(indvars_exitvalue_no_poison_operand_ity w), (indvars_exitvalue_no_poison_operand_ity w)]).Var (indvars_exitvalue_no_poison_operand_ity w)) ::ₕ HVector.nil

private def indvars_exitvalue_no_poison_operand_srcLoopVal (w : Nat) (j1 j2 : TyDenote.toType (indvars_exitvalue_no_poison_operand_ity w)) :
    Ctxt.Valuation (Ctxt.ofList [(indvars_exitvalue_no_poison_operand_ity w), (indvars_exitvalue_no_poison_operand_ity w)]) :=
  Ctxt.Valuation.ofHVector (j1 ::ₕ j2 ::ₕ HVector.nil)

private theorem indvars_exitvalue_no_poison_operand_src_loop_dispatch (w : Nat)
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation (indvars_exitvalue_no_poison_operand_ctx w)) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a1 a2 : Γcur.Var (indvars_exitvalue_no_poison_operand_ity w)) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (indvars_exitvalue_no_poison_operand_srcBlocks w) V W
            ({ name := "loop", argTys := [(indvars_exitvalue_no_poison_operand_ity w), (indvars_exitvalue_no_poison_operand_ity w)], args := a1 ::ₕ a2 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (indvars_exitvalue_no_poison_operand_srcBlocks w) V
            ((indvars_exitvalue_no_poison_operand_srcLoopVal w) (W a1) (W a2)) (indvars_exitvalue_no_poison_operand_srcLoopTarget w))
          ∅)
        s := by
  cases fuel <;>
    simp [indvars_exitvalue_no_poison_operand_src, indvars_exitvalue_no_poison_operand_srcBlocks, indvars_exitvalue_no_poison_operand_srcLoopTarget, indvars_exitvalue_no_poison_operand_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

private def indvars_exitvalue_no_poison_operand_tgtResult (w : Nat) (V : Ctxt.Valuation (indvars_exitvalue_no_poison_operand_ctx w)) : TyDenote.toType (indvars_exitvalue_no_poison_operand_ity w) :=
  (V (Ctxt.Var.last (Ctxt.ofList [(indvars_exitvalue_no_poison_operand_ity w)]) (indvars_exitvalue_no_poison_operand_ity w)))

private def indvars_exitvalue_no_poison_operand_inv (w : Nat) (j1 j2 : TyDenote.toType (indvars_exitvalue_no_poison_operand_ity w))
    (V : Ctxt.Valuation (indvars_exitvalue_no_poison_operand_ctx w)) : Prop :=
  j1 = j2

private theorem indvars_exitvalue_no_poison_operand_step (w : Nat) (V : Ctxt.Valuation (indvars_exitvalue_no_poison_operand_ctx w)) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (indvars_exitvalue_no_poison_operand_ity w)),
      (indvars_exitvalue_no_poison_operand_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (indvars_exitvalue_no_poison_operand_srcBlocks w) V
              ((indvars_exitvalue_no_poison_operand_srcLoopVal w) j1 j2) (indvars_exitvalue_no_poison_operand_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((indvars_exitvalue_no_poison_operand_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(indvars_exitvalue_no_poison_operand_ity w)] × LLVMMemory.State))) :
    ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (indvars_exitvalue_no_poison_operand_ity w)),
      (indvars_exitvalue_no_poison_operand_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) (indvars_exitvalue_no_poison_operand_srcBlocks w) V
              ((indvars_exitvalue_no_poison_operand_srcLoopVal w) j1 j2) (indvars_exitvalue_no_poison_operand_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((indvars_exitvalue_no_poison_operand_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(indvars_exitvalue_no_poison_operand_ity w)] × LLVMMemory.State)) :=
  by
    intro s j1 j2 hinv
    subst j1
    cases j2 with
    | none =>
        simp [indvars_exitvalue_no_poison_operand_src, indvars_exitvalue_no_poison_operand_srcBlocks, indvars_exitvalue_no_poison_operand_srcLoopTarget,
          indvars_exitvalue_no_poison_operand_srcLoopVal, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
          LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
          LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
          LLVMMemory.throwUB, DialectDenote.denote, InstCombine.Op.denote,
          InstCombine.Op.denoteVec, InstCombine.lift1, InstCombine.lift2,
          InstCombine.lift2UB, Ctxt.Valuation.cons_eval, Ctxt.Valuation.ofHVector_cons,
          LLVM.add, LLVM.add?, LLVM.const?, LLVM.icmp, LLVM.icmp?]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    | some j2v =>
        cases j2v with
        | poison =>
            cases hN :
                V (Ctxt.Var.last (Ctxt.ofList [(indvars_exitvalue_no_poison_operand_ity w)]) (indvars_exitvalue_no_poison_operand_ity w)) with
            | none =>
                simp [indvars_exitvalue_no_poison_operand_src, indvars_exitvalue_no_poison_operand_srcBlocks, indvars_exitvalue_no_poison_operand_srcLoopTarget,
                  indvars_exitvalue_no_poison_operand_srcLoopVal, indvars_exitvalue_no_poison_operand_tgtResult,
                  LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                  LLVMMemory.CFGBlocks.findMemoryBlock?,
                  LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                  LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
                  LLVMMemory.throwUB, hN, DialectDenote.denote, InstCombine.Op.denote,
                  InstCombine.Op.denoteVec, InstCombine.lift1, InstCombine.lift2,
                  InstCombine.lift2UB, Ctxt.Valuation.cons_eval,
                  Ctxt.Valuation.ofHVector_cons, LLVM.add, LLVM.add?, LLVM.const?,
                  LLVM.icmp, LLVM.icmp?]
                exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
            | some nv =>
                cases nv <;>
                  simp [indvars_exitvalue_no_poison_operand_src, indvars_exitvalue_no_poison_operand_srcBlocks, indvars_exitvalue_no_poison_operand_srcLoopTarget,
                    indvars_exitvalue_no_poison_operand_srcLoopVal, indvars_exitvalue_no_poison_operand_tgtResult,
                    LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                    LLVMMemory.CFGBlocks.findMemoryBlock?,
                    LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                    LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
                    LLVMMemory.throwUB, hN, DialectDenote.denote, InstCombine.Op.denote,
                    InstCombine.Op.denoteVec, InstCombine.lift1, InstCombine.lift2,
                    InstCombine.lift2UB, Ctxt.Valuation.cons_eval,
                    Ctxt.Valuation.ofHVector_cons, LLVM.add, LLVM.add?, LLVM.const?,
                    LLVM.icmp, LLVM.icmp?] <;>
                  exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        | value j2v =>
            cases hN :
                V (Ctxt.Var.last (Ctxt.ofList [(indvars_exitvalue_no_poison_operand_ity w)]) (indvars_exitvalue_no_poison_operand_ity w)) with
            | none =>
                simp [indvars_exitvalue_no_poison_operand_src, indvars_exitvalue_no_poison_operand_srcBlocks, indvars_exitvalue_no_poison_operand_srcLoopTarget,
                  indvars_exitvalue_no_poison_operand_srcLoopVal, indvars_exitvalue_no_poison_operand_tgtResult,
                  LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                  LLVMMemory.CFGBlocks.findMemoryBlock?,
                  LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                  LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
                  LLVMMemory.throwUB, hN, DialectDenote.denote, InstCombine.Op.denote,
                  InstCombine.Op.denoteVec, InstCombine.lift1, InstCombine.lift2,
                  InstCombine.lift2UB, Ctxt.Valuation.cons_eval,
                  Ctxt.Valuation.ofHVector_cons, LLVM.add, LLVM.add?, LLVM.const?,
                  LLVM.icmp, LLVM.icmp?]
                exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
            | some nv =>
                cases nv with
                | poison =>
                    simp [indvars_exitvalue_no_poison_operand_src, indvars_exitvalue_no_poison_operand_srcBlocks, indvars_exitvalue_no_poison_operand_srcLoopTarget,
                      indvars_exitvalue_no_poison_operand_srcLoopVal, indvars_exitvalue_no_poison_operand_tgtResult,
                      LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                      LLVMMemory.CFGBlocks.findMemoryBlock?,
                      LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                      LLVMMemory.CFGTerm.denoteWithMemoryFuelCore,
                      LLVMMemory.Expr.denoteWithMemory, LLVMMemory.throwUB, hN,
                      DialectDenote.denote, InstCombine.Op.denote, InstCombine.Op.denoteVec,
                      InstCombine.lift1, InstCombine.lift2, InstCombine.lift2UB,
                      Ctxt.Valuation.cons_eval, Ctxt.Valuation.ofHVector_cons, LLVM.add,
                      LLVM.add?, LLVM.const?, LLVM.icmp, LLVM.icmp?]
                    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                | value nv =>
                    by_cases hEq : j2v = nv
                    · subst nv
                      cases fuel with
                      | zero =>
                          simp [indvars_exitvalue_no_poison_operand_src, indvars_exitvalue_no_poison_operand_srcBlocks, indvars_exitvalue_no_poison_operand_srcLoopTarget,
                            indvars_exitvalue_no_poison_operand_srcLoopVal, indvars_exitvalue_no_poison_operand_tgtResult,
                            LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                            LLVMMemory.CFGBlocks.findMemoryBlock?,
                            LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                            LLVMMemory.CFGTerm.denoteWithMemoryFuelCore,
                            LLVMMemory.Expr.denoteWithMemory, LLVMMemory.throwUB, hN,
                            DialectDenote.denote, InstCombine.Op.denote,
                            InstCombine.Op.denoteVec, InstCombine.lift1, InstCombine.lift2,
                            InstCombine.lift2UB, Ctxt.Valuation.cons_eval,
                            Ctxt.Valuation.ofHVector_cons, LLVM.add, LLVM.add?, LLVM.const?,
                            LLVM.icmp, LLVM.icmp?, LLVM.icmp']
                          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                      | succ fuel =>
                          simp [indvars_exitvalue_no_poison_operand_src, indvars_exitvalue_no_poison_operand_srcBlocks, indvars_exitvalue_no_poison_operand_srcLoopTarget,
                            indvars_exitvalue_no_poison_operand_srcLoopVal, indvars_exitvalue_no_poison_operand_tgtResult,
                            LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                            LLVMMemory.CFGBlocks.findMemoryBlock?,
                            LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                            LLVMMemory.CFGTerm.denoteWithMemoryFuelCore,
                            LLVMMemory.Expr.denoteWithMemory, LLVMMemory.throwUB, hN,
                            DialectDenote.denote, InstCombine.Op.denote,
                            InstCombine.Op.denoteVec, InstCombine.lift1, InstCombine.lift2,
                            InstCombine.lift2UB, Ctxt.Valuation.cons_eval,
                            Ctxt.Valuation.ofHVector_cons, LLVM.add, LLVM.add?, LLVM.const?,
                            LLVM.icmp, LLVM.icmp?, LLVM.icmp']
                          exact ImmediateUBOr.IsRefinedBy.bothValues (by
                            simp only [Prod.isRefinedBy_iff, HVector.cons_isRefinedBy_cons,
                              HVector.nil_isRefinedBy_nil, and_true]
                            exact ⟨ImmediateUBOr.IsRefinedBy.bothValues
                              (IntW_le_self (LLVM.SemVal.value j2v)), rfl⟩)
                    ·
                      have hCond : ¬((j2v == nv) = true) := by
                        intro h
                        apply hEq
                        exact beq_iff_eq.mp h
                      simp [indvars_exitvalue_no_poison_operand_src, indvars_exitvalue_no_poison_operand_srcBlocks, indvars_exitvalue_no_poison_operand_srcLoopTarget,
                        indvars_exitvalue_no_poison_operand_srcLoopVal, indvars_exitvalue_no_poison_operand_tgtResult,
                        LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                        LLVMMemory.CFGBlocks.findMemoryBlock?,
                        LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore,
                        LLVMMemory.Expr.denoteWithMemory, LLVMMemory.throwUB, hN, hCond,
                        DialectDenote.denote, InstCombine.Op.denote, InstCombine.Op.denoteVec,
                        InstCombine.lift1, InstCombine.lift2, InstCombine.lift2UB,
                        Ctxt.Valuation.cons_eval, Ctxt.Valuation.ofHVector_cons, LLVM.add,
                        LLVM.add?, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp']
                      erw [indvars_exitvalue_no_poison_operand_src_loop_dispatch w]
                      simpa [indvars_exitvalue_no_poison_operand_tgtResult, hN] using
                        ih s
                          (some (LLVM.SemVal.value (j2v + 1#w)))
                          (some (LLVM.SemVal.value (j2v + 1#w)))
                          rfl

private theorem indvars_exitvalue_no_poison_operand_loop_refine (w : Nat) (V : Ctxt.Valuation (indvars_exitvalue_no_poison_operand_ctx w)) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (indvars_exitvalue_no_poison_operand_ity w)),
      (indvars_exitvalue_no_poison_operand_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (indvars_exitvalue_no_poison_operand_srcBlocks w) V
              ((indvars_exitvalue_no_poison_operand_srcLoopVal w) j1 j2) (indvars_exitvalue_no_poison_operand_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((indvars_exitvalue_no_poison_operand_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(indvars_exitvalue_no_poison_operand_ity w)] × LLVMMemory.State)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s j1 j2 _hinv
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact (indvars_exitvalue_no_poison_operand_step w) V fuel ih

private theorem indvars_exitvalue_no_poison_operand_src_ub_of_poison_input1 (w : Nat)
    (V : InstCombine.InputValuation (indvars_exitvalue_no_poison_operand_ctx w)) (fuel : Nat) (s : LLVMMemory.State)
    (hA : V (Ctxt.Var.last (Ctxt.ofList [(indvars_exitvalue_no_poison_operand_ity w)]) (indvars_exitvalue_no_poison_operand_ity w)) = LLVM.SemVal.poison) :
    LLVMMemory.Com.denoteWithMemoryFuel fuel (indvars_exitvalue_no_poison_operand_src w)
        (V := InstCombine.InputValuation.lift V) s = none := by
  match fuel with
  | 0 =>
        simp [indvars_exitvalue_no_poison_operand_src, LLVMMemory.Com.denoteWithMemoryFuel, LLVMMemory.Com.denoteWithMemoryFuelIn, LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore, LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory, LLVMMemory.throwUB, hA, DialectDenote.denote, InstCombine.Op.denote, InstCombine.Op.denoteVec, InstCombine.lift1, InstCombine.lift2, InstCombine.lift2UB, Ctxt.Valuation.cons_eval, Ctxt.Valuation.ofHVector_cons, LLVM.add, LLVM.add?, LLVM.const?, LLVM.icmp, LLVM.icmp?] <;> rfl
  | 1 =>
        simp [indvars_exitvalue_no_poison_operand_src, LLVMMemory.Com.denoteWithMemoryFuel, LLVMMemory.Com.denoteWithMemoryFuelIn, LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore, LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory, LLVMMemory.throwUB, hA, DialectDenote.denote, InstCombine.Op.denote, InstCombine.Op.denoteVec, InstCombine.lift1, InstCombine.lift2, InstCombine.lift2UB, Ctxt.Valuation.cons_eval, Ctxt.Valuation.ofHVector_cons, LLVM.add, LLVM.add?, LLVM.const?, LLVM.icmp, LLVM.icmp?] <;> rfl
  | (n + 2) =>
        simp [indvars_exitvalue_no_poison_operand_src, LLVMMemory.Com.denoteWithMemoryFuel, LLVMMemory.Com.denoteWithMemoryFuelIn, LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore, LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory, LLVMMemory.throwUB, hA, DialectDenote.denote, InstCombine.Op.denote, InstCombine.Op.denoteVec, InstCombine.lift1, InstCombine.lift2, InstCombine.lift2UB, Ctxt.Valuation.cons_eval, Ctxt.Valuation.ofHVector_cons, LLVM.add, LLVM.add?, LLVM.const?, LLVM.icmp, LLVM.icmp?] <;> rfl

theorem indvars_exitvalue_no_poison_operand_correct (w : Nat) :
    IsRefinedByOnIntWInputsWithMemory (indvars_exitvalue_no_poison_operand_src w) ((indvars_exitvalue_no_poison_operand_tgt w).castPureToEff .impure) := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>
      cases hA1 : V (Ctxt.Var.last (Ctxt.ofList [(indvars_exitvalue_no_poison_operand_ity w)]) (indvars_exitvalue_no_poison_operand_ity w)) with
      | poison =>

          rw [(indvars_exitvalue_no_poison_operand_src_ub_of_poison_input1 w) V (fuel + 1) s hA1]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      | value av2 =>

          simp [indvars_exitvalue_no_poison_operand_src, indvars_exitvalue_no_poison_operand_tgt, indvars_exitvalue_no_poison_operand_srcBlocks,
            indvars_exitvalue_no_poison_operand_srcLoopTarget, indvars_exitvalue_no_poison_operand_srcLoopVal, indvars_exitvalue_no_poison_operand_tgtResult,
            indvars_exitvalue_no_poison_operand_inv, LLVMMemory.Com.denoteWithMemoryFuel,
            LLVMMemory.Com.denoteWithMemoryFuelIn, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
            LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
            LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, LLVMMemory.Expr.denoteWithMemory,
            LLVMMemory.throwUB, hA1, DialectDenote.denote, InstCombine.Op.denote,
            InstCombine.Op.denoteVec, InstCombine.lift1, InstCombine.lift2,
            InstCombine.lift2UB, Ctxt.Valuation.cons_eval, Ctxt.Valuation.ofHVector_cons,
            LLVM.add, LLVM.add?, LLVM.const?, LLVM.icmp, LLVM.icmp?]
          erw [indvars_exitvalue_no_poison_operand_src_loop_dispatch w]
          simpa [indvars_exitvalue_no_poison_operand_tgtResult, indvars_exitvalue_no_poison_operand_inv, hA1,
            LLVMMemory.Com.denoteWithMemoryCore, InstCombine.InputValuation.lift,
            Ctxt.Valuation.cons_eval] using
            (indvars_exitvalue_no_poison_operand_loop_refine w (InstCombine.InputValuation.lift V) fuel s
              (some (LLVM.SemVal.value 0#w) : TyDenote.toType (indvars_exitvalue_no_poison_operand_ity w))
              (some (LLVM.SemVal.value 0#w) : TyDenote.toType (indvars_exitvalue_no_poison_operand_ity w))
              rfl)

end TestLoop
end InstCombine
