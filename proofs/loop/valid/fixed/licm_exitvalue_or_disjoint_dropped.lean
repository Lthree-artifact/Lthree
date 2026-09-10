import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace InstCombine
namespace TestLoop

def rq3_or_disjoint_allwidth_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @rq3_or_disjoint_allwidth_src(%c1 : _, %c2 : _) -> _ {
  ^entry(%c1 : _, %c2 : _):
    %e_zero = llvm.mlir.constant 0 : _
    %e_start = llvm.mlir.constant 0 : _
    llvm.br ^loop(%e_zero : _, %e_start : _)
  ^loop(%k : _, %index : _):
    %step_add = llvm.or %index, %c1 : _
    %index_next = llvm.or disjoint %c2, %step_add : _
    %l_one = llvm.mlir.constant 1 : _
    %k1 = llvm.add %k, %l_one : _
    %l_three = llvm.mlir.constant 3 : _
    %cond = llvm.icmp "eq" %k1, %l_three : _
    llvm.cond_br %cond : i1, ^out(%index_next : _), ^loop(%k1 : _, %index_next : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

def rq3_or_disjoint_allwidth_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @rq3_or_disjoint_allwidth_tgt(%c1 : _, %c2 : _) -> _ {
  ^entry(%c1 : _, %c2 : _):
    %invariant_op = llvm.or %c1, %c2 : _
    %s2 = llvm.or %invariant_op, %invariant_op : _
    %s3 = llvm.or %s2, %invariant_op : _
    llvm.return %s3 : _
  }
  }]

private abbrev rq3_or_disjoint_allwidth_ity (w : Nat) : LLVM.Ty := LLVM.Ty.bitvec w

private abbrev rq3_or_disjoint_allwidth_ctx (w : Nat) : Ctxt LLVM.Ty := Ctxt.ofList [(rq3_or_disjoint_allwidth_ity w), (rq3_or_disjoint_allwidth_ity w)]

private def rq3_or_disjoint_allwidth_srcBlocks (w : Nat) : CFGBlocks LLVM (rq3_or_disjoint_allwidth_ctx w) .impure [(rq3_or_disjoint_allwidth_ity w)] :=
  match (rq3_or_disjoint_allwidth_src w) with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private theorem rq3_or_disjoint_allwidth_entry_ne_loop (w : Nat) : ¬ ("entry" = "loop") := by
  decide

private theorem rq3_or_disjoint_allwidth_out_ne_loop (w : Nat) : ¬ ("out" = "loop") := by
  decide

private def rq3_or_disjoint_allwidth_srcLoopTarget (w : Nat) : CFGTarget LLVM (Ctxt.ofList [(rq3_or_disjoint_allwidth_ity w), (rq3_or_disjoint_allwidth_ity w)]) where
  name := "loop"
  argTys := [(rq3_or_disjoint_allwidth_ity w), (rq3_or_disjoint_allwidth_ity w)]
  args := (⟨0, by rfl⟩ : (Ctxt.ofList [(rq3_or_disjoint_allwidth_ity w), (rq3_or_disjoint_allwidth_ity w)]).Var (rq3_or_disjoint_allwidth_ity w)) ::ₕ (⟨1, by rfl⟩ : (Ctxt.ofList [(rq3_or_disjoint_allwidth_ity w), (rq3_or_disjoint_allwidth_ity w)]).Var (rq3_or_disjoint_allwidth_ity w)) ::ₕ HVector.nil

private def rq3_or_disjoint_allwidth_srcLoopVal (w : Nat) (j1 j2 : TyDenote.toType (rq3_or_disjoint_allwidth_ity w)) :
    Ctxt.Valuation (Ctxt.ofList [(rq3_or_disjoint_allwidth_ity w), (rq3_or_disjoint_allwidth_ity w)]) :=
  Ctxt.Valuation.ofHVector (j1 ::ₕ j2 ::ₕ HVector.nil)

private theorem rq3_or_disjoint_allwidth_src_loop_dispatch (w : Nat)
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation (rq3_or_disjoint_allwidth_ctx w)) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a1 a2 : Γcur.Var (rq3_or_disjoint_allwidth_ity w)) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (rq3_or_disjoint_allwidth_srcBlocks w) V W
            ({ name := "loop", argTys := [(rq3_or_disjoint_allwidth_ity w), (rq3_or_disjoint_allwidth_ity w)], args := a1 ::ₕ a2 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (rq3_or_disjoint_allwidth_srcBlocks w) V
            ((rq3_or_disjoint_allwidth_srcLoopVal w) (W a1) (W a2)) (rq3_or_disjoint_allwidth_srcLoopTarget w))
          ∅)
        s := by
  cases fuel <;>
    simp [rq3_or_disjoint_allwidth_src, rq3_or_disjoint_allwidth_srcBlocks, rq3_or_disjoint_allwidth_srcLoopTarget, rq3_or_disjoint_allwidth_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

private def rq3_or_disjoint_allwidth_tgtResult (w : Nat) (V : Ctxt.Valuation (rq3_or_disjoint_allwidth_ctx w)) : TyDenote.toType (rq3_or_disjoint_allwidth_ity w) :=
  (InstCombine.lift2 (fun x y => LLVM.or x y) (InstCombine.lift2 (fun x y => LLVM.or x y) (InstCombine.lift2 (fun x y => LLVM.or x y) (V ((⟨1, by rfl⟩ : (rq3_or_disjoint_allwidth_ctx w).Var (rq3_or_disjoint_allwidth_ity w)))) (V (Ctxt.Var.last (Ctxt.ofList [(rq3_or_disjoint_allwidth_ity w)]) (rq3_or_disjoint_allwidth_ity w)))) (InstCombine.lift2 (fun x y => LLVM.or x y) (V ((⟨1, by rfl⟩ : (rq3_or_disjoint_allwidth_ctx w).Var (rq3_or_disjoint_allwidth_ity w)))) (V (Ctxt.Var.last (Ctxt.ofList [(rq3_or_disjoint_allwidth_ity w)]) (rq3_or_disjoint_allwidth_ity w))))) (InstCombine.lift2 (fun x y => LLVM.or x y) (V ((⟨1, by rfl⟩ : (rq3_or_disjoint_allwidth_ctx w).Var (rq3_or_disjoint_allwidth_ity w)))) (V (Ctxt.Var.last (Ctxt.ofList [(rq3_or_disjoint_allwidth_ity w)]) (rq3_or_disjoint_allwidth_ity w)))))

private def rq3_or_disjoint_allwidth_inv (w : Nat) (j1 j2 : TyDenote.toType (rq3_or_disjoint_allwidth_ity w))
    (V : Ctxt.Valuation (rq3_or_disjoint_allwidth_ctx w)) : Prop :=
  let z : LLVM.IntWUB w := LLVM.IntWUB.value (0#w)
  let c1 : LLVM.IntWUB w :=
    V ((⟨1, by rfl⟩ : (rq3_or_disjoint_allwidth_ctx w).Var (rq3_or_disjoint_allwidth_ity w)))
  let c2 : LLVM.IntWUB w :=
    V (Ctxt.Var.last (Ctxt.ofList [(rq3_or_disjoint_allwidth_ity w)]) (rq3_or_disjoint_allwidth_ity w))
  let step : LLVM.IntWUB w → LLVM.IntWUB w := fun idx =>
    InstCombine.lift2 (fun x y => LLVM.or x y { «disjoint» := true }) c2
      (InstCombine.lift2 (fun x y => LLVM.or x y) idx c1)
  match j1 with
  | .some (.value k) =>
      (k = 0#w ∧ j2 = z) ∨
        (k = 1#w ∧ 1#w ≠ 3#w ∧ j2 = step z) ∨
        (k = 2#w ∧ 1#w ≠ 3#w ∧ 2#w ≠ 3#w ∧ j2 = step (step z))
  | _ => False

private theorem rq3_or_disjoint_allwidth_step (w : Nat) (V : Ctxt.Valuation (rq3_or_disjoint_allwidth_ctx w)) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (rq3_or_disjoint_allwidth_ity w)),
      (rq3_or_disjoint_allwidth_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (rq3_or_disjoint_allwidth_srcBlocks w) V
              ((rq3_or_disjoint_allwidth_srcLoopVal w) j1 j2) (rq3_or_disjoint_allwidth_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((rq3_or_disjoint_allwidth_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(rq3_or_disjoint_allwidth_ity w)] × LLVMMemory.State))) :
    ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (rq3_or_disjoint_allwidth_ity w)),
      (rq3_or_disjoint_allwidth_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) (rq3_or_disjoint_allwidth_srcBlocks w) V
              ((rq3_or_disjoint_allwidth_srcLoopVal w) j1 j2) (rq3_or_disjoint_allwidth_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((rq3_or_disjoint_allwidth_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(rq3_or_disjoint_allwidth_ity w)] × LLVMMemory.State)) :=
  by
    let c1 : LLVM.IntWUB w :=
      V ((⟨1, by rfl⟩ : (rq3_or_disjoint_allwidth_ctx w).Var (rq3_or_disjoint_allwidth_ity w)))
    let c2 : LLVM.IntWUB w :=
      V (Ctxt.Var.last (Ctxt.ofList [(rq3_or_disjoint_allwidth_ity w)]) (rq3_or_disjoint_allwidth_ity w))
    let z : LLVM.IntWUB w := LLVM.IntWUB.value (0#w)
    let step : LLVM.IntWUB w → LLVM.IntWUB w := fun idx =>
      InstCombine.lift2 (fun x y => LLVM.or x y { «disjoint» := true }) c2
        (InstCombine.lift2 (fun x y => LLVM.or x y) idx c1)
    let tgt : LLVM.IntWUB w := (rq3_or_disjoint_allwidth_tgtResult w) V
    have step_z_refines :
        step z ⊑ tgt := by
      have h :
          (let z : LLVM.IntWUB w := LLVM.IntWUB.value (0#w)
           let step : LLVM.IntWUB w → LLVM.IntWUB w := fun idx =>
             InstCombine.lift2 (fun x y => LLVM.or x y { «disjoint» := true }) c2
               (InstCombine.lift2 (fun x y => LLVM.or x y) idx c1)
           step z) ⊑
            (InstCombine.lift2 (fun x y => LLVM.or x y)
              (InstCombine.lift2 (fun x y => LLVM.or x y)
                (InstCombine.lift2 (fun x y => LLVM.or x y) c1 c2)
                (InstCombine.lift2 (fun x y => LLVM.or x y) c1 c2))
              (InstCombine.lift2 (fun x y => LLVM.or x y) c1 c2)) := by
        dsimp
        cases c1 with
        | none => simp [InstCombine.lift2]
        | some s1 =>
            cases s1 with
            | poison =>
                cases c2 with
                | none => simp [InstCombine.lift2]
                | some s2 =>
                    cases s2 <;>
                      simp [InstCombine.lift2, LLVM.or, LLVM.or?, LLVM.SemVal.instMonad]
            | value a =>
                cases c2 with
                | none => simp [InstCombine.lift2]
                | some s2 =>
                    cases s2 with
                    | poison =>
                        simp [InstCombine.lift2, LLVM.or, LLVM.or?, LLVM.SemVal.instMonad]
                    | value b =>
                        by_cases h0 : b &&& (0#w ||| a) = 0#w
                        · have h0' : b &&& a = 0#w := by simpa using h0
                          simp [InstCombine.lift2, LLVM.or, LLVM.or?, LLVM.SemVal.instMonad, h0']
                          apply ImmediateUBOr.IsRefinedBy.bothValues
                          rw [LLVM.IntW.isRefinedBy_iff]
                          rw [LLVM.SemVal.value_isRefinedBy_value]
                          rw [InstCombine.bv_isRefinedBy_iff]
                          ext i
                          simp [BitVec.getElem_or]
                          cases a[i] <;> cases b[i] <;> simp
                        · have h0' : ¬ b &&& a = 0#w := by
                            intro hb
                            apply h0
                            simpa using hb
                          simp [InstCombine.lift2, LLVM.or, LLVM.or?, LLVM.SemVal.instMonad, h0']
                          apply ImmediateUBOr.IsRefinedBy.bothValues
                          rw [LLVM.IntW.isRefinedBy_iff]
                          exact LLVM.SemVal.poison_isRefinedBy _
      simpa [tgt, step, z, c1, c2, rq3_or_disjoint_allwidth_tgtResult] using h
    have step_step_z_refines :
        step (step z) ⊑ tgt := by
      have h :
          (let z : LLVM.IntWUB w := LLVM.IntWUB.value (0#w)
           let step : LLVM.IntWUB w → LLVM.IntWUB w := fun idx =>
             InstCombine.lift2 (fun x y => LLVM.or x y { «disjoint» := true }) c2
               (InstCombine.lift2 (fun x y => LLVM.or x y) idx c1)
           step (step z)) ⊑
            (InstCombine.lift2 (fun x y => LLVM.or x y)
              (InstCombine.lift2 (fun x y => LLVM.or x y)
                (InstCombine.lift2 (fun x y => LLVM.or x y) c1 c2)
                (InstCombine.lift2 (fun x y => LLVM.or x y) c1 c2))
              (InstCombine.lift2 (fun x y => LLVM.or x y) c1 c2)) := by
        dsimp
        cases c1 with
        | none => simp [InstCombine.lift2]
        | some s1 =>
            cases s1 with
            | poison =>
                cases c2 with
                | none => simp [InstCombine.lift2]
                | some s2 =>
                    cases s2 <;>
                      simp [InstCombine.lift2, LLVM.or, LLVM.or?, LLVM.SemVal.instMonad]
            | value a =>
                cases c2 with
                | none => simp [InstCombine.lift2]
                | some s2 =>
                    cases s2 with
                    | poison =>
                        simp [InstCombine.lift2, LLVM.or, LLVM.or?, LLVM.SemVal.instMonad]
                    | value b =>
                        by_cases h0 : b &&& a = 0#w
                        · by_cases h1 : b &&& ((b ||| a) ||| a) = 0#w
                          · simp [InstCombine.lift2, LLVM.or, LLVM.or?, LLVM.SemVal.instMonad,
                              h0, h1]
                            apply ImmediateUBOr.IsRefinedBy.bothValues
                            rw [LLVM.IntW.isRefinedBy_iff]
                            rw [LLVM.SemVal.value_isRefinedBy_value]
                            rw [InstCombine.bv_isRefinedBy_iff]
                            ext i
                            simp [BitVec.getElem_or]
                            cases a[i] <;> cases b[i] <;> simp
                          · simp [InstCombine.lift2, LLVM.or, LLVM.or?, LLVM.SemVal.instMonad,
                              h0, h1]
                            apply ImmediateUBOr.IsRefinedBy.bothValues
                            rw [LLVM.IntW.isRefinedBy_iff]
                            exact LLVM.SemVal.poison_isRefinedBy _
                        · simp [InstCombine.lift2, LLVM.or, LLVM.or?, LLVM.SemVal.instMonad, h0]
                          apply ImmediateUBOr.IsRefinedBy.bothValues
                          rw [LLVM.IntW.isRefinedBy_iff]
                          exact LLVM.SemVal.poison_isRefinedBy _
      simpa [tgt, step, z, c1, c2, rq3_or_disjoint_allwidth_tgtResult] using h
    have step_step_step_z_refines :
        step (step (step z)) ⊑ tgt := by
      have h :
          (let z : LLVM.IntWUB w := LLVM.IntWUB.value (0#w)
           let step : LLVM.IntWUB w → LLVM.IntWUB w := fun idx =>
             InstCombine.lift2 (fun x y => LLVM.or x y { «disjoint» := true }) c2
               (InstCombine.lift2 (fun x y => LLVM.or x y) idx c1)
           step (step (step z))) ⊑
            (InstCombine.lift2 (fun x y => LLVM.or x y)
              (InstCombine.lift2 (fun x y => LLVM.or x y)
                (InstCombine.lift2 (fun x y => LLVM.or x y) c1 c2)
                (InstCombine.lift2 (fun x y => LLVM.or x y) c1 c2))
              (InstCombine.lift2 (fun x y => LLVM.or x y) c1 c2)) := by
        dsimp
        cases c1 with
        | none => simp [InstCombine.lift2]
        | some s1 =>
            cases s1 with
            | poison =>
                cases c2 with
                | none => simp [InstCombine.lift2]
                | some s2 =>
                    cases s2 <;>
                      simp [InstCombine.lift2, LLVM.or, LLVM.or?, LLVM.SemVal.instMonad]
            | value a =>
                cases c2 with
                | none => simp [InstCombine.lift2]
                | some s2 =>
                    cases s2 with
                    | poison =>
                        simp [InstCombine.lift2, LLVM.or, LLVM.or?, LLVM.SemVal.instMonad]
                    | value b =>
                        by_cases h0 : b &&& a = 0#w
                        · by_cases h1 : b &&& ((b ||| a) ||| a) = 0#w
                          · by_cases h2 : b &&& ((b ||| ((b ||| a) ||| a)) ||| a) = 0#w
                            · simp [InstCombine.lift2, LLVM.or, LLVM.or?,
                                LLVM.SemVal.instMonad, h0, h1, h2]
                              apply ImmediateUBOr.IsRefinedBy.bothValues
                              rw [LLVM.IntW.isRefinedBy_iff]
                              rw [LLVM.SemVal.value_isRefinedBy_value]
                              rw [InstCombine.bv_isRefinedBy_iff]
                              ext i
                              simp [BitVec.getElem_or]
                              cases a[i] <;> cases b[i] <;> simp
                            · simp [InstCombine.lift2, LLVM.or, LLVM.or?,
                                LLVM.SemVal.instMonad, h0, h1, h2]
                              apply ImmediateUBOr.IsRefinedBy.bothValues
                              rw [LLVM.IntW.isRefinedBy_iff]
                              exact LLVM.SemVal.poison_isRefinedBy _
                          · simp [InstCombine.lift2, LLVM.or, LLVM.or?, LLVM.SemVal.instMonad,
                              h0, h1]
                            apply ImmediateUBOr.IsRefinedBy.bothValues
                            rw [LLVM.IntW.isRefinedBy_iff]
                            exact LLVM.SemVal.poison_isRefinedBy _
                        · simp [InstCombine.lift2, LLVM.or, LLVM.or?, LLVM.SemVal.instMonad, h0]
                          apply ImmediateUBOr.IsRefinedBy.bothValues
                          rw [LLVM.IntW.isRefinedBy_iff]
                          exact LLVM.SemVal.poison_isRefinedBy _
      simpa [tgt, step, z, c1, c2, rq3_or_disjoint_allwidth_tgtResult] using h
    have h12 : (1#w + 1#w : BitVec w) = 2#w := by
      rw [show (1#w : BitVec w) = BitVec.ofNat w 1 by rfl]
      rw [show (2#w : BitVec w) = BitVec.ofNat w 2 by rfl]
      rw [BitVec.ofNat_add_ofNat]
    have h23add : (2#w + 1#w : BitVec w) = 3#w := by
      rw [show (2#w : BitVec w) = BitVec.ofNat w 2 by rfl]
      rw [show (1#w : BitVec w) = BitVec.ofNat w 1 by rfl]
      rw [show (3#w : BitVec w) = BitVec.ofNat w 3 by rfl]
      rw [BitVec.ofNat_add_ofNat]
    intro s j1 j2 hinv
    cases j1 with
    | none =>
        simp [rq3_or_disjoint_allwidth_inv] at hinv
    | some j1v =>
        cases j1v with
        | poison =>
            simp [rq3_or_disjoint_allwidth_inv] at hinv
        | value k =>
            simp [rq3_or_disjoint_allwidth_inv] at hinv
            rcases hinv with hzero | hone | htwo
            · rcases hzero with ⟨rfl, rfl⟩
              by_cases hbr : BitVec.ofBool (1#w == 3#w) = 1#1
              · simp [rq3_or_disjoint_allwidth_src, rq3_or_disjoint_allwidth_srcBlocks, rq3_or_disjoint_allwidth_srcLoopTarget,
                  rq3_or_disjoint_allwidth_srcLoopVal, rq3_or_disjoint_allwidth_tgtResult, hbr,
                  LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                  LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.Expr.denoteWithMemory,
                  LLVMMemory.Op.denoteVec, DialectDenote.denote, DialectSignature.signature,
                  DialectSignature.effectKind, DialectSignature.returnTypes, DialectSignature.sig,
                  MOp.sig, MOp.outTy, EffectKind.liftEffect, InstCombine.Op.denote,
                  LLVM.const?, LLVM.add, LLVM.add?, LLVM.or, LLVM.or?, LLVM.icmp, LLVM.icmp?,
                  LLVM.icmp', LLVM.SemVal.instMonad, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                  LLVMMemory.CFGTerm.denoteWithMemoryFuelCore]
                cases fuel with
                | zero =>
                    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                | succ fuel =>
                    simp [LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                      LLVMMemory.CFGBlocks.findMemoryBlock?,
                      LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                      LLVMMemory.CFGTerm.denoteWithMemoryFuelCore]
                    apply ImmediateUBOr.IsRefinedBy.bothValues
                    constructor
                    · simpa [tgt, step, z, c1, c2, rq3_or_disjoint_allwidth_tgtResult, InstCombine.lift2,
                        LLVM.or, LLVM.or?, LLVM.SemVal.instMonad] using step_z_refines
                    · rfl
              · have h13 : (1#w : BitVec w) ≠ 3#w := by
                  intro h
                  apply hbr
                  simp [h]
                have hnew : (rq3_or_disjoint_allwidth_inv w) (LLVM.IntWUB.value (1#w)) (step z) V := by
                  simp [rq3_or_disjoint_allwidth_inv, step, z, c1, c2, h13]
                simp [rq3_or_disjoint_allwidth_src, rq3_or_disjoint_allwidth_srcBlocks, rq3_or_disjoint_allwidth_srcLoopTarget,
                  rq3_or_disjoint_allwidth_srcLoopVal, hbr,
                  LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                  LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.Expr.denoteWithMemory,
                  LLVMMemory.Op.denoteVec, DialectDenote.denote, DialectSignature.signature,
                  DialectSignature.effectKind, DialectSignature.returnTypes, DialectSignature.sig,
                  MOp.sig, MOp.outTy, EffectKind.liftEffect, InstCombine.Op.denote,
                  LLVM.const?, LLVM.add, LLVM.add?, LLVM.or, LLVM.or?, LLVM.icmp, LLVM.icmp?,
                  LLVM.icmp', LLVM.SemVal.instMonad, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                  LLVMMemory.CFGTerm.denoteWithMemoryFuelCore]
                change StateT.run
                    (ReaderT.run
                      (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (rq3_or_disjoint_allwidth_srcBlocks w)
                        V _ _)
                      ∅)
                    s ⊑ _
                rw [rq3_or_disjoint_allwidth_src_loop_dispatch]
                simpa [rq3_or_disjoint_allwidth_src, rq3_or_disjoint_allwidth_srcBlocks, rq3_or_disjoint_allwidth_srcLoopTarget,
                  rq3_or_disjoint_allwidth_srcLoopVal, step, z, c1, c2, InstCombine.lift2, LLVM.or,
                  LLVM.or?, LLVM.SemVal.instMonad] using
                  ih s (LLVM.IntWUB.value (1#w)) (step z) hnew
            · rcases hone with ⟨rfl, h13, hj2⟩
              by_cases hbr : BitVec.ofBool (1#w + 1#w == 3#w) = 1#1
              · simp [rq3_or_disjoint_allwidth_src, rq3_or_disjoint_allwidth_srcBlocks, rq3_or_disjoint_allwidth_srcLoopTarget,
                  rq3_or_disjoint_allwidth_srcLoopVal, rq3_or_disjoint_allwidth_tgtResult, hj2, hbr,
                  LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                  LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.Expr.denoteWithMemory,
                  LLVMMemory.Op.denoteVec, DialectDenote.denote, DialectSignature.signature,
                  DialectSignature.effectKind, DialectSignature.returnTypes, DialectSignature.sig,
                  MOp.sig, MOp.outTy, EffectKind.liftEffect, InstCombine.Op.denote,
                  LLVM.const?, LLVM.add, LLVM.add?, LLVM.or, LLVM.or?, LLVM.icmp, LLVM.icmp?,
                  LLVM.icmp', LLVM.SemVal.instMonad, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                  LLVMMemory.CFGTerm.denoteWithMemoryFuelCore]
                cases fuel with
                | zero =>
                    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                | succ fuel =>
                    simp [LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                      LLVMMemory.CFGBlocks.findMemoryBlock?,
                      LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                      LLVMMemory.CFGTerm.denoteWithMemoryFuelCore]
                    apply ImmediateUBOr.IsRefinedBy.bothValues
                    constructor
                    · simpa [tgt, step, z, c1, c2, rq3_or_disjoint_allwidth_tgtResult, InstCombine.lift2,
                        LLVM.or, LLVM.or?, LLVM.SemVal.instMonad] using step_step_z_refines
                    · rfl
              · have h23 : (2#w : BitVec w) ≠ 3#w := by
                  intro h
                  apply hbr
                  simp [h12, h]
                have hnew :
                    (rq3_or_disjoint_allwidth_inv w) (LLVM.IntWUB.value (1#w + 1#w)) (step (step z)) V := by
                  simp [rq3_or_disjoint_allwidth_inv, step, z, c1, c2, h12, h13, h23]
                simp [rq3_or_disjoint_allwidth_src, rq3_or_disjoint_allwidth_srcBlocks, rq3_or_disjoint_allwidth_srcLoopTarget,
                  rq3_or_disjoint_allwidth_srcLoopVal, hj2, hbr,
                  LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                  LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.Expr.denoteWithMemory,
                  LLVMMemory.Op.denoteVec, DialectDenote.denote, DialectSignature.signature,
                  DialectSignature.effectKind, DialectSignature.returnTypes, DialectSignature.sig,
                  MOp.sig, MOp.outTy, EffectKind.liftEffect, InstCombine.Op.denote,
                  LLVM.const?, LLVM.add, LLVM.add?, LLVM.or, LLVM.or?, LLVM.icmp, LLVM.icmp?,
                  LLVM.icmp', LLVM.SemVal.instMonad, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                  LLVMMemory.CFGTerm.denoteWithMemoryFuelCore]
                change StateT.run
                    (ReaderT.run
                      (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (rq3_or_disjoint_allwidth_srcBlocks w)
                        V _ _)
                      ∅)
                    s ⊑ _
                rw [rq3_or_disjoint_allwidth_src_loop_dispatch]
                simpa [rq3_or_disjoint_allwidth_src, rq3_or_disjoint_allwidth_srcBlocks, rq3_or_disjoint_allwidth_srcLoopTarget,
                  rq3_or_disjoint_allwidth_srcLoopVal, step, z, c1, c2, InstCombine.lift2, LLVM.or,
                  LLVM.or?, LLVM.SemVal.instMonad] using
                  ih s (LLVM.IntWUB.value (1#w + 1#w)) (step (step z)) hnew
            · rcases htwo with ⟨rfl, h13, h23, hj2⟩
              simp [rq3_or_disjoint_allwidth_src, rq3_or_disjoint_allwidth_srcBlocks, rq3_or_disjoint_allwidth_srcLoopTarget,
                rq3_or_disjoint_allwidth_srcLoopVal, rq3_or_disjoint_allwidth_tgtResult, hj2, h23add,
                LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
                LLVMMemory.Expr.denoteWithMemory, LLVMMemory.Op.denoteVec,
                DialectDenote.denote, DialectSignature.signature, DialectSignature.effectKind,
                DialectSignature.returnTypes, DialectSignature.sig, MOp.sig, MOp.outTy,
                EffectKind.liftEffect, InstCombine.Op.denote, LLVM.const?, LLVM.add, LLVM.add?,
                LLVM.or, LLVM.or?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.SemVal.instMonad,
                LLVMMemory.CFGBody.denoteWithMemoryFuelCore, LLVMMemory.CFGTerm.denoteWithMemoryFuelCore] at hj2 ⊢
              cases fuel with
              | zero =>
                  exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
              | succ fuel =>
                  simp [LLVMMemory.CFGTarget.denoteWithMemoryFuel,
                    LLVMMemory.CFGBlocks.findMemoryBlock?,
                    LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
                    LLVMMemory.CFGTerm.denoteWithMemoryFuelCore]
                  apply ImmediateUBOr.IsRefinedBy.bothValues
                  constructor
                  · simpa [tgt, step, z, c1, c2, rq3_or_disjoint_allwidth_tgtResult, InstCombine.lift2,
                      LLVM.or, LLVM.or?, LLVM.SemVal.instMonad] using step_step_step_z_refines
                  · rfl

private theorem rq3_or_disjoint_allwidth_loop_refine (w : Nat) (V : Ctxt.Valuation (rq3_or_disjoint_allwidth_ctx w)) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (rq3_or_disjoint_allwidth_ity w)),
      (rq3_or_disjoint_allwidth_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (rq3_or_disjoint_allwidth_srcBlocks w) V
              ((rq3_or_disjoint_allwidth_srcLoopVal w) j1 j2) (rq3_or_disjoint_allwidth_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((rq3_or_disjoint_allwidth_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(rq3_or_disjoint_allwidth_ity w)] × LLVMMemory.State)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s j1 j2 _hinv
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact (rq3_or_disjoint_allwidth_step w) V fuel ih

theorem rq3_or_disjoint_allwidth_correct (w : Nat) :
    IsRefinedByOnIntWInputsWithMemory (rq3_or_disjoint_allwidth_src w) ((rq3_or_disjoint_allwidth_tgt w).castPureToEff .impure) := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>

      let VL : Ctxt.Valuation (rq3_or_disjoint_allwidth_ctx w) := InputValuation.lift V
      have hinit : (rq3_or_disjoint_allwidth_inv w) (LLVM.IntWUB.value (0#w)) (LLVM.IntWUB.value (0#w)) VL := by
        simp [rq3_or_disjoint_allwidth_inv, VL]
      simp [rq3_or_disjoint_allwidth_src, rq3_or_disjoint_allwidth_tgt, LLVMMemory.Com.denoteWithMemoryFuel,
        LLVMMemory.Com.denoteWithMemoryFuelIn_eq, LLVMMemory.Com.denoteWithMemoryCore,
        LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
        LLVMMemory.Expr.denoteWithMemory, LLVMMemory.Op.denoteVec, DialectDenote.denote,
        DialectSignature.signature, DialectSignature.effectKind, DialectSignature.returnTypes,
        DialectSignature.sig, MOp.sig, MOp.outTy, EffectKind.liftEffect, InstCombine.Op.denote,
        LLVM.const?, LLVM.or, LLVM.or?, LLVM.SemVal.instMonad,
        LLVMMemory.CFGBody.denoteWithMemoryFuelCore, LLVMMemory.CFGTerm.denoteWithMemoryFuelCore]
      change StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (rq3_or_disjoint_allwidth_srcBlocks w) VL _ _)
            ∅)
          s ⊑ _
      rw [rq3_or_disjoint_allwidth_src_loop_dispatch]
      simpa [rq3_or_disjoint_allwidth_src, rq3_or_disjoint_allwidth_srcBlocks, rq3_or_disjoint_allwidth_srcLoopTarget,
        rq3_or_disjoint_allwidth_srcLoopVal, VL] using
        rq3_or_disjoint_allwidth_loop_refine w VL fuel s (LLVM.IntWUB.value (0#w)) (LLVM.IntWUB.value (0#w)) hinit

end TestLoop
end InstCombine

namespace InstCombine
namespace TestLoop

def licm_exitvalue_or_disjoint_dropped_src :=
  [llvm()| {
  llvm.func @licm_exitvalue_or_disjoint_dropped_src(%c1 : i64, %c2 : i64) -> i64 {
  ^entry(%c1 : i64, %c2 : i64):
    %e_zero = llvm.mlir.constant 0 : i64
    %e_start = llvm.mlir.constant 0 : i64
    llvm.br ^loop(%e_zero : i64, %e_start : i64)
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

def licm_exitvalue_or_disjoint_dropped_tgt :=
  [llvm()| {
  llvm.func @licm_exitvalue_or_disjoint_dropped_tgt(%c1 : i64, %c2 : i64) -> i64 {
  ^entry(%c1 : i64, %c2 : i64):
    %invariant_op = llvm.or %c1, %c2 : i64
    %s2 = llvm.or %invariant_op, %invariant_op : i64
    %s3 = llvm.or %s2, %invariant_op : i64
    llvm.return %s3 : i64
  }
  }]

theorem licm_exitvalue_or_disjoint_dropped_src_matches :
    licm_exitvalue_or_disjoint_dropped_src = rq3_or_disjoint_allwidth_src 64 := by
  rfl

theorem licm_exitvalue_or_disjoint_dropped_tgt_matches :
    licm_exitvalue_or_disjoint_dropped_tgt = rq3_or_disjoint_allwidth_tgt 64 := by
  rfl

theorem licm_exitvalue_or_disjoint_dropped_correct :
    IsRefinedByOnIntWInputsWithMemory licm_exitvalue_or_disjoint_dropped_src
      (licm_exitvalue_or_disjoint_dropped_tgt.castPureToEff .impure) := by
  exact rq3_or_disjoint_allwidth_correct 64

#print axioms licm_exitvalue_or_disjoint_dropped_correct

end TestLoop
end InstCombine
