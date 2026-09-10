import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace InstCombine
namespace TestLoop

def licm_exitvalue_or_disjoint_dropped_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @licm_exitvalue_or_disjoint_dropped_src(%c1 : _, %c2 : _) -> _ {
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

def licm_exitvalue_or_disjoint_dropped_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @licm_exitvalue_or_disjoint_dropped_tgt(%c1 : _, %c2 : _) -> _ {
  ^entry(%c1 : _, %c2 : _):
    %invariant_op = llvm.or %c1, %c2 : _
    %s2 = llvm.or %invariant_op, %invariant_op : _
    %s3 = llvm.or %s2, %invariant_op : _
    llvm.return %s3 : _
  }
  }]

private abbrev licm_exitvalue_or_disjoint_dropped_ity (w : Nat) : LLVM.Ty := LLVM.Ty.bitvec w

private abbrev licm_exitvalue_or_disjoint_dropped_ctx (w : Nat) : Ctxt LLVM.Ty := Ctxt.ofList [(licm_exitvalue_or_disjoint_dropped_ity w), (licm_exitvalue_or_disjoint_dropped_ity w)]

private def licm_exitvalue_or_disjoint_dropped_srcBlocks (w : Nat) : CFGBlocks LLVM (licm_exitvalue_or_disjoint_dropped_ctx w) .impure [(licm_exitvalue_or_disjoint_dropped_ity w)] :=
  match (licm_exitvalue_or_disjoint_dropped_src w) with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private theorem licm_exitvalue_or_disjoint_dropped_entry_ne_loop (w : Nat) : ¬ ("entry" = "loop") := by
  decide

private theorem licm_exitvalue_or_disjoint_dropped_out_ne_loop (w : Nat) : ¬ ("out" = "loop") := by
  decide

private def licm_exitvalue_or_disjoint_dropped_srcLoopTarget (w : Nat) : CFGTarget LLVM (Ctxt.ofList [(licm_exitvalue_or_disjoint_dropped_ity w), (licm_exitvalue_or_disjoint_dropped_ity w)]) where
  name := "loop"
  argTys := [(licm_exitvalue_or_disjoint_dropped_ity w), (licm_exitvalue_or_disjoint_dropped_ity w)]
  args := (⟨0, by rfl⟩ : (Ctxt.ofList [(licm_exitvalue_or_disjoint_dropped_ity w), (licm_exitvalue_or_disjoint_dropped_ity w)]).Var (licm_exitvalue_or_disjoint_dropped_ity w)) ::ₕ (⟨1, by rfl⟩ : (Ctxt.ofList [(licm_exitvalue_or_disjoint_dropped_ity w), (licm_exitvalue_or_disjoint_dropped_ity w)]).Var (licm_exitvalue_or_disjoint_dropped_ity w)) ::ₕ HVector.nil

private def licm_exitvalue_or_disjoint_dropped_srcLoopVal (w : Nat) (j1 j2 : TyDenote.toType (licm_exitvalue_or_disjoint_dropped_ity w)) :
    Ctxt.Valuation (Ctxt.ofList [(licm_exitvalue_or_disjoint_dropped_ity w), (licm_exitvalue_or_disjoint_dropped_ity w)]) :=
  Ctxt.Valuation.ofHVector (j1 ::ₕ j2 ::ₕ HVector.nil)

private theorem licm_exitvalue_or_disjoint_dropped_src_loop_dispatch (w : Nat)
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation (licm_exitvalue_or_disjoint_dropped_ctx w)) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a1 a2 : Γcur.Var (licm_exitvalue_or_disjoint_dropped_ity w)) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (licm_exitvalue_or_disjoint_dropped_srcBlocks w) V W
            ({ name := "loop", argTys := [(licm_exitvalue_or_disjoint_dropped_ity w), (licm_exitvalue_or_disjoint_dropped_ity w)], args := a1 ::ₕ a2 ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (licm_exitvalue_or_disjoint_dropped_srcBlocks w) V
            ((licm_exitvalue_or_disjoint_dropped_srcLoopVal w) (W a1) (W a2)) (licm_exitvalue_or_disjoint_dropped_srcLoopTarget w))
          ∅)
        s := by
  cases fuel <;>
    simp [licm_exitvalue_or_disjoint_dropped_src, licm_exitvalue_or_disjoint_dropped_srcBlocks, licm_exitvalue_or_disjoint_dropped_srcLoopTarget, licm_exitvalue_or_disjoint_dropped_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

private def licm_exitvalue_or_disjoint_dropped_tgtResult (w : Nat) (V : Ctxt.Valuation (licm_exitvalue_or_disjoint_dropped_ctx w)) : TyDenote.toType (licm_exitvalue_or_disjoint_dropped_ity w) :=
  (InstCombine.lift2 (fun x y => LLVM.or x y) (InstCombine.lift2 (fun x y => LLVM.or x y) (InstCombine.lift2 (fun x y => LLVM.or x y) (V ((⟨1, by rfl⟩ : (licm_exitvalue_or_disjoint_dropped_ctx w).Var (licm_exitvalue_or_disjoint_dropped_ity w)))) (V (Ctxt.Var.last (Ctxt.ofList [(licm_exitvalue_or_disjoint_dropped_ity w)]) (licm_exitvalue_or_disjoint_dropped_ity w)))) (InstCombine.lift2 (fun x y => LLVM.or x y) (V ((⟨1, by rfl⟩ : (licm_exitvalue_or_disjoint_dropped_ctx w).Var (licm_exitvalue_or_disjoint_dropped_ity w)))) (V (Ctxt.Var.last (Ctxt.ofList [(licm_exitvalue_or_disjoint_dropped_ity w)]) (licm_exitvalue_or_disjoint_dropped_ity w))))) (InstCombine.lift2 (fun x y => LLVM.or x y) (V ((⟨1, by rfl⟩ : (licm_exitvalue_or_disjoint_dropped_ctx w).Var (licm_exitvalue_or_disjoint_dropped_ity w)))) (V (Ctxt.Var.last (Ctxt.ofList [(licm_exitvalue_or_disjoint_dropped_ity w)]) (licm_exitvalue_or_disjoint_dropped_ity w)))))

private def licm_exitvalue_or_disjoint_dropped_inv (w : Nat) (j1 j2 : TyDenote.toType (licm_exitvalue_or_disjoint_dropped_ity w))
    (V : Ctxt.Valuation (licm_exitvalue_or_disjoint_dropped_ctx w)) : Prop :=
  let z : LLVM.IntWUB w := LLVM.IntWUB.value (0#w)
  let c1 : LLVM.IntWUB w :=
    V ((⟨1, by rfl⟩ : (licm_exitvalue_or_disjoint_dropped_ctx w).Var (licm_exitvalue_or_disjoint_dropped_ity w)))
  let c2 : LLVM.IntWUB w :=
    V (Ctxt.Var.last (Ctxt.ofList [(licm_exitvalue_or_disjoint_dropped_ity w)]) (licm_exitvalue_or_disjoint_dropped_ity w))
  let step : LLVM.IntWUB w → LLVM.IntWUB w := fun idx =>
    InstCombine.lift2 (fun x y => LLVM.or x y { «disjoint» := true }) c2
      (InstCombine.lift2 (fun x y => LLVM.or x y) idx c1)
  match j1 with
  | .some (.value k) =>
      (k = 0#w ∧ j2 = z) ∨
        (k = 1#w ∧ 1#w ≠ 3#w ∧ j2 = step z) ∨
        (k = 2#w ∧ 1#w ≠ 3#w ∧ 2#w ≠ 3#w ∧ j2 = step (step z))
  | _ => False

private theorem licm_exitvalue_or_disjoint_dropped_step (w : Nat) (V : Ctxt.Valuation (licm_exitvalue_or_disjoint_dropped_ctx w)) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (licm_exitvalue_or_disjoint_dropped_ity w)),
      (licm_exitvalue_or_disjoint_dropped_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (licm_exitvalue_or_disjoint_dropped_srcBlocks w) V
              ((licm_exitvalue_or_disjoint_dropped_srcLoopVal w) j1 j2) (licm_exitvalue_or_disjoint_dropped_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((licm_exitvalue_or_disjoint_dropped_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(licm_exitvalue_or_disjoint_dropped_ity w)] × LLVMMemory.State))) :
    ∀ (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (licm_exitvalue_or_disjoint_dropped_ity w)),
      (licm_exitvalue_or_disjoint_dropped_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel (fuel + 1) (licm_exitvalue_or_disjoint_dropped_srcBlocks w) V
              ((licm_exitvalue_or_disjoint_dropped_srcLoopVal w) j1 j2) (licm_exitvalue_or_disjoint_dropped_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((licm_exitvalue_or_disjoint_dropped_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(licm_exitvalue_or_disjoint_dropped_ity w)] × LLVMMemory.State)) :=
  by
    let c1 : LLVM.IntWUB w :=
      V ((⟨1, by rfl⟩ : (licm_exitvalue_or_disjoint_dropped_ctx w).Var (licm_exitvalue_or_disjoint_dropped_ity w)))
    let c2 : LLVM.IntWUB w :=
      V (Ctxt.Var.last (Ctxt.ofList [(licm_exitvalue_or_disjoint_dropped_ity w)]) (licm_exitvalue_or_disjoint_dropped_ity w))
    let z : LLVM.IntWUB w := LLVM.IntWUB.value (0#w)
    let step : LLVM.IntWUB w → LLVM.IntWUB w := fun idx =>
      InstCombine.lift2 (fun x y => LLVM.or x y { «disjoint» := true }) c2
        (InstCombine.lift2 (fun x y => LLVM.or x y) idx c1)
    let tgt : LLVM.IntWUB w := (licm_exitvalue_or_disjoint_dropped_tgtResult w) V
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
      simpa [tgt, step, z, c1, c2, licm_exitvalue_or_disjoint_dropped_tgtResult] using h
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
      simpa [tgt, step, z, c1, c2, licm_exitvalue_or_disjoint_dropped_tgtResult] using h
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
      simpa [tgt, step, z, c1, c2, licm_exitvalue_or_disjoint_dropped_tgtResult] using h
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
        simp [licm_exitvalue_or_disjoint_dropped_inv] at hinv
    | some j1v =>
        cases j1v with
        | poison =>
            simp [licm_exitvalue_or_disjoint_dropped_inv] at hinv
        | value k =>
            simp [licm_exitvalue_or_disjoint_dropped_inv] at hinv
            rcases hinv with hzero | hone | htwo
            · rcases hzero with ⟨rfl, rfl⟩
              by_cases hbr : BitVec.ofBool (1#w == 3#w) = 1#1
              · simp [licm_exitvalue_or_disjoint_dropped_src, licm_exitvalue_or_disjoint_dropped_srcBlocks, licm_exitvalue_or_disjoint_dropped_srcLoopTarget,
                  licm_exitvalue_or_disjoint_dropped_srcLoopVal, licm_exitvalue_or_disjoint_dropped_tgtResult, hbr,
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
                    · simpa [tgt, step, z, c1, c2, licm_exitvalue_or_disjoint_dropped_tgtResult, InstCombine.lift2,
                        LLVM.or, LLVM.or?, LLVM.SemVal.instMonad] using step_z_refines
                    · rfl
              · have h13 : (1#w : BitVec w) ≠ 3#w := by
                  intro h
                  apply hbr
                  simp [h]
                have hnew : (licm_exitvalue_or_disjoint_dropped_inv w) (LLVM.IntWUB.value (1#w)) (step z) V := by
                  simp [licm_exitvalue_or_disjoint_dropped_inv, step, z, c1, c2, h13]
                simp [licm_exitvalue_or_disjoint_dropped_src, licm_exitvalue_or_disjoint_dropped_srcBlocks, licm_exitvalue_or_disjoint_dropped_srcLoopTarget,
                  licm_exitvalue_or_disjoint_dropped_srcLoopVal, hbr,
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
                      (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (licm_exitvalue_or_disjoint_dropped_srcBlocks w)
                        V _ _)
                      ∅)
                    s ⊑ _
                rw [licm_exitvalue_or_disjoint_dropped_src_loop_dispatch]
                simpa [licm_exitvalue_or_disjoint_dropped_src, licm_exitvalue_or_disjoint_dropped_srcBlocks, licm_exitvalue_or_disjoint_dropped_srcLoopTarget,
                  licm_exitvalue_or_disjoint_dropped_srcLoopVal, step, z, c1, c2, InstCombine.lift2, LLVM.or,
                  LLVM.or?, LLVM.SemVal.instMonad] using
                  ih s (LLVM.IntWUB.value (1#w)) (step z) hnew
            · rcases hone with ⟨rfl, h13, hj2⟩
              by_cases hbr : BitVec.ofBool (1#w + 1#w == 3#w) = 1#1
              · simp [licm_exitvalue_or_disjoint_dropped_src, licm_exitvalue_or_disjoint_dropped_srcBlocks, licm_exitvalue_or_disjoint_dropped_srcLoopTarget,
                  licm_exitvalue_or_disjoint_dropped_srcLoopVal, licm_exitvalue_or_disjoint_dropped_tgtResult, hj2, hbr,
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
                    · simpa [tgt, step, z, c1, c2, licm_exitvalue_or_disjoint_dropped_tgtResult, InstCombine.lift2,
                        LLVM.or, LLVM.or?, LLVM.SemVal.instMonad] using step_step_z_refines
                    · rfl
              · have h23 : (2#w : BitVec w) ≠ 3#w := by
                  intro h
                  apply hbr
                  simp [h12, h]
                have hnew :
                    (licm_exitvalue_or_disjoint_dropped_inv w) (LLVM.IntWUB.value (1#w + 1#w)) (step (step z)) V := by
                  simp [licm_exitvalue_or_disjoint_dropped_inv, step, z, c1, c2, h12, h13, h23]
                simp [licm_exitvalue_or_disjoint_dropped_src, licm_exitvalue_or_disjoint_dropped_srcBlocks, licm_exitvalue_or_disjoint_dropped_srcLoopTarget,
                  licm_exitvalue_or_disjoint_dropped_srcLoopVal, hj2, hbr,
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
                      (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (licm_exitvalue_or_disjoint_dropped_srcBlocks w)
                        V _ _)
                      ∅)
                    s ⊑ _
                rw [licm_exitvalue_or_disjoint_dropped_src_loop_dispatch]
                simpa [licm_exitvalue_or_disjoint_dropped_src, licm_exitvalue_or_disjoint_dropped_srcBlocks, licm_exitvalue_or_disjoint_dropped_srcLoopTarget,
                  licm_exitvalue_or_disjoint_dropped_srcLoopVal, step, z, c1, c2, InstCombine.lift2, LLVM.or,
                  LLVM.or?, LLVM.SemVal.instMonad] using
                  ih s (LLVM.IntWUB.value (1#w + 1#w)) (step (step z)) hnew
            · rcases htwo with ⟨rfl, h13, h23, hj2⟩
              simp [licm_exitvalue_or_disjoint_dropped_src, licm_exitvalue_or_disjoint_dropped_srcBlocks, licm_exitvalue_or_disjoint_dropped_srcLoopTarget,
                licm_exitvalue_or_disjoint_dropped_srcLoopVal, licm_exitvalue_or_disjoint_dropped_tgtResult, hj2, h23add,
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
                  · simpa [tgt, step, z, c1, c2, licm_exitvalue_or_disjoint_dropped_tgtResult, InstCombine.lift2,
                      LLVM.or, LLVM.or?, LLVM.SemVal.instMonad] using step_step_step_z_refines
                  · rfl

private theorem licm_exitvalue_or_disjoint_dropped_loop_refine (w : Nat) (V : Ctxt.Valuation (licm_exitvalue_or_disjoint_dropped_ctx w)) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) (j1 j2 : TyDenote.toType (licm_exitvalue_or_disjoint_dropped_ity w)),
      (licm_exitvalue_or_disjoint_dropped_inv w) j1 j2 V →
      StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (licm_exitvalue_or_disjoint_dropped_srcBlocks w) V
              ((licm_exitvalue_or_disjoint_dropped_srcLoopVal w) j1 j2) (licm_exitvalue_or_disjoint_dropped_srcLoopTarget w))
            ∅)
          s
        ⊑
        (some ((licm_exitvalue_or_disjoint_dropped_tgtResult w) V ::ₕ HVector.nil, s) :
          ImmediateUBOr (HVector TyDenote.toType [(licm_exitvalue_or_disjoint_dropped_ity w)] × LLVMMemory.State)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s j1 j2 _hinv
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact (licm_exitvalue_or_disjoint_dropped_step w) V fuel ih

theorem licm_exitvalue_or_disjoint_dropped_correct (w : Nat) :
    IsRefinedByOnIntWInputsWithMemory (licm_exitvalue_or_disjoint_dropped_src w) ((licm_exitvalue_or_disjoint_dropped_tgt w).castPureToEff .impure) := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>

      let VL : Ctxt.Valuation (licm_exitvalue_or_disjoint_dropped_ctx w) := InputValuation.lift V
      have hinit : (licm_exitvalue_or_disjoint_dropped_inv w) (LLVM.IntWUB.value (0#w)) (LLVM.IntWUB.value (0#w)) VL := by
        simp [licm_exitvalue_or_disjoint_dropped_inv, VL]
      simp [licm_exitvalue_or_disjoint_dropped_src, licm_exitvalue_or_disjoint_dropped_tgt, LLVMMemory.Com.denoteWithMemoryFuel,
        LLVMMemory.Com.denoteWithMemoryFuelIn_eq, LLVMMemory.Com.denoteWithMemoryCore,
        LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
        LLVMMemory.Expr.denoteWithMemory, LLVMMemory.Op.denoteVec, DialectDenote.denote,
        DialectSignature.signature, DialectSignature.effectKind, DialectSignature.returnTypes,
        DialectSignature.sig, MOp.sig, MOp.outTy, EffectKind.liftEffect, InstCombine.Op.denote,
        LLVM.const?, LLVM.or, LLVM.or?, LLVM.SemVal.instMonad,
        LLVMMemory.CFGBody.denoteWithMemoryFuelCore, LLVMMemory.CFGTerm.denoteWithMemoryFuelCore]
      change StateT.run
          (ReaderT.run
            (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel (licm_exitvalue_or_disjoint_dropped_srcBlocks w) VL _ _)
            ∅)
          s ⊑ _
      rw [licm_exitvalue_or_disjoint_dropped_src_loop_dispatch]
      simpa [licm_exitvalue_or_disjoint_dropped_src, licm_exitvalue_or_disjoint_dropped_srcBlocks, licm_exitvalue_or_disjoint_dropped_srcLoopTarget,
        licm_exitvalue_or_disjoint_dropped_srcLoopVal, VL] using
        licm_exitvalue_or_disjoint_dropped_loop_refine w VL fuel s (LLVM.IntWUB.value (0#w)) (LLVM.IntWUB.value (0#w)) hinit

end TestLoop
end InstCombine
