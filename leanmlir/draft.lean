
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import SSA.Projects.InstCombine.MemoryTactic
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.InstCombine.TacticAuto
import LeanMLIR.Dialects.LLVM.Syntax
import SSA.Projects.InstCombine.ForLean

namespace InstCombine
namespace TestLoop

namespace IndVarTrueSemantics

open InstCombine.LLVMMemory

private abbrev RetTy := HVector TyDenote.toType [LLVM.Ty.bitvec 32]

private def ret0 : RetTy :=
  (LLVM.IntWUB.value (0#32)) ::ₕ HVector.nil

private def sextUB {w : Nat} (w' : Nat) (x : LLVM.IntWUB w) : LLVM.IntWUB w' := do
  let x' ← x
  pure (LLVM.sext w' x')

private def addUB {w : Nat} (x y : LLVM.IntWUB w) : LLVM.IntWUB w := do
  let x' ← x
  let y' ← y
  pure (LLVM.add x' y')

private def icmpUB {w : Nat} (p : LLVM.IntPred) (x y : LLVM.IntWUB w) : LLVM.IntWUB 1 := do
  let x' ← x
  let y' ← y
  pure (LLVM.icmp p x' y')

private def throwRet : LLVMMemory.M RetTy :=
  LLVMMemory.throwUB

private def exitTarget : Nat → LLVMMemory.M RetTy
  | 0 => throwRet
  | _ + 1 => pure ret0

def srcLoopTarget : Nat → LLVMMemory.PtrValUB → LLVM.IntWUB 32 → LLVM.IntWUB 32 →
    LLVMMemory.M RetTy
  | 0, _, _, _ => throwRet
  | fuel + 1, base, limit, iv => do
      let p := LLVMMemory.gep 8 base (sextUB 64 iv)
      let _ ← LLVMMemory.store p (LLVM.IntWUB.value (0#8))
      let ivNext := addUB iv (LLVM.IntWUB.value (1#32))
      let cond := icmpUB LLVM.IntPred.sgt limit iv
      match cond with
      | .none => LLVMMemory.throwUB
      | .some .poison => LLVMMemory.throwUB
      | .some (.value c) =>
          if c == 1#1 then
            srcLoopTarget fuel base limit ivNext
          else
            exitTarget fuel

def tgtLoopTarget : Nat → LLVMMemory.PtrValUB → LLVM.IntWUB 64 → LLVM.IntWUB 64 →
    LLVMMemory.M RetTy
  | 0, _, _, _ => throwRet
  | fuel + 1, base, limit64, iv64 => do
      let p := LLVMMemory.gep 8 base iv64
      let _ ← LLVMMemory.store p (LLVM.IntWUB.value (0#8))
      let ivNext := addUB iv64 (LLVM.IntWUB.value (1#64))
      let cond := icmpUB LLVM.IntPred.sgt limit64 iv64
      match cond with
      | .none => LLVMMemory.throwUB
      | .some .poison => LLVMMemory.throwUB
      | .some (.value c) =>
          if c == 1#1 then
            tgtLoopTarget fuel base limit64 ivNext
          else
            exitTarget fuel

def srcEntryTarget (fuel : Nat) (base : LLVMMemory.PtrValUB) (limit : LLVM.IntWUB 32) :
    LLVMMemory.M RetTy :=
  match fuel with
  | 0 => throwRet
  | fuel + 1 => srcLoopTarget fuel base limit (LLVM.IntWUB.value (0#32))

def tgtEntryTarget (fuel : Nat) (base : LLVMMemory.PtrValUB) (limit : LLVM.IntWUB 32) :
    LLVMMemory.M RetTy :=
  match fuel with
  | 0 => throwRet
  | fuel + 1 =>
      tgtLoopTarget fuel base (sextUB 64 limit) (LLVM.IntWUB.value (0#64))

private lemma slt_signExtend64_eq (x y : BitVec 32) :
    (BitVec.signExtend 64 x <ₛ BitVec.signExtend 64 y) = (x <ₛ y) := by
  simp [BitVec.slt]
  rw [BitVec.toInt_signExtend_of_le (x := x) (v := 64) (by omega)]
  rw [BitVec.toInt_signExtend_of_le (x := y) (v := 64) (by omega)]

private lemma signExtend64_add_one_of_sgt {limit iv : BitVec 32}
    (h : iv <ₛ limit) :
    BitVec.signExtend 64 (iv + 1#32) = BitVec.signExtend 64 iv + 1#64 := by
  bv_decide

theorem src_tgt_loopTarget_eq (fuel : Nat) (base : LLVMMemory.PtrValUB)
    (limit iv : LLVM.IntWUB 32) (s : LLVMMemory.State) :
    (srcLoopTarget fuel base limit iv).run s =
      (tgtLoopTarget fuel base (sextUB 64 limit) (sextUB 64 iv)).run s := by
  induction fuel generalizing base limit iv s with
  | zero =>
      simp [srcLoopTarget, tgtLoopTarget, throwRet, LLVMMemory.throwUB]
  | succ fuel ih =>
      cases limit with
      | none =>
          simp [srcLoopTarget, tgtLoopTarget, sextUB, icmpUB, LLVM.sext,
            LLVM.sext?, LLVM.icmp, LLVM.icmp?, LLVMMemory.throwUB]
      | some limitv =>
          cases limitv with
          | poison =>
              cases iv with
              | none =>
                  simp [srcLoopTarget, tgtLoopTarget, sextUB, icmpUB, LLVM.sext,
                    LLVM.sext?, LLVM.icmp, LLVM.icmp?, LLVMMemory.gep,
                    LLVMMemory.gepOffset, LLVMMemory.gepNormalizeIdx, LLVMMemory.throwUB]
              | some ivv =>
                  cases ivv with
                  | poison =>
                      simp [srcLoopTarget, tgtLoopTarget, sextUB, icmpUB, LLVM.sext,
                        LLVM.sext?, LLVM.icmp, LLVM.icmp?, LLVMMemory.gep,
                        LLVMMemory.gepOffset, LLVMMemory.gepNormalizeIdx, LLVMMemory.throwUB]
                  | value ivbv =>
                      simp [srcLoopTarget, tgtLoopTarget, sextUB, icmpUB, LLVM.sext,
                        LLVM.sext?, LLVM.icmp, LLVM.icmp?, LLVMMemory.throwUB]
          | value limitbv =>
              cases iv with
              | none =>
                  simp [srcLoopTarget, tgtLoopTarget, sextUB, icmpUB, LLVM.sext,
                    LLVM.sext?, LLVM.icmp, LLVM.icmp?, LLVMMemory.gep,
                    LLVMMemory.gepOffset, LLVMMemory.gepNormalizeIdx, LLVMMemory.throwUB]
              | some ivv =>
                  cases ivv with
                  | poison =>
                      simp [srcLoopTarget, tgtLoopTarget, sextUB, icmpUB, LLVM.sext,
                        LLVM.sext?, LLVM.icmp, LLVM.icmp?, LLVMMemory.gep,
                        LLVMMemory.gepOffset, LLVMMemory.gepNormalizeIdx, LLVMMemory.throwUB]
                  | value ivbv =>
                      simp [srcLoopTarget, tgtLoopTarget, sextUB, addUB, icmpUB,
                        LLVM.sext, LLVM.sext?, LLVM.add, LLVM.add?, LLVM.icmp,
                        LLVM.icmp?, LLVM.icmp']
                      cases hstore :
                          StateT.run
                            (LLVMMemory.store
                              (LLVMMemory.gep 8 base
                                (some (LLVM.SemVal.value (BitVec.signExtend 64 ivbv))))
                              (some (LLVM.SemVal.value (0#8)))) s with
                      | none =>
                          simp
                      | some ps =>
                          rcases ps with ⟨_, s'⟩
                          by_cases hlt : (ivbv <ₛ limitbv) = true
                          · have hone : BitVec.ofBool (ivbv <ₛ limitbv) = 1#1 :=
                              (BitVec.ofBool_eq_one_iff _).mpr hlt
                            have hlt64 :
                                (BitVec.signExtend 64 ivbv <ₛ
                                  BitVec.signExtend 64 limitbv) = true := by
                              simpa [slt_signExtend64_eq] using hlt
                            have hone64 :
                                BitVec.ofBool
                                  (BitVec.signExtend 64 ivbv <ₛ
                                    BitVec.signExtend 64 limitbv) = 1#1 :=
                              (BitVec.ofBool_eq_one_iff _).mpr hlt64
                            have hnext :=
                              signExtend64_add_one_of_sgt (limit := limitbv) (iv := ivbv) hlt
                            simp [hone, hone64]
                            simpa [sextUB, LLVM.sext, LLVM.sext?, hnext] using
                              ih base (LLVM.IntWUB.value limitbv)
                                (LLVM.IntWUB.value (ivbv + 1#32)) s'
                          · have hne : BitVec.ofBool (ivbv <ₛ limitbv) ≠ 1#1 := by
                              intro hb
                              exact hlt ((BitVec.ofBool_eq_one_iff _).mp hb)
                            have hne64 :
                                BitVec.ofBool
                                  (BitVec.signExtend 64 ivbv <ₛ
                                    BitVec.signExtend 64 limitbv) ≠ 1#1 := by
                              intro hb
                              have hlt64 :
                                  (BitVec.signExtend 64 ivbv <ₛ
                                    BitVec.signExtend 64 limitbv) = true :=
                                (BitVec.ofBool_eq_one_iff _).mp hb
                              have hlt32 : (ivbv <ₛ limitbv) = true := by
                                simpa [slt_signExtend64_eq] using hlt64
                              exact hlt hlt32
                            simp [hne, hne64]

theorem src_tgt_entryTarget_eq (fuel : Nat) (base : LLVMMemory.PtrValUB)
    (limit : LLVM.IntWUB 32) (s : LLVMMemory.State) :
    (srcEntryTarget fuel base limit).run s =
      (tgtEntryTarget fuel base limit).run s := by
  cases fuel with
  | zero =>
      simp [srcEntryTarget, tgtEntryTarget, throwRet, LLVMMemory.throwUB]
  | succ fuel =>
      simpa [srcEntryTarget, tgtEntryTarget, sextUB] using
        src_tgt_loopTarget_eq fuel base limit (LLVM.IntWUB.value (0#32)) s

end IndVarTrueSemantics

/-!
# Example 8 — IndVarSimplify: widen i32 induction variable to i64

**Upstream test**: `llvm/test/Transforms/IndVarSimplify/elim-extend.ll @postincConstIV`
  https://github.com/llvm/llvm-project/blob/main/llvm/test/Transforms/IndVarSimplify/elim-extend.ll

**Optimization form**:
  Source: a loop carrying an i32 induction variable `%iv` and computing
    `%iv_ext = sext %iv to i64` each iteration for use as a GEP offset.
    ⇒  Target: the IV is promoted to i64 (`%indvars_iv : i64`), the explicit
       `sext` instruction is eliminated, and the GEP uses the wider IV
       directly. The trip-count compare is also widened.

**Why bounded unroll cannot save Alive2**: equivalence requires the
inductive invariant `indvars_iv_k = sext(iv_k)` for *every* iteration `k`,
together with the fact that `sext(iv_k + 1) = sext(iv_k) + 1` when no
i32 overflow occurs (guarded by `nsw`). Bounded unroll proves the
invariant only for k ∈ {0,…,K}; iteration K+1 is not encoded in the SMT
formula. The overflow-freedom propagation across iterations is itself
∀k, beyond SMT's quantifier-free fragment.
-/

def indvar_widen_i32_to_i64_src :=
  [llvm()| {
  llvm.func @indvar_widen_i32_to_i64_src(%base : ptr, %limit : i32) -> i32 {
  ^entry(%base : ptr, %limit : i32):
    %zero32 = llvm.mlir.constant 0 : i32
    llvm.br ^loop(%zero32 : i32)
  ^loop(%iv : i32):
    %iv_ext = llvm.sext %iv : i32 to i64
    %p = llvm.getelementptr i8, ptr %base, %iv_ext : i64
    %zero8 = llvm.mlir.constant 0 : i8
    llvm.store %p, %zero8 : i8
    %one32 = llvm.mlir.constant 1 : i32
    %iv_next = llvm.add %iv, %one32 : i32
    %cond = llvm.icmp "sgt" %limit, %iv : i32
    llvm.cond_br %cond : i1, ^loop(%iv_next : i32), ^exit()
  ^exit():
    %ret = llvm.mlir.constant 0 : i32
    llvm.return %ret : i32
  }
  }]

def indvar_widen_i32_to_i64_tgt :=
  [llvm()| {
  llvm.func @indvar_widen_i32_to_i64_tgt(%base : ptr, %limit : i32) -> i32 {
  ^entry(%base : ptr, %limit : i32):
    %limit64 = llvm.sext %limit : i32 to i64
    %zero64 = llvm.mlir.constant 0 : i64
    llvm.br ^loop(%zero64 : i64, %limit64 : i64)
  ^loop(%iv : i64, %limit64_loop : i64):
    %p = llvm.getelementptr i8, ptr %base, %iv : i64
    %zero8 = llvm.mlir.constant 0 : i8
    llvm.store %p, %zero8 : i8
    %one64 = llvm.mlir.constant 1 : i64
    %iv_next = llvm.add %iv, %one64 : i64
    %cond = llvm.icmp "sgt" %limit64_loop, %iv : i64
    llvm.cond_br %cond : i1, ^loop(%iv_next : i64, %limit64_loop : i64), ^exit()
  ^exit():
    %ret = llvm.mlir.constant 0 : i32
    llvm.return %ret : i32
  }
  }]


/-- Fuel-based loop proof that executes the store, branch, and recursive loop step. -/
theorem indvar_widen_i32_to_i64_true_loop_correct
    (fuel : Nat) (base : LLVMMemory.PtrValUB) (limit : LLVM.IntWUB 32)
    (s : LLVMMemory.State) :
    (IndVarTrueSemantics.srcEntryTarget fuel base limit).run s =
      (IndVarTrueSemantics.tgtEntryTarget fuel base limit).run s :=
  IndVarTrueSemantics.src_tgt_entryTarget_eq fuel base limit s

end TestLoop
end InstCombine
