import LeanMLIR.Dialects.LLVM.Syntax

namespace LeanMLIR.Tests

open InstCombine

/-! ## Poison and Value -/

example : LLVM.IntW.canBe (.poison : LLVM.IntW 8) (0#8) = false := by
  rfl

example : LLVM.IntW.canBe (.value (0#8) : LLVM.IntW 8) (0#8) = true := by
  simp [LLVM.IntW.canBe]

example : LLVM.freeze (.poison : LLVM.SemVal (BitVec 8)) = (.value (0#8) : LLVM.IntW 8) := by
  rfl


/-! ## Immediate UB for div/rem by zero -/

example : LLVM.udiv? (5#8) (0#8) = (.immediateUB : LLVM.IntWUB 8) := by
  simp [LLVM.udiv?]

example : LLVM.urem? (5#8) (0#8) = (.immediateUB : LLVM.IntWUB 8) := by
  simp [LLVM.urem?]

example : LLVM.sdiv? (BitVec.intMin 8) (-1#8) = (.immediateUB : LLVM.IntWUB 8) := by
  simp [LLVM.sdiv?]

example : LLVM.srem? (BitVec.intMin 8) (-1#8) = (.immediateUB : LLVM.IntWUB 8) := by
  simp [LLVM.srem?]

example : LLVM.udiv? (5#8) (0#8) ≠ (.poison : LLVM.IntWUB 8) := by
  decide

/-! ## `Op.denote` now carries `IntWUB` directly -/

example :
    (InstCombine.Op.denote (LLVM.Op.udiv 8 {})
      [(.value (5#8) : LLVM.IntWUB 8), (.value (0#8) : LLVM.IntWUB 8)]ₕ).isNone = true := by
  native_decide

example :
    (InstCombine.Op.denote (LLVM.Op.add 8 {})
      [(.value (1#8) : LLVM.IntWUB 8), (.none : LLVM.IntWUB 8)]ₕ).isNone = true := by
  native_decide

example :
    InstCombine.Op.denote (LLVM.Op.const 8 5) []ₕ
    = (.value (5#8) : LLVM.IntWUB 8) := by
  simp [InstCombine.Op.denote, LLVM.const?]

/-! ## `llvm.assume` -/

example :
    (InstCombine.Op.denoteVec LLVM.Op.assume
      [(.value (1#1) : LLVM.IntWUB 1)]ₕ).isSome = true := by
  native_decide

example :
    (InstCombine.Op.denoteVec LLVM.Op.assume
      [(.value (0#1) : LLVM.IntWUB 1)]ₕ).isNone = true := by
  native_decide

/-! ## `isPowerOf2` helper -/

example : LLVM.isPowerOf2? (8#8) = (.value (1#1) : LLVM.IntW 1) := by
  native_decide

example : LLVM.isPowerOf2? (6#8) = (.value (0#1) : LLVM.IntW 1) := by
  native_decide

example : LLVM.isPowerOf2? (5#8) = (.value (0#1) : LLVM.IntW 1) := by
  native_decide

example : LLVM.isPowerOf2 (.poison : LLVM.IntW 8) = (.poison : LLVM.IntW 1) := by
  rfl

/-! ## `IntWUB` simp lemmas -/

example : (LLVM.IntWUB.immediateUB : LLVM.IntWUB 8) = .none := by
  simp

example :
    (LLVM.IntWUB.value (7#8) : LLVM.IntWUB 8) = .some (.value (7#8) : LLVM.IntW 8) := by
  simp

/--
info: builtin.module {
  ^bb0(%0 : i1):
    "llvm.assume"(%0) : (i1) -> ()
    "llvm.return"(%0) : (i1) -> ()
}
-/
#guard_msgs in #eval Com.printModule [llvm| {
  ^bb0(%c : i1):
    llvm.assume %c : i1
    llvm.return %c : i1
}]

end LeanMLIR.Tests
