import LeanMLIR.Dialects.LLVM.Syntax

namespace LeanMLIR.Tests

open InstCombine

/-!
Tests for `llvm.isPowerOf2`.

The expected concrete semantics are:
`c` is nonzero, and clearing its lowest set bit gives zero:
`(c &&& (c - 1)) == 0 && c != 0`.
-/

private def i1 (b : Bool) : LLVM.IntW 1 :=
  .value (BitVec.ofBool b)

private def i1UB (b : Bool) : LLVM.IntWUB 1 :=
  LLVM.IntWUB.value (BitVec.ofBool b)

private def isTrueI1 : LLVM.IntW 1 → Bool
  | .value x => x == (1#1)
  | .poison => false

private def isPowerOf2TruthTable4 : List Bool :=
  (List.range 16).map fun n =>
    isTrueI1 (LLVM.isPowerOf2? (BitVec.ofNat 4 n))

example :
    isPowerOf2TruthTable4 =
      [false, true, true, false,
       true, false, false, false,
       true, false, false, false,
       false, false, false, false] := by
  native_decide

example : LLVM.isPowerOf2? (0#8) = i1 false := by
  native_decide

example : LLVM.isPowerOf2? (1#8) = i1 true := by
  native_decide

example : LLVM.isPowerOf2? (2#8) = i1 true := by
  native_decide

example : LLVM.isPowerOf2? (8#8) = i1 true := by
  native_decide

example : LLVM.isPowerOf2? (128#8) = i1 true := by
  native_decide

example : LLVM.isPowerOf2? (3#8) = i1 false := by
  native_decide

example : LLVM.isPowerOf2? (6#8) = i1 false := by
  native_decide

example : LLVM.isPowerOf2? (255#8) = i1 false := by
  native_decide

example : LLVM.isPowerOf2 (.poison : LLVM.IntW 8) = (.poison : LLVM.IntW 1) := by
  rfl

example :
    (InstCombine.Op.denote (LLVM.Op.isPowerOf2 4)
      [(.value (8#4) : LLVM.IntWUB 4)]ₕ : LLVM.IntWUB 1) = i1UB true := by
  simp [InstCombine.Op.denote, InstCombine.lift1, i1UB, LLVM.isPowerOf2, LLVM.isPowerOf2?]

example :
    (InstCombine.Op.denote (LLVM.Op.isPowerOf2 4)
      [(.value (6#4) : LLVM.IntWUB 4)]ₕ : LLVM.IntWUB 1) = i1UB false := by
  simp [InstCombine.Op.denote, InstCombine.lift1, i1UB, LLVM.isPowerOf2, LLVM.isPowerOf2?]

example :
    (InstCombine.Op.denote (LLVM.Op.isPowerOf2 4)
      [(.poison : LLVM.IntWUB 4)]ₕ : LLVM.IntWUB 1) = (.poison : LLVM.IntWUB 1) := by
  simp [InstCombine.Op.denote, InstCombine.lift1, LLVM.isPowerOf2]

end LeanMLIR.Tests
