import LeanMLIR.Dialects.LLVM.Syntax
import LeanMLIR.Tactic

namespace LeanMLIR.Tests

open InstCombine

private def absPretty :=
  [llvm()| {
    ^bb0(%x : i8):
      %r = llvm.abs %x, true : i8
      llvm.return %r : i8
  }]

private def absGeneric :=
  [llvm()| {
    ^bb0(%x : i8):
      %r = "llvm.intr.abs"(%x) <{is_int_min_poison = true}> : (i8) -> (i8)
      llvm.return %r : i8
  }]

example : absPretty = absPretty := by
  rfl

example : absGeneric = absGeneric := by
  rfl

private def intMinPoisonTrue : _root_.LLVM.IntMinPoisonFlag :=
  ((_root_.LLVM.IntMinPoisonFlag.mk) (Bool.true))

private def intMinPoisonFalse : _root_.LLVM.IntMinPoisonFlag :=
  ((_root_.LLVM.IntMinPoisonFlag.mk) (Bool.false))

example : _root_.LLVM.abs? (BitVec.ofInt 8 (-5)) =
    (.value (5#8) : _root_.LLVM.IntW 8) := by
  native_decide

example : _root_.LLVM.abs? (5#8) =
    (.value (5#8) : _root_.LLVM.IntW 8) := by
  native_decide

example : _root_.LLVM.abs? (BitVec.ofInt 8 (-128)) intMinPoisonFalse =
    (.value (128#8) : _root_.LLVM.IntW 8) := by
  native_decide

example : _root_.LLVM.abs? (BitVec.ofInt 8 (-128)) intMinPoisonTrue =
    (.poison : _root_.LLVM.IntW 8) := by
  native_decide

example : _root_.LLVM.abs (.poison : _root_.LLVM.IntW 8) intMinPoisonTrue =
    (.poison : _root_.LLVM.IntW 8) := by
  rfl

end LeanMLIR.Tests
