import LeanMLIR.Dialects.LLVM.Syntax
import LeanMLIR.Tactic

namespace LeanMLIR.Tests

open InstCombine

private def ctlzPretty :=
  [llvm| {
    ^bb0(%x : i8):
      %r = llvm.ctlz %x, false : i8
      llvm.return %r : i8
  }]

private def cttzPretty :=
  [llvm| {
    ^bb0(%x : i8):
      %r = llvm.cttz %x, true : i8
      llvm.return %r : i8
  }]

private def ctlzPretty1 :=
  [llvm| {
    ^bb0(%x : i8):
      %one = llvm.mlir.constant(8 : i8) : i8
      %r = llvm.ctlz %one, false: i8
      llvm.return %r : i8
  }]

private def ctlzPretty2 :=
  [llvm| {
    ^bb0(%x : i8):
      %e = llvm.mlir.constant(24 : i8) : i8
      %r = llvm.ctlz %e, false: i8
      llvm.return %r : i8
  }]

example : ctlzPretty1.denote = ctlzPretty2.denote := by
  sorry


private def zeroPoisonTrue : _root_.LLVM.ZeroPoisonFlag :=
  ((_root_.LLVM.ZeroPoisonFlag.mk) (Bool.true))


example : _root_.LLVM.cttz? (8#8) = (.value (3#8) : _root_.LLVM.IntW 8) := by
  native_decide

example : _root_.LLVM.ctlz? (8#8) = (.value (4#8) : _root_.LLVM.IntW 8) := by
  native_decide

example : _root_.LLVM.cttz? (0#8) = (.value (8#8) : _root_.LLVM.IntW 8) := by
  native_decide

example : _root_.LLVM.ctlz? (0#8) = (.value (8#8) : _root_.LLVM.IntW 8) := by
  native_decide

example : _root_.LLVM.cttz? (0#8) zeroPoisonTrue = (.poison : _root_.LLVM.IntW 8) := by
  native_decide

example : _root_.LLVM.ctlz? (0#8) zeroPoisonTrue = (.poison : _root_.LLVM.IntW 8) := by
  native_decide

example : _root_.LLVM.cttz (.poison : _root_.LLVM.IntW 8) = (.poison : _root_.LLVM.IntW 8) := by
  rfl

example : _root_.LLVM.ctlz (.poison : _root_.LLVM.IntW 8) = (.poison : _root_.LLVM.IntW 8) := by
  rfl

end LeanMLIR.Tests
