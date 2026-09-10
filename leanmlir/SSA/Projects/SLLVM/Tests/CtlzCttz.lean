import SSA.Projects.SLLVM.Dialect

namespace LeanMLIR.SLLVM.Tests

open LeanMLIR
open LeanMLIR.SLLVM

private def ctlzPretty :=
  [sllvm| {
    ^bb0(%x : i8):
      %r = llvm.ctlz %x, false : i8
      llvm.return %r : i8
  }]

private def cttzPretty :=
  [sllvm| {
    ^bb0(%x : i8):
      %r = llvm.cttz %x, true : i8
      llvm.return %r : i8
  }]

example : ctlzPretty = ctlzPretty := by
  rfl

example : cttzPretty = cttzPretty := by
  rfl

end LeanMLIR.SLLVM.Tests
