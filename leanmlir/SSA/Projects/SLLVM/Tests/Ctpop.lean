import SSA.Projects.SLLVM.Dialect

namespace LeanMLIR.SLLVM.Tests

open LeanMLIR
open LeanMLIR.SLLVM

private def ctpopPretty :=
  [sllvm| {
    ^bb0(%x : i8):
      %r = llvm.ctpop %x : i8
      llvm.return %r : i8
  }]

private def ctpopGeneric :=
  [sllvm| {
    ^bb0(%x : i8):
      %r = "llvm.ctpop"(%x) : (i8) -> (i8)
      llvm.return %r : i8
  }]

example : ctpopPretty = ctpopGeneric := by
  rfl

end LeanMLIR.SLLVM.Tests
