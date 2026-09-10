import LeanMLIR.Dialects.LLVM.Syntax
import LeanMLIR.Tactic
namespace LeanMLIR.Tests

open InstCombine

private def ctpopPretty :=
  [llvm| {
    ^bb0(%x : i8):
      %one = llvm.mlir.constant(1 : i8) : i8
      %r = llvm.ctpop %one: i8
      llvm.return %r : i8
  }]

private def ctpopPretty1 :=
  [llvm| {
    ^bb0(%x : i8):
      %e = llvm.mlir.constant(8 : i8) : i8
      %r = llvm.ctpop %e: i8
      llvm.return %r : i8
  }]

example : ctpopPretty.denote = ctpopPretty1.denote := by
  simp_peephole
  intro e
  simp [ctpopPretty, ctpopPretty1]
  simp_peephole
  simp [Op.denoteVec, Op.denote, lift1, LLVM.ctpop, LLVM.ctpop?]
  simp_peephole
  decide

-- private def ctpopGeneric :=
--   [llvm| {
--     ^bb0(%x : i8):
--       %r = "llvm.ctpop"(%x) : (i8) -> (i8)
--       llvm.return %r : i8
--   }]



example : _root_.LLVM.ctpop? (8#8) = (.value (1#8) : _root_.LLVM.IntW 8) := by
  decide

example : _root_.LLVM.ctpop (.poison : _root_.LLVM.IntW 8) = (.poison : _root_.LLVM.IntW 8) := by
  rfl

end LeanMLIR.Tests
