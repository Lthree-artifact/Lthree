import SSA.Projects.SLLVM.Dialect

namespace LeanMLIR.SLLVM.Tests

open LeanMLIR
open LeanMLIR.SLLVM

/-! ## LLVM/SLLVM consistency for arithmetic -/

example (x y : LLVM.IntW 8) (flag : LLVM.ExactFlag) (s : GlobalState)
    (hy : y.canBe (0#8) = false) :
    StateT.run (SLLVM.udiv x y flag) s =
      match LLVM.udiv x y flag with
      | .none => .immediateUB
      | .some v => .some (v, s) := by
  cases h : LLVM.udiv x y flag <;> simp [SLLVM.udiv, hy, h]

/-! ## SLLVM immediate UB is distinct and triggered on div-by-zero -/

example (s : GlobalState) :
    StateT.run (SLLVM.udiv (.value (7#8)) (.value (0#8)) {}) s = ImmediateUBOr.immediateUB := by
  simp [SLLVM.udiv, LLVM.IntW.canBe, ImmediateUBOr.immediateUB]

end LeanMLIR.SLLVM.Tests
