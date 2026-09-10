import LeanMLIR.Dialects.LLVM.Semantics

namespace LeanMLIR.Tests

open InstCombine

/-!
## Refinement Matrix for `IntWUB`

States (at width 8):
- `I`: `immediateUB` (`none`)
- `P`: `poison` (`some poison`)
- `V`: concrete value (`some (value 7)`)
-/

private abbrev I : LLVM.IntWUB 8 := ImmediateUBOr.immediateUB
private abbrev P : LLVM.IntWUB 8 := ImmediateUBOr.value (.poison : LLVM.IntW 8)
private abbrev V : LLVM.IntWUB 8 := ImmediateUBOr.value (.value (7#8) : LLVM.IntW 8)

/-! ### Row `I` -/

example : I ⊑ I := by simp
example : I ⊑ P := by simp
example : I ⊑ V := by simp

/-! ### Row `P` -/

example : ¬(P ⊑ I) := by simp [P, I]
example : P ⊑ P := by simp [P]
example : P ⊑ V := by simp [P, V]

/-! ### Row `V` -/

example : ¬(V ⊑ I) := by simp [V, I]
example : ¬(V ⊑ P) := by
  intro h
  cases h with
  | bothValues h =>
      cases h
example : V ⊑ V := by simp [V]

/-! ### Value-vs-value sanity checks -/

example : (LLVM.IntWUB.value (7#8) : LLVM.IntWUB 8) ⊑ (LLVM.IntWUB.value (7#8) : LLVM.IntWUB 8) := by
  exact ImmediateUBOr.IsRefinedBy.bothValues <|
    LLVM.SemVal.IsRefinedBy.bothValues rfl

example : ¬((LLVM.IntWUB.value (7#8) : LLVM.IntWUB 8) ⊑ (LLVM.IntWUB.value (8#8) : LLVM.IntWUB 8)) := by
  intro h
  cases h with
  | bothValues h =>
      have hEq : (7#8 : BitVec 8) = (8#8 : BitVec 8) := by
        simpa using (LLVM.SemVal.value_isRefinedBy_value (x := (7#8)) (y := (8#8))).1 h
      have hne : (7#8 : BitVec 8) ≠ (8#8 : BitVec 8) := by native_decide
      exact hne hEq

end LeanMLIR.Tests
