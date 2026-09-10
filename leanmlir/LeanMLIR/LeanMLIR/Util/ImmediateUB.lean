/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.Framework.Refinement

/-!
# Immediate UB Semantics
This file defines a generic `ImmediateUBOr α` type, which dialects can use to
model *immediate* undefined behavior as a distinct execution result.
-/

/--
Elements of type `ImmediateUBOr α` are either `immediateUB`, or values of type
`α`.

`ImmediateUBOr α` is represented as `Option α`, but we prefer this name in
semantics to avoid conflating immediate UB with poison values.
-/
abbrev ImmediateUBOr (α : Type) := Option α

namespace ImmediateUBOr

/-! ### Constructors -/
@[match_pattern] def immediateUB : ImmediateUBOr α := none
@[match_pattern] def value : α → ImmediateUBOr α := some

/-! ### Formatting -/
instance [ToString α] : ToString (ImmediateUBOr α) where
  toString
  | .none => "immediateUB"
  | .some a => "(value " ++ addParenHeuristic (toString a) ++ ")"

/-! ### Monad instance and lemmas -/
instance : Monad ImmediateUBOr := inferInstanceAs (Monad Option)
instance : LawfulMonad ImmediateUBOr := inferInstanceAs (LawfulMonad Option)

section Lemmas

@[simp] theorem pure_def : pure = @value α := rfl

@[simp] theorem immediateUB_bind : immediateUB >>= f = immediateUB := rfl
@[simp] theorem value_bind : value a >>= f = f a := rfl
@[simp] theorem bind_immediateUB : x >>= (fun _ => @immediateUB β) = immediateUB := by
  cases x <;> rfl

@[simp] theorem map_immediateUB : f <$> immediateUB = immediateUB := rfl
@[simp] theorem map_value : f <$> value a = value (f a) := rfl

@[simp] theorem value_inj {a b : α} : value a = value b ↔ a = b := by
  constructor
  · rintro ⟨⟩; rfl
  · intro h; cases h; rfl

theorem immediateUB_ne_value (a : α) : immediateUB ≠ value a := Option.noConfusion

theorem value_ne_immediateUB (a : α) : value a ≠ immediateUB := Option.noConfusion

end Lemmas

/-! ### Refinement -/
inductive IsRefinedBy [HRefinement α β] : ImmediateUBOr α → ImmediateUBOr β → Prop
  /-- `immediateUB` is refined by anything -/
  | immediateUBLeft : IsRefinedBy immediateUB b?
  /-- `value a` is only refined by `value b` s.t. `a ⊑ b` -/
  | bothValues : a ⊑ b → IsRefinedBy (value a) (value b)

section Refinement
variable [HRefinement α β] (a? : ImmediateUBOr α) (b? : ImmediateUBOr β) (a : α) (b : β)

instance : HRefinement (ImmediateUBOr α) (ImmediateUBOr β) where
  IsRefinedBy := IsRefinedBy

@[simp] theorem immediateUB_isRefinedBy : (@immediateUB α) ⊑ b? :=
  IsRefinedBy.immediateUBLeft

@[simp] theorem value_isRefinedBy_value : value a ⊑ value b ↔ a ⊑ b := by
  constructor
  · rintro ⟨⟩; assumption
  · exact IsRefinedBy.bothValues

@[simp] theorem not_value_isRefinedBy_immediateUB : ¬value a ⊑ (@immediateUB β) := by
  rintro ⟨⟩

@[simp, simp_denote] theorem eq_squb : ImmediateUBOr.IsRefinedBy a? b? ↔ a? ⊑ b? := by
  rfl

instance [HRefinement α α] [Std.Refl (· ⊑ · : α → α → _)] :
    Std.Refl (· ⊑ · : ImmediateUBOr α → ImmediateUBOr α → _) where
  refl a? := by
    cases a? with
    | none => exact IsRefinedBy.immediateUBLeft
    | some a => exact IsRefinedBy.bothValues (Std.Refl.refl a)

theorem isRefinedBy_self [HRefinement α α] [Std.Refl (· ⊑ · : α → α → _)]
    (a? : ImmediateUBOr α) : a? ⊑ a? :=
  Std.Refl.refl _

instance [HRefinement α α] [DecidableRel (· ⊑ · : α → α → _)] :
    DecidableRel (· ⊑ · : ImmediateUBOr α → ImmediateUBOr α → _)
  | .none, _ => .isTrue <| by exact IsRefinedBy.immediateUBLeft
  | .some _, .none => .isFalse <| by intro h; cases h
  | .some a', .some b' =>
    decidable_of_decidable_of_iff (p := a' ⊑ b') <| by
      constructor
      · intro h
        exact IsRefinedBy.bothValues h
      · intro h
        cases h with
        | bothValues h => exact h

end Refinement

end ImmediateUBOr
