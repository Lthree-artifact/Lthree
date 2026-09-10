/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanMLIR.Dialects.LLVM.Semantics
import SSA.Projects.SLLVM.Dialect.Semantics.EffectM
import SSA.Projects.SLLVM.Tactic.SimpSet

/-- `x.canBe y` returns true exactly when `x` is the concrete value `y`. -/
@[simp_sllvm]
theorem LLVM.IntW.canBe_iff (x : LLVM.IntW w) (y : BitVec w) :
    x.canBe y = true ↔ x = .value y := by
  cases x with
  | poison =>
    constructor
    · intro h
      simp [LLVM.IntW.canBe] at h
    · intro h
      cases h
  | value a =>
    constructor
    · intro h
      have hEq : a = y := by
        simpa [LLVM.IntW.canBe] using h
      simp [hEq]
    · intro h
      injection h with hEq
      simp [LLVM.IntW.canBe, hEq]

namespace LeanMLIR.SLLVM

/-- An LLVM pointer, or `poison` -/
def Ptr : Type := PoisonOr Pointer

@[simp, simp_sllvm] private def lowerIntWUB (x : LLVM.IntWUB w) : EffectM (LLVM.IntW w) :=
  match x with
  | .none => throwUB
  | .some v => pure v

/-! ### div / rem -/

@[simp_sllvm]
def udiv (x y : LLVM.IntW w) (flag : LLVM.ExactFlag) : EffectM (LLVM.IntW w) := do
  if y.canBe 0#w then
    throwUB
  else
    lowerIntWUB <| LLVM.udiv x y flag

@[simp_sllvm]
def sdiv (x y : LLVM.IntW w) (flag : LLVM.ExactFlag) : EffectM (LLVM.IntW w) := do
  if y.canBe 0#w then
    throwUB
  else
    lowerIntWUB <| LLVM.sdiv x y flag

@[simp_sllvm]
def urem (x y : LLVM.IntW w) : EffectM (LLVM.IntW w) := do
  if y.canBe 0#w then
    throwUB
  else
    lowerIntWUB <| LLVM.urem x y

@[simp_sllvm]
def srem (x y : LLVM.IntW w) : EffectM (LLVM.IntW w) := do
  if y.canBe 0#w then
    throwUB
  else
    lowerIntWUB <| LLVM.srem x y

/-! ### pointer arithmetic -/

def ptradd (p : SLLVM.Ptr) (x : LLVM.IntW 64) : SLLVM.Ptr := do
  let p ← p
  match x with
  | .value x => pure { p with offset := p.offset + x }
  | .poison => .poison

/-!
**SIMPLIFICATION**
We deliberately don't support int-to-ptr nor ptr-to-int casts
-/
