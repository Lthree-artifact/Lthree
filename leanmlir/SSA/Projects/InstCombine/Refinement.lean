/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.Dialects.LLVM.Basic
import LeanMLIR.Framework.ExprRefinement
import LeanMLIR.Util.Poison

namespace InstCombine
open LLVM.Ty

@[simp, simp_denote]
instance instRefinement : DialectHRefinement LLVM LLVM where
  MonadIsRefinedBy := by
    intro α β inst
    letI : HRefinement α β := inst
    simpa [LLVM] using (inferInstance : HRefinement (ImmediateUBOr α) (ImmediateUBOr β))
  IsRefinedBy := by
    intro t u
    cases t with
    | ptr =>
        cases u with
        | ptr =>
            simpa [TyDenote.toType] using
              (inferInstance : HRefinement LLVMMemory.PtrValUB LLVMMemory.PtrValUB)
        | bitvec w =>
            exact ⟨fun _ _ => False⟩
    | bitvec w =>
        cases w with
        | concrete n =>
            cases u with
            | ptr =>
                exact ⟨fun _ _ => False⟩
            | bitvec w' =>
                cases w' with
                | concrete n' =>
                    simpa [TyDenote.toType] using
                      (inferInstance : HRefinement (LLVM.IntWUB n) (LLVM.IntWUB n'))
                | mvar idx =>
                    exact idx.elim0
        | mvar idx =>
            exact idx.elim0

/--
LLVM program inputs restricted to `IntW` values (no direct `ImmediateUBOr` inputs).
-/
abbrev InputValuation (Γ : Ctxt LLVM.Ty) : Type :=
  ⦃t : LLVM.Ty⦄ → Γ.Var t → LLVM.IntW (LLVM.Ty.width t)

def ptrOfIntW64 (x : LLVM.IntW 64) : LLVMMemory.PtrVal :=
  match x with
  | .poison => .poison
  | .value v => .value { blockId := v.toNat, offset := 0#64 }

@[simp] theorem ptrOfIntW64_poison :
    ptrOfIntW64 (.poison : LLVM.IntW 64) = .poison := rfl

@[simp] theorem ptrOfIntW64_value (v : BitVec 64) :
    ptrOfIntW64 (.value v : LLVM.IntW 64) = .value { blockId := v.toNat, offset := 0#64 } := rfl

/--
Lift an `IntW`-only input valuation to the default LLVM valuation domain.
This enforces that each input is wrapped as `ImmediateUBOr.value`.
-/
def InputValuation.lift {Γ : Ctxt LLVM.Ty} (V : InputValuation Γ) : Γ.Valuation := by
  intro t v
  cases t with
  | ptr =>
      exact some (ptrOfIntW64 (V v))
  | bitvec w =>
      cases w with
      | concrete n =>
          let h :
              TyDenote.toType (LLVM.Ty.bitvec (LLVM.Ty.width (LLVM.Ty.bitvec n)))
                = TyDenote.toType (LLVM.Ty.bitvec n) := by
            simp [LLVM.Ty.width, TyDenote.toType]
          let x : TyDenote.toType (LLVM.Ty.bitvec (LLVM.Ty.width (LLVM.Ty.bitvec n))) := some (V v)
          exact cast h x
      | mvar idx =>
          exact idx.elim0

@[simp] theorem InputValuation.lift_apply_ptr {Γ : Ctxt LLVM.Ty}
    (V : InputValuation Γ) (v : Γ.Var LLVM.Ty.ptr) :
    InputValuation.lift V v = some (ptrOfIntW64 (V v)) := by
  simp [InputValuation.lift]

@[simp] theorem InputValuation.lift_apply_bitvec_concrete {Γ : Ctxt LLVM.Ty}
    (V : InputValuation Γ) (n : Nat) (v : Γ.Var (LLVM.Ty.bitvec n)) :
    InputValuation.lift V v = some (V v) := by
  simp [InputValuation.lift]

/--
Concrete relation used by LLVM expression/program refinement after restricting
inputs to `IntW`.
-/
def IsRefinedByOnIntWInputs
    {Γ : Ctxt LLVM.Ty} {eff₁ eff₂ : EffectKind} {tys : List LLVM.Ty}
    (c₁ : Com LLVM Γ eff₁ tys) (c₂ : Com LLVM Γ eff₂ tys) : Prop :=
  ∀ V : InputValuation Γ,
    c₁.denote (InputValuation.lift V) ⊑ c₂.denote (InputValuation.lift V)

scoped infix:50 " ⊑ᵢ " => IsRefinedByOnIntWInputs

/--
Legacy relation that quantifies over full LLVM valuations (`IntWUB` inputs).
Useful as a compatibility layer for older proofs.
-/
def IsRefinedByWithUBInputs
    {Γ : Ctxt LLVM.Ty} {eff1 eff2 : EffectKind} {tys : List LLVM.Ty}
    (c1 : Com LLVM Γ eff1 tys) (c2 : Com LLVM Γ eff2 tys) : Prop :=
  ∀ V : Γ.Valuation, c1.denote V ⊑ c2.denote V

/--
Global override for LLVM expression refinement:
`⊑` now quantifies over `InputValuation` and lifts internally.
-/
instance (priority := 10000)
    {Γ : Ctxt LLVM.Ty} {eff1 eff2 : EffectKind} {tys : List LLVM.Ty} :
    HRefinement (Expr LLVM Γ eff1 tys) (Expr LLVM Γ eff2 tys) where
  IsRefinedBy e1 e2 :=
    ∀ V : InputValuation Γ,
      e1.denote (InputValuation.lift V) ⊑ e2.denote (InputValuation.lift V)

/--
Global override for LLVM program refinement:
`⊑` now quantifies over `InputValuation` and lifts internally.
-/
instance (priority := 10000)
    {Γ : Ctxt LLVM.Ty} {eff1 eff2 : EffectKind} {tys : List LLVM.Ty} :
    HRefinement (Com LLVM Γ eff1 tys) (Com LLVM Γ eff2 tys) where
  IsRefinedBy := IsRefinedByOnIntWInputs

@[simp] theorem isRefinedByOnIntWInputs_iff
    {Γ : Ctxt LLVM.Ty} {eff1 eff2 : EffectKind} {tys : List LLVM.Ty}
    (c1 : Com LLVM Γ eff1 tys) (c2 : Com LLVM Γ eff2 tys) :
    c1 ⊑ c2 ↔ IsRefinedByOnIntWInputs c1 c2 := by
  rfl

theorem isRefinedBy_of_isRefinedByWithUBInputs
    {Γ : Ctxt LLVM.Ty} {eff1 eff2 : EffectKind} {tys : List LLVM.Ty}
    {c1 : Com LLVM Γ eff1 tys} {c2 : Com LLVM Γ eff2 tys}
    (h : IsRefinedByWithUBInputs c1 c2) : c1 ⊑ c2 := by
  intro V
  exact h (InputValuation.lift V)
