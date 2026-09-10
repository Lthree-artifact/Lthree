import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.Tactic.SimpMemory
import LeanMLIR.Dialects.LLVM.MemoryModel

namespace InstCombine

open InstCombine.LLVMMemory

attribute [simp_memory]
  LLVMMemory.Com.denoteWithMemory
  LLVMMemory.Com.denoteWithMemoryFuel
  LLVMMemory.Com.denoteWithMemoryFuelIn
  LLVMMemory.Com.denoteWithDefaultFunctionEnvFuel
  LLVMMemory.Com.denoteWithMemoryCore
  LLVMMemory.Expr.denoteWithMemory
  LLVMMemory.Op.denoteVec
  LLVMMemory.gep_lift2_add_zero_right
  LLVMMemory.gep_zero_store_load_fusion

attribute [simp_memory_store_defs]
  LLVMMemory.store
  LLVMMemory.getIntWUBOrUB
  LLVMMemory.getIntWOrUB
  LLVMMemory.getPtrOrUB
  LLVMMemory.throwUB
  ImmediateUBOr.immediateUB

attribute [simp_memory_alloca_defs]
  LLVMMemory.alloca

attribute [simp_memory_gep_defs]
  LLVMMemory.gep
  LLVMMemory.gepOffset
  LLVMMemory.gepNormalizeIdx
  LLVMMemory.bytesForWidth
  LLVM.sext
  LLVM.sext?
  LLVM.mul
  LLVM.mul?

instance : Refinement LLVMMemory.State := Refinement.ofEq
instance : HRefinement LLVMMemory.State LLVMMemory.State where
  IsRefinedBy := Eq

/-- Optional call-environment override for memory refinement on impure commands. -/
class RefinementFunctionEnvFor (Γ : Ctxt LLVM.Ty) (tys : List LLVM.Ty) where
  env : FunctionEnv LLVMMemory.State

instance (priority := 500) instRefinementFunctionEnvForOfLLVMCalleeEnv
    [LLVMCalleeEnv LLVMMemory.State Γ tys] :
    RefinementFunctionEnvFor Γ tys where
  env := LLVMCalleeEnv.env (σ := LLVMMemory.State) (Γ := Γ) (tys := tys)

/--
Default refinement for impure `Com LLVM` terms interpreted with executable
memory semantics. CFG commands are interpreted with the fuel-bounded CFG
interpreter rather than their fallback body, and the relation quantifies over
input valuation, initial memory state, and fuel.
-/
def IsRefinedByOnIntWInputsWithMemory
    {Γ : Ctxt LLVM.Ty} {tys : List LLVM.Ty}
    (c₁ c₂ : Com LLVM Γ .impure tys) : Prop :=
  ∀ V : InputValuation Γ,
    ∀ s : LLVMMemory.State,
      ∀ fuel : Nat,
        c₁.denoteWithMemoryFuel fuel (V := InputValuation.lift V) s ⊑
        c₂.denoteWithMemoryFuel fuel (V := InputValuation.lift V) s

/--
Environment-aware refinement for impure `Com LLVM` terms interpreted with
`denoteWithMemoryFuelIn env`, where `env` is provided by
`RefinementFunctionEnvFor Γ tys`. CFG commands are interpreted by fuel.
-/
def IsRefinedByOnIntWInputsWithMemoryIn
    {Γ : Ctxt LLVM.Ty} {tys : List LLVM.Ty}
    [RefinementFunctionEnvFor Γ tys]
    (c₁ c₂ : Com LLVM Γ .impure tys) : Prop :=
  ∀ V : InputValuation Γ,
    ∀ s : LLVMMemory.State,
      ∀ fuel : Nat,
        c₁.denoteWithMemoryFuelIn
          (env := (RefinementFunctionEnvFor.env (Γ := Γ) (tys := tys)))
          fuel
          (V := InputValuation.lift V) s
        ⊑
        c₂.denoteWithMemoryFuelIn
          (env := (RefinementFunctionEnvFor.env (Γ := Γ) (tys := tys)))
          fuel
          (V := InputValuation.lift V) s

scoped instance (priority := 12000)
    {Γ : Ctxt LLVM.Ty} {tys : List LLVM.Ty}
    [RefinementFunctionEnvFor Γ tys] :
    HRefinement (Com LLVM Γ .impure tys) (Com LLVM Γ .impure tys) where
  IsRefinedBy := IsRefinedByOnIntWInputsWithMemoryIn

scoped instance (priority := 11000)
    {Γ : Ctxt LLVM.Ty} {tys : List LLVM.Ty} :
    HRefinement (Com LLVM Γ .impure tys) (Com LLVM Γ .impure tys) where
  IsRefinedBy := IsRefinedByOnIntWInputsWithMemory

/-- `IntW w` refines itself. -/
@[simp] theorem IntW_le_self (x : LLVM.IntW w) : x ⊑ x := by
  rw [LLVM.IntW.isRefinedBy_iff]
  exact LLVM.SemVal.isRefinedBy_self x

/-- `IntWUB w` refines itself. -/
@[simp] theorem IntWUB_le_self (x : LLVM.IntWUB w) : x ⊑ x := by
  cases x with
  | none => exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | some v => exact ImmediateUBOr.IsRefinedBy.bothValues (IntW_le_self v)

/-- Pointer values refines themselves. -/
@[simp] theorem PtrValUB_le_self (x : LLVMMemory.PtrValUB) : x ⊑ x := by
  cases x with
  | none => exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | some v => exact ImmediateUBOr.IsRefinedBy.bothValues (LLVM.SemVal.isRefinedBy_self v)

/-- Any `x : TyDenote.toType t` for `t : LLVM.Ty` refines itself. -/
theorem tyDenote_le_self {t : LLVM.Ty} (x : TyDenote.toType t) : x ⊑ x := by
  cases t with
  | ptr => exact PtrValUB_le_self x
  | bitvec w =>
    cases w with
    | concrete n => exact IntWUB_le_self x
    | mvar idx => exact idx.elim0

/-- An `HVector` over LLVM types refines itself. -/
theorem hvec_le_self {tys : List LLVM.Ty} (hvec : HVector TyDenote.toType tys) : hvec ⊑ hvec := by
  induction hvec with
  | nil => exact HVector.nil_isRefinedBy_nil
  | cons x xs ih =>
    rw [HVector.cons_isRefinedBy_cons]
    exact ⟨tyDenote_le_self x, ih⟩

/-- The memory result type refines itself. -/
theorem mem_result_le_self
    {tys : List LLVM.Ty}
    (r : ImmediateUBOr (HVector TyDenote.toType tys × LLVMMemory.State)) :
    r ⊑ r := by
  cases r with
  | none => exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | some p =>
    obtain ⟨hvec, state⟩ := p
    apply ImmediateUBOr.IsRefinedBy.bothValues
    simp only [Prod.isRefinedBy_iff]
    exact ⟨hvec_le_self hvec, rfl⟩

end InstCombine
