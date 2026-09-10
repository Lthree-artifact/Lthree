import LeanMLIR.Dialects.LLVM.FunctionEnv

namespace InstCombine

open LLVM

namespace LLVMMemory

variable {σ : Type} [HRefinement σ σ]

/-- Constant function body that returns `c` and leaves memory unchanged. -/
def constFuncDef (argTys : List LLVM.Ty) (retTy : LLVM.Ty) (c : TySemVal retTy) : FuncDef σ where
  argTys := argTys
  retTy := retTy
  denote := fun _ _ s => .value (c, s)

/-- Pointwise refinement relation for function definitions with matching signatures. -/
def FuncDef.IsRefinedBy (src tgt : FuncDef σ) : Prop :=
  ∃ (hArg : src.argTys = tgt.argTys),
    ∃ (hRet : src.retTy = tgt.retTy),
      ∀ fuel (args : HVector TySemVal src.argTys) s,
        src.denote fuel args s ⊑
          (hRet.symm ▸ tgt.denote fuel (hArg ▸ args) s)

instance : HRefinement (FuncDef σ) (FuncDef σ) where
  IsRefinedBy := FuncDef.IsRefinedBy

/-- Core function-level refinement theorem from pointwise denotation refinement. -/
theorem function_refinement
    (env : FunctionEnv σ)
    (src tgt : FuncDef σ)
    (hArg : src.argTys = tgt.argTys)
    (hRet : src.retTy = tgt.retTy)
    (h : ∀ fuel (args : HVector TySemVal src.argTys) s,
      src.denote fuel args s ⊑
        (hRet.symm ▸ tgt.denote fuel (hArg ▸ args) s))
    : src ⊑ tgt := by
  let _ := env
  exact ⟨hArg, hRet, h⟩

/-- If a function always returns the same value, it refines the corresponding constant function. -/
theorem refines_const_of_always_returns
    [Std.Refl (· ⊑ · : σ → σ → _)]
    (recFn : FuncDef σ) (c : TySemVal recFn.retTy)
    (h : ∀ fuel (args : HVector TySemVal recFn.argTys) s,
      recFn.denote fuel args s = .value (c, s))
    : recFn ⊑ (constFuncDef (σ := σ) recFn.argTys recFn.retTy c) := by
  refine ⟨rfl, rfl, ?_⟩
  intro fuel args s
  rw [h fuel args s]
  apply ImmediateUBOr.IsRefinedBy.bothValues
  simpa [Prod.isRefinedBy_iff] using
    (And.intro (LLVM.SemVal.isRefinedBy_self c) (Std.Refl.refl s))

end LLVMMemory

end InstCombine
