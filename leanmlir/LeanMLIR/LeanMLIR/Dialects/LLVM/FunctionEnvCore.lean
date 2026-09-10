import LeanMLIR.Dialects.LLVM.Basic

namespace InstCombine

open LLVM

namespace LLVMMemory

/-- Underlying concrete carrier used by function denotations for each LLVM type. -/
def TyBase : LLVM.Ty → Type
  | .bitvec (.concrete w) => BitVec w
  | .bitvec (.mvar idx) => nomatch idx
  | .ptr => Ptr

/-- Semantic value family used for function denotations. -/
abbrev TySemVal (ty : LLVM.Ty) : Type := LLVM.SemVal (TyBase ty)

instance (ty : LLVM.Ty) : Refinement (TyBase ty) := .ofEq
instance (ty : LLVM.Ty) : HRefinement (TyBase ty) (TyBase ty) := inferInstance

/-- Convert a typed LLVM value into its `SemVal` layer, preserving immediate UB. -/
def toSemValOrUB {ty : LLVM.Ty} (x : TyDenote.toType ty) : ImmediateUBOr (TySemVal ty) := by
  cases ty with
  | bitvec w =>
      cases w with
      | concrete _ => exact x
      | mvar idx => exact idx.elim0
  | ptr =>
      exact x

/-- Strip immediate UB from every argument in a call-argument vector. -/
def toSemValVecOrUB : HVector TyDenote.toType tys → ImmediateUBOr (HVector TySemVal tys)
  | .nil => .value .nil
  | .cons x xs => do
      let x' ← toSemValOrUB x
      let xs' ← toSemValVecOrUB xs
      pure (x' ::ₕ xs')

/-- Lift a semantic value back into the dialect's typed denotation family. -/
def fromSemVal {ty : LLVM.Ty} (x : TySemVal ty) : TyDenote.toType ty := by
  cases ty with
  | bitvec w =>
      cases w with
      | concrete _ => exact ImmediateUBOr.value x
      | mvar idx => exact idx.elim0
  | ptr =>
      exact ImmediateUBOr.value x

/-- Lift a vector of semantic values back into the dialect's typed denotation family. -/
def fromSemValVec : HVector TySemVal tys → HVector TyDenote.toType tys
  | .nil => .nil
  | .cons x xs => .cons (fromSemVal x) (fromSemValVec xs)

/-- Fuel-bounded denotational semantics for a single LLVM function body. -/
structure FuncDef (σ : Type) where
  argTys : List LLVM.Ty
  retTy  : LLVM.Ty
  denote : (fuel : Nat)
        → (args : HVector TySemVal argTys)
        → σ
        → ImmediateUBOr (TySemVal retTy × σ)

/--
Lift a pure, single-result LLVM body into a callable `FuncDef`.
The body is evaluated on the supplied arguments, and leaves the ambient state unchanged.
-/
def FuncDef.ofCom {σ : Type} {argTys : List LLVM.Ty} {retTy : LLVM.Ty}
    (body : Com LLVM ⟨argTys⟩ .pure [retTy]) : FuncDef σ where
  argTys := argTys
  retTy := retTy
  denote := fun _fuel args s => do
    let args' : HVector TyDenote.toType argTys := fromSemValVec args
    let v : TyDenote.toType retTy := by
      simpa using (body.denote (Ctxt.Valuation.ofHVector args') |>.getN 0 (by simp))
    let v ← toSemValOrUB v
    pure (v, s)

/-- Name-indexed function environment used by `llvm.call` semantics. -/
abbrev FunctionEnv (σ : Type) := Std.HashMap String (FuncDef σ)

namespace FunctionEnv

/-- Singleton function environment containing only the given definition. -/
def singleton (name : String) (f : FuncDef σ) : FunctionEnv σ :=
  ({} : FunctionEnv σ).insert name f

@[simp] theorem lookup_singleton_eq (name : String) (f : FuncDef σ) :
    (singleton (σ := σ) name f)[name]? = some f := by
  simp [singleton]

@[simp] theorem lookup_singleton_ne (name other : String) (f : FuncDef σ)
    (h : other ≠ name) :
    (singleton (σ := σ) name f)[other]? = none := by
  simp [singleton, h.symm]

end FunctionEnv

/-- Default recursion fuel used by `llvm.call` in executable memory semantics. -/
def defaultFuel : Nat := 1000

end LLVMMemory

end InstCombine
