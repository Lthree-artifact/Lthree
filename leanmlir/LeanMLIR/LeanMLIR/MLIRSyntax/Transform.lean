/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- should replace with Lean import once Pure is upstream
import LeanMLIR.MLIRSyntax.AST
import LeanMLIR.MLIRSyntax.Transform.NameMapping
import LeanMLIR.MLIRSyntax.Transform.TransformError
import LeanMLIR.Framework
import LeanMLIR.ErasedContext

/-!
# `Transform*` typeclasses
This file defines `TransformTy`, `TransformExpr`, and `TransformReturn` typeclasses,
which dictate how generic MLIR syntax (as defined in `MLIRSyntax.AST`) can be transformed into
an instance of `Com` or `Expr` for a specific dialect.
-/

universe u

namespace MLIR.AST

open Ctxt

instance {d : Dialect} [DialectSignature d] {t} {Γ : Ctxt d.Ty} {Γ' : DerivedCtxt Γ} :
    Coe (Expr d Γ eff t) (Expr d Γ'.ctxt eff t) where
  coe e := e.changeVars Γ'.diff.toHom


section Monads

/-!
  Even though we technically only need to know the `Ty` type,
  our typeclass hierarchy is fully based on `Op`.
  It is thus more convenient to incorporate `Op` in these types, so that there will be no ambiguity
  errors.
-/

abbrev ExceptM  (_ : Dialect) := Except TransformError
abbrev BuilderM (d : Dialect) := StateT NameMapping (ExceptM d)
abbrev ReaderM  (d : Dialect) := ReaderT NameMapping (ExceptM d)

instance : Inhabited (ReaderT NameMapping (ExceptM d) α) where
  default := throw <| .generic ""

instance {d : Dialect} : MonadLift (ReaderM d) (BuilderM d) where
  monadLift x := do (ReaderT.run x (←get) : ExceptM ..)

instance {d : Dialect} : MonadLift (ExceptM d) (ReaderM d) where
  monadLift x := do return ←x

def BuilderM.runWithEmptyMapping (k : BuilderM d α) : ExceptM d α :=
  Prod.fst <$> StateT.run k []

end Monads

/-!
  These typeclasses provide a natural flow to how users should implement `TransformDialect`.
  - First declare how to transform types with `TransformTy`.
  - Second, using `TransformTy`, declare how to transform expressions with `TransformExpr`.
  - Third, using both type and expression conversion, declare how to transform
  returns with `TransformReturn`.
  - These three automatically give an instance of `TransformDialect`.
-/

/- TODO: the above mentions a `TransformDialect`, but such a class does not
          exist. Was it removed for some reason, or did we just not implement it?
          It would be nice to not have to spell out the three different classes
          in, e.g., `mkCom` -/

class TransformTy (d : Dialect) (φ : outParam Nat) [DialectSignature d]  where
  mkTy   : MLIRType φ → ExceptM d d.Ty

class TransformExpr (d : Dialect) (φ : outParam Nat) [DialectSignature d] [TransformTy d φ]  where
  mkExpr   : (Γ : Ctxt d.Ty) → (opStx : AST.Op φ) → ReaderM d (Σ eff ty, Expr d Γ eff ty)

/-- NOTE: You probably don't wan't to implement this class directly, consider
implementing `LeanMLIR.DialectParse` instead! -/
class TransformReturn (d : Dialect) (φ : outParam Nat) [DialectSignature d] [TransformTy d φ] where
  mkReturn : (Γ : Ctxt d.Ty) → (opStx : AST.Op φ) → ReaderM d (Σ eff ty, Com d Γ eff ty)

/- instance of the transform dialect, plus data needed about `Op` and `Ty`. -/
variable {d φ} [DialectSignature d] [DecidableEq d.Ty] [DecidableEq d.Op]

/--
  Add a new variable to the context, and record its (absolute) index in the name mapping

  Throws an error if the variable name already exists in the mapping, essentially disallowing
  shadowing
-/
def addValToMapping (Γ : Ctxt d.Ty) (name : String) (ty : d.Ty) :
    BuilderM d (Σ (Γ' : DerivedCtxt Γ), Ctxt.Var Γ'.ctxt ty) := do
  let some nm := (←get).add name
    | throw <| .nameAlreadyDeclared name
  set nm
  return ⟨DerivedCtxt.ofCtxt Γ |>.cons ty, Ctxt.Var.last ..⟩

variable [ToString d.Ty]

/--
  Look up a name from the name mapping, and return the corresponding variable in the given context.

  Throws an error if the name is not present in the mapping (this indicates the name may be free),
  or if the type of the variable in the context is different from `expectedType`
-/
def getValFromCtxt (Γ : Ctxt d.Ty) (name : String) (expectedType : d.Ty) :
    ReaderM d (Ctxt.Var Γ expectedType) := do
  let index := (←read).lookup name
  let some index := index | throw <| .undeclaredName name
  let n := Γ.length
  if h : index >= n then
    /-  This should not happen, it indicates the passed context `Γ` is out of sync with the
        namemapping stored in the monad -/
    throw <| .indexOutOfBounds name index n
  else
    let t := Γ.toList[index]'(Nat.lt_of_not_le h)
    if h : t = expectedType then
      return ⟨index, by
        simp [← h, t, Ctxt.getElem?_eq_toList_getElem?]
      ⟩
    else
      throw <| .typeError (toString expectedType) (toString t)

def BuilderM.isOk {α : Type} (x : BuilderM d α) : Bool :=
  match x.run [] with
  | Except.ok _ => true
  | Except.error _ => false

def BuilderM.isErr {α : Type} (x : BuilderM d α) : Bool :=
  match x.run [] with
  | Except.ok _ => true
  | Except.error _ => false

def TypedSSAVal.mkTy [TransformTy d φ] : TypedSSAVal φ → ExceptM d d.Ty
  | (.name _, ty) => TransformTy.mkTy ty

/-- Translate a `TypedSSAVal` (a name with an expected type), to a variable in the context.
    This expects the name to have already been declared before -/
def TypedSSAVal.mkVal [instTransformTy : TransformTy d φ] (Γ : Ctxt d.Ty) : TypedSSAVal φ →
    ReaderM d (Σ (ty : d.Ty), Ctxt.Var Γ ty)
| (.name valStx, tyStx) => do
    let ty ← instTransformTy.mkTy tyStx
    let var ← getValFromCtxt Γ valStx ty
    return ⟨ty, var⟩

/-- A variant of `TypedSSAVal.mkVal` that takes the function `mkTy` as an argument
    instead of using the typeclass `TransformDialect`.
    This is useful when trying to implement an instance of `TransformDialect` itself,
    to cut infinite regress. -/
def TypedSSAVal.mkVal' [instTransformTy : TransformTy d φ] (Γ : Ctxt d.Ty) : TypedSSAVal φ →
    ReaderM d (Σ (ty : d.Ty), Ctxt.Var Γ ty)
| (.name valStx, tyStx) => do
    let ty ← instTransformTy.mkTy tyStx
    let var ← getValFromCtxt Γ valStx ty
    return ⟨ty, var⟩

/-- Declare a new variable,
    by adding the passed name to the name mapping stored in the monad state -/
def TypedSSAVal.newVal [instTransformTy : TransformTy d φ] (Γ : Ctxt d.Ty) : TypedSSAVal φ →
    BuilderM d (Σ (Γ' : DerivedCtxt Γ) (ty : d.Ty), Ctxt.Var Γ'.ctxt ty)
| (.name valStx, tyStx) => do
    let ty ← instTransformTy.mkTy tyStx
    let ⟨Γ, var⟩ ← addValToMapping Γ valStx ty
    return ⟨Γ, ty, var⟩

/-- Given a list of `TypedSSAVal`s, treat each as a binder and declare a new variable with the
    given name and type -/
private def declareBindings [TransformTy d φ] (Γ : Ctxt d.Ty) (vals : List (TypedSSAVal φ)) :
    BuilderM d (DerivedCtxt Γ) := do
  vals.foldlM (fun Γ' ssaVal => do
    let ⟨Γ'', _⟩ ← TypedSSAVal.newVal Γ'.ctxt ssaVal
    return Γ''
  ) (.ofCtxt Γ)

private def ssaValName : TypedSSAVal φ → String
  | (.name name, _) => name

private def typedValsToTypes [TransformTy d φ] (vals : List (TypedSSAVal φ)) :
    ExceptM d (List d.Ty) :=
  vals.mapM TypedSSAVal.mkTy

private def sigmaVarsToHVector {Γ : Ctxt d.Ty} :
    (xs : List (Σ t, Γ.Var t)) → HVector Γ.Var (xs.map Sigma.fst)
  | [] => .nil
  | ⟨_, x⟩ :: xs => .cons x (sigmaVarsToHVector xs)

private def parseValList [TransformTy d φ] (Γ : Ctxt d.Ty)
    (vals : List (TypedSSAVal φ)) : BuilderM d (List (Σ t, Γ.Var t)) := do
  (vals.mapM (TypedSSAVal.mkVal Γ) : ReaderM d _)

private def Ctxt.findVarOfType [DecidableEq Ty] : (Γ : Ctxt Ty) → (ty : Ty) → Option (Γ.Var ty)
  | ⟨[]⟩, _ => none
  | ⟨t :: ts⟩, ty =>
      if h : t = ty then
        some ⟨0, by simp [h]⟩
      else
        match Ctxt.findVarOfType ⟨ts⟩ ty with
        | some v => some v.toCons
        | none => none

private def pickVarsByType [DecidableEq d.Ty] (Γ : Ctxt d.Ty) :
    (tys : List d.Ty) → ExceptM d (HVector Γ.Var tys)
  | [] => return .nil
  | ty :: tys => do
      let some v := Ctxt.findVarOfType Γ ty
        | throw <| .generic s!"Could not build CFG fallback return: no entry variable of type {ty}"
      return .cons v (← pickVarsByType Γ tys)

private structure CFGBlockInfo (d : Dialect) [DialectSignature d] where
  name : String
  argNames : List String
  argTys : List d.Ty
  args : Ctxt d.Ty

private def mkCFGBlockInfo [TransformTy d φ] (reg : MLIR.AST.Region φ) :
    ExceptM d (CFGBlockInfo d) := do
  let argTys ← typedValsToTypes reg.args
  let argNames := reg.args.map ssaValName
  return {
    name := reg.name
    argNames := argNames
    argTys := argTys
    args := Ctxt.ofList argTys
  }

private def mkCFGEntryInfo : CFGBlockInfo d where
  name := ""
  argNames := []
  argTys := []
  args := ∅

private def lookupCFGBlockInfo (infos : List (CFGBlockInfo d)) (name : String) :
    ExceptM d (CFGBlockInfo d) := do
  let some info := infos.find? (fun info => info.name == name)
    | throw <| .generic s!"Unknown CFG block ^{name}"
  return info

private def getSymbolAttr (op : MLIR.AST.Op φ) (name : String) : ExceptM d String := do
  let some (.symbol target) := op.getAttr? name
    | throw <| .generic s!"Expected symbol attribute `{name}` on {op.name}"
  return target

private def mkCFGTarget [TransformTy d φ] (Γ : Ctxt d.Ty)
    (infos : List (CFGBlockInfo d)) (name : String) (vals : List (TypedSSAVal φ)) :
    BuilderM d (CFGTarget d Γ) := do
  let info ← lookupCFGBlockInfo infos name
  let args ← parseValList Γ vals
  if h : args.map Sigma.fst = info.argTys then
    return {
      name := info.name
      argTys := info.argTys
      args := h ▸ sigmaVarsToHVector args
    }
  else
    throw <| .generic s!"Block ^{name} expects argument types {info.argTys}, \
      but branch passes {(args.map Sigma.fst)}"

private def mkCFGTerm [TransformTy d φ] (Γ : Ctxt d.Ty)
    (infos : List (CFGBlockInfo d)) (retTys : List d.Ty) (op : MLIR.AST.Op φ) :
    BuilderM d (CFGTerm d Γ retTys) := do
  match op.name with
  | "llvm.return" =>
      let args ← parseValList Γ op.args
      if h : args.map Sigma.fst = retTys then
        return .ret (h ▸ sigmaVarsToHVector args)
      else
        throw <| .generic s!"Return types {(args.map Sigma.fst)} do not match expected {retTys}"
  | "llvm.br" =>
      let target ← getSymbolAttr (d:=d) op "target"
      return .br (← mkCFGTarget Γ infos target op.args)
  | "llvm.cond_br" =>
      let trueName ← getSymbolAttr (d:=d) op "trueTarget"
      let falseName ← getSymbolAttr (d:=d) op "falseTarget"
      let trueInfo ← lookupCFGBlockInfo infos trueName
      match op.args with
      | [] => throw <| .generic "llvm.cond_br expects a condition argument"
      | condArg :: branchArgs =>
          let ⟨condTy, cond⟩ ← TypedSSAVal.mkVal Γ condArg
          let trueArgs := branchArgs.take trueInfo.argTys.length
          let falseArgs := branchArgs.drop trueInfo.argTys.length
          let trueTarget ← mkCFGTarget Γ infos trueName trueArgs
          let falseTarget ← mkCFGTarget Γ infos falseName falseArgs
          return .condBr (condTy := condTy) cond trueTarget falseTarget
  | opName =>
      throw <| .unsupportedOp s!"Expected CFG terminator, found {opName}"

private def isCFGTerminatorName (name : String) : Bool :=
  name == "llvm.return" || name == "llvm.br" || name == "llvm.cond_br"

private def mkCFGBodyHelper
    [TransformTy d φ] [instTransformExpr : TransformExpr d φ]
    (Γ : Ctxt d.Ty) (infos : List (CFGBlockInfo d)) (retTys : List d.Ty) :
    List (MLIR.AST.Op φ) → BuilderM d (CFGBody d Γ .impure retTys)
  | [] => throw <| .generic "Ill-formed CFG block (empty)"
  | [term] => do
      return .terminator (← mkCFGTerm Γ infos retTys term)
  | op :: rest => do
      if isCFGTerminatorName op.name then
        throw <| .generic s!"CFG terminator {op.name} must be the final operation in a block"
      let ⟨eff₁, ty₁, expr⟩ ← instTransformExpr.mkExpr Γ op
      let numExpectedReturns := ty₁.length
      if op.res.length != numExpectedReturns then
        throw <| .generic
          s!"Expected {numExpectedReturns} return variables, but found {op.res.length}"
      else
        let _ ← (op.res.zip ty₁).foldlM (init:=Γ) fun Γ ⟨var, ty⟩ => do
          let ⟨Γ', _⟩ ← addValToMapping Γ (SSAValToString var.1) ty
          return Γ'
        let body ← mkCFGBodyHelper (ty₁ ++ Γ) infos retTys rest
        let expr := expr.changeEffect (by cases eff₁ <;> simp)
        return .var expr body

private def mkCFGBlock [TransformTy d φ] [TransformExpr d φ]
    (Γ : Ctxt d.Ty) (baseMapping : NameMapping) (infos : List (CFGBlockInfo d))
    (retTys : List d.Ty) (info : CFGBlockInfo d) (ops : List (MLIR.AST.Op φ)) :
    ExceptM d (CFGBlock d Γ .impure retTys) := do
  let bodyΓ := info.args ++ Γ
  let mapping := info.argNames ++ baseMapping
  let ⟨body, _⟩ ← StateT.run (mkCFGBodyHelper bodyΓ infos retTys ops) mapping
  return .mk info.name info.args body

private def cfgBlocksOfList {Γ : Ctxt d.Ty} {retTys : List d.Ty} :
    List (CFGBlock d Γ .impure retTys) → CFGBlocks d Γ .impure retTys
  | [] => .nil
  | block :: blocks => .cons block (cfgBlocksOfList blocks)

private def findReturnTypes [TransformTy d φ] : List (MLIR.AST.Region φ) →
    ExceptM d (Option (List d.Ty))
  | [] => return none
  | reg :: regs => do
      match reg.ops.find? (fun op => op.name == "llvm.return") with
      | some op => return some (← typedValsToTypes op.args)
      | none => findReturnTypes regs

private def regionNeedsCFG (reg : MLIR.AST.Region φ) : Bool :=
  !reg.blocks.isEmpty || reg.ops.any (fun op => op.name == "llvm.br" || op.name == "llvm.cond_br")

private def mkCFGCom [TransformTy d φ] [TransformExpr d φ]
    (reg : MLIR.AST.Region φ) :
    ExceptM d (Σ (Γ : Ctxt d.Ty) (eff : EffectKind) (ty : _), Com d Γ eff ty) := do
  let entryTys ← typedValsToTypes reg.args
  let entryNames := reg.args.map ssaValName
  -- The straight-line front-end (`mkCom` -> `declareBindings`) declares the
  -- surface arguments left-to-right with `addValToMapping`, and that PREPENDS
  -- to both the context and the name mapping.  Its entry context and mapping
  -- are therefore the REVERSE of surface order.  Building the CFG entry context
  -- in surface order instead made the two front-ends resolve the same `%name`
  -- to OPPOSITE de Bruijn indices while producing an identical `Ctxt` type, so
  -- nothing caught the divergence: one shared `InputValuation` bound the
  -- arguments in opposite orders on a CFG source and a straight-line target,
  -- which fabricates counterexamples for >=2-argument mixed-front-end pairs.
  -- Reverse both together so the invariant (mapping index i <-> Γ index i) is
  -- preserved and the two front-ends agree.
  let Γ := Ctxt.ofList entryTys.reverse
  let baseMapping := entryNames.reverse
  let entryInfo : CFGBlockInfo d := { mkCFGEntryInfo with name := reg.name }
  let blockInfos ← reg.blocks.mapM mkCFGBlockInfo
  let infos := entryInfo :: blockInfos
  let some retTys ← findReturnTypes (reg :: reg.blocks)
    | throw <| .generic "Could not infer CFG return types: no llvm.return terminator found"
  let entryBlock ← mkCFGBlock Γ baseMapping infos retTys entryInfo reg.ops
  let blocks ← (blockInfos.zip reg.blocks).mapM fun ⟨info, blockReg⟩ =>
    mkCFGBlock Γ baseMapping infos retTys info blockReg.ops
  let fallbackVars ← pickVarsByType Γ retTys
  let fallback : Com d Γ .impure retTys := .rets fallbackVars
  return ⟨Γ, .impure, retTys, Com.cfg reg.name (cfgBlocksOfList (entryBlock :: blocks)) fallback⟩

private def mkComHelper
  [TransformTy d φ] [instTransformExpr : TransformExpr d φ] [instTransformReturn :
    TransformReturn d φ]
  (Γ : Ctxt d.Ty) :
    List (MLIR.AST.Op φ) → BuilderM d (Σ eff ty, Com d Γ eff ty)
  | [retStx] => do
      instTransformReturn.mkReturn Γ retStx
  | var::rest => do
    let ⟨_eff₁, ty₁, expr⟩ ← (instTransformExpr.mkExpr Γ var)
    let numExpectedReturns := ty₁.length
    if var.res.length != numExpectedReturns then
      throw <| .generic
        s!"Expected {numExpectedReturns} return variables, but found {var.res.length}"
    else
      let _ ← (var.res.zip ty₁).foldlM (init:=Γ) fun Γ ⟨var, ty⟩ => do
        let ⟨Γ', _⟩ ← addValToMapping Γ (SSAValToString var.1) ty
        return Γ'
      let ⟨_eff₂, ty₂, body⟩ ← mkComHelper (ty₁ ++ Γ) rest
      return ⟨_, ty₂, Com.letSup expr body⟩
  | [] => throw <| .generic "Ill-formed (empty) block"

def mkCom [TransformTy d φ] [TransformExpr d φ] [TransformReturn d φ]
  (reg : MLIR.AST.Region φ) :
  ExceptM d (Σ (Γ : Ctxt d.Ty) (eff : EffectKind) (ty : _), Com d Γ eff ty) :=
  if regionNeedsCFG reg then
    mkCFGCom reg
  else
    match reg.ops with
    | [] => throw <| .generic "Ill-formed region (empty)"
    | coms => BuilderM.runWithEmptyMapping <| do
      let Γ ← declareBindings ∅ reg.args
      let com ← mkComHelper Γ coms
      return ⟨Γ, com⟩

end MLIR.AST
