import Lean.Elab.Command
import Lean.Meta
import LeanMLIR.Dialects.LLVM.FunctionEnvCore

namespace InstCombine

open LLVM

namespace LLVMMemory

/--
Auto-resolved callee implementation for an LLVM symbol name and call signature.

`name` is expected to be a compile-time literal at `llvm.call` sites.
-/
class LLVMCallee (σ : Type) (name : outParam String)
    (argTys : outParam (List LLVM.Ty)) (retTy : LLVM.Ty) where
  funcDef : FuncDef σ

/--
Auto-generated call environment keyed by caller context/result shape.
Attribute expansion creates one instance per `@[llvm_callee]` declaration.
-/
class LLVMCalleeEnv (σ : Type) (Γ : Ctxt LLVM.Ty) (tys : List LLVM.Ty) where
  env : FunctionEnv σ

/-- Poison fallback used when generated callee wrappers cannot satisfy side conditions. -/
def poisonFuncDef (argTys : List LLVM.Ty) (retTy : LLVM.Ty) : FuncDef σ where
  argTys := argTys
  retTy := retTy
  denote := fun _ _ s => .value (.poison, s)

end LLVMMemory

end InstCombine

open Lean Meta

namespace InstCombine.LLVMMemory

private def mkDefaultCalleeName (declName : Name) : String :=
  declName.getString!

/-- Parser for `@[llvm_callee]` and `@[llvm_callee "custom_name"]`. -/
syntax (name := llvm_callee) "llvm_callee" (ppSpace (ident <|> str))? : attr

private def parseCalleeNameArg (stx : Syntax) : CoreM String := do
  if stx.isIdent then
    pure stx.getId.toString
  else if let some s := stx.isStrLit? then
    pure s
  else
    throwErrorAt stx
      "invalid `[llvm_callee]` argument, expected identifier or string literal"

private def getCalleeNameFromAttr (declName : Name) (stx : Syntax) : CoreM String := do
  if stx.getKind == ``llvm_callee then
    if stx[1].isNone then
      pure (mkDefaultCalleeName declName)
    else
      parseCalleeNameArg stx[1][0]
  else
    match (← Attribute.Builtin.getId? stx) with
    | none => pure (mkDefaultCalleeName declName)
    | some id => pure id.toString

private def parseSingletonTyList (tys : Expr) : MetaM Expr := do
  let tys ← whnf tys
  let fn := tys.getAppFn
  let args := tys.getAppArgs
  if fn.isConstOf ``_root_.List.singleton && args.size ≥ 1 then
    pure args[args.size - 1]!
  else if fn.isConstOf ``_root_.List.cons && args.size ≥ 2 then
    let retTy := args[args.size - 2]!
    let tail := args[args.size - 1]!
    let tail ← whnf tail
    let tailFn := tail.getAppFn
    unless tailFn.isConstOf ``_root_.List.nil do
      throwError "only single-result callees are supported by `[llvm_callee]`"
    pure retTy
  else
    throwError "expected return type list of shape `[retTy]`, got{indentExpr tys}"

private def parsePureComType (ty : Expr) : MetaM (Expr × Expr × Expr × Expr) := do
  let ty ← whnf ty
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  unless fn.isConstOf ``_root_.Com && args.size ≥ 4 do
    throwError "`[llvm_callee]` expects a declaration returning `Com LLVM ⟨argTys⟩ .pure [retTy]`, got{indentExpr ty}"
  let ctx := args[args.size - 3]!
  let eff := args[args.size - 2]!
  let retTys := args[args.size - 1]!
  unless (← isDefEq eff (mkConst ``_root_.EffectKind.pure)) do
    throwError "`[llvm_callee]` only supports `.pure` callee bodies"
  let argTys ← mkAppM ``Ctxt.toList #[ctx]
  let retTy ← parseSingletonTyList retTys
  pure (ctx, argTys, retTy, retTys)

private partial def mkFuncDefExpr
    (σ declConst argTys retTy : Expr)
    (binders : Array Expr) (i : Nat) (argsForDecl : Array Expr) : MetaM Expr := do
  if h : i < binders.size then
    let b := binders[i]
    let bTy ← inferType b
    if (← isProp bTy) then
      let poisonFd ← mkAppOptM ``_root_.InstCombine.LLVMMemory.poisonFuncDef
        #[some σ, some argTys, some retTy]
      withLocalDeclD `h bTy fun hp => do
        let thenExpr ← mkFuncDefExpr σ declConst argTys retTy binders (i + 1) (argsForDecl.push hp)
        let thenFn ← mkLambdaFVars #[hp] thenExpr
        withLocalDeclD `hn (mkApp (mkConst ``_root_.Not) bTy) fun hn => do
          let elseFn ← mkLambdaFVars #[hn] poisonFd
          let dec := mkApp (mkConst ``_root_.Classical.propDecidable) bTy
          mkAppOptM ``_root_.dite #[none, some bTy, some dec, some thenFn, some elseFn]
    else
      mkFuncDefExpr σ declConst argTys retTy binders (i + 1) (argsForDecl.push b)
  else
    let body := mkAppN declConst argsForDecl
    mkAppOptM ``_root_.InstCombine.LLVMMemory.FuncDef.ofCom
      #[some σ, some argTys, some retTy, some body]

private def mkAndRegisterLLVMCalleeInstance (declName : Name) (calleeName : String) : MetaM Unit := do
  let constInfo ← getConstInfo declName
  let levelParams := constInfo.levelParams
  let declConst := mkConst declName (levelParams.map Level.param)
  withLocalDeclD `σ (mkSort (Level.succ levelZero)) fun σ => do
    forallTelescopeReducing constInfo.type fun binders suffixTy => do
      let allBinders := binders
      let calleeNameExpr := mkStrLit calleeName
      let (ctx, argTys, retTy, retTys) ← parsePureComType suffixTy
      let fd ← mkFuncDefExpr σ declConst argTys retTy allBinders 0 #[]
      let valueBody ← mkAppOptM ``_root_.InstCombine.LLVMMemory.LLVMCallee.mk
        #[some σ, some calleeNameExpr, some argTys, some retTy, some fd]

      let instTypeBody ← mkAppOptM ``_root_.InstCombine.LLVMMemory.LLVMCallee
        #[some σ, some calleeNameExpr, some argTys, some retTy]

      let closed ← Closure.mkValueTypeClosure instTypeBody valueBody (zetaDelta := true)
      let instType := closed.type
      let instValue := closed.value

      if instType.hasMVar || instValue.hasMVar then
        throwError "internal error while generating `[llvm_callee]` instance for `{declName}`"

      let instName ← mkFreshUserName (declName ++ `_llvm_callee_inst)
      let instDecl ← mkDefinitionValInferringUnsafe
        instName closed.levelParams.toList instType instValue ReducibilityHints.abbrev
      modifyEnv (Lean.addNoncomputable · instName)
      addDecl (.defnDecl instDecl)
      addInstance instName .global (eval_prio default)

      let envExpr ← mkAppOptM ``_root_.InstCombine.LLVMMemory.FunctionEnv.singleton
        #[some σ, some calleeNameExpr, some fd]
      let envValueBody ← mkAppOptM ``_root_.InstCombine.LLVMMemory.LLVMCalleeEnv.mk
        #[some σ, some ctx, some retTys, some envExpr]
      let envTypeBody ← mkAppOptM ``_root_.InstCombine.LLVMMemory.LLVMCalleeEnv
        #[some σ, some ctx, some retTys]

      let envClosed ← Closure.mkValueTypeClosure envTypeBody envValueBody (zetaDelta := true)
      let envInstType := envClosed.type
      let envInstValue := envClosed.value

      if envInstType.hasMVar || envInstValue.hasMVar then
        throwError "internal error while generating `[llvm_callee]` call-environment instance for `{declName}`"

      let envInstName ← mkFreshUserName (declName ++ `_llvm_callee_env_inst)
      let envInstDecl ← mkDefinitionValInferringUnsafe
        envInstName envClosed.levelParams.toList envInstType envInstValue ReducibilityHints.abbrev
      modifyEnv (Lean.addNoncomputable · envInstName)
      addDecl (.defnDecl envInstDecl)
      addInstance envInstName .global (eval_prio default)

private def registerLLVMCalleeAttribute (attrName : Name) : IO Unit :=
  registerBuiltinAttribute {
    name := attrName
    descr := "register an LLVM callee definition for automatic call-environment synthesis"
    add := fun declName stx kind => Prod.fst <$> MetaM.run do
      unless kind == .global do
        throwAttrMustBeGlobal attrName kind
      let calleeName ← getCalleeNameFromAttr declName stx
      mkAndRegisterLLVMCalleeInstance declName calleeName
  }

initialize do
  registerLLVMCalleeAttribute `llvm_callee

end InstCombine.LLVMMemory
