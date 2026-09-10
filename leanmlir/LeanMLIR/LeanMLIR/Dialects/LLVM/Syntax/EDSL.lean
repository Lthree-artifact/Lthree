/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.MLIRSyntax
import LeanMLIR.Dialects.LLVM.Basic
import LeanMLIR.Dialects.LLVM.Syntax.PrettyEDSL

import Qq

open Qq Lean Meta Elab.Term Elab Command
open InstCombine (LLVM MetaLLVM MOp Width)

open MLIR

namespace InstcombineTransformDialect
open AST (Op TransformError)
private abbrev ReaderM (φ) := AST.ReaderM (MetaLLVM φ)
private abbrev NoWrapFlags := _root_.LLVM.NoWrapFlags
private abbrev ZeroPoisonFlag := _root_.LLVM.ZeroPoisonFlag
private abbrev IntMinPoisonFlag := _root_.LLVM.IntMinPoisonFlag
private def noWrapNone : NoWrapFlags := ((_root_.LLVM.NoWrapFlags.mk) (Bool.false) (Bool.false))
private def noWrapNSW : NoWrapFlags := ((_root_.LLVM.NoWrapFlags.mk) (Bool.true) (Bool.false))
private def noWrapNUW : NoWrapFlags := ((_root_.LLVM.NoWrapFlags.mk) (Bool.false) (Bool.true))
private def noWrapBoth : NoWrapFlags := ((_root_.LLVM.NoWrapFlags.mk) (Bool.true) (Bool.true))
private def zeroPoisonFalse : ZeroPoisonFlag := ((_root_.LLVM.ZeroPoisonFlag.mk) (Bool.false))
private def zeroPoisonTrue : ZeroPoisonFlag := ((_root_.LLVM.ZeroPoisonFlag.mk) (Bool.true))
private def intMinPoisonFalse : IntMinPoisonFlag := ((_root_.LLVM.IntMinPoisonFlag.mk) (Bool.false))
private def intMinPoisonTrue : IntMinPoisonFlag := ((_root_.LLVM.IntMinPoisonFlag.mk) (Bool.true))
private def widthParamIdxAttrName : String := "__leanmlir_width_param_idx"

private def parseSymbolRef : MLIR.AST.AttrValue φ → Except TransformError String
  | .symbol s => return s
  | .nestedsymbol lhs rhs => return s!"{← parseSymbolRef lhs}::{← parseSymbolRef rhs}"
  | _ => throw <| .generic "Expected symbol reference"

private def natToAttrValStx (n : Nat) (ty : TSyntax `mlir_type) : TermElabM (TSyntax `mlir_attr_val) := do
  let nStx : TSyntax `num := Syntax.mkNumLit (toString n)
  `(mlir_attr_val| $nStx:num : $ty)

def mkTy : MLIR.AST.MLIRType φ → MLIR.AST.ExceptM (MetaLLVM φ) ((MetaLLVM φ).Ty)
  | MLIR.AST.MLIRType.int MLIR.AST.Signedness.Signless w => return .bitvec w
  | MLIR.AST.MLIRType.undefined s =>
      if s.startsWith "llvm.ptr" || s.startsWith "ptr" then
        return .ptr
      else
        throw .unsupportedType
  | _ => throw .unsupportedType

instance instTransformTy : AST.TransformTy (MetaLLVM φ) φ := { mkTy }
instance : AST.TransformTy (LLVM) 0 := { mkTy }

def getOutputWidth (opStx : MLIR.AST.Op φ) (op : String) :
    Except TransformError (Width φ) := do
  match opStx.res with
  | res::[] =>
    match res.2 with
    | .int _ w => pure w
    | _ => throw <| .generic s!"The operation {op} must output an integer type"
  | _ => throw <| .generic s!"The operation {op} must have a single output"

/-- Given a variable of arbitrary type, return its width.

This relies on the fact that `bitvec _` is the only type currently modelled.
In future, this might start throwing errors, if the type is not a bitvec.
-/
def getVarWidth {Γ : Ctxt (MetaLLVM φ).Ty} : (Σ t, Γ.Var t) → Width φ
  | ⟨.bitvec w, _⟩ => w
  | ⟨.ptr, _⟩ => .concrete 64

def parseOverflowFlags (op : AST.Op φ) : ReaderM φ NoWrapFlags := do
  match op.getAttr? "overflowFlags" with
  | .none => return noWrapNone
  | .some y => match y with
    | .opaque_ "llvm.overflow" "nsw" => return noWrapNSW
    | .opaque_ "llvm.overflow" "nuw" => return noWrapNUW
    | .opaque_ "llvm.overflow" "none" => return noWrapNone
    | .list [.opaque_ "llvm.overflow" "nuw", .opaque_ "llvm.overflow" "nsw"]
    | .list [.opaque_ "llvm.overflow" "nsw", .opaque_ "llvm.overflow" "nuw"] =>
        return noWrapBoth
    | _ =>
      -- Parse oveflowFlags passed as integer attribute
          let ⟨n, _ ⟩ ← op.getIntAttr "overflowFlags"
          match n with
          | 0 => return noWrapNone
          | 1 => return noWrapNSW
          | 2 => return noWrapNUW
          | 3 => return noWrapBoth
          | s => throw <| .generic s!"The overflow flag with predicate {s} is not allowed. \
            We currently support nsw (no signed wrap) and nuw (no unsigned wrap)"

def parseZeroPoisonFlag (op : AST.Op φ) : ReaderM φ ZeroPoisonFlag := do
  match op.getAttr? "is_zero_poison" with
  | .none => return zeroPoisonFalse
  | .some _ =>
      if (← op.getBoolAttr "is_zero_poison") then
        return zeroPoisonTrue
      else
        return zeroPoisonFalse

def parseIntMinPoisonFlag (op : AST.Op φ) : ReaderM φ IntMinPoisonFlag := do
  match op.getAttr? "is_int_min_poison" with
  | .none => return intMinPoisonFalse
  | .some _ =>
      if (← op.getBoolAttr "is_int_min_poison") then
        return intMinPoisonTrue
      else
        return intMinPoisonFalse
/--
Maps integer predicate codes (as defined in the MLIR LLVM dialect) to their corresponding
`LLVM.IntPred` constructors.
This reflects MLIR’s encoding of predicates as numeric values in attributes-/
def parseIcmpPredicate (n : Int) : AST.ReaderM (MetaLLVM φ) (LLVM.IntPred) := do
  match n with
  | 0 => return .eq
  | 1 => return .ne
  | 8 => return .ugt
  | 9 => return .uge
  | 6 => return .ult
  | 7 => return .ule
  | 4 => return .sgt
  | 5 => return .sge
  | 2 => return .slt
  | 3 => return .sle
  | _ => throw <| .generic s!"The icmp predicate {n} is not supported"

open InstCombine.MOp in
def mkExpr (Γ : Ctxt (MetaLLVM φ).Ty) (opStx : MLIR.AST.Op φ) :
    AST.ReaderM (MetaLLVM φ) (Σ eff ty, Expr (MetaLLVM φ) Γ eff ty) := do
  let args ← opStx.parseArgs Γ

  /- `binW` is the (lazily computed) width, assuming a binary operation -/
  let binW : AST.ReaderM (MetaLLVM φ) (Width φ) := do
  -- ^^ NOTE: `binW` is bound with := rather than ← on purpose, to ensure laziness
    let args ← args.assumeArity 2
    return getVarWidth args[0]

  /- `unW` is the (lazily computed) width, assuming an unary operation -/
  let unW := do
    let args ← args.assumeArity 1
    return getVarWidth args[0]

  let mkExprOf := opStx.mkExprOf (args? := args) Γ
  match opStx.name with
    -- Ternary Operations
    | "llvm.select" =>
        let args ← args.assumeArity 3
        let w := getVarWidth args[1]
        mkExprOf <| select w
    -- Binary Operations
    | "llvm.and"      => mkExprOf <| and (← binW)
    | "llvm.isPowerOf2" => mkExprOf <| InstCombine.MOp.isPowerOf2 (← unW)
    | "llvm.or"       => mkExprOf <| or (← binW) ⟨opStx.hasAttr "isDisjoint"⟩
    | "llvm.xor"      => mkExprOf <| xor (← binW)
    | "llvm.urem"     => mkExprOf <| urem (← binW)
    | "llvm.srem"     => mkExprOf <| srem (← binW)
    | "llvm.getelementptr" =>
      let args ← args.assumeArity 2
      let elemTy ← opStx.getTypeAttr "elem_type"
      let .int _ elemW := elemTy
        | throw <| .generic s!"Expected value of attribute `elem_type` to be an integer type"
      let idxW := getVarWidth args[1]
      mkExprOf <| getelementptr elemW idxW
    | "llvm.lshr"     => mkExprOf <| lshr (← binW) ⟨opStx.hasAttr "isExact"⟩
    | "llvm.ashr"     => mkExprOf <| ashr (← binW) ⟨opStx.hasAttr "isExact"⟩
    | "llvm.sdiv"     => mkExprOf <| sdiv (← binW) ⟨opStx.hasAttr "isExact"⟩
    | "llvm.udiv"     => mkExprOf <| udiv (← binW) ⟨opStx.hasAttr "isExact"⟩
    | "llvm.shl"      => mkExprOf <| shl (← binW) (← parseOverflowFlags opStx)
    | "llvm.add"      => mkExprOf <| add (← binW) (← parseOverflowFlags opStx)
    | "llvm.mul"      => mkExprOf <| mul (← binW) (← parseOverflowFlags opStx)
    | "llvm.sub"      => mkExprOf <| sub (← binW) (← parseOverflowFlags opStx)
    | "llvm.icmp.eq"  => mkExprOf <| icmp .eq (← binW)
    | "llvm.icmp.ne"  => mkExprOf <| icmp .ne (← binW)
    | "llvm.icmp.ugt" => mkExprOf <| icmp .ugt (← binW)
    | "llvm.icmp.uge" => mkExprOf <| icmp .uge (← binW)
    | "llvm.icmp.ult" => mkExprOf <| icmp .ult (← binW)
    | "llvm.icmp.ule" => mkExprOf <| icmp .ule (← binW)
    | "llvm.icmp.sgt" => mkExprOf <| icmp .sgt (← binW)
    | "llvm.icmp.sge" => mkExprOf <| icmp .sge (← binW)
    | "llvm.icmp.slt" => mkExprOf <| icmp .slt (← binW)
    | "llvm.icmp.sle" => mkExprOf <| icmp .sle (← binW)
     -- Alternative representation of icmp instructions like in MLIR generic syntax
    | "llvm.icmp" =>
      let ⟨n, ty⟩ ← opStx.getIntAttr "predicate"
      mkExprOf <| icmp (← parseIcmpPredicate n) (← binW)
    -- Unary Operations
    | "llvm.not"    => mkExprOf <| .not (← unW)
    | "llvm.neg"    => mkExprOf <| neg (← unW)
    | "llvm.copy"   => mkExprOf <| copy (← unW)
    | "llvm.freeze" => mkExprOf <| freeze (← unW)
    | "llvm.abs" | "llvm.intr.abs" => mkExprOf <| abs (← unW) (← parseIntMinPoisonFlag opStx)
    | "llvm.ctpop"  => mkExprOf <| ctpop (← unW)
    | "llvm.ctlz" | "llvm.intr.ctlz" => mkExprOf <| ctlz (← unW) (← parseZeroPoisonFlag opStx)
    | "llvm.cttz" | "llvm.intr.cttz" => mkExprOf <| cttz (← unW) (← parseZeroPoisonFlag opStx)
    | "llvm.assume" => mkExprOf <| .assume_
    | "llvm.load"   => mkExprOf <| load (← getOutputWidth opStx "load")
    | "llvm.store"  =>
      let args ← args.assumeArity 2
      mkExprOf <| store (getVarWidth args[1])
    | "llvm.call" =>
      let calleeAttr ← opStx.getAttr "callee"
      let calleeName ← parseSymbolRef calleeAttr
      let retTy ←
        match opStx.res with
        | [(_, t)] => mkTy t
        | [] => throw <| .generic "llvm.call must have exactly one result"
        | _ => throw <| .generic "llvm.call with multiple results is not supported"
      mkExprOf <| MOp.call retTy calleeName args.types
    | "llvm.alloca" =>
      let t ← opStx.getTypeAttr "elem_type"
      let .int _ w := t
        | throw <| .generic s!"Expected value of attribute `elem_type` to be an integer type"
      mkExprOf <| alloca w
    | "llvm.zext"   => mkExprOf <| zext (← unW) (← getOutputWidth opStx "zext") ⟨ opStx.hasAttr "nonNeg" ⟩
    | "llvm.sext"   => mkExprOf <| sext (← unW) (← getOutputWidth opStx "sext")
    | "llvm.trunc"  => mkExprOf <| trunc (← unW) (← getOutputWidth opStx "trunc") (← parseOverflowFlags opStx)
    -- Constant
    | "llvm.mlir.constant" =>
      let ⟨val, ty⟩ ← opStx.getIntAttr "value"
      let opTy ← mkTy ty
      let .bitvec w := opTy
        | throw <| .generic "llvm.mlir.constant expects integer result type"
      match opStx.getAttr? widthParamIdxAttrName with
      | .none =>
          mkExprOf <| const w val
      | .some (.int idx _) =>
          if hidx : idx ≥ 0 then
            let idxNat := Int.toNat idx
            if h : idxNat < φ then
              mkExprOf <| MOp.constParam w ⟨idxNat, h⟩
            else
              throw <| .generic s!"Attribute `{widthParamIdxAttrName}` out of bounds: {idxNat}, φ = {φ}"
          else
            throw <| .generic s!"Attribute `{widthParamIdxAttrName}` must be nonnegative, got {idx}"
      | .some _ =>
          throw <| .generic s!"Attribute `{widthParamIdxAttrName}` must be an integer"
    -- Fallback
    | opName => throw <| .unsupportedOp opName

instance : AST.TransformExpr (MetaLLVM φ) φ := { mkExpr }

def mkReturn (Γ : Ctxt (MetaLLVM φ).Ty) (opStx : MLIR.AST.Op φ) :
    MLIR.AST.ReaderM (MetaLLVM φ) (Σ eff ty, Com (MetaLLVM φ) Γ eff ty) := do
  if opStx.name ≠ "llvm.return" then
    throw <| .unsupportedOp s!"Tried to build return out of non-return statement {opStx.name}"
  else
    let args ← (← opStx.parseArgs Γ).assumeArity 1
    let ⟨ty, v⟩ := args[0]
    return ⟨.pure, [ty], Com.ret v⟩

instance : AST.TransformReturn (MetaLLVM φ) φ := { mkReturn }

/-!
  ## Instantiation
  Finally, we show how to instantiate a family of programs to a concrete program
-/

open InstCombine LLVM Qq in
def MetaLLVM.instantiate (vals : Vector Expr φ) : DialectMetaMorphism (MetaLLVM φ) q(LLVM) where
  mapTy := fun
  | .bitvec w =>
    mkApp (mkConst ``Ty.bitvec) <| w.metaInstantiate vals
  | .ptr =>
    mkConst ``Ty.ptr
  mapOp :=
    fun
    | .binary w binOp =>
      let w := w.metaInstantiate vals
      mkApp2 (mkConst ``Op.binary) w (toExpr binOp)
    | .unary w unOp =>
      let w := w.metaInstantiate vals

      /- NOTE: `Op` contructors expect a `Nat` argument to indicate the width,
          but `MOp.UnaryOp` constructors expect `ConcreteOrMVar Nat 0`.
          Hence, we define `mapWidth` to construct the latter
      -/
      let mapWidth (w : ConcreteOrMVar Nat φ) : Q(ConcreteOrMVar Nat 0) :=
        let w : Q(Nat) := w.metaInstantiate vals
        q(.concrete $w)
      open MOp (UnaryOp) in
      let unOp : Q(UnaryOp 0) := match unOp with
        | .neg => q(.neg)
        | .not => q(.not)
        | .copy => q(.copy)
        | .freeze => q(.freeze)
        | .abs flag => q(.abs $flag)
        | .ctpop => q(.ctpop)
        | .ctlz flag => q(.ctlz $flag)
        | .cttz flag => q(.cttz $flag)
        | .trunc w' flags => q(.trunc $(mapWidth w') $flags)
        | .zext w' nnegFlag => q(.zext $(mapWidth w') $nnegFlag)
        | .sext w' => q(.sext $(mapWidth w'))
      mkApp2 (mkConst ``Op.unary) w unOp
    | .isPowerOf2 w =>
      let w : Q(Nat) := w.metaInstantiate vals
      mkApp (mkConst ``Op.isPowerOf2) w
    | .select w =>
      let w : Q(Nat) := w.metaInstantiate vals
      mkApp (mkConst ``Op.select) w
    | .icmp c w =>
      let w := w.metaInstantiate vals
      let c := toExpr c
      mkApp2 (mkConst ``Op.icmp) c w
    | .assume_ =>
      mkConst ``Op.assume
    | .getelementptr elemW idxW =>
      let elemW := elemW.metaInstantiate vals
      let idxW := idxW.metaInstantiate vals
      mkApp2 (mkConst ``Op.getelementptr) elemW idxW
    | .load w =>
      let w := w.metaInstantiate vals
      mkApp (mkConst ``Op.load) w
    | .store w =>
      let w := w.metaInstantiate vals
      mkApp (mkConst ``Op.store) w
    | .alloca w =>
      let w := w.metaInstantiate vals
      mkApp (mkConst ``Op.alloca) w
    | .call retTy fnName argTys =>
      let rec mapTyQ : MTy φ → Q(LLVM.Ty)
        | .bitvec w =>
            let w : Q(Nat) := w.metaInstantiate vals
            q(Ty.bitvec $w)
        | .ptr =>
            q(Ty.ptr)
      let rec mapTyListQ : List (MTy φ) → Q(List LLVM.Ty)
        | [] => q([])
        | ty :: tys => q($(mapTyQ ty) :: $(mapTyListQ tys))
      mkApp3 (mkConst ``Op.call) (mapTyQ retTy) (toExpr fnName) (mapTyListQ argTys)
    | .const w val =>
      let w := w.metaInstantiate vals
      let val := toExpr val
      mkApp2 (mkConst ``Op.const) w val
    | .constParam w idx =>
      let w := w.metaInstantiate vals
      let n : Q(Nat) := vals.get idx
      let val : Q(Int) := q(Int.ofNat $n)
      mkApp2 (mkConst ``Op.const) w val

end InstcombineTransformDialect


open SSA InstcombineTransformDialect InstCombine in
elab "[llvm(" mvars:term,* ")| " reg:mlir_region "]" : term => do
  withTraceNode `LeanMLIR.Elab (pure m!"{exceptEmoji ·} elaborate LLVM program") <| do

  let φ : Nat := mvars.getElems.size
  let mut mvarNameToIdx : Std.HashMap Name Nat := {}
  for i in [:mvars.getElems.size] do
    let stx := mvars.getElems[i]!
    match stx with
    | `(term| $id:ident) =>
        mvarNameToIdx := mvarNameToIdx.insert id.getId.eraseMacroScopes i
    | _ =>
        pure ()

  let reg'Raw ← reg.raw.rewriteBottomUpM fun stx => do
    match stx with
    | `(mlir_op| $res:mlir_op_operand = llvm.mlir.constant( $x:ident $[: $inner_type]? ) $[: $outer_type]? ) =>
        let key := x.getId.eraseMacroScopes
        match mvarNameToIdx[key]? with
        | some idx =>
            let outerTy : TSyntax `mlir_type ← match outer_type with
              | some t => pure t
              | none => `(mlir_type| _)
            let innerTy : TSyntax `mlir_type := match inner_type with
              | some t => t
              | none => outerTy
            let idxAttrTy : TSyntax `mlir_type ← `(mlir_type| i64)
            let valueAttr ← natToAttrValStx 0 innerTy
            let idxAttr ← natToAttrValStx idx idxAttrTy
            let repl ← `(mlir_op| $res:mlir_op_operand = "llvm.mlir.constant"()
              {value = $valueAttr, __leanmlir_width_param_idx = $idxAttr} : () -> ($outerTy))
            pure repl.raw
        | none =>
            pure stx
    | _ =>
        pure stx
  let reg' : TSyntax `mlir_region := ⟨reg'Raw⟩
  let ⟨_, _, _, mcom⟩ ← SSA.elabIntoComObj reg' (MetaLLVM φ)

  let res ← mcom.metaMap <| MetaLLVM.instantiate <| ←do
    let mvars : Vector _ φ := ⟨mvars.getElems, rfl⟩
    mvars.mapM fun (stx : Term) =>
      elabTermEnsuringType stx (mkConst ``Nat)

  trace[LeanMLIR.Elab] "elaborated expression: {res}"
  return res

macro "[llvm| " reg:mlir_region "]" : term => `([llvm()| $reg])
