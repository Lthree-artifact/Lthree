import LeanMLIR.MLIRSyntax.PrettyEDSL
open Lean

namespace MLIR.EDSL
open Pretty

/-!
# Pretty syntax for `ctlz` / `cttz` zero-poison flags

This file defines the `MLIR.Pretty.zero_poison_op` syntax category for unary LLVM
operations whose semantics depend on the Boolean `is_zero_poison` attribute.

The pretty syntax is:
`%r = llvm.ctlz %x, false : i32`
`%r = llvm.cttz %x, true : i32`

These forms expand to the canonical generic LLVM intrinsic names:
`"llvm.intr.ctlz"` and `"llvm.intr.cttz"`.
-/

declare_syntax_cat MLIR.Pretty.zero_poison_op
syntax (mlir_op_operand " = ")? MLIR.Pretty.zero_poison_op mlir_op_operand ", " term
  (" : " mlir_type)? : mlir_op

private def canonicalizeZeroPoisonOpName (name : TSyntax `str) : TSyntax `str :=
  if name.getString == "llvm.ctlz" then
    Syntax.mkStrLit "llvm.intr.ctlz"
  else if name.getString == "llvm.cttz" then
    Syntax.mkStrLit "llvm.intr.cttz"
  else
    name

macro_rules
  | `(mlir_op| $[$resName =]? $name:MLIR.Pretty.zero_poison_op $x, true $[: $t]? ) => do
    let some opName := extractOpName name.raw | Macro.throwUnsupported
    let opName := canonicalizeZeroPoisonOpName opName
    let flagVal : TSyntax `term ← `(MLIR.AST.AttrValue.bool True)
    let t ← t.getDM `(mlir_type| _)
    let retTy : TSyntaxArray `mlir_type := match resName with
      | some _ => #[t]
      | none => #[]
    `([mlir_op| $[$resName =]? $opName ($x) <{is_zero_poison = $$($flagVal)}> : ($t) -> ($retTy:mlir_type,*) ])
  | `(mlir_op| $[$resName =]? $name:MLIR.Pretty.zero_poison_op $x, Bool.true $[: $t]? ) => do
    let some opName := extractOpName name.raw | Macro.throwUnsupported
    let opName := canonicalizeZeroPoisonOpName opName
    let flagVal : TSyntax `term ← `(MLIR.AST.AttrValue.bool True)
    let t ← t.getDM `(mlir_type| _)
    let retTy : TSyntaxArray `mlir_type := match resName with
      | some _ => #[t]
      | none => #[]
    `([mlir_op| $[$resName =]? $opName ($x) <{is_zero_poison = $$($flagVal)}> : ($t) -> ($retTy:mlir_type,*) ])
  | `(mlir_op| $[$resName =]? $name:MLIR.Pretty.zero_poison_op $x, false $[: $t]? ) => do
    let some opName := extractOpName name.raw | Macro.throwUnsupported
    let opName := canonicalizeZeroPoisonOpName opName
    let flagVal : TSyntax `term ← `(MLIR.AST.AttrValue.bool False)
    let t ← t.getDM `(mlir_type| _)
    let retTy : TSyntaxArray `mlir_type := match resName with
      | some _ => #[t]
      | none => #[]
    `([mlir_op| $[$resName =]? $opName ($x) <{is_zero_poison = $$($flagVal)}> : ($t) -> ($retTy:mlir_type,*) ])
  | `(mlir_op| $[$resName =]? $name:MLIR.Pretty.zero_poison_op $x, Bool.false $[: $t]? ) => do
    let some opName := extractOpName name.raw | Macro.throwUnsupported
    let opName := canonicalizeZeroPoisonOpName opName
    let flagVal : TSyntax `term ← `(MLIR.AST.AttrValue.bool False)
    let t ← t.getDM `(mlir_type| _)
    let retTy : TSyntaxArray `mlir_type := match resName with
      | some _ => #[t]
      | none => #[]
    `([mlir_op| $[$resName =]? $opName ($x) <{is_zero_poison = $$($flagVal)}> : ($t) -> ($retTy:mlir_type,*) ])
  | `(mlir_op| $[$_resName =]? $_name:MLIR.Pretty.zero_poison_op $_x, $flag:term $[: $_t]? ) =>
      Macro.throwErrorAt flag
        "expected a Bool literal flag (`true` or `false`) for llvm.ctlz/llvm.cttz"

end MLIR.EDSL
