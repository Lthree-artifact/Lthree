import LeanMLIR.MLIRSyntax.PrettyEDSL
open Lean

namespace MLIR.EDSL
open Pretty

/-!
# Pretty syntax for `abs` int-min poison flag

This file defines the `MLIR.Pretty.int_min_poison_op` syntax category for LLVM
operations whose semantics depend on the Boolean `is_int_min_poison` attribute.

The pretty syntax is:
`%r = llvm.abs %x, false : i32`
`%r = llvm.abs %x, true : i32`

These forms expand to the canonical generic LLVM intrinsic name
`"llvm.intr.abs"`.
-/

declare_syntax_cat MLIR.Pretty.int_min_poison_op
syntax (name := intMinPoisonOpSyntax)
  (mlir_op_operand " = ")? MLIR.Pretty.int_min_poison_op mlir_op_operand ", " term
  (" : " mlir_type)? : mlir_op

private def canonicalizeIntMinPoisonOpName (name : TSyntax `str) : TSyntax `str :=
  if name.getString == "llvm.abs" then
    Syntax.mkStrLit "llvm.intr.abs"
  else
    name

macro_rules
  | `(mlir_op| $[$resName =]? $name:MLIR.Pretty.int_min_poison_op $x, true $[: $t]? ) => do
    let some opName := extractOpName name.raw | Macro.throwUnsupported
    let opName := canonicalizeIntMinPoisonOpName opName
    let flagVal : TSyntax `term ← `(MLIR.AST.AttrValue.bool True)
    let t ← t.getDM `(mlir_type| _)
    let retTy : TSyntaxArray `mlir_type := match resName with
      | some _ => #[t]
      | none => #[]
    `([mlir_op| $[$resName =]? $opName ($x) <{is_int_min_poison = $$($flagVal)}> : ($t) -> ($retTy:mlir_type,*) ])
  | `(mlir_op| $[$resName =]? $name:MLIR.Pretty.int_min_poison_op $x, Bool.true $[: $t]? ) => do
    let some opName := extractOpName name.raw | Macro.throwUnsupported
    let opName := canonicalizeIntMinPoisonOpName opName
    let flagVal : TSyntax `term ← `(MLIR.AST.AttrValue.bool True)
    let t ← t.getDM `(mlir_type| _)
    let retTy : TSyntaxArray `mlir_type := match resName with
      | some _ => #[t]
      | none => #[]
    `([mlir_op| $[$resName =]? $opName ($x) <{is_int_min_poison = $$($flagVal)}> : ($t) -> ($retTy:mlir_type,*) ])
  | `(mlir_op| $[$resName =]? $name:MLIR.Pretty.int_min_poison_op $x, false $[: $t]? ) => do
    let some opName := extractOpName name.raw | Macro.throwUnsupported
    let opName := canonicalizeIntMinPoisonOpName opName
    let flagVal : TSyntax `term ← `(MLIR.AST.AttrValue.bool False)
    let t ← t.getDM `(mlir_type| _)
    let retTy : TSyntaxArray `mlir_type := match resName with
      | some _ => #[t]
      | none => #[]
    `([mlir_op| $[$resName =]? $opName ($x) <{is_int_min_poison = $$($flagVal)}> : ($t) -> ($retTy:mlir_type,*) ])
  | `(mlir_op| $[$resName =]? $name:MLIR.Pretty.int_min_poison_op $x, Bool.false $[: $t]? ) => do
    let some opName := extractOpName name.raw | Macro.throwUnsupported
    let opName := canonicalizeIntMinPoisonOpName opName
    let flagVal : TSyntax `term ← `(MLIR.AST.AttrValue.bool False)
    let t ← t.getDM `(mlir_type| _)
    let retTy : TSyntaxArray `mlir_type := match resName with
      | some _ => #[t]
      | none => #[]
    `([mlir_op| $[$resName =]? $opName ($x) <{is_int_min_poison = $$($flagVal)}> : ($t) -> ($retTy:mlir_type,*) ])
  | `(mlir_op| $[$_resName =]? $_name:MLIR.Pretty.int_min_poison_op $_x, $flag:term $[: $_t]? ) =>
      Macro.throwErrorAt flag
        "expected a Bool literal flag (`true` or `false`) for llvm.abs"

end MLIR.EDSL
