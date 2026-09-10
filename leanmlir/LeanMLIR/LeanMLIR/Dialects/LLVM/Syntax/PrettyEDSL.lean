import LeanMLIR.MLIRSyntax.PrettyEDSL

import LeanMLIR.Dialects.LLVM.Syntax.Pretty.Overflow
import LeanMLIR.Dialects.LLVM.Syntax.Pretty.Exact
import LeanMLIR.Dialects.LLVM.Syntax.Pretty.NonNeg
import LeanMLIR.Dialects.LLVM.Syntax.Pretty.Disjoint
import LeanMLIR.Dialects.LLVM.Syntax.Pretty.ZeroPoison
import LeanMLIR.Dialects.LLVM.Syntax.Pretty.IntMinPoison

open Lean

namespace MLIR.EDSL
open Pretty

syntax "ptr" : mlir_type
macro_rules
  | `([mlir_type| ptr]) => `([mlir_type| !"llvm.ptr"])

syntax "llvm.return"  : MLIR.Pretty.uniform_op
syntax "llvm.assume"  : MLIR.Pretty.uniform_op
syntax "llvm.copy"    : MLIR.Pretty.uniform_op
syntax "llvm.freeze"  : MLIR.Pretty.uniform_op
syntax "llvm.ctpop"   : MLIR.Pretty.uniform_op
syntax "llvm.neg"     : MLIR.Pretty.uniform_op
syntax "llvm.not"     : MLIR.Pretty.uniform_op
syntax "llvm.abs"     : MLIR.Pretty.int_min_poison_op
syntax "llvm.ctlz"    : MLIR.Pretty.zero_poison_op
syntax "llvm.cttz"    : MLIR.Pretty.zero_poison_op
syntax "llvm.or"      : MLIR.Pretty.uniform_op
syntax "llvm.and"     : MLIR.Pretty.uniform_op
syntax "llvm.srem"    : MLIR.Pretty.uniform_op
syntax "llvm.urem"    : MLIR.Pretty.uniform_op
syntax "llvm.xor"     : MLIR.Pretty.uniform_op

syntax "llvm.add"     : MLIR.Pretty.overflow_op
syntax "llvm.shl"     : MLIR.Pretty.overflow_op
syntax "llvm.mul"     : MLIR.Pretty.overflow_op
syntax "llvm.sub"     : MLIR.Pretty.overflow_op

syntax "llvm.udiv"    : MLIR.Pretty.exact_op
syntax "llvm.sdiv"    : MLIR.Pretty.exact_op
syntax "llvm.lshr"    : MLIR.Pretty.exact_op
syntax "llvm.ashr"    : MLIR.Pretty.exact_op

syntax "llvm.or"      : MLIR.Pretty.disjoint_op

declare_syntax_cat InstCombine.cmp_op_name
syntax "llvm.icmp.eq"  : InstCombine.cmp_op_name
syntax "llvm.icmp.ne"  : InstCombine.cmp_op_name
syntax "llvm.icmp.slt" : InstCombine.cmp_op_name
syntax "llvm.icmp.sle" : InstCombine.cmp_op_name
syntax "llvm.icmp.sgt" : InstCombine.cmp_op_name
syntax "llvm.icmp.sge" : InstCombine.cmp_op_name
syntax "llvm.icmp.ult" : InstCombine.cmp_op_name
syntax "llvm.icmp.ule" : InstCombine.cmp_op_name
syntax "llvm.icmp.ugt" : InstCombine.cmp_op_name
syntax "llvm.icmp.uge" : InstCombine.cmp_op_name

syntax mlir_op_operand " = " InstCombine.cmp_op_name mlir_op_operand ", " mlir_op_operand
        (" : " mlir_type)? : mlir_op
macro_rules
  | `(mlir_op| $resName:mlir_op_operand = $name:InstCombine.cmp_op_name $x, $y $[: $t]?) => do
    let some opName := extractOpName name.raw
      | Macro.throwUnsupported
    let t ← t.getDM `(mlir_type| _)
    `(mlir_op| $resName:mlir_op_operand = $opName ($x, $y) : ($t, $t) -> (i1) )

declare_syntax_cat InstCombine.int_cast_op
syntax "llvm.trunc" : MLIR.Pretty.overflow_int_cast_op
syntax "llvm.zext" : MLIR.Pretty.nneg_op
syntax "llvm.sext" : InstCombine.int_cast_op

syntax mlir_op_operand " = " InstCombine.int_cast_op mlir_op_operand " : " mlir_type " to " mlir_type : mlir_op
macro_rules
  | `(mlir_op| $resName:mlir_op_operand = $name:InstCombine.int_cast_op $x : $t to $t') => do
    let some opName := extractOpName name.raw
      | Macro.throwUnsupported
    `(mlir_op| $resName:mlir_op_operand = $opName ($x) : ($t) -> $t')

syntax mlir_op_operand " = " "llvm.mlir.constant" "("   neg_num (" : " mlir_type)? ")"
  (" : " mlir_type)? : mlir_op
syntax mlir_op_operand " = " "llvm.mlir.constant" "("   ident (" : " mlir_type)? ")"
  (" : " mlir_type)? : mlir_op
syntax mlir_op_operand " = " "llvm.mlir.constant" "("  ("$" noWs "{" term "}") ")"
  (" : " mlir_type)?   : mlir_op
macro_rules
  | `(mlir_op| $res:mlir_op_operand = llvm.mlir.constant( $x:neg_num $[: $inner_type]?)
      $[: $outer_type]? ) => do
      /- We deviate slightly from LLVM by allowing syntax such as `llvm.mlir.constant (10) : i62`.
          Strictly speaking, the spec mandates that the *inner* type annotation may only be left out
          if the type is `i64` or `f64`.
          Since the type in this case is unambiguous, there is no harm in allowing this for other
          widths as well.
        If no annotation is given at all, then the width is assumed to be `_`,
        a symbolic/metavariable width
      -/
      let outer_type ← outer_type.getDM `(mlir_type| _)
      let inner_type := inner_type.getD outer_type
      `(mlir_op| $res:mlir_op_operand = "llvm.mlir.constant"()
          {value = $x:neg_num : $inner_type} : () -> ($outer_type) )
  | `(mlir_op| $res:mlir_op_operand = llvm.mlir.constant( $x:ident $[: $inner_type]?)
      $[: $outer_type]? ) => do
      let outer_type ← outer_type.getDM `(mlir_type| _)
      let inner_type := inner_type.getD outer_type
      `(mlir_op| $res:mlir_op_operand = "llvm.mlir.constant"()
          {value = $x:ident : $inner_type} : () -> ($outer_type) )
  | `(mlir_op| $res:mlir_op_operand = llvm.mlir.constant( ${ $x:term }) $[: $t]?) => do
      let t ← t.getDM `(mlir_type| _)
      let x ← `(MLIR.AST.AttrValue.int $x [mlir_type| $t])
      `(mlir_op| $res:mlir_op_operand = "llvm.mlir.constant"() {value = $$($x) } : () -> ($t) )

syntax mlir_op_operand " = " "llvm.mlir.constant" "(true)" (" : " mlir_type)? : mlir_op
syntax mlir_op_operand " = " "llvm.mlir.constant" "(false)" (" : " mlir_type)? : mlir_op
syntax mlir_op_operand " = " "llvm.mlir.constant" neg_num (" : " mlir_type)? : mlir_op
syntax mlir_op_operand " = " "llvm.mlir.constant" ("$" noWs "{" term "}")
  (" : " mlir_type)? : mlir_op
macro_rules
  | `(mlir_op| $res:mlir_op_operand = llvm.mlir.constant (true) $[: $t]?) =>
      `(mlir_op| $res:mlir_op_operand = llvm.mlir.constant (1 : i1) : i1)
  | `(mlir_op| $res:mlir_op_operand = llvm.mlir.constant (false) $[: $t]?) =>
      `(mlir_op| $res:mlir_op_operand = llvm.mlir.constant (0 : i1) : i1)
  | `(mlir_op| $res:mlir_op_operand = llvm.mlir.constant $x:neg_num $[: $t]?) =>
      `(mlir_op| $res:mlir_op_operand = llvm.mlir.constant($x:neg_num $[: $t]?) $[: $t]?)
  | `(mlir_op| $res:mlir_op_operand = llvm.mlir.constant ${ $x:term } $[: $t]?) =>
      `(mlir_op| $res:mlir_op_operand = llvm.mlir.constant($$($x) $[: $t]?) $[: $t]?)


syntax mlir_op_operand " = " "llvm.icmp" str mlir_op_operand ", " mlir_op_operand (" : " mlir_type)? : mlir_op
macro_rules
  | `(mlir_op| $res:mlir_op_operand = llvm.icmp $p $x, $y $[: $t]?) => do
    let t ← t.getDM `(mlir_type| _)
    match p.getString with
      | "eq" => `(mlir_op| $res:mlir_op_operand = "llvm.icmp.eq" ($x, $y) : ($t, $t) -> (i1))
      | "ne" => `(mlir_op| $res:mlir_op_operand = "llvm.icmp.ne" ($x, $y) : ($t, $t) -> (i1))
      | "slt" => `(mlir_op| $res:mlir_op_operand = "llvm.icmp.slt" ($x, $y) : ($t, $t) -> (i1))
      | "sle" => `(mlir_op| $res:mlir_op_operand = "llvm.icmp.sle" ($x, $y) : ($t, $t) -> (i1))
      | "sgt" => `(mlir_op| $res:mlir_op_operand = "llvm.icmp.sgt" ($x, $y) : ($t, $t) -> (i1))
      | "sge" => `(mlir_op| $res:mlir_op_operand = "llvm.icmp.sge" ($x, $y) : ($t, $t) -> (i1))
      | "ult" => `(mlir_op| $res:mlir_op_operand = "llvm.icmp.ult" ($x, $y) : ($t, $t) -> (i1))
      | "ule" => `(mlir_op| $res:mlir_op_operand = "llvm.icmp.ule" ($x, $y) : ($t, $t) -> (i1))
      | "ugt" => `(mlir_op| $res:mlir_op_operand = "llvm.icmp.ugt" ($x, $y) : ($t, $t) -> (i1))
      | "uge" => `(mlir_op| $res:mlir_op_operand = "llvm.icmp.uge" ($x, $y) : ($t, $t) -> (i1))
      | _ => Macro.throwErrorAt p s!"unexpected predicate {p.getString}"

syntax mlir_op_operand " = " "llvm.isPowerOf2" mlir_op_operand (" : " mlir_type)? : mlir_op
macro_rules
  | `(mlir_op| $res:mlir_op_operand = llvm.isPowerOf2 $x $[: $t]?) => do
    let t ← t.getDM `(mlir_type| _)
    `(mlir_op| $res:mlir_op_operand = "llvm.isPowerOf2"($x) : ($t) -> (i1))

syntax mlir_op_operand " = " "llvm.select" mlir_op_operand ", " mlir_op_operand ", " mlir_op_operand
    (" : " mlir_type)? : mlir_op
macro_rules
  | `(mlir_op| $res:mlir_op_operand = llvm.select $c, $x, $y $[: $t]?) => do
    let t ← t.getDM `(mlir_type| _)
    `(mlir_op| $res:mlir_op_operand = "llvm.select" ($c, $x, $y) : (i1, $t, $t) -> ($t))

syntax mlir_op_operand " = " "llvm.getelementptr" mlir_type ", " "ptr" mlir_op_operand ", " mlir_op_operand
    (" : " mlir_type)? : mlir_op
macro_rules
  | `(mlir_op| $res:mlir_op_operand = llvm.getelementptr $elemTy:mlir_type, ptr $p, $idx $[: $idxTy]?) => do
    let idxTy ← idxTy.getDM `(mlir_type| _)
    let elemTyAttr ← `(mlir_attr_val| $elemTy:mlir_type)
    `(mlir_op| $res:mlir_op_operand = "llvm.getelementptr" ($p, $idx) {elem_type = $elemTyAttr} : (ptr, $idxTy) -> (ptr))

syntax mlir_op_operand " = " "llvm.getelementptr" mlir_type ", " mlir_op_operand ", " mlir_op_operand
    (" : " mlir_type)? : mlir_op
macro_rules
  | `(mlir_op| $res:mlir_op_operand = llvm.getelementptr $elemTy:mlir_type, $p, $idx $[: $idxTy]?) =>
      `(mlir_op| $res:mlir_op_operand = llvm.getelementptr $elemTy:mlir_type, ptr $p, $idx $[: $idxTy]?)

syntax mlir_op_operand " = " "llvm.load" mlir_op_operand (" : " mlir_type)? : mlir_op
macro_rules
  | `(mlir_op| $res:mlir_op_operand = llvm.load $p $[: $t]?) => do
    let t ← t.getDM `(mlir_type| _)
    `(mlir_op| $res:mlir_op_operand = "llvm.load" ($p) : (ptr) -> ($t))

syntax "llvm.store" mlir_op_operand ", " mlir_op_operand (" : " mlir_type)? : mlir_op
macro_rules
  | `(mlir_op| llvm.store $p, $val $[: $t]?) => do
    let t ← t.getDM `(mlir_type| _)
    `(mlir_op| "llvm.store" ($p, $val) : (ptr, $t) -> ())

syntax mlir_op_operand " = " "llvm.alloca" mlir_type : mlir_op
macro_rules
  | `(mlir_op| $res:mlir_op_operand = llvm.alloca $t:mlir_type) => do
    let elemTy ← `(mlir_attr_val| $t:mlir_type)
    `(mlir_op| $res:mlir_op_operand = "llvm.alloca" () {elem_type = $elemTy} : () -> (ptr))

syntax mlir_op_operand " = " "llvm.call" "@" ident "(" mlir_op_operand,* ")"
    " : " "(" mlir_type,* ")" " -> " mlir_type : mlir_op
syntax mlir_op_operand " = " "llvm.call" "@" str "(" mlir_op_operand,* ")"
    " : " "(" mlir_type,* ")" " -> " mlir_type : mlir_op
macro_rules
  | `(mlir_op| $res:mlir_op_operand = llvm.call @ $callee:ident ($args,*) :
      ($argTys:mlir_type,*) -> $retTy:mlir_type) => do
      let calleeAttr ← `(mlir_attr_val| @ $callee:ident)
      `(mlir_op| $res:mlir_op_operand = "llvm.call" ($args,*)
          {callee = $calleeAttr}
          : ($argTys:mlir_type,*) -> ($retTy:mlir_type))
  | `(mlir_op| $res:mlir_op_operand = llvm.call @ $callee:str ($args,*) :
      ($argTys:mlir_type,*) -> $retTy:mlir_type) => do
      let calleeAttr ← `(mlir_attr_val| @ $callee:str)
      `(mlir_op| $res:mlir_op_operand = "llvm.call" ($args,*)
          {callee = $calleeAttr}
          : ($argTys:mlir_type,*) -> ($retTy:mlir_type))

/-!
AST-only branch syntax.

These forms let examples spell MLIR-style CFG loops with block arguments and
backedges. They elaborate to generic `MLIR.AST.Op`s, but the LLVM dialect still
does not have `MOp` semantics for `llvm.br` or `llvm.cond_br`.
-/
declare_syntax_cat llvm_br_arg
syntax mlir_op_operand " : " mlir_type : llvm_br_arg

private def llvmBrArgTerm (arg : TSyntax `llvm_br_arg) : MacroM (TSyntax `term) := do
  match arg with
  | `(llvm_br_arg| $v:mlir_op_operand : $t:mlir_type) =>
      `(([mlir_op_operand| $v], [mlir_type| $t]))
  | _ => Macro.throwUnsupported

private def llvmBrArgsTerm (args : Syntax.TSepArray [`llvm_br_arg] ",") :
    MacroM (TSyntax `term) := do
  let args ← args.getElems.mapM llvmBrArgTerm
  quoteMList args.toList (← `(MLIR.AST.TypedSSAVal _))

private def llvmCondBrArgsTerm
    (cond : TSyntax `mlir_op_operand) (condTy : TSyntax `mlir_type)
    (trueArgs falseArgs : Syntax.TSepArray [`llvm_br_arg] ",") :
    MacroM (TSyntax `term) := do
  let condArg ← `(([mlir_op_operand| $cond], [mlir_type| $condTy]))
  let trueArgs ← trueArgs.getElems.mapM llvmBrArgTerm
  let falseArgs ← falseArgs.getElems.mapM llvmBrArgTerm
  quoteMList (condArg :: (trueArgs.toList ++ falseArgs.toList)) (← `(MLIR.AST.TypedSSAVal _))

syntax "llvm.br" "^" mlir_suffix_id "(" sepBy(llvm_br_arg, ",") ")" : mlir_op
syntax "llvm.cond_br" mlir_op_operand " : " mlir_type ", "
  "^" mlir_suffix_id "(" sepBy(llvm_br_arg, ",") ")" ", "
  "^" mlir_suffix_id "(" sepBy(llvm_br_arg, ",") ")" : mlir_op

macro_rules
  | `(mlir_op| llvm.br ^ $target:mlir_suffix_id ( $args,* )) => do
      let args ← llvmBrArgsTerm args
      `(MLIR.AST.Op.mk "llvm.br" [] $args [] <|
          MLIR.AST.AttrDict.mk [
            MLIR.AST.AttrEntry.mk "target"
              (MLIR.AST.AttrValue.symbol $(Lean.quote (getSuffixId target)))])
  | `(mlir_op| llvm.cond_br $cond:mlir_op_operand : $condTy:mlir_type,
        ^ $trueTarget:mlir_suffix_id ( $trueArgs,* ),
        ^ $falseTarget:mlir_suffix_id ( $falseArgs,* )) => do
      let args ← llvmCondBrArgsTerm cond condTy trueArgs falseArgs
      `(MLIR.AST.Op.mk "llvm.cond_br" [] $args [] <|
          MLIR.AST.AttrDict.mk [
            MLIR.AST.AttrEntry.mk "trueTarget"
              (MLIR.AST.AttrValue.symbol $(Lean.quote (getSuffixId trueTarget))),
            MLIR.AST.AttrEntry.mk "falseTarget"
              (MLIR.AST.AttrValue.symbol $(Lean.quote (getSuffixId falseTarget)))])

syntax "{" "llvm.func" "@" ident "(" mlir_bb_operand,* ")" "->" mlir_type "{"
    mlir_ops
  "}" "}" : mlir_region
syntax "{" "llvm.func" "@" str "(" mlir_bb_operand,* ")" "->" mlir_type "{"
    mlir_ops
  "}" "}" : mlir_region

declare_syntax_cat llvm_func_block
syntax "^" mlir_suffix_id "(" sepBy(mlir_bb_operand, ",") ")" ":" mlir_ops : llvm_func_block
syntax "^" mlir_suffix_id ":" mlir_ops : llvm_func_block

syntax "{" "llvm.func" "@" ident "(" mlir_bb_operand,* ")" "->" mlir_type "{"
    llvm_func_block*
  "}" "}" : mlir_region
syntax "{" "llvm.func" "@" str "(" mlir_bb_operand,* ")" "->" mlir_type "{"
    llvm_func_block*
  "}" "}" : mlir_region

private def mkLLVMFuncBlock (block : TSyntax `llvm_func_block) : MacroM (TSyntax `term) := do
  match block with
  | `(llvm_func_block| ^ $bb:mlir_suffix_id ( $bbargs,* ) : $ops:mlir_ops) => do
      let bbargs ← bbargs.getElems.foldrM
        (init := ← `(@List.nil (MLIR.AST.SSAVal × MLIR.AST.MLIRType _)))
        fun x xs => `([mlir_bb_operand| $x] :: $xs)
      `(MLIR.AST.Region.mk $(Lean.quote (getSuffixId bb)) $bbargs [mlir_ops| $ops] [])
  | `(llvm_func_block| ^ $bb:mlir_suffix_id : $ops:mlir_ops) =>
      `(MLIR.AST.Region.mk $(Lean.quote (getSuffixId bb)) [] [mlir_ops| $ops] [])
  | _ => Macro.throwUnsupported

private def mkLLVMFuncBlockList (blocks : List (TSyntax `llvm_func_block)) :
    MacroM (TSyntax `term) := do
  blocks.foldrM (init := ← `(@List.nil (MLIR.AST.Region _))) fun block blocks => do
    let block ← mkLLVMFuncBlock block
    `($block :: $blocks)

private def mkLLVMFuncRegionWithBlocks (blocks : List (TSyntax `llvm_func_block)) :
    MacroM (TSyntax `term) := do
  match blocks with
  | [] => Macro.throwUnsupported
  | entry :: blocks => do
      let entry ← mkLLVMFuncBlock entry
      let blocks ← mkLLVMFuncBlockList blocks
      `({ $entry with blocks := $blocks })

macro_rules
  | `(mlir_region| { llvm.func @ $_callee:ident ( $args,* ) -> $_retTy:mlir_type {
        $ops:mlir_ops
      } }) => do
      let bbargs ← args.getElems.mapM (fun x => `([mlir_bb_operand| $x]))
      let bbargs ← quoteMList bbargs.toList (← `(MLIR.AST.SSAVal × MLIR.AST.MLIRType _))
      `(MLIR.AST.Region.mk "entry" $bbargs [mlir_ops| $ops] [])
  | `(mlir_region| { llvm.func @ $_callee:str ( $args,* ) -> $_retTy:mlir_type {
        $ops:mlir_ops
      } }) => do
      let bbargs ← args.getElems.mapM (fun x => `([mlir_bb_operand| $x]))
      let bbargs ← quoteMList bbargs.toList (← `(MLIR.AST.SSAVal × MLIR.AST.MLIRType _))
      `(MLIR.AST.Region.mk "entry" $bbargs [mlir_ops| $ops] [])
  | `(mlir_region| { llvm.func @ $_callee:ident ( $_args,* ) -> $_retTy:mlir_type {
        $blocks:llvm_func_block*
      } }) =>
      mkLLVMFuncRegionWithBlocks blocks.toList
  | `(mlir_region| { llvm.func @ $_callee:str ( $_args,* ) -> $_retTy:mlir_type {
        $blocks:llvm_func_block*
      } }) =>
      mkLLVMFuncRegionWithBlocks blocks.toList

end EDSL

end MLIR
