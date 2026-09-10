/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.Framework
import LeanMLIR.Util
import LeanMLIR.Tactic.SimpSet

import LeanMLIR.Dialects.LLVM.Semantics

/-!
  # InstCombine Dialect

  This file defines a dialect of basic arithmetic and bitwise operations on bitvectors.

  The dialect supports types of arbitrary-width bitvectors.
  Thus, some definitions wil be parameterized by `φ`, the number of width meta-variables there are.
  This parameter will usually be either `0`, indicating that all widths are known, concrete values,
  or `1`, indicating there is exactly one distinct width meta-variable.

  In particular, we only define a denotational semantics for concrete programs (i.e., where `φ = 0`)


  see https://releases.llvm.org/14.0.0/docs/LangRef.html#bitwise-binary-operations
-/

namespace InstCombine

open BitVec

open LLVM

/-! ### Types -/

abbrev Width φ := ConcreteOrMVar Nat φ

inductive MTy (φ : Nat)
  | bitvec (w : Width φ) : MTy φ
  | ptr : MTy φ
  deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

/-! ### Operations -/

/-- Homogeneous, unary operations -/
inductive MOp.UnaryOp (φ : Nat) : Type
  | neg
  | not
  | copy
  | freeze
  | abs   (flag : _root_.LLVM.IntMinPoisonFlag := {is_int_min_poison := false})
  | ctpop
  | ctlz  (flag : _root_.LLVM.ZeroPoisonFlag := {is_zero_poison := false})
  | cttz  (flag : _root_.LLVM.ZeroPoisonFlag := {is_zero_poison := false})
  | trunc (w' : Width φ) (noWrapFlags : NoWrapFlags := {nsw := false, nuw := false} )
  | zext  (w' : Width φ) (nneg : NonNegFlag := {nneg := false} )
  | sext  (w' : Width φ)
deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

/-- Homogeneous, binary operations -/
inductive MOp.BinaryOp : Type
  | and
  | or   (disjoint : DisjointFlag := {disjoint := false} )
  | xor
  | shl  (nswnuw : NoWrapFlags := {nsw := false, nuw := false} )
  | lshr (exact : ExactFlag := {exact := false} )
  | ashr (exact : ExactFlag := {exact := false} )
  | urem
  | srem
  | add  (nswnuw : NoWrapFlags := {nsw := false, nuw := false} )
  | mul  (nswnuw : NoWrapFlags := {nsw := false, nuw := false} )
  | sub  (nswnuw : NoWrapFlags := {nsw := false, nuw := false} )
  | sdiv (exact : ExactFlag := {exact := false} )
  | udiv (exact : ExactFlag := {exact := false} )
deriving DecidableEq, Inhabited, Lean.ToExpr

open Std (Format) in
/--
If both the nuw and nsw flags are the default value (false,false),
then we should not print them. This should be the default
behavior in Lean, but it isn't
-/
def reprWithoutFlags (op : MOp.BinaryOp) (prec : Nat) : Format :=
  let op  : String := match op with
    | .and                => "and"
    | .or   ⟨false⟩        => "or"
    | .or   ⟨true⟩         => "or disjoint"
    | .xor                => "xor"
    | .shl  ⟨false, false⟩ => "shl"
    | .shl  ⟨nsw, nuw⟩     => toString f!"shl {nsw} {nuw}"
    | .lshr ⟨false⟩        => "lshr"
    | .lshr ⟨true⟩         => "lshr exact"
    | .ashr ⟨false⟩        => "ashr"
    | .ashr ⟨true⟩         => "ashr exact"
    | .urem               => "urem"
    | .srem               => "srem"
    | .add  ⟨false, false⟩ => "add"
    | .add  ⟨nsw, nuw⟩     => toString f!"add {nsw} {nuw}"
    | .mul  ⟨false, false⟩ => "mul"
    | .mul  ⟨nsw, nuw⟩     => toString f!"mul {nsw} {nuw}"
    | .sub  ⟨false, false⟩ => "sub"
    | .sub  ⟨nsw, nuw⟩     => toString f!"sub {nsw} {nuw}"
    | .sdiv ⟨false⟩        => "sdiv"
    | .sdiv ⟨true⟩         => "sdiv exact"
    | .udiv ⟨false⟩        => "udiv"
    | .udiv ⟨true⟩         => "udiv exact"
  Repr.addAppParen (Format.group (Format.nest
    (if prec >= max_prec then 1 else 2) f!"InstCombine.MOp.BinaryOp.{op}"))
    prec

instance : Repr (MOp.BinaryOp) where
  reprPrec := reprWithoutFlags

-- See: https://releases.llvm.org/14.0.0/docs/LangRef.html#bitwise-binary-operations
inductive MOp (φ : Nat) : Type
  | unary   (w : Width φ) (op : MOp.UnaryOp φ) :  MOp φ
  | binary  (w : Width φ) (op : MOp.BinaryOp) :  MOp φ
  | call (retTy : MTy φ) (fnName : String) (argTys : List (MTy φ)) : MOp φ
  | isPowerOf2 (w : Width φ) : MOp φ
  | select  (w : Width φ) : MOp φ
  | icmp    (c : IntPred) (w : Width φ) : MOp φ
  | assume_ : MOp φ
  | getelementptr (elemW : Width φ) (idxW : Width φ) : MOp φ
  | load (w : Width φ) : MOp φ
  | store (w : Width φ) : MOp φ
  | alloca (w : Width φ) : MOp φ
  /-- Since the width of the const might not be known, we just store the value as an `Int` -/
  | const (w : Width φ) (val : ℤ) : MOp φ
  /-- A constant that should be instantiated from the width parameter vector. -/
  | constParam (w : Width φ) (idx : Fin φ) : MOp φ
deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

def toStringWithFlags (op : MOp.BinaryOp) : String :=
  let op  : String := match op with
    | .and                  => "and"
    | .or   ⟨false⟩         => "or"
    | .or   ⟨true⟩          => "or disjoint"
    | .xor                  => "xor"
    | .shl  ⟨false, false⟩  => "shl"
    | .shl  ⟨nsw, nuw⟩      => toString f!"shl {nsw} {nuw}"
    | .lshr ⟨false⟩         => "lshr"
    | .lshr ⟨true⟩          => "lshr exact"
    | .ashr ⟨false⟩         => "ashr"
    | .ashr ⟨true⟩          => "ashr exact"
    | .urem                 => "urem"
    | .srem                 => "srem"
    | .add  ⟨false, false⟩  => "add"
    | .add  ⟨nsw, nuw⟩      => toString f!"add {nsw} {nuw}"
    | .mul  ⟨false, false⟩  => "mul"
    | .mul  ⟨nsw, nuw⟩      => toString f!"mul {nsw} {nuw}"
    | .sub  ⟨false, false⟩  => "sub"
    | .sub  ⟨nsw, nuw⟩      => toString f!"sub {nsw} {nuw}"
    | .sdiv ⟨false⟩         => "sdiv"
    | .sdiv ⟨true⟩          => "sdiv exact"
    | .udiv ⟨false⟩         => "udiv"
    | .udiv ⟨true⟩          => "udiv exact"
  s!"llvm.{op}"

instance : ToString (MOp.BinaryOp) where
  toString := toStringWithFlags

instance : ToString (MOp.UnaryOp (φ : Nat)) where
  toString
    | .neg => "neg"
    | .not => "not"
    | .copy => "copy"
    | .freeze => "freeze"
    | .abs _ => "abs"
    | .ctpop => "ctpop"
    | .ctlz _ => "ctlz"
    | .cttz _ => "cttz"
    | .trunc _ _ => "trunc"
    | .zext _ _ => "zext"
    | .sext _ => "sext"

instance : ToString (MOp 0) where
   toString  op :=
     match op with
     | .unary _w op => s!"\"{toString op}\""
     | .binary _w op => s!"\"{toString  op}\""
     | .isPowerOf2 _w => "\"llvm.isPowerOf2\""
     | .select  _w => "select"
     | .icmp  _pred _w => "icmp"
     | .assume_ => "assume"
     | .getelementptr _ _ => "\"llvm.getelementptr\""
     | .load _ => "\"llvm.load\""
     | .store _ => "\"llvm.store\""
     | .alloca _ => "\"llvm.alloca\""
     | .call _ _ _ => "\"llvm.call\""
     | .const w val => s!"\"llvm.mlir.constant\"() \{value = {val} : {w}}"
     | .constParam _w idx => nomatch idx

/-! ## Dialect -/

/-- `MetaLLVM φ` is the `LLVM` dialect with at most `φ` metavariables -/
abbrev MetaLLVM (φ : Nat) : Dialect where
  Op := MOp φ
  Ty := MTy φ
  m := ImmediateUBOr

def LLVM : Dialect where
  Op := MOp 0
  Ty := MTy 0
  m := ImmediateUBOr

/-- Defining an instance for LLVM.Ty from InstCombine.Ty instance.-/
instance : DecidableEq LLVM.Ty :=
  inferInstanceAs <| DecidableEq (InstCombine.MTy _)

/-- Defining an instance for LLVM.Op from InstCombine.Op instance. -/
instance : DecidableEq LLVM.Op :=
    inferInstanceAs <| DecidableEq (InstCombine.MOp 0)

@[deprecated "Use `LLVM.Op` instead" (since:="2025-04-30")] abbrev Op := LLVM.Op
@[deprecated "Use `LLVM.Ty` instead" (since:="2025-04-30")] abbrev Ty := LLVM.Ty

namespace MOp

@[match_pattern] def neg    (w : Width φ) : MOp φ := .unary w .neg
@[match_pattern] def not    (w : Width φ) : MOp φ := .unary w .not
@[match_pattern] def copy   (w : Width φ) : MOp φ := .unary w .copy
@[match_pattern] def freeze (w : Width φ) : MOp φ := .unary w .freeze
@[match_pattern] def abs    (w : Width φ) (flag : _root_.LLVM.IntMinPoisonFlag := {is_int_min_poison := false}) : MOp φ := .unary w (.abs flag)
@[match_pattern] def ctpop  (w : Width φ) : MOp φ := .unary w .ctpop
@[match_pattern] def ctlz   (w : Width φ) (flag : _root_.LLVM.ZeroPoisonFlag := {is_zero_poison := false}) : MOp φ := .unary w (.ctlz flag)
@[match_pattern] def cttz   (w : Width φ) (flag : _root_.LLVM.ZeroPoisonFlag := {is_zero_poison := false}) : MOp φ := .unary w (.cttz flag)
@[match_pattern] def sext   (w w' : Width φ) : MOp φ := .unary w (.sext w')

/- This definition uses a nneg flag -/
@[match_pattern] def zext (w w' : Width φ)
  (NonNegFlag: NonNegFlag := {nneg := false}) : MOp φ
    := .unary w (.zext w' NonNegFlag)

@[match_pattern] def and    (w : Width φ) : MOp φ := .binary w .and
@[match_pattern] def xor    (w : Width φ) : MOp φ := .binary w .xor
@[match_pattern] def urem   (w : Width φ) : MOp φ := .binary w .urem
@[match_pattern] def srem   (w : Width φ) : MOp φ := .binary w .srem

/- This definition uses a disjoint flag -/
@[match_pattern] def or (w : Width φ)
  (DisjointFlag : DisjointFlag := {disjoint := false} ) : MOp φ
    := .binary w (.or DisjointFlag )

/- These definitions use NoWrapFlags -/
@[match_pattern] def trunc  (w w' : Width φ)
  (noWrapFlags: NoWrapFlags := {nsw := false , nuw := false}) : MOp φ
    := .unary w (.trunc w' noWrapFlags)

@[match_pattern] def shl (w : Width φ)
  (NoWrapFlags: NoWrapFlags := {nsw := false , nuw := false}) : MOp φ
    := .binary w (.shl NoWrapFlags )
@[match_pattern] def add (w : Width φ)
  (NoWrapFlags: NoWrapFlags := {nsw := false , nuw := false}) : MOp φ
    := .binary w (.add NoWrapFlags )
@[match_pattern] def mul (w : Width φ)
  (NoWrapFlags: NoWrapFlags := {nsw := false , nuw := false}) : MOp φ
    := .binary w (.mul NoWrapFlags )
@[match_pattern] def sub (w : Width φ)
  (NoWrapFlags: NoWrapFlags := {nsw := false , nuw := false}) : MOp φ
    := .binary w (.sub NoWrapFlags )

/- These definitions use an exact flag -/
@[match_pattern] def lshr (w : Width φ)
  (ExactFlag : ExactFlag := {exact := false} ) : MOp φ
    := .binary w (.lshr ExactFlag )
@[match_pattern] def ashr (w : Width φ)
  (ExactFlag : ExactFlag := {exact := false} ) : MOp φ
    := .binary w (.ashr ExactFlag )
@[match_pattern] def sdiv (w : Width φ)
  (ExactFlag : ExactFlag := {exact := false} ) : MOp φ
    := .binary w (.sdiv ExactFlag )
@[match_pattern] def udiv (w : Width φ)
  (ExactFlag : ExactFlag := {exact := false} ) : MOp φ
    := .binary w (.udiv ExactFlag )

/-- Recursion principle in terms of individual operations, rather than `unary` or `binary` -/
def deepCasesOn {motive : ∀ {φ}, MOp φ → Sort*}
    (neg    : ∀ {φ} {w : Width φ},               motive (neg  w))
    (not    : ∀ {φ} {w : Width φ},               motive (not  w))
    (trunc  : ∀ {φ noWrapFlags} {w w' : Width φ},            motive (trunc w w' noWrapFlags))
    (zext   : ∀ {φ NonNegFlag} {w w' : Width φ}, motive (zext  w w' NonNegFlag))
    (sext   : ∀ {φ} {w w' : Width φ},            motive (sext  w w'))
    (copy   : ∀ {φ} {w : Width φ},               motive (copy w))
    (freeze : ∀ {φ} {w : Width φ},               motive (freeze w))
    (abs    : ∀ {φ} {flag : _root_.LLVM.IntMinPoisonFlag} {w : Width φ}, motive (abs w flag))
    (ctpop  : ∀ {φ} {w : Width φ},               motive (ctpop w))
    (ctlz   : ∀ {φ} {flag : _root_.LLVM.ZeroPoisonFlag} {w : Width φ}, motive (ctlz w flag))
    (cttz   : ∀ {φ} {flag : _root_.LLVM.ZeroPoisonFlag} {w : Width φ}, motive (cttz w flag))
    (and    : ∀ {φ} {w : Width φ},               motive (and  w))
    (or     : ∀ {φ DisjointFlag} {w : Width φ},  motive (or w DisjointFlag))
    (xor    : ∀ {φ} {w : Width φ},               motive (xor  w))
    (isPowerOf2 : ∀ {φ} {w : Width φ},           motive (.isPowerOf2 w))
    (shl    : ∀ {φ NoWrapFlags} {w : Width φ},   motive (shl  w NoWrapFlags))
    (lshr   : ∀ {φ ExactFlag} {w : Width φ},     motive (lshr w ExactFlag))
    (ashr   : ∀ {φ ExactFlag} {w : Width φ},     motive (ashr w ExactFlag))
    (urem   : ∀ {φ} {w : Width φ},               motive (urem w))
    (srem   : ∀ {φ} {w : Width φ},               motive (srem w))
    (add    : ∀ {φ NoWrapFlags} {w : Width φ},   motive (add w NoWrapFlags))
    (mul    : ∀ {φ NoWrapFlags} {w : Width φ},   motive (mul w NoWrapFlags))
    (sub    : ∀ {φ NoWrapFlags} {w : Width φ},   motive (sub w NoWrapFlags))
    (sdiv   : ∀ {φ ExactFlag} {w : Width φ},     motive (sdiv w ExactFlag))
    (udiv   : ∀ {φ ExactFlag} {w : Width φ},     motive (udiv w ExactFlag))
    (getelementptr : ∀ {φ} {elemW idxW : Width φ}, motive (.getelementptr elemW idxW))
    (load   : ∀ {φ} {w : Width φ},               motive (.load w))
    (store  : ∀ {φ} {w : Width φ},               motive (.store w))
    (alloca : ∀ {φ} {w : Width φ},               motive (.alloca w))
    (call   : ∀ {φ} {retTy : MTy φ} {fnName : String} {argTys : List (MTy φ)},
      motive (.call retTy fnName argTys))
    (select : ∀ {φ} {w : Width φ},               motive (select w))
    (icmp   : ∀ {φ c} {w : Width φ},             motive (icmp c w))
    (assume : ∀ {φ},                              motive (.assume_ (φ := φ)))
    (const  : ∀ {φ v} {w : Width φ},             motive (const w v))
    (constParam : ∀ {φ i} {w : Width φ},         motive (constParam w i)) :
    ∀ {φ} (op : MOp φ), motive op
  | _, .neg _      => neg
  | _, .not _      => not
  | _, .trunc _ _ _  => trunc
  | _, .zext _ _ _ => zext
  | _, .sext _ _   => sext
  | _, .copy _     => copy
  | _, .freeze _   => freeze
  | _, .abs _ _     => abs
  | _, .ctpop _    => ctpop
  | _, .ctlz _ _   => ctlz
  | _, .cttz _ _   => cttz
  | _, .and _      => and
  | _, .or _ _     => or
  | _, .xor _      => xor
  | _, .isPowerOf2 _ => isPowerOf2
  | _, .shl _ _    => shl
  | _, .lshr _ _   => lshr
  | _, .ashr _ _   => ashr
  | _, .urem _     => urem
  | _, .srem _     => srem
  | _, .add _ _    => add
  | _, .mul _ _    => mul
  | _, .sub _ _    => sub
  | _, .sdiv _ _   => sdiv
  | _, .udiv _ _   => udiv
  | _, .getelementptr _ _ => getelementptr
  | _, .load _     => load
  | _, .store _    => store
  | _, .alloca _   => alloca
  | _, .call _ _ _ => call
  | _, .select _   => select
  | _, .icmp ..    => icmp
  | _, .assume_    => assume
  | _, .const ..   => const
  | _, .constParam .. => constParam

end MOp

namespace LLVM.Op

@[match_pattern] abbrev unary  (w : Nat) (op : MOp.UnaryOp 0) : LLVM.Op :=
  MOp.unary (.concrete w) op

@[match_pattern] abbrev binary (w : Nat) (op : MOp.BinaryOp) : LLVM.Op :=
  MOp.binary (.concrete w) op

@[match_pattern] abbrev and    : Nat → LLVM.Op := MOp.and    ∘ .concrete
@[match_pattern] abbrev not    : Nat → LLVM.Op := MOp.not    ∘ .concrete
@[match_pattern] abbrev sext   : Nat → Nat → LLVM.Op := fun w w' => MOp.sext (.concrete w) (.concrete w')
@[match_pattern] abbrev xor    : Nat → LLVM.Op := MOp.xor    ∘ .concrete
@[match_pattern] abbrev urem   : Nat → LLVM.Op := MOp.urem   ∘ .concrete
@[match_pattern] abbrev srem   : Nat → LLVM.Op := MOp.srem   ∘ .concrete
@[match_pattern] abbrev isPowerOf2 : Nat → LLVM.Op := MOp.isPowerOf2 ∘ .concrete
@[match_pattern] abbrev assume : LLVM.Op := MOp.assume_
@[match_pattern] abbrev select : Nat → LLVM.Op := MOp.select ∘ .concrete
@[match_pattern] abbrev getelementptr (elemW idxW : Nat) : LLVM.Op :=
  MOp.getelementptr (.concrete elemW) (.concrete idxW)
@[match_pattern] abbrev load (w : Nat) : LLVM.Op := MOp.load (.concrete w)
@[match_pattern] abbrev store (w : Nat) : LLVM.Op := MOp.store (.concrete w)
@[match_pattern] abbrev alloca (w : Nat) : LLVM.Op := MOp.alloca (.concrete w)
@[match_pattern] abbrev call (retTy : LLVM.Ty) (fnName : String) (argTys : List LLVM.Ty) : LLVM.Op :=
  MOp.call retTy fnName argTys
@[match_pattern] abbrev neg    : Nat → LLVM.Op := MOp.neg    ∘ .concrete
@[match_pattern] abbrev copy   : Nat → LLVM.Op := MOp.copy   ∘ .concrete
@[match_pattern] abbrev freeze : Nat → LLVM.Op := MOp.freeze  ∘ .concrete
@[match_pattern] abbrev abs (w : Nat) (flag : _root_.LLVM.IntMinPoisonFlag := {is_int_min_poison := false}) : LLVM.Op := MOp.abs (.concrete w) flag
@[match_pattern] abbrev ctpop  : Nat → LLVM.Op := MOp.ctpop  ∘ .concrete
@[match_pattern] abbrev ctlz (w : Nat) (flag : _root_.LLVM.ZeroPoisonFlag := {is_zero_poison := false}) : LLVM.Op := MOp.ctlz (.concrete w) flag
@[match_pattern] abbrev cttz (w : Nat) (flag : _root_.LLVM.ZeroPoisonFlag := {is_zero_poison := false}) : LLVM.Op := MOp.cttz (.concrete w) flag

@[match_pattern] abbrev icmp (c : IntPred)   : Nat → LLVM.Op  := MOp.icmp c ∘ .concrete
@[match_pattern] abbrev const (w : Nat) (val : ℤ) : LLVM.Op        := MOp.const (.concrete w) val

/- This operation is separate from the others because it takes in a flag: nneg. -/
@[match_pattern] abbrev zext (w w': Nat) (flag : NonNegFlag := {nneg := false}) : LLVM.Op :=
  MOp.zext (.concrete w) (.concrete w') flag

/- This operation is separate from the others because it takes in a flag: disjoint. -/
@[match_pattern] abbrev or (w : Nat) (flag : DisjointFlag := {disjoint := false} ) : LLVM.Op :=
  MOp.or (.concrete w) flag

/- These operations are separate from the others because they take in 2 flags: nuw and nsw.-/
@[match_pattern] abbrev trunc (w w': Nat) (flags: NoWrapFlags := {}) : LLVM.Op :=
  MOp.trunc (.concrete w) (.concrete w') flags

@[match_pattern] abbrev shl (w : Nat) (flags: NoWrapFlags := {}) : LLVM.Op := MOp.shl (.concrete w) flags
@[match_pattern] abbrev add (w : Nat) (flags: NoWrapFlags := {}) : LLVM.Op := MOp.add (.concrete w) flags
@[match_pattern] abbrev mul (w : Nat) (flags: NoWrapFlags := {}) : LLVM.Op := MOp.mul (.concrete w) flags
@[match_pattern] abbrev sub (w : Nat) (flags: NoWrapFlags := {}) : LLVM.Op := MOp.sub (.concrete w) flags

/- These operations are separate from the others because they take in 1 flag: exact.-/
@[match_pattern] abbrev lshr (w : Nat) (flag : ExactFlag := {} ) : LLVM.Op := MOp.lshr (.concrete w) flag
@[match_pattern] abbrev ashr (w : Nat) (flag : ExactFlag := {} ) : LLVM.Op := MOp.ashr (.concrete w) flag
@[match_pattern] abbrev sdiv (w : Nat) (flag : ExactFlag := {} ) : LLVM.Op := MOp.sdiv (.concrete w) flag
@[match_pattern] abbrev udiv (w : Nat) (flag : ExactFlag := {} ) : LLVM.Op := MOp.udiv (.concrete w) flag

end LLVM.Op

/-! ### Basic Instances -/

instance : Monad (MetaLLVM φ).m := by unfold MetaLLVM; infer_instance
instance : LawfulMonad (MetaLLVM φ).m := by unfold MetaLLVM; infer_instance
instance : Monad LLVM.m := by unfold LLVM; infer_instance
instance : LawfulMonad LLVM.m := by unfold LLVM; infer_instance

instance {φ} : DialectToExpr (MetaLLVM φ) where
  toExprM := .const ``ImmediateUBOr [0]
  toExprDialect := .app (.const ``MetaLLVM []) (Lean.toExpr φ)

instance : Lean.ToExpr (LLVM.Op) := by unfold LLVM; infer_instance
instance : Lean.ToExpr (LLVM.Ty) := by unfold LLVM; infer_instance
instance : DialectToExpr LLVM where
  toExprM := .const ``ImmediateUBOr [0]
  toExprDialect := .const ``LLVM []

/-! ### Operation Formatting -/

instance : ToString (MOp φ) where
  toString
  | .and _      => "and"
  | .or _ _     => "or"
  | .not _      => "not"
  | .xor _      => "xor"
  | .shl _ _    => "shl"
  | .lshr _ _   => "lshr"
  | .ashr _ _   => "ashr"
  | .urem _     => "urem"
  | .srem _     => "srem"
  | .isPowerOf2 _ => "isPowerOf2"
  | .select _   => "select"
  | .add _ _    => "add"
  | .mul _ _    => "mul"
  | .sub _ _    => "sub"
  | .neg _      => "neg"
  | .copy _     => "copy"
  | .freeze _   => "freeze"
  | .abs _ _     => "abs"
  | .ctpop _    => "ctpop"
  | .ctlz _ _   => "ctlz"
  | .cttz _ _   => "cttz"
  | .trunc _ _ _  => "trunc"
  | .zext _ _ _ => "zext"
  | .sext _ _   => "sext"
  | .sdiv _ _   => "sdiv"
  | .udiv _ _   => "udiv"
  | .getelementptr _ _ => "getelementptr"
  | .load _     => "load"
  | .store _    => "store"
  | .alloca _   => "alloca"
  | .call _ fnName _ => s!"call @{fnName}"
  | .icmp ty _  => s!"icmp {ty}"
  | .assume_    => "assume"
  | .const _ v  => s!"const {v}"
  | .constParam _ idx => s!"constParam %{idx.val}"

-- TODO: the `ToString Op` and `ToString MOp` instances have different behaviour;
--       this is not likely to be what we want
-- instance : ToString Op where
--   toString o := repr o |>.pretty

instance : ToString LLVM.Op := by unfold LLVM; infer_instance
instance : Repr LLVM.Op     := by unfold LLVM; infer_instance

/-! ### Type Formatting -/

def MetaLLVM.printType : (MetaLLVM φ).Ty → String
  | .bitvec (.concrete w)  => s!"i{w}"
  | .bitvec (.mvar ⟨i, _⟩) => s!"i$\{%{i}}"
  | .ptr => "ptr"

instance : ToString (MetaLLVM φ).Ty := ⟨MetaLLVM.printType⟩
instance : Repr (MetaLLVM φ).Ty where
  reprPrec ty _ := s!"{ty}"

instance : ToString LLVM.Ty := by unfold LLVM; infer_instance
instance : Repr LLVM.Ty     := by unfold LLVM; infer_instance

def MetaLLVM.opName : (MetaLLVM φ).Op → String
  | .and _      => "llvm.and"
  | .or _ _     => "llvm.or"
  | .not _      => "llvm.not"
  | .xor _      => "llvm.xor"
  | .shl _ _    => "llvm.shl"
  | .lshr _ _   => "llvm.lshr"
  | .ashr _ _   => "llvm.ashr"
  | .urem _     => "llvm.urem"
  | .srem _     => "llvm.srem"
  | .isPowerOf2 _ => "llvm.isPowerOf2"
  | .select _   => "llvm.select"
  | .add _ _    => "llvm.add"
  | .mul _ _    => "llvm.mul"
  | .sub _ _    => "llvm.sub"
  | .neg _      => "llvm.neg"
  | .copy _     => "llvm.copy"
  | .freeze _   => "llvm.freeze"
  | .abs _ _     => "llvm.intr.abs"
  | .ctpop _    => "llvm.ctpop"
  | .ctlz _ _   => "llvm.intr.ctlz"
  | .cttz _ _   => "llvm.intr.cttz"
  | .trunc ..   => "llvm.trunc"
  | .zext ..    => "llvm.zext"
  | .sext _ _   => "llvm.sext"
  | .sdiv _ _   => "llvm.sdiv"
  | .udiv _ _   => "llvm.udiv"
  | .getelementptr _ _ => "llvm.getelementptr"
  | .load _     => "llvm.load"
  | .store _    => "llvm.store"
  | .alloca _   => "llvm.alloca"
  | .call _ _ _ => "llvm.call"
  | .icmp ty _  => s!"llvm.icmp.{ty}"
  | .assume_    => "llvm.assume"
  | .const _ _  => "llvm.mlir.constant"
  | .constParam _ _ => "llvm.mlir.constant"

def MetaLLVM.printAttributes : (MetaLLVM φ).Op → String
  | .const w v => s!"\{value = {v} : {w}}"
  | .constParam w idx => s!"\{value = 0 : {w}, __leanmlir_width_param_idx = {idx.val} : i64}"
  | .getelementptr elemW _ =>
      s!"\{elem_type = {MetaLLVM.printType (.bitvec elemW)}}"
  | .alloca w => s!"\{elem_type = {MetaLLVM.printType (.bitvec w)}}"
  | .call _ fnName _ => s!"\{callee = @{fnName}}"
  | .or w ⟨true⟩ => s!"\{disjoint = true : {w}}"
  | .unary _ (.abs flag) => s!"\{is_int_min_poison = {flag.is_int_min_poison}}"
  | .unary _ (.ctlz flag) | .unary _ (.cttz flag) => s!"\{is_zero_poison = {flag.is_zero_poison}}"
  | .add _ f | .shl _ f | .sub _ f | .mul _ f => printOverflowFlags f
  | .udiv _ ⟨true⟩ | .sdiv _ ⟨true⟩ | .lshr _ ⟨true⟩ => "<{isExact}> "
  | _ => ""
where
  printOverflowFlags : NoWrapFlags → String
  | ⟨false, false⟩ => "<{overflowFlags = #llvm.overflow<none>}>"
  -- TODO: ^^ since this case matches the default, do we even want to print any
  --          flags in this case?
  | ⟨true, false⟩  => "<{overflowFlags = #llvm.overflow<nsw>}>"
  | ⟨false, true⟩  => "<{overflowFlags = #llvm.overflow<nuw>}>"
  | ⟨true, true⟩   => "<{overflowFlags = #llvm.overflow<nsw,nuw>}>"

instance : DialectPrint (MetaLLVM φ) where
  printOpName := MetaLLVM.opName
  printTy := MetaLLVM.printType
  printAttributes := MetaLLVM.printAttributes
  dialectName := "llvm"
  printReturn _:= "llvm.return"
  printFunc _:= "^bb0"

instance : DialectPrint LLVM := by unfold LLVM; infer_instance

/-! ### Signature -/

@[simp, reducible]
def MOp.sig : MOp φ → List (MTy φ)
| .binary w _ | .icmp _ w =>
  [.bitvec w, .bitvec w]
| .isPowerOf2 w =>
  [.bitvec w]
| .unary w _ => [.bitvec w]
| .call _ _ argTys => argTys
| .getelementptr _ idxW => [.ptr, .bitvec idxW]
| .load _ => [.ptr]
| .store w => [.ptr, .bitvec w]
| .alloca _ => []
| .select w => [.bitvec 1, .bitvec w, .bitvec w]
| .assume_ => [.bitvec 1]
| .const _ _ => []
| .constParam _ _ => []

@[simp, reducible]
def MOp.UnaryOp.outTy (w : Width φ) : MOp.UnaryOp φ → MTy φ
| .trunc w' _ => .bitvec w'
| .zext w' _ => .bitvec w'
| .sext w' => .bitvec w'
| _ => .bitvec w

@[simp, reducible]
def MOp.outTy : MOp φ → MTy φ
| .binary w _ | .select w | .const w _ | .constParam w _ =>
  .bitvec w
| .unary w op => UnaryOp.outTy w op
| .call retTy _ _ => retTy
| .getelementptr _ _ => .ptr
| .load w => .bitvec w
| .store _ => .bitvec 1
| .alloca _ => .ptr
| .isPowerOf2 _ => .bitvec 1
| .icmp _ _ => .bitvec 1
| .assume_ => .bitvec 1

instance {φ} : DialectSignature (MetaLLVM φ) where
  signature
    | .assume_ => ⟨[.bitvec 1], [], [], .impure⟩
    | .store w => ⟨[.ptr, .bitvec w], [], [], .impure⟩
    | .load w => ⟨[.ptr], [], [.bitvec w], .impure⟩
    | .alloca _w => ⟨[], [], [.ptr], .impure⟩
    | .call retTy _ argTys => ⟨argTys, [], [retTy], .impure⟩
    | op => ⟨op.sig, [], [op.outTy], .pure⟩
instance : DialectSignature LLVM where
  signature
    | .assume_ => ⟨[.bitvec 1], [], [], .impure⟩
    | .store w => ⟨[.ptr, .bitvec w], [], [], .impure⟩
    | .load w => ⟨[.ptr], [], [.bitvec w], .impure⟩
    | .alloca _w => ⟨[], [], [.ptr], .impure⟩
    | .call retTy _ argTys => ⟨argTys, [], [retTy], .impure⟩
    | op => ⟨op.sig, [], [op.outTy], .pure⟩

/-! ### Type Semantics -/

namespace LLVMMemory

/-- A structured pointer: which allocation + byte offset within it. -/
structure Ptr where
  blockId : Nat
  offset  : BitVec 64
  deriving Repr, DecidableEq, Inhabited

abbrev PtrVal := LLVM.SemVal Ptr
abbrev PtrValUB := ImmediateUBOr PtrVal

instance : ToString Ptr where
  toString p := s!"({p.blockId}, {p.offset})"

instance : HRefinement Ptr Ptr where
  IsRefinedBy x y := x = y

end LLVMMemory

namespace LLVM.Ty

@[match_pattern] abbrev bitvec (w : Nat) : LLVM.Ty :=
  MTy.bitvec (.concrete w)

@[match_pattern] abbrev ptr : LLVM.Ty := MTy.ptr

def width : LLVM.Ty → Nat
  | .bitvec (.concrete w) => w
  | .bitvec (.mvar idx) => nomatch idx
  | ptr => 64

@[simp] -- TODO: this def should not live here
def BitVec.width {n : Nat} (_ : BitVec n) : Nat := n

instance : TyDenote LLVM.Ty where
  toType := fun
    | .bitvec (.concrete w) => LLVM.IntWUB w
    | .bitvec (.mvar idx) => nomatch idx
    | ptr => InstCombine.LLVMMemory.PtrValUB

@[simp_denote] lemma toType_bitvec : TyDenote.toType (Ty.bitvec w) = LLVM.IntWUB w := rfl
@[simp_denote] lemma toType_ptr : TyDenote.toType Ty.ptr = InstCombine.LLVMMemory.PtrValUB := rfl

instance (ty : LLVM.Ty) : Coe ℤ (TyDenote.toType ty) where
  coe z := match ty with
    | .bitvec (.concrete w) => .value <| BitVec.ofInt w z
    | .bitvec (.mvar idx) => nomatch idx
    | ptr => .some (.value { blockId := Int.toNat z, offset := 0#64 })

instance (ty : LLVM.Ty) : Inhabited (TyDenote.toType ty) where
  default := match ty with
    | .bitvec (.concrete _) => (.poison : LLVM.IntWUB _)
    | .bitvec (.mvar idx) => nomatch idx
    | ptr => (.some (.poison : LLVM.SemVal InstCombine.LLVMMemory.Ptr))

-- TODO: this instance should not live here
instance : Repr (BitVec n) where
  reprPrec
    | v, n => reprPrec (BitVec.toInt v) n

end LLVM.Ty

/-! ### Operation Semantics -/

def lift1
    (f : LLVM.IntW w₁ → LLVM.IntW w₂) (x : LLVM.IntWUB w₁) : LLVM.IntWUB w₂ :=
  f <$> x

def lift2
    (f : LLVM.IntW w₁ → LLVM.IntW w₂ → LLVM.IntW w₃)
    (x : LLVM.IntWUB w₁) (y : LLVM.IntWUB w₂) : LLVM.IntWUB w₃ := do
  let x' ← x
  let y' ← y
  pure <| f x' y'

def lift3
    (f : LLVM.IntW w₁ → LLVM.IntW w₂ → LLVM.IntW w₃ → LLVM.IntW w₄)
    (x : LLVM.IntWUB w₁) (y : LLVM.IntWUB w₂) (z : LLVM.IntWUB w₃) : LLVM.IntWUB w₄ := do
  let x' ← x
  let y' ← y
  let z' ← z
  pure <| f x' y' z'

def lift2UB
    (f : LLVM.IntW w₁ → LLVM.IntW w₂ → LLVM.IntWUB w₃)
    (x : LLVM.IntWUB w₁) (y : LLVM.IntWUB w₂) : LLVM.IntWUB w₃ := do
  let x' ← x
  let y' ← y
  f x' y'

/-- `lift1` spelled out as an explicit `Option.bind`, exposing the underlying
`Option` structure to the standard `Option` simp set. -/
@[simp] theorem lift1_eq_bind {w₁ w₂ : Nat}
    (f : LLVM.IntW w₁ → LLVM.IntW w₂) (x : LLVM.IntWUB w₁) :
    lift1 f x = Option.bind x (fun x' => some (f x')) := by
  cases x <;> rfl

/-- `lift2` spelled out as nested explicit `Option.bind`s, exposing the
underlying `Option` structure to the standard `Option` simp set. -/
@[simp] theorem lift2_eq_bind {w₁ w₂ w₃ : Nat}
    (f : LLVM.IntW w₁ → LLVM.IntW w₂ → LLVM.IntW w₃)
    (x : LLVM.IntWUB w₁) (y : LLVM.IntWUB w₂) :
    lift2 f x y =
      Option.bind x (fun x' => Option.bind y (fun y' => some (f x' y'))) := by
  cases x <;> cases y <;> rfl

@[simp]
def Op.denote (o : LLVM.Op) (op : HVector TyDenote.toType (DialectSignature.sig o)) :
    (TyDenote.toType (β := LLVM.Ty) o.outTy) :=
  match o with
  | LLVM.Op.const _ val    => pure <| const? _ val
  | LLVM.Op.copy _         =>               (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.freeze _       => lift1 (fun x => LLVM.freeze x) (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.abs _ flag     => lift1 (fun x => _root_.LLVM.abs x flag) (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.ctpop _        => lift1 (fun x => _root_.LLVM.ctpop x) (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.ctlz _ flag    => lift1 (fun x => _root_.LLVM.ctlz x flag) (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.cttz _ flag    => lift1 (fun x => _root_.LLVM.cttz x flag) (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.not _          => lift1 (fun x => LLVM.not x) (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.neg _          => lift1 (fun x => LLVM.neg x) (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.trunc _ w' flags =>
      lift1 (fun x => LLVM.trunc w' x flags) (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.zext _ w' flag =>
      lift1 (fun x => LLVM.zext w' x flag) (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.sext _ w'      =>
      lift1 (fun x => LLVM.sext w' x) (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.and _          =>
      lift2 (fun x y => LLVM.and x y)
        (op.getN 0 (by simp [DialectSignature.sig, signature]))
        (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.or _ flag      =>
      lift2 (fun x y => LLVM.or x y flag)
        (op.getN 0 (by simp [DialectSignature.sig, signature]))
        (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.xor _          =>
      lift2 (fun x y => LLVM.xor x y)
        (op.getN 0 (by simp [DialectSignature.sig, signature]))
        (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.shl _ flags    =>
      lift2 (fun x y => LLVM.shl x y flags)
        (op.getN 0 (by simp [DialectSignature.sig, signature]))
        (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.lshr _ flag    =>
      lift2 (fun x y => LLVM.lshr x y flag)
        (op.getN 0 (by simp [DialectSignature.sig, signature]))
        (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.ashr _ flag    =>
      lift2 (fun x y => LLVM.ashr x y flag)
        (op.getN 0 (by simp [DialectSignature.sig, signature]))
        (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.sub _ flags    =>
      lift2 (fun x y => LLVM.sub x y flags)
        (op.getN 0 (by simp [DialectSignature.sig, signature]))
        (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.add _ flags    =>
      lift2 (fun x y => LLVM.add x y flags)
        (op.getN 0 (by simp [DialectSignature.sig, signature]))
        (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.mul _ flags    =>
      lift2 (fun x y => LLVM.mul x y flags)
        (op.getN 0 (by simp [DialectSignature.sig, signature]))
        (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.sdiv _ flag    =>
      lift2UB (fun x y => LLVM.sdiv x y flag)
        (op.getN 0 (by simp [DialectSignature.sig, signature]))
        (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.udiv _ flag    =>
      lift2UB (fun x y => LLVM.udiv x y flag)
        (op.getN 0 (by simp [DialectSignature.sig, signature]))
        (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.urem _         =>
      lift2UB (fun x y => LLVM.urem x y)
        (op.getN 0 (by simp [DialectSignature.sig, signature]))
        (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.srem _         =>
      lift2UB (fun x y => LLVM.srem x y)
        (op.getN 0 (by simp [DialectSignature.sig, signature]))
        (op.getN 1 (by simp [DialectSignature.sig, signature]))
  -- Memory ops are intentionally disabled in the base LLVM entrypoint.
  -- Use `InstCombine.LLVMMemory.Com.denoteWithMemory` for executable memory semantics.
  | LLVM.Op.getelementptr _ _  =>
      let _ := op.getN 0 (by simp [DialectSignature.sig, signature])
      let _ := op.getN 1 (by simp [DialectSignature.sig, signature])
      .immediateUB
  | LLVM.Op.load w         =>
      let _ := op.getN 0 (by simp [DialectSignature.sig, signature])
      (.immediateUB : LLVM.IntWUB w)
  | LLVM.Op.store _        =>
      let _ := op.getN 0 (by simp [DialectSignature.sig, signature])
      let _ := op.getN 1 (by simp [DialectSignature.sig, signature])
      (.immediateUB : LLVM.IntWUB 1)
  | LLVM.Op.alloca _       =>
      .immediateUB
  | LLVM.Op.call retTy _ _ =>
      let _ := op
      match retTy with
      | .bitvec (.concrete w) =>
          (.immediateUB : LLVM.IntWUB w)
      | .bitvec (.mvar idx) =>
          nomatch idx
      | .ptr =>
          (.immediateUB : InstCombine.LLVMMemory.PtrValUB)
  | LLVM.Op.isPowerOf2 _   =>
      lift1 (fun x => LLVM.isPowerOf2 x)
        (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.icmp c _       =>
      lift2 (fun x y => LLVM.icmp c x y)
        (op.getN 0 (by simp [DialectSignature.sig, signature]))
        (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.select _       =>
      lift3 (fun c x y => LLVM.select c x y)
        (op.getN 0 (by simp [DialectSignature.sig, signature]))
        (op.getN 1 (by simp [DialectSignature.sig, signature]))
        (op.getN 2 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.assume         => do
      let c ← op.getN 0 (by simp [DialectSignature.sig, signature])
      let _ ← _root_.LLVM.assume_ c
      pure (.value (1#1) : LLVM.IntW 1)
  | .constParam _ idx => nomatch idx

@[simp]
def Op.denoteVec (o : LLVM.Op) (args : HVector TyDenote.toType (DialectSignature.sig o)) :
    ((DialectSignature.effectKind o).toMonad LLVM.m
      (HVector TyDenote.toType <| DialectSignature.returnTypes o)) :=
  match o with
  | .assume_ => do
      let c ← args.getN 0 (by simp [DialectSignature.sig, signature])
      let _ ← _root_.LLVM.assume_ c
      pure ([]ₕ)
  -- Memory effects are unavailable on the base `Com LLVM` path.
  | .store _w => ImmediateUBOr.immediateUB
  | .load _w => ImmediateUBOr.immediateUB
  | .alloca _w => ImmediateUBOr.immediateUB
  | .call _ _ _ => ImmediateUBOr.immediateUB
  | .unary w op' =>
      [Op.denote (.unary w op') args]ₕ
  | .binary w op' =>
      [Op.denote (.binary w op') args]ₕ
  | .getelementptr elemW idxW =>
      [Op.denote (.getelementptr elemW idxW) args]ₕ
  | .isPowerOf2 w =>
      [Op.denote (.isPowerOf2 w) args]ₕ
  | .select w =>
      [Op.denote (.select w) args]ₕ
  | .icmp c w =>
      [Op.denote (.icmp c w) args]ₕ
  | .const w val =>
      [Op.denote (.const w val) args]ₕ
  | .constParam w idx =>
      nomatch idx

instance : DialectDenote LLVM := ⟨
  fun o args _ => Op.denoteVec o args
⟩

/-! ### CFG execution semantics -/

private structure RuntimeCFGBlock (Γ : Ctxt LLVM.Ty) (retTys : List LLVM.Ty) where
  args : Ctxt LLVM.Ty
  body : CFGBody LLVM (args ++ Γ) .impure retTys

def CFGBlocks.findBlock? {Γ : Ctxt LLVM.Ty} {retTys : List LLVM.Ty}
    (name : String) : CFGBlocks LLVM Γ .impure retTys → Option (RuntimeCFGBlock Γ retTys)
  | .nil => none
  | .cons (.mk blockName args body) blocks =>
      if blockName == name then
        some ⟨args, body⟩
      else
        findBlock? name blocks

mutual

partial def CFGTarget.denoteFuel {Γ Γcur : Ctxt LLVM.Ty} {retTys : List LLVM.Ty}
    (fuel : Nat) (blocks : CFGBlocks LLVM Γ .impure retTys)
    (baseV : Γ.Valuation) (V : Γcur.Valuation) (target : CFGTarget LLVM Γcur) :
    ImmediateUBOr (HVector TyDenote.toType retTys) :=
  match fuel with
  | 0 => .immediateUB
  | fuel + 1 =>
      match CFGBlocks.findBlock? target.name blocks with
      | none => .immediateUB
      | some ⟨args, body⟩ =>
          if h : target.argTys = args.toList then
            let argVals : HVector TyDenote.toType args.toList :=
              h ▸ target.args.map V
            let blockV : (args ++ Γ).Valuation :=
              Ctxt.Valuation.cast (by cases args; rfl) (argVals ++ baseV)
            CFGBody.denoteFuel fuel blocks baseV body blockV
          else
            .immediateUB

partial def CFGTerm.denoteFuel {Γ Γcur : Ctxt LLVM.Ty} {retTys : List LLVM.Ty}
    (fuel : Nat) (blocks : CFGBlocks LLVM Γ .impure retTys)
    (baseV : Γ.Valuation) (V : Γcur.Valuation) :
    CFGTerm LLVM Γcur retTys → ImmediateUBOr (HVector TyDenote.toType retTys)
  | .ret vs => pure (vs.map V)
  | .br target => CFGTarget.denoteFuel fuel blocks baseV V target
  | .condBr (condTy := condTy) cond trueTarget falseTarget =>
      if h : condTy = LLVM.Ty.bitvec 1 then
        let condVal : TyDenote.toType (LLVM.Ty.bitvec 1) := h ▸ V cond
        let condUB : LLVM.IntWUB 1 := condVal
        match condUB with
        | .none => .immediateUB
        | .some .poison => .immediateUB
        | .some (.value c) =>
            if c == 1#1 then
              CFGTarget.denoteFuel fuel blocks baseV V trueTarget
            else
              CFGTarget.denoteFuel fuel blocks baseV V falseTarget
      else
        .immediateUB

partial def CFGBody.denoteFuel {Γ Γcur : Ctxt LLVM.Ty} {retTys : List LLVM.Ty}
    (fuel : Nat) (blocks : CFGBlocks LLVM Γ .impure retTys)
    (baseV : Γ.Valuation) :
    CFGBody LLVM Γcur .impure retTys → Γcur.Valuation →
    ImmediateUBOr (HVector TyDenote.toType retTys)
  | .terminator term, V => CFGTerm.denoteFuel fuel blocks baseV V term
  | .var e body, V => do
      let V' ← e.denote V
      CFGBody.denoteFuel fuel blocks baseV body V'

end

def Com.denoteCFGFuel {Γ : Ctxt LLVM.Ty} {retTys : List LLVM.Ty}
    (fuel : Nat) (com : Com LLVM Γ .impure retTys) (V : Γ.Valuation) :
    ImmediateUBOr (HVector TyDenote.toType retTys) :=
  match com with
  | .cfg entry blocks _fallback =>
      let target : CFGTarget LLVM Γ := { name := entry, argTys := [], args := .nil }
      CFGTarget.denoteFuel fuel blocks V V target
  | _ =>
      com.denote V

end InstCombine
