/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanMLIR.Framework.Macro

import LeanMLIR.Dialects.LLVM.Basic
import SSA.Projects.SLLVM.Dialect.Semantics

namespace LeanMLIR
open InstCombine (LLVM)

/-!
## SLLVM Dialect
SLLVM stands for "Structured LLVM"; eventually this dialect will become a
formalization of the `ptr + arith + scf` MLIR dialects.
This IR is conceptually similar to LLVM IR, except it uses only *structured*
control flow, hence the name.

Note that in the formalization, we assume a 64-bit architecture!
Nothing in the formalization itself should depend on the exact pointer-width,
but this assumption does affect which optimizations are admitted.

For now, though, this dialect just models only arithmetic, just like our
existing LLVM dialect, *but* it refines the semantics to include a proper model
of (side-effecting) UB.
-/

/-! ### Dialect definition -/

inductive SLLVMOp where
  | arith (o : LLVM.Op)
  | ptradd
  | load (w : Nat)
  | store (w : Nat)
  | alloca (w : Nat)
  | loadPure (w : Nat)
  | storePure (w : Nat)
  deriving DecidableEq, Lean.ToExpr

inductive SLLVMTy where
  | arith (t : LLVM.Ty)
  | ptr
  | mem
  deriving DecidableEq, Lean.ToExpr

def SLLVM : Dialect where
  Op := SLLVMOp
  Ty := SLLVMTy
  m := EffectM

namespace SLLVM

instance : TyDenote SLLVM.Ty where
  toType
  | .arith (.bitvec w) => LLVM.IntW (ConcreteOrMVar.toConcrete w)
  | .arith (.ptr) => LLVM.IntW 64
  | .ptr => SLLVM.Ptr
  | .mem => MemorySSAState

instance : DecidableEq SLLVM.Op := by unfold SLLVM; infer_instance
instance : DecidableEq SLLVM.Ty := by unfold SLLVM; infer_instance
instance : Lean.ToExpr SLLVM.Op := by unfold SLLVM; infer_instance
instance : Lean.ToExpr SLLVM.Ty := by unfold SLLVM; infer_instance

instance : Monad SLLVM.m        := by unfold SLLVM; infer_instance
instance : LawfulMonad SLLVM.m  := by unfold SLLVM; infer_instance

open Qq in instance : DialectToExpr SLLVM where
  toExprDialect := q(SLLVM)
  toExprM := q(Id.{0})

@[simp, simp_denote]
theorem m_eq : SLLVM.m α = EffectM α := by rfl

/-! ### Aliasses -/
section Alias
open InstCombine.LLVM SLLVMOp

@[match_pattern] nonrec abbrev Ty.arith : LLVM.Ty → SLLVM.Ty := .arith

@[match_pattern] abbrev Ty.bitvec (w : Nat) : SLLVM.Ty := .arith (.bitvec w)
@[match_pattern] abbrev Ty.ptr : SLLVM.Ty := .ptr
@[match_pattern] abbrev Ty.mem : SLLVM.Ty := .mem

@[match_pattern] nonrec abbrev Op.arith : LLVM.Op → SLLVM.Op := .arith

@[match_pattern] nonrec abbrev Op.neg (w : Nat) : SLLVM.Op := arith <| Op.neg w
@[match_pattern] nonrec abbrev Op.not (w : Nat) : SLLVM.Op := arith <| Op.not w
@[match_pattern] nonrec abbrev Op.copy (w : Nat) : SLLVM.Op := arith <| Op.copy w
@[match_pattern] nonrec abbrev Op.freeze (w : Nat) : SLLVM.Op := arith <| Op.freeze w
@[match_pattern] nonrec abbrev Op.ctpop (w : Nat) : SLLVM.Op := arith <| Op.ctpop w
@[match_pattern] nonrec abbrev Op.ctlz (w : Nat) (flag : _root_.LLVM.ZeroPoisonFlag := { }) : SLLVM.Op := arith <| Op.ctlz w flag
@[match_pattern] nonrec abbrev Op.cttz (w : Nat) (flag : _root_.LLVM.ZeroPoisonFlag := { }) : SLLVM.Op := arith <| Op.cttz w flag
@[match_pattern] nonrec abbrev Op.sext (w w' : Nat) : SLLVM.Op := arith <| Op.sext w w'
@[match_pattern] nonrec abbrev Op.zext (w w' : Nat) (flag : LLVM.NonNegFlag := { }) : SLLVM.Op := arith <| Op.zext w w' flag
@[match_pattern] nonrec abbrev Op.trunc (w w' : Nat) (flags : LLVM.NoWrapFlags := { }) : SLLVM.Op := arith <| Op.trunc w w' flags

@[match_pattern] nonrec abbrev Op.and (w : Nat) : SLLVM.Op := arith <| Op.and w
@[match_pattern] nonrec abbrev Op.or (w : Nat) (flag : LLVM.DisjointFlag := { }) : SLLVM.Op := arith <| Op.or w flag
@[match_pattern] nonrec abbrev Op.xor (w : Nat) : SLLVM.Op := arith <| Op.xor w
@[match_pattern] nonrec abbrev Op.shl (w : Nat) (flags : LLVM.NoWrapFlags := { }) : SLLVM.Op := arith <| Op.shl w flags
@[match_pattern] nonrec abbrev Op.lshr (w : Nat) (flag : LLVM.ExactFlag := { }) : SLLVM.Op := arith <| Op.lshr w flag
@[match_pattern] nonrec abbrev Op.ashr (w : Nat) (flag : LLVM.ExactFlag := { }) : SLLVM.Op := arith <| Op.ashr w flag
@[match_pattern] nonrec abbrev Op.add (w : Nat) (flags : LLVM.NoWrapFlags := { }) : SLLVM.Op := arith <| Op.add w flags
@[match_pattern] nonrec abbrev Op.mul (w : Nat) (flags : LLVM.NoWrapFlags := { }) : SLLVM.Op := arith <| Op.mul w flags
@[match_pattern] nonrec abbrev Op.sub (w : Nat) (flags : LLVM.NoWrapFlags := { }) : SLLVM.Op := arith <| Op.sub w flags

@[match_pattern] nonrec abbrev Op.icmp (c : LLVM.IntPred) (w : Nat) : SLLVM.Op := arith <| Op.icmp c w
@[match_pattern] nonrec abbrev Op.const (w : Nat) (val : Int) : SLLVM.Op := arith <| Op.const w val
@[match_pattern] nonrec abbrev Op.select (w : Nat) : SLLVM.Op := arith <| Op.select w

@[match_pattern] nonrec abbrev Op.getelementptr (elemW idxW : Nat) : SLLVM.Op := arith <| InstCombine.LLVM.Op.getelementptr elemW idxW
@[match_pattern] nonrec abbrev Op.load (w : Nat) : SLLVM.Op := arith <| InstCombine.LLVM.Op.load w
@[match_pattern] nonrec abbrev Op.store (w : Nat) : SLLVM.Op := arith <| InstCombine.LLVM.Op.store w
@[match_pattern] nonrec abbrev Op.alloca (w : Nat) : SLLVM.Op := arith <| InstCombine.LLVM.Op.alloca w
@[match_pattern] nonrec abbrev Op.call
    (retTy : InstCombine.LLVM.Ty) (fnName : String) (argTys : List InstCombine.LLVM.Ty) :
    SLLVM.Op := arith <| InstCombine.LLVM.Op.call retTy fnName argTys
@[match_pattern] nonrec abbrev Op.udiv (w : Nat) (flag : LLVM.ExactFlag := { }) : SLLVM.Op := arith <| Op.udiv w flag
@[match_pattern] nonrec abbrev Op.sdiv (w : Nat) (flag : LLVM.ExactFlag := { }) : SLLVM.Op := arith <| Op.sdiv w flag
@[match_pattern] nonrec abbrev Op.urem : Nat → SLLVM.Op := arith ∘ Op.urem
@[match_pattern] nonrec abbrev Op.srem : Nat → SLLVM.Op := arith ∘ Op.srem
@[match_pattern] nonrec abbrev Op.isPowerOf2 : Nat → SLLVM.Op := arith ∘ Op.isPowerOf2
@[match_pattern] nonrec abbrev Op.assume : SLLVM.Op := arith <| Op.assume


@[simp, simp_denote] theorem toType_arith : toType (Ty.arith t) = LLVM.IntW (LLVM.Ty.width t) := by
  cases t with
  | bitvec w =>
      cases w with
      | concrete w =>
          change LLVM.IntW (ConcreteOrMVar.toConcrete (ConcreteOrMVar.concrete w)) = LLVM.IntW w
          simp
      | mvar i => exact (False.elim (Nat.not_lt_zero _ i.isLt))
  | ptr =>
      rfl
@[simp, simp_denote] theorem toType_bitvec : toType (Ty.bitvec w) = LLVM.IntW w := by
  change LLVM.IntW (ConcreteOrMVar.toConcrete (ConcreteOrMVar.concrete w)) = LLVM.IntW w
  simp

end Alias

/-! ### Signature -/

open Ty in
/- The signature of each operation is the same as in LLVM. -/
def_signature for SLLVM
  -- New operations
  | .ptradd          => (ptr, bitvec 64) -> ptr
  | .load w          => (ptr) -[.impure]-> bitvec w
  | .loadPure w      => (mem, ptr) -> [mem, bitvec w]
  | .store w         => (ptr, bitvec w) -[.impure]-> []
  | .storePure w     => (mem, ptr, bitvec w) -> [mem]
  | .alloca _w       => () -[.impure]-> ptr
  -- LLVM operations with modified effect signature
  | Op.load w        => (bitvec 64) -[.impure]-> bitvec w
  | Op.store w       => (bitvec 64, bitvec w) -[.impure]-> []
  | Op.alloca _w     => () -[.impure]-> bitvec 64
  | Op.call retTy _fnName argTys => ${(Ty.arith <$> argTys)} -[.impure]-> [Ty.arith retTy]
  | Op.urem w        => (bitvec w, bitvec w) -[.impure]-> bitvec w
  | Op.srem w        => (bitvec w, bitvec w) -[.impure]-> bitvec w
  | Op.sdiv w _flag  => (bitvec w, bitvec w) -[.impure]-> bitvec w
  | Op.udiv w _flag  => (bitvec w, bitvec w) -[.impure]-> bitvec w
  | Op.assume        => (bitvec 1) -[.impure]-> []
  -- Other LLVM operations
  | Op.getelementptr _elemW idxW => (bitvec 64, bitvec idxW) -> bitvec 64
  | Op.isPowerOf2 w  => (bitvec w) -> bitvec 1
  | Op.neg w         => (bitvec w) -> bitvec w
  | Op.not w         => (bitvec w) -> bitvec w
  | Op.copy w        => (bitvec w) -> bitvec w
  | Op.freeze w      => (bitvec w) -> bitvec w
  | Op.ctpop w       => (bitvec w) -> bitvec w
  | Op.ctlz w _flag  => (bitvec w) -> bitvec w
  | Op.cttz w _flag  => (bitvec w) -> bitvec w
  | Op.sext w w'     => (bitvec w) -> bitvec w'
  | Op.zext w w' _flag   => (bitvec w) -> bitvec w'
  | Op.trunc w w' _flags => (bitvec w) -> bitvec w'
  | Op.and w         => (bitvec w, bitvec w) -> bitvec w
  | Op.xor w         => (bitvec w, bitvec w) -> bitvec w
  | Op.or w _flag    => (bitvec w, bitvec w) -> bitvec w
  | Op.shl w _flags  => (bitvec w, bitvec w) -> bitvec w
  | Op.add w _flags  => (bitvec w, bitvec w) -> bitvec w
  | Op.mul w _flags  => (bitvec w, bitvec w) -> bitvec w
  | Op.sub w _flags  => (bitvec w, bitvec w) -> bitvec w
  | Op.lshr w _flag  => (bitvec w, bitvec w) -> bitvec w
  | Op.ashr w _flag  => (bitvec w, bitvec w) -> bitvec w
  | Op.icmp _c w     => (bitvec w, bitvec w) -> bitvec 1
  | Op.select w      => (bitvec 1, bitvec w, bitvec w) -> bitvec w
  | Op.const w _val  => () -> bitvec w

attribute [local irreducible] EffectM
-- ^^ This is needed so that `EffectM` doesn't get unfolded in the `def_denote` macro

private def bytesForWidth (w : Nat) : Nat :=
  max 1 ((w + 7) / 8)

def_denote for SLLVM
  -- New operations
  | .ptradd   => fun p x => [SLLVM.ptradd p x]ₕ
  | .load w   => fun p   => ([·]ₕ) <$> SLLVM.load p w
  | .loadPure w => fun m p => HVector.ofPair <| SLLVM.loadPure m p w
  | .store _  => fun p x => (fun _ => []ₕ) <$> SLLVM.store p x
  | .storePure _ => fun m p x => [SLLVM.storePure m p x]ₕ
  | .alloca w => ([·]ₕ) <$> SLLVM.alloca w
  -- LLVM operations with modified effect signature
  | Op.load _w      => fun _ => throwUB
  | Op.store _w     => fun _ _ => throwUB
  | Op.alloca _w    => throwUB
  | Op.call _retTy _fnName _argTys => fun _ => throwUB
  | Op.udiv _w flag => fun x y => ([·]ₕ) <$> SLLVM.udiv x y flag
  | Op.sdiv _w flag => fun x y => ([·]ₕ) <$> SLLVM.sdiv x y flag
  | Op.urem _w      => fun x y => ([·]ₕ) <$> SLLVM.urem x y
  | Op.srem _w      => fun x y => ([·]ₕ) <$> SLLVM.srem x y
  | Op.assume       => fun c =>
      if c = (.value (1#1) : LLVM.IntW 1) then
        pure ([]ₕ)
      else
        throwUB
  -- Other LLVM operations
  | Op.getelementptr elemW _idxW => fun x y =>
      let idx64 := LLVM.sext 64 y
      let scaled := LLVM.mul idx64 (LLVM.SemVal.value (BitVec.ofNat 64 (bytesForWidth elemW))) {}
      [LLVM.add x scaled {}]ₕ
  | Op.isPowerOf2 _w => fun x => [LLVM.isPowerOf2 x]ₕ
  | Op.neg _w       => fun x => [LLVM.neg x]ₕ
  | Op.not _w       => fun x => [LLVM.not x]ₕ
  | Op.copy _w      => fun x => [x]ₕ
  | Op.freeze _w    => fun x => [LLVM.freeze x]ₕ
  | Op.ctpop _w     => fun x => [_root_.LLVM.ctpop x]ₕ
  | Op.ctlz _w flag => fun x => [_root_.LLVM.ctlz x flag]ₕ
  | Op.cttz _w flag => fun x => [_root_.LLVM.cttz x flag]ₕ
  | Op.sext _w w'   => fun x => [LLVM.sext w' x]ₕ
  | Op.zext _w w' flag   => fun x => [LLVM.zext w' x flag]ₕ
  | Op.trunc _w w' flags => fun x => [LLVM.trunc w' x flags]ₕ
  | Op.and _w       => fun x y => [LLVM.and x y]ₕ
  | Op.xor _w       => fun x y => [LLVM.xor x y]ₕ
  | Op.or _w flag   => fun x y => [LLVM.or x y flag]ₕ
  | Op.shl _w flags => fun x y => [LLVM.shl x y flags]ₕ
  | Op.add _w flags => fun x y => [LLVM.add x y flags]ₕ
  | Op.mul _w flags => fun x y => [LLVM.mul x y flags]ₕ
  | Op.sub _w flags => fun x y => [LLVM.sub x y flags]ₕ
  | Op.lshr _w flag => fun x y => [LLVM.lshr x y flag]ₕ
  | Op.ashr _w flag => fun x y => [LLVM.ashr x y flag]ₕ
  | Op.icmp c _w    => fun x y => [LLVM.icmp c x y]ₕ
  | Op.select _w    => fun c x y => [LLVM.select c x y]ₕ
  | Op.const _w val => [LLVM.const? _ val]ₕ

/-! ### Printing -/
section Print
open DialectPrint

instance : DialectPrint SLLVM where
  printOpName
    | .arith llvmOp => printOpName llvmOp
    | .storePure _
    | .store _w   => "ptr.store"
    | .loadPure _
    | .load _w    => "ptr.load"
    | .ptradd     => "ptr.add"
    | .alloca _w  => "ptr.alloca"
  printAttributes
    | .arith llvmOp => printAttributes llvmOp
    | .alloca w => s!"\{elem_type = i{w}}"
    | _ => ""
  printTy
    | .arith llvmTy => printTy llvmTy
    | .ptr => "!ptr"
    | .mem => "!mem"
  dialectName := "sllvm"
  printReturn _ := "llvm.return"
  printFunc _ := "^entry"

end Print
