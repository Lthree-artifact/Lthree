import LeanMLIR.Dialects.LLVM

namespace LeanMLIR.Tests

open InstCombine

private def singleBlockReturn :=
  [llvm()| {
    llvm.func @single_block_return() -> i32 {
    ^entry:
      %c = llvm.mlir.constant 7 : i32
      llvm.return %c : i32
    }
  }]

private def twoBlockBr :=
  [llvm()| {
    llvm.func @two_block_br(%seed : i32) -> i32 {
    ^entry(%seed : i32):
      %c = llvm.mlir.constant 7 : i32
      llvm.br ^exit(%c : i32)
    ^exit(%x : i32):
      llvm.return %x : i32
    }
  }]

private def diamondCondBr :=
  [llvm()| {
    llvm.func @diamond_cond_br(%seed : i32, %cond : i1) -> i32 {
    ^entry(%seed : i32, %cond : i1):
      llvm.cond_br %cond : i1, ^then_bb(), ^else_bb()
    ^then_bb:
      %t = llvm.mlir.constant 11 : i32
      llvm.return %t : i32
    ^else_bb:
      %f = llvm.mlir.constant 22 : i32
      llvm.return %f : i32
    }
  }]

private def symbolicWidthBr (w1 : Nat) :=
  [llvm(w1)| {
    llvm.func @symbolic_width_br(%x : _) -> _ {
    ^entry(%x : _):
      llvm.br ^exit(%x : _)
    ^exit(%y : _):
      llvm.return %y : _
    }
  }]

private def simpleLoop :=
  [llvm()| {
    llvm.func @simple_loop(%n : i32, %acc0 : i32) -> i32 {
    ^entry(%n : i32, %acc0 : i32):
      %zero = llvm.mlir.constant 0 : i32
      llvm.br ^header(%zero : i32, %acc0 : i32)
    ^header(%i : i32, %acc : i32):
      %done = llvm.icmp "eq" %i, %n : i32
      llvm.cond_br %done : i1, ^exit(%acc : i32), ^body(%i : i32, %acc : i32)
    ^body(%i : i32, %acc : i32):
      %one = llvm.mlir.constant 1 : i32
      %i_next = llvm.add %i, %one : i32
      llvm.br ^header(%i_next : i32, %acc : i32)
    ^exit(%acc : i32):
      llvm.return %acc : i32
    }
  }]

private def retI32? :
    ImmediateUBOr (HVector TyDenote.toType [LLVM.Ty.bitvec 32]) → LLVM.IntWUB 32
  | .none => .none
  | .some (v ::ₕ .nil) => v

example :
    retI32? (Com.denoteCFGFuel 4 twoBlockBr
      (Ctxt.Valuation.ofHVector
        [((.value (0#32)) : TyDenote.toType (LLVM.Ty.bitvec 32))]ₕ))
      = ((.value (7#32)) : LLVM.IntWUB 32) := by
  native_decide

example :
    retI32? (Com.denoteCFGFuel 4 diamondCondBr
        (Ctxt.Valuation.ofHVector
          [((.value (0#32)) : TyDenote.toType (LLVM.Ty.bitvec 32)),
           ((.value (1#1)) : TyDenote.toType (LLVM.Ty.bitvec 1))]ₕ))
      = ((.value (11#32)) : LLVM.IntWUB 32) := by
  native_decide

example :
    retI32? (Com.denoteCFGFuel 4 diamondCondBr
        (Ctxt.Valuation.ofHVector
          [((.value (0#32)) : TyDenote.toType (LLVM.Ty.bitvec 32)),
           ((.value (0#1)) : TyDenote.toType (LLVM.Ty.bitvec 1))]ₕ))
      = ((.value (22#32)) : LLVM.IntWUB 32) := by
  native_decide

example :
    retI32? (Com.denoteCFGFuel 6 simpleLoop
        (Ctxt.Valuation.ofHVector
          [((.value (0#32)) : TyDenote.toType (LLVM.Ty.bitvec 32)),
           ((.value (9#32)) : TyDenote.toType (LLVM.Ty.bitvec 32))]ₕ))
      = ((.value (9#32)) : LLVM.IntWUB 32) := by
  native_decide

#check singleBlockReturn
#check symbolicWidthBr

end LeanMLIR.Tests
