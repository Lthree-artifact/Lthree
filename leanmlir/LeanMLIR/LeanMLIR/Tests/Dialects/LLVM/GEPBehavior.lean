import LeanMLIR.Dialects.LLVM.MemoryModel
import LeanMLIR.Dialects.LLVM.Syntax

namespace LeanMLIR.Tests

open InstCombine
open LLVM.Ty (bitvec)
open InstCombine.LLVMMemory

private def ret0? {w : Nat} (r : ImmediateUBOr (HVector TyDenote.toType [bitvec w] × State)) :
    ImmediateUBOr (LLVM.IntWUB w) :=
  r.map fun (outs, _) => outs.getN 0 (by simp)

/--
`gep i16, ptr %p, 1` advances by 2 bytes.
On a 2-byte allocation this points to one-past-end, so `load i8` is UB.
-/
private def gep_i16_stride_oob := [llvm| {
  ^bb0:
    %p = llvm.alloca i16
    %one = llvm.mlir.constant 1 : i8
    %q = llvm.getelementptr i16, ptr %p, %one : i8
    %x = llvm.load %q : i8
    llvm.return %x : i8
}]

example :
    (gep_i16_stride_oob.denoteWithMemory (V := Ctxt.Valuation.nil)).isNone = true := by
  native_decide

/--
Element type `i5` has byte-size `1` in this model (`bytesForWidth` ceiling rule),
so offset `3` reaches byte 3 (within a 4-byte allocation).
-/
private def gep_i5_stride_is_one_byte := [llvm| {
  ^bb0:
    %p = llvm.alloca i32
    %base = llvm.mlir.constant(17 : i8) : i8
    llvm.store %p, %base : i8
    %three = llvm.mlir.constant 3 : i8
    %q = llvm.getelementptr i5, ptr %p, %three : i8
    %tail = llvm.mlir.constant(99 : i8) : i8
    llvm.store %q, %tail : i8
    %x = llvm.load %p : i8
    llvm.return %x : i8
}]

example :
    ret0? (gep_i5_stride_is_one_byte.denoteWithMemory (V := Ctxt.Valuation.nil))
      = (LLVM.IntWUB.value (17#8) : LLVM.IntWUB 8) := by
  native_decide

private def gep_idx_i8 := [llvm| {
  ^bb0:
    %p = llvm.alloca i16
    %one = llvm.mlir.constant 1 : i8
    %q = llvm.getelementptr i8, ptr %p, %one : i8
    %v = llvm.mlir.constant(77 : i8) : i8
    llvm.store %q, %v : i8
    %x = llvm.load %q : i8
    llvm.return %x : i8
}]

private def gep_idx_i64 := [llvm| {
  ^bb0:
    %p = llvm.alloca i16
    %one = llvm.mlir.constant 1 : i64
    %q = llvm.getelementptr i8, ptr %p, %one : i64
    %v = llvm.mlir.constant(77 : i8) : i8
    llvm.store %q, %v : i8
    %x = llvm.load %q : i8
    llvm.return %x : i8
}]

/-- Same logical offset with `i8` and `i64` index gives the same result. -/
example :
    ret0? (gep_idx_i8.denoteWithMemory (V := Ctxt.Valuation.nil))
      = ret0? (gep_idx_i64.denoteWithMemory (V := Ctxt.Valuation.nil)) := by
  native_decide

/--
Index `255 : i8` has sign bit set; after sign-extension it behaves like `-1`.
This points outside the allocated block in this model, so `load` is UB.
-/
private def gep_negative_i8_oob := [llvm| {
  ^bb0:
    %p = llvm.alloca i8
    %ff = llvm.mlir.constant 255 : i8
    %q = llvm.getelementptr i8, ptr %p, %ff : i8
    %x = llvm.load %q : i8
    llvm.return %x : i8
}]

example :
    (gep_negative_i8_oob.denoteWithMemory (V := Ctxt.Valuation.nil)).isNone = true := by
  native_decide

end LeanMLIR.Tests

