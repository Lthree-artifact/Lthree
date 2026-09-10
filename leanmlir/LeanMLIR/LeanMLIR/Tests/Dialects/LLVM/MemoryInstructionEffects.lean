import LeanMLIR.Dialects.LLVM.MemoryModel
import LeanMLIR.Dialects.LLVM.Syntax

namespace LeanMLIR.Tests

open InstCombine
open LLVM.Ty (bitvec)
open InstCombine.LLVMMemory

private def ret0? {w : Nat} (r : ImmediateUBOr (HVector TyDenote.toType [bitvec w] × State)) :
    ImmediateUBOr (LLVM.IntWUB w) :=
  r.map fun (outs, _) => outs.getN 0 (by simp)

/-- `store` then `load` at the same pointer returns the written value. -/
private def roundtrip_store_load := [llvm| {
  ^bb0:
    %p = llvm.alloca i8
    %v = llvm.mlir.constant(171 : i8) : i8
    llvm.store %p, %v : i8
    %x = llvm.load %p : i8
    llvm.return %x : i8
}]

/--
Same observable result as `roundtrip_store_load`, but with a different syntax
tree and computation path:
- build `171` via `170 + 1`
- access the store address via `gep i8, %p, 0`
-/
private def roundtrip_store_load_alt := [llvm| {
  ^bb0:
    %p = llvm.alloca i8

    %c170 = llvm.mlir.constant(170 : i8) : i8
    %c1 = llvm.mlir.constant(1 : i8) : i8
    %v = llvm.add %c170, %c1 : i8

    %zero = llvm.mlir.constant 0 : i8
    %q = llvm.getelementptr i8, ptr %p, %zero : i8
    llvm.store %q, %v : i8
    %x = llvm.load %p : i8
    llvm.return %x : i8
}]

example :
    ret0? (roundtrip_store_load.denoteWithMemory (V := Ctxt.Valuation.nil))
      = ret0? (roundtrip_store_load_alt.denoteWithMemory (V := Ctxt.Valuation.nil)) := by
  native_decide

/-- Distinct `alloca` pointers are disjoint in the memory model. -/
private def two_alloca_disjoint := [llvm| {
  ^bb0:
    %p = llvm.alloca i8
    %q = llvm.alloca i8
    %vp = llvm.mlir.constant(12 : i8) : i8
    %vq = llvm.mlir.constant(99 : i8) : i8
    llvm.store %p, %vp : i8
    llvm.store %q, %vq : i8
    %x = llvm.load %p : i8
    llvm.return %x : i8
}]

example :
    ret0? (two_alloca_disjoint.denoteWithMemory (V := Ctxt.Valuation.nil))
      = (LLVM.IntWUB.value (12#8) : LLVM.IntWUB 8) := by
  native_decide

/--
Writing through `gep i8, ptr %p, 1` on a 2-byte allocation touches byte 1,
while byte 0 stays uninitialized, so `load i8` at `%p` yields poison.
-/
private def store_at_offset_keeps_base := [llvm| {
  ^bb0:
    %p = llvm.alloca i16
    %one = llvm.mlir.constant 1 : i8
    %q = llvm.getelementptr i8, ptr %p, %one : i8
    %v = llvm.mlir.constant(34 : i8) : i8
    llvm.store %q, %v : i8
    %x = llvm.load %p : i8
    llvm.return %x : i8
}]

example :
    ret0? (store_at_offset_keeps_base.denoteWithMemory (V := Ctxt.Valuation.nil))
      = (LLVM.IntWUB.poison : LLVM.IntWUB 8) := by
  native_decide

/-- Loading from fresh `alloca` memory yields poison in this model. -/
private def uninitialized_load_is_poison := [llvm| {
  ^bb0:
    %p = llvm.alloca i8
    %x = llvm.load %p : i8
    llvm.return %x : i8
}]

example :
    ret0? (uninitialized_load_is_poison.denoteWithMemory (V := Ctxt.Valuation.nil))
      = (LLVM.IntWUB.poison : LLVM.IntWUB 8) := by
  native_decide

/--
Matches `alloca; load; add; ret`: uninitialized `load` yields poison, and `add`
propagates poison.
-/
private def uninitialized_load_add_is_poison := [llvm| {
  ^bb0:
    %p = llvm.alloca i8
    %x = llvm.load %p : i8
    %y = llvm.add %x, %x : i8
    llvm.return %y : i8
}]

example :
    ret0? (uninitialized_load_add_is_poison.denoteWithMemory (V := Ctxt.Valuation.nil))
      = (LLVM.IntWUB.poison : LLVM.IntWUB 8) := by
  native_decide

/-- One-byte allocation + offset `1` is out-of-bounds for `load i8`. -/
private def one_byte_oob := [llvm| {
  ^bb0:
    %p = llvm.alloca i8
    %one = llvm.mlir.constant 1 : i8
    %q = llvm.getelementptr i8, ptr %p, %one : i8
    %x = llvm.load %q : i8
    llvm.return %x : i8
}]

example :
    (one_byte_oob.denoteWithMemory (V := Ctxt.Valuation.nil)).isNone = true := by
  native_decide

end LeanMLIR.Tests
