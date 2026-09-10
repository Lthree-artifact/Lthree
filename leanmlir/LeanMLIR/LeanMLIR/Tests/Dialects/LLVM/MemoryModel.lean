import LeanMLIR.Dialects.LLVM.MemoryModel
import LeanMLIR.Dialects.LLVM.Syntax

namespace LeanMLIR.Tests

open InstCombine
open LLVM.Ty (bitvec)
open InstCombine.LLVMMemory

private def ret0? {w : Nat} (r : ImmediateUBOr (HVector TyDenote.toType [bitvec w] × State)) :
    ImmediateUBOr (LLVM.IntWUB w) :=
  r.map fun (outs, _) => outs.getN 0 (by simp)

private def store_load (w1 : Nat) (_h : 0 < w1) := [llvm(w1)| {
  ^bb0:
    %p = llvm.alloca w1
    %v = llvm.mlir.constant(42 : w1) : w1
    llvm.store %p, %v : w1
    %x = llvm.load %p : w1
    llvm.return %x : w1
}]

private def store_load_i8 := store_load 8 (by decide)

example :
    ret0? (store_load_i8.denoteWithMemory (V := Ctxt.Valuation.nil))
      = (LLVM.IntWUB.value (42#8) : LLVM.IntWUB 8) := by
  native_decide

private def gep_store_load (w1 : Nat) (_h : 0 < w1) := [llvm(w1)| {
  ^bb0:
    %p = llvm.alloca w1
    %zero = llvm.mlir.constant 0 : i64
    %q = llvm.getelementptr i8, ptr %p, %zero : i64
    %v = llvm.mlir.constant(513 : w1) : w1
    llvm.store %q, %v : w1
    %x = llvm.load %q : w1
    llvm.return %x : w1
}]

private def gep_store_load_i16 := gep_store_load 16 (by decide)

example :
    ret0? (gep_store_load_i16.denoteWithMemory (V := Ctxt.Valuation.nil))
      = (LLVM.IntWUB.value (513#16) : LLVM.IntWUB 16) := by
  native_decide

private def two_alloca_no_alias_generic (w1 : Nat) (_h : 0 < w1) := [llvm(w1)| {
  ^bb0:
    %p = llvm.alloca w1
    %v1 = llvm.mlir.constant(7 : w1) : w1
    llvm.store %p, %v1 : w1
    %q = llvm.alloca w1
    %v2 = llvm.mlir.constant(9 : w1) : w1
    llvm.store %q, %v2 : w1
    %x = llvm.load %p : w1
    llvm.return %x : w1
}]

private def two_alloca_no_alias := two_alloca_no_alias_generic 8 (by decide)

example :
    ret0? (two_alloca_no_alias.denoteWithMemory (V := Ctxt.Valuation.nil))
      = (LLVM.IntWUB.value (7#8) : LLVM.IntWUB 8) := by
  native_decide

private def oob_load_generic (w1 : Nat) (_h : 0 < w1) := [llvm(w1)| {
  ^bb0:
    %p = llvm.alloca w1
    %one = llvm.mlir.constant 1 : i64
    %q = llvm.getelementptr i8, ptr %p, %one : i64
    %x = llvm.load %q : w1
    llvm.return %x : w1
}]

private def oob_load := oob_load_generic 8 (by decide)

example :
    (oob_load.denoteWithMemory (V := Ctxt.Valuation.nil)).isNone = true := by
  native_decide

end LeanMLIR.Tests
