import LeanMLIR.Dialects.LLVM.Syntax

namespace LeanMLIR.Tests

open InstCombine
open LLVM.Ty (bitvec)

private def parse_memory_ops_generic (w1 : Nat) (_h : 0 < w1) := [llvm(w1)| {
  ^bb0:
    %p = llvm.alloca w1
    %zero = llvm.mlir.constant 0 : i64
    %q = llvm.getelementptr i8, ptr %p, %zero : i64
    %v = llvm.mlir.constant 7 : w1
    llvm.store %q, %v : w1
    %x = llvm.load %q : w1
    llvm.return %x : w1
}]

private def parse_memory_ops := parse_memory_ops_generic 8 (by decide)

example : DialectSignature.returnTypes (LLVM.Op.alloca 8) = [LLVM.Ty.ptr] := by
  rfl

example : DialectSignature.sig (LLVM.Op.load 8) = [LLVM.Ty.ptr] := by
  rfl

example : DialectSignature.sig (LLVM.Op.store 8) = [LLVM.Ty.ptr, LLVM.Ty.bitvec 8] := by
  rfl

example : DialectSignature.sig (LLVM.Op.getelementptr 8 64) = [LLVM.Ty.ptr, LLVM.Ty.bitvec 64] := by
  rfl

example :
    InstCombine.Op.denote (LLVM.Op.getelementptr 8 64)
      [(.value (10#64) : LLVM.IntWUB 64), (.value (5#64) : LLVM.IntWUB 64)]ₕ
      = (.immediateUB : LLVM.IntWUB 64) := by
  rfl

example :
    InstCombine.Op.denote (LLVM.Op.load 8)
      [(.value (0#64) : LLVM.IntWUB 64)]ₕ
      = (.immediateUB : LLVM.IntWUB 8) := by
  rfl

example :
    InstCombine.Op.denote (LLVM.Op.alloca 8) []ₕ
      = (.immediateUB : LLVM.IntWUB 64) := by
  rfl

example :
    (InstCombine.Op.denoteVec (LLVM.Op.store 8)
      [(.value (0#64) : LLVM.IntWUB 64), (.value (7#8) : LLVM.IntWUB 8)]ₕ).isNone = true := by
  native_decide

example :
    (InstCombine.Op.denoteVec (LLVM.Op.load 8)
      [(.value (0#64) : LLVM.IntWUB 64)]ₕ).isNone = true := by
  native_decide

example :
    (InstCombine.Op.denoteVec (LLVM.Op.alloca 8) []ₕ).isNone = true := by
  native_decide

end LeanMLIR.Tests
