import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def B_shift_mul__corpus3_src :=
  [llvm()| {
  llvm.func @B_shift_mul__corpus3_src(%v0 : i32, %v1 : i32) -> i32 {
  ^bb0(%v0 : i32, %v1 : i32):
    %c_i32_1 = llvm.mlir.constant(1 : i32) : i32
    %v2 = llvm.shl %v0, %c_i32_1 overflow<nsw> : i32
    %v3 = llvm.mul %v1, %v2 overflow<nsw> : i32
    %v4 = llvm.or %c_i32_1, %v3 : i32
    %v5 = llvm.icmp "slt" %v4, %c_i32_1 : i32
    %v6 = llvm.select %v5, %v1, %c_i32_1 : i32
    %v7 = llvm.mul %v0, %v6 overflow<nsw> : i32
    llvm.return %v7 : i32
  }
  }]

def B_shift_mul__corpus3_tgt :=
  [llvm()| {
  llvm.func @B_shift_mul__corpus3_tgt(%v0 : i32, %v1 : i32) -> i32 {
  ^bb0(%v0 : i32, %v1 : i32):
    %v2 = llvm.mul %v0, %v1 overflow<nsw> : i32
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %v3 = llvm.icmp "slt" %v2, %c_i32_0 : i32
    %v5 = llvm.select %v3, %v2, %v0 : i32
    llvm.return %v5 : i32
  }
  }]
