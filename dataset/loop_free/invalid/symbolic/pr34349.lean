import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr34349_src (w1 w2 : Nat) (_h : w1 < w2) (_h1 : 0 < w1) :=
  [llvm(w1, w2)| {
  llvm.func @pr34349_src(%p : w1) -> w1 {
  ^bb0(%p : w1):
    %v3 = llvm.zext %p : w1 to w2
    %c_i16_71 = llvm.mlir.constant(71 : w2) : w2
    %v4 = llvm.mul %v3, %c_i16_71 : w2
    %c_i16_8 = llvm.mlir.constant(8 : w2) : w2
    %v5 = llvm.lshr %v4, %c_i16_8 : w2
    %v6 = llvm.trunc %v5 : w2 to w1
    %v7 = llvm.sub %p, %v6 : w1
    %c_i8_1 = llvm.mlir.constant(1 : w1) : w1
    %v8 = llvm.lshr %v7, %c_i8_1 : w1
    %v9 = llvm.zext %p : w1 to w2
    %v10 = llvm.mul %v9, %c_i16_71 : w2
    %v11 = llvm.lshr %v10, %c_i16_8 : w2
    %v12 = llvm.trunc %v11 : w2 to w1
    %v13 = llvm.add %v12, %v8 : w1
    %c_i8_7 = llvm.mlir.constant(7 : w1) : w1
    %v14 = llvm.lshr %v13, %c_i8_7 : w1
    llvm.return %v14 : w1
  }
  }]

def pr34349_tgt (w1 w2 : Nat) (_h : w1 < w2) (_h1 : 0 < w1) :=
  [llvm(w1, w2)| {
  llvm.func @pr34349_tgt(%p : w1) -> w1 {
  ^bb0(%p : w1):
    %c_i8_0 = llvm.mlir.constant(0 : w1) : w1
    llvm.return %c_i8_0 : w1
  }
  }]
