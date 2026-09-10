import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr34349_src :=
  [llvm()| {
  llvm.func @pr34349_src(%p : i8) -> i8 {
  ^bb0(%p : i8):
    %v3 = llvm.zext %p : i8 to i16
    %c_i16_71 = llvm.mlir.constant(71 : i16) : i16
    %v4 = llvm.mul %v3, %c_i16_71 : i16
    %c_i16_8 = llvm.mlir.constant(8 : i16) : i16
    %v5 = llvm.lshr %v4, %c_i16_8 : i16
    %v6 = llvm.trunc %v5 : i16 to i8
    %v7 = llvm.sub %p, %v6 : i8
    %c_i8_1 = llvm.mlir.constant(1 : i8) : i8
    %v8 = llvm.lshr %v7, %c_i8_1 : i8
    %v9 = llvm.zext %p : i8 to i16
    %v10 = llvm.mul %v9, %c_i16_71 : i16
    %v11 = llvm.lshr %v10, %c_i16_8 : i16
    %v12 = llvm.trunc %v11 : i16 to i8
    %v13 = llvm.add %v12, %v8 : i8
    %c_i8_7 = llvm.mlir.constant(7 : i8) : i8
    %v14 = llvm.lshr %v13, %c_i8_7 : i8
    llvm.return %v14 : i8
  }
  }]

def pr34349_tgt :=
  [llvm()| {
  llvm.func @pr34349_tgt(%p : i8) -> i8 {
  ^bb0(%p : i8):
    %c_i8_0 = llvm.mlir.constant(0 : i8) : i8
    llvm.return %c_i8_0 : i8
  }
  }]
