import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i154246_src :=
  [llvm()| {
  llvm.func @i154246_src(%arg0 : i8, %arg1 : i8) -> i8 {
  ^bb0(%arg0 : i8, %arg1 : i8):
    %c_8_m1 = llvm.mlir.constant(-1 : i8) : i8
    %v0 = llvm.icmp "eq" %arg1, %c_8_m1 : i8
    %c_8_4 = llvm.mlir.constant(4 : i8) : i8
    %v1 = llvm.or %arg0, %c_8_4 : i8
    %v2 = llvm.select %v0, %v1, %arg0 : i8
    %c_8_1 = llvm.mlir.constant(1 : i8) : i8
    %v3 = llvm.or %v2, %c_8_1 : i8
    llvm.return %v3 : i8
  }
  }]

def i154246_tgt :=
  [llvm()| {
  llvm.func @i154246_tgt(%arg0 : i8, %arg1 : i8) -> i8 {
  ^bb0(%arg0 : i8, %arg1 : i8):
    %c_8_m1 = llvm.mlir.constant(-1 : i8) : i8
    %v0 = llvm.icmp "eq" %arg1, %c_8_m1 : i8
    %c_8_5 = llvm.mlir.constant(5 : i8) : i8
    %c_8_1 = llvm.mlir.constant(1 : i8) : i8
    %v1 = llvm.select %v0, %c_8_5, %c_8_1 : i8
    %v2 = llvm.or %arg0, %v1 : i8
    llvm.return %v2 : i8
  }
  }]
