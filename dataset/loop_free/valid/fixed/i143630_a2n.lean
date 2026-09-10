import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i143630_a2n_src :=
  [llvm()| {
  llvm.func @i143630_a2n_src(%arg0 : i32, %arg1 : i32) -> i1 {
  ^bb0(%arg0 : i32, %arg1 : i32):
    %c_32_31 = llvm.mlir.constant(31 : i32) : i32
    %1 = llvm.ashr %arg0, %c_32_31 : i32
    %c_32_1 = llvm.mlir.constant(1 : i32) : i32
    %2 = llvm.lshr %1, %c_32_1 : i32
    %3 = llvm.xor %2, %arg0 : i32
    %4 = llvm.ashr %arg1, %c_32_31 : i32
    %5 = llvm.lshr %4, %c_32_1 : i32
    %6 = llvm.xor %5, %arg1 : i32
    %7 = llvm.icmp "eq" %3, %6 : i32
    llvm.return %7 : i1
  }
  }]

def i143630_a2n_tgt :=
  [llvm()| {
  llvm.func @i143630_a2n_tgt(%arg0 : i32, %arg1 : i32) -> i1 {
  ^bb0(%arg0 : i32, %arg1 : i32):
    %1 = llvm.icmp "eq" %arg0, %arg1 : i32
    llvm.return %1 : i1
  }
  }]
