import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i143636_a2n_src :=
  [llvm()| {
  llvm.func @i143636_a2n_src(%arg0 : i32) -> i1 {
  ^bb0(%arg0 : i32):
    %c_32_1 = llvm.mlir.constant(1 : i32) : i32
    %1 = llvm.add %arg0, %c_32_1 : i32
    %c_32_4 = llvm.mlir.constant(4 : i32) : i32
    %2 = llvm.lshr %1, %c_32_4 : i32
    %c_32_15 = llvm.mlir.constant(15 : i32) : i32
    %3 = llvm.and %1, %c_32_15 : i32
    %c_32_0 = llvm.mlir.constant(0 : i32) : i32
    %4 = llvm.icmp "ne" %3, %c_32_0 : i32
    %5 = llvm.zext %4 : i1 to i32
    %6 = llvm.add %2, %5 overflow<nsw,nuw> : i32
    %7 = llvm.icmp "eq" %6, %c_32_0 : i32
    llvm.return %7 : i1
  }
  }]

def i143636_a2n_tgt :=
  [llvm()| {
  llvm.func @i143636_a2n_tgt(%arg0 : i32) -> i1 {
  ^bb0(%arg0 : i32):
    %c_32_m1 = llvm.mlir.constant(-1 : i32) : i32
    %5 = llvm.icmp "eq" %arg0, %c_32_m1 : i32
    llvm.return %5 : i1
  }
  }]
