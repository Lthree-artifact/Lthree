import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i144020_a2n_src :=
  [llvm()| {
  llvm.func @i144020_a2n_src(%arg0 : i40) -> i40 {
  ^bb0(%arg0 : i40):
    %1 = llvm.trunc %arg0 : i40 to i8
    %c_8_2 = llvm.mlir.constant(2 : i8) : i8
    %2 = llvm.icmp "eq" %1, %c_8_2 : i8
    %c_40_m256 = llvm.mlir.constant(-256 : i40) : i40
    %3 = llvm.and %arg0, %c_40_m256 : i40
    %c_8_0 = llvm.mlir.constant(0 : i8) : i8
    %4 = llvm.select %2, %c_8_0, %1 : i8
    %c_40_0 = llvm.mlir.constant(0 : i40) : i40
    %5 = llvm.select %2, %c_40_0, %3 : i40
    %6 = llvm.zext %4 : i8 to i40
    %7 = llvm.or disjoint %5, %6 : i40
    llvm.return %7 : i40
  }
  }]

def i144020_a2n_tgt :=
  [llvm()| {
  llvm.func @i144020_a2n_tgt(%arg0 : i40) -> i40 {
  ^bb0(%arg0 : i40):
    %1 = llvm.trunc %arg0 : i40 to i8
    %c_8_2 = llvm.mlir.constant(2 : i8) : i8
    %2 = llvm.icmp "eq" %1, %c_8_2 : i8
    %c_40_0 = llvm.mlir.constant(0 : i40) : i40
    %3 = llvm.select %2, %c_40_0, %arg0 : i40
    llvm.return %3 : i40
  }
  }]
