import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i139786_a2n_src :=
  [llvm()| {
  llvm.func @i139786_a2n_src(%arg0 : i8) -> i8 {
  ^bb0(%arg0 : i8):
    %c_8_1 = llvm.mlir.constant(1 : i8) : i8
    %v1_umax_cmp = llvm.icmp "ugt" %arg0, %c_8_1 : i8
    %1 = llvm.select %v1_umax_cmp, %arg0, %c_8_1 : i8
    %2 = llvm.shl %1, %c_8_1 overflow<nuw> : i8
    %c_8_16 = llvm.mlir.constant(16 : i8) : i8
    %v3_umax_cmp = llvm.icmp "ugt" %2, %c_8_16 : i8
    %3 = llvm.select %v3_umax_cmp, %2, %c_8_16 : i8
    %c_8_m1 = llvm.mlir.constant(-1 : i8) : i8
    %4 = llvm.icmp "sgt" %1, %c_8_m1 : i8
    %5 = llvm.select %4, %3, %c_8_m1 : i8
    llvm.return %3 : i8
  }
  }]

def i139786_a2n_tgt :=
  [llvm()| {
  llvm.func @i139786_a2n_tgt(%arg0 : i8) -> i8 {
  ^bb0(%arg0 : i8):
    %c_8_1 = llvm.mlir.constant(1 : i8) : i8
    %1 = llvm.shl %arg0, %c_8_1 overflow<nuw> : i8
    %c_8_16 = llvm.mlir.constant(16 : i8) : i8
    %v2_umax_cmp = llvm.icmp "ugt" %1, %c_8_16 : i8
    %2 = llvm.select %v2_umax_cmp, %1, %c_8_16 : i8
    %c_8_m1 = llvm.mlir.constant(-1 : i8) : i8
    %3 = llvm.icmp "sgt" %2, %c_8_m1 : i8
    %4 = llvm.select %3, %2, %c_8_m1 : i8
    llvm.return %2 : i8
  }
  }]
