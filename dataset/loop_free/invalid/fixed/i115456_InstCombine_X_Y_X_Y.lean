import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i115456_InstCombine_X_Y_X_Y_src :=
  [llvm()| {
  llvm.func @i115456_InstCombine_X_Y_X_Y_src(%b : i32, %z : i32) -> i32 {
  ^bb0(%b : i32, %z : i32):
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %c = llvm.sub %c_i32_0, %z : i32
    %v1 = llvm.sdiv %z, %c : i32
    %d = llvm.mul %v1, %b overflow<nsw> : i32
    %e = llvm.mul %c, %d : i32
    llvm.return %e : i32
  }
  }]

def i115456_InstCombine_X_Y_X_Y_tgt :=
  [llvm()| {
  llvm.func @i115456_InstCombine_X_Y_X_Y_tgt(%b : i32, %z : i32) -> i32 {
  ^bb0(%b : i32, %z : i32):
    %c_i32_2147483648 = llvm.mlir.constant(2147483648 : i32) : i32
    %v1 = llvm.icmp "eq" %z, %c_i32_2147483648 : i32
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %v2 = llvm.sub %c_i32_0, %b overflow<nsw> : i32
    %v3 = llvm.select %v1, %v2, %b : i32
    %_neg = llvm.mul %v3, %z : i32
    llvm.return %_neg : i32
  }
  }]
