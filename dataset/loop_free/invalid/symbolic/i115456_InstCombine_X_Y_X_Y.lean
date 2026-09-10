import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i115456_InstCombine_X_Y_X_Y_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i115456_InstCombine_X_Y_X_Y_src(%b : _, %z : _) -> _ {
  ^bb0(%b : _, %z : _):
    %c_i32_0 = llvm.mlir.constant(0 : _) : _
    %c = llvm.sub %c_i32_0, %z : _
    %v1 = llvm.sdiv %z, %c : _
    %d = llvm.mul %v1, %b overflow<nsw> : _
    %e = llvm.mul %c, %d : _
    llvm.return %e : _
  }
  }]

def i115456_InstCombine_X_Y_X_Y_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i115456_InstCombine_X_Y_X_Y_tgt(%b : _, %z : _) -> _ {
  ^bb0(%b : _, %z : _):
    %c_i32_2147483648 = llvm.mlir.constant(2147483648 : _) : _
    %v1 = llvm.icmp "eq" %z, %c_i32_2147483648 : _
    %c_i32_0 = llvm.mlir.constant(0 : _) : _
    %v2 = llvm.sub %c_i32_0, %b overflow<nsw> : _
    %v3 = llvm.select %v1, %v2, %b : _
    %_neg = llvm.mul %v3, %z : _
    llvm.return %_neg : _
  }
  }]
