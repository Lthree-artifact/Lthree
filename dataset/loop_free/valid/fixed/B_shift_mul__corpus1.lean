import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def B_shift_mul__corpus1_src :=
  [llvm()| {
  llvm.func @B_shift_mul__corpus1_src(%v0 : i32, %v1 : i1, %C1 : i32, %C2 : i32, %C3 : i32) -> i32 {
  ^bb0(%v0 : i32, %v1 : i1, %C1 : i32, %C2 : i32, %C3 : i32):
    %v3 = llvm.select %v1, %C1, %C2 : i32
    %v4 = llvm.shl %v0, %C3 : i32
    %v5 = llvm.mul %v4, %v3 : i32
    llvm.return %v5 : i32
  }
  }]

def B_shift_mul__corpus1_tgt :=
  [llvm()| {
  llvm.func @B_shift_mul__corpus1_tgt(%v0 : i32, %v1 : i1, %C1 : i32, %C2 : i32, %C3 : i32) -> i32 {
  ^bb0(%v0 : i32, %v1 : i1, %C1 : i32, %C2 : i32, %C3 : i32):
    %v3 = llvm.shl %C1, %C3 : i32
    %v4 = llvm.shl %C2, %C3 : i32
    %v5 = llvm.select %v1, %v3, %v4 : i32
    %v6 = llvm.mul %v0, %v5 : i32
    llvm.return %v6 : i32
  }
  }]
