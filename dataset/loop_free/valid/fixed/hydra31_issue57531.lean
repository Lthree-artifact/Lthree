import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def hydra31_issue57531_src :=
  [llvm()| {
  llvm.func @hydra31_issue57531_src(%v0 : i32, %C1 : i32) -> i32 {
  ^bb0(%v0 : i32, %C1 : i32):
    %v0_f = llvm.freeze %v0 : i32
    %C1_f = llvm.freeze %C1 : i32
    %v1 = llvm.sub %C1_f, %v0_f : i32
    %v2 = llvm.or %v0_f, %v1 : i32
    %v3 = llvm.add %v0_f, %v2 : i32
    llvm.return %v3 : i32
  }
  }]

def hydra31_issue57531_tgt :=
  [llvm()| {
  llvm.func @hydra31_issue57531_tgt(%v0 : i32, %C1 : i32) -> i32 {
  ^bb0(%v0 : i32, %C1 : i32):
    %v0_f = llvm.freeze %v0 : i32
    %C1_f = llvm.freeze %C1 : i32
    %v1 = llvm.sub %C1_f, %v0_f : i32
    %v2 = llvm.and %v0_f, %v1 : i32
    %v3 = llvm.add %v0_f, %C1_f : i32
    %v4 = llvm.sub %v3, %v2 : i32
    llvm.return %v4 : i32
  }
  }]
