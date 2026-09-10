import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr39510_src :=
  [llvm()| {
  llvm.func @pr39510_src(%a : i32) -> i1 {
  ^bb0(%a : i32):
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %cmp = llvm.icmp "slt" %a, %c_i32_0 : i32
    %sub = llvm.sub %c_i32_0, %a overflow<nsw> : i32
    %cond = llvm.select %cmp, %sub, %a : i32
    %c_i32_2 = llvm.mlir.constant(2 : i32) : i32
    %r = llvm.icmp "ne" %cond, %c_i32_2 : i32
    llvm.return %r : i1
  }
  }]

def pr39510_tgt :=
  [llvm()| {
  llvm.func @pr39510_tgt(%a : i32) -> i1 {
  ^bb0(%a : i32):
    %c_i1_1 = llvm.mlir.constant(1 : i1) : i1
    llvm.return %c_i1_1 : i1
  }
  }]
