import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr39510_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr39510_src(%a : _) -> i1 {
  ^bb0(%a : _):
    %c_i32_0 = llvm.mlir.constant(0 : _) : _
    %cmp = llvm.icmp "slt" %a, %c_i32_0 : _
    %sub = llvm.sub %c_i32_0, %a overflow<nsw> : _
    %cond = llvm.select %cmp, %sub, %a : _
    %c_i32_2 = llvm.mlir.constant(2 : _) : _
    %r = llvm.icmp "ne" %cond, %c_i32_2 : _
    llvm.return %r : i1
  }
  }]

def pr39510_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr39510_tgt(%a : _) -> i1 {
  ^bb0(%a : _):
    %c_i1_1 = llvm.mlir.constant(1 : i1) : i1
    llvm.return %c_i1_1 : i1
  }
  }]
