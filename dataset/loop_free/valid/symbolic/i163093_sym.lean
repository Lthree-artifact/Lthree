import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i163093_sym_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i163093_sym_src(%arg0 : _, %arg1 : _, %arg2 : _, %C : _) -> i1 {
  ^bb0(%arg0 : _, %arg1 : _, %arg2 : _, %C : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %v4 = llvm.sub %arg2, %arg1 : _
    %v5 = llvm.icmp "slt" %arg2, %C : _
    %v6 = llvm.select %v5, %C, %v4 : _
    %v7 = llvm.sub %arg1, %arg0 : _
    %v8 = llvm.add %v7, %v6 : _
    %v9 = llvm.icmp "eq" %v8, %zero : _
    llvm.return %v9 : i1
  }
  }]

def i163093_sym_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i163093_sym_tgt(%arg0 : _, %arg1 : _, %arg2 : _, %C : _) -> i1 {
  ^bb0(%arg0 : _, %arg1 : _, %arg2 : _, %C : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %v4 = llvm.icmp "slt" %arg2, %C : _
    %v5sub = llvm.add %arg1, %C : _
    %v5 = llvm.select %v4, %v5sub, %arg2 : _
    %v6 = llvm.sub %v5, %arg0 : _
    %v7 = llvm.icmp "eq" %v6, %zero : _
    llvm.return %v7 : i1
  }
  }]
