import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i167199_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167199_src(%C1 : _, %C2 : _, %newvar_v0 : _, %v1 : _) -> i1 {
  ^bb0(%C1 : _, %C2 : _, %newvar_v0 : _, %v1 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %v2 = llvm.shl %C1, %v1 : _
    %v4 = llvm.and %newvar_v0, %v2 : _
    %v5 = llvm.shl %C2, %v1 : _
    %v7 = llvm.and %newvar_v0, %v5 : _
    %v8 = llvm.icmp "ne" %v4, %zero : _
    %v9 = llvm.icmp "ne" %v7, %zero : _
    %v10 = llvm.or %v8, %v9 : i1
    llvm.return %v10 : i1
  }
  }]

def i167199_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167199_tgt(%C1 : _, %C2 : _, %newvar_v0 : _, %v1 : _) -> i1 {
  ^bb0(%C1 : _, %C2 : _, %newvar_v0 : _, %v1 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %C3 = llvm.or %C1, %C2 : _
    %x1 = llvm.shl %C3, %v1 : _
    %x2 = llvm.and %newvar_v0, %x1 : _
    %v8 = llvm.icmp "ne" %x2, %zero : _
    llvm.return %v8 : i1
  }
  }]
