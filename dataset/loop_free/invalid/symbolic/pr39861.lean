import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr39861_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr39861_src(%x : _, %y : _) -> i1 {
  ^bb0(%x : _, %y : _):
    %c_i8_255 = llvm.mlir.constant(255 : _) : _
    %tmp0 = llvm.lshr %c_i8_255, %y : _
    %tmp1 = llvm.and %tmp0, %x : _
    %ret = llvm.icmp "sge" %tmp1, %x : _
    llvm.return %ret : i1
  }
  }]

def pr39861_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr39861_tgt(%x : _, %y : _) -> i1 {
  ^bb0(%x : _, %y : _):
    %c_i8_255 = llvm.mlir.constant(255 : _) : _
    %tmp0 = llvm.lshr %c_i8_255, %y : _
    %1 = llvm.icmp "sge" %tmp0, %x : _
    llvm.return %1 : i1
  }
  }]
