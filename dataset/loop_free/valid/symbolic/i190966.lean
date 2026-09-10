import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i190966_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i190966_src(%x0 : _, %x1 : _, %C1 : _) -> i1 {
  ^bb0(%x0 : _, %x1 : _, %C1 : _):
    %a = llvm.add %x0, %C1 : _
    %b = llvm.sub %a, %x1 : _
    %r = llvm.icmp "eq" %b, %C1 : _
    llvm.return %r : i1
  }
  }]

def i190966_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i190966_tgt(%x0 : _, %x1 : _, %C1 : _) -> i1 {
  ^bb0(%x0 : _, %x1 : _, %C1 : _):
    %r = llvm.icmp "eq" %x0, %x1 : _
    llvm.return %r : i1
  }
  }]
