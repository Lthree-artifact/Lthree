import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i191169_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i191169_src(%C1 : _, %C2 : _, %C3 : _, %X : _, %Y : _) -> _ {
  ^bb0(%C1 : _, %C2 : _, %C3 : _, %X : _, %Y : _):
    %xor_c = llvm.xor %C1, %C2 : _
    %cmp = llvm.icmp "eq" %C3, %xor_c : _
    llvm.assume %cmp : i1
    %or = llvm.or disjoint %X, %C1 : _
    %xor1 = llvm.xor %Y, %or : _
    %res = llvm.xor %xor1, %C2 : _
    llvm.return %res : _
  }
  }]

def i191169_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i191169_tgt(%C1 : _, %C2 : _, %C3 : _, %X : _, %Y : _) -> _ {
  ^bb0(%C1 : _, %C2 : _, %C3 : _, %X : _, %Y : _):
    %xor_c = llvm.xor %C1, %C2 : _
    %cmp = llvm.icmp "eq" %C3, %xor_c : _
    llvm.assume %cmp : i1
    %xor1 = llvm.xor %X, %Y : _
    %res = llvm.xor %xor1, %C3 : _
    llvm.return %res : _
  }
  }]
