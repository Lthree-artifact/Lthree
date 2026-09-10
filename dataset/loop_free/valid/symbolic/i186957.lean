import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i186957_src (w : Nat) (_h : 2 ≤ w) :=
  [llvm(w)| {
  llvm.func @i186957_src(%x : _, %y : _, %z : _) -> i1 {
  ^bb0(%x : _, %y : _, %z : _):
    %px = llvm.ctpop %x : _
    %py = llvm.ctpop %y : _
    %add1 = llvm.add %px, %py : _
    %add2 = llvm.add %add1, %z : _
    %res = llvm.trunc %add2 : _ to i1
    llvm.return %res : i1
  }
  }]

def i186957_tgt (w : Nat) (_h : 2 ≤ w) :=
  [llvm(w)| {
  llvm.func @i186957_tgt(%x : _, %y : _, %z : _) -> i1 {
  ^bb0(%x : _, %y : _, %z : _):
    %xor = llvm.xor %x, %y : _
    %pop = llvm.ctpop %xor : _
    %add = llvm.add %pop, %z : _
    %res = llvm.trunc %add : _ to i1
    llvm.return %res : i1
  }
  }]
