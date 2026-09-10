import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr140526_smin_srem_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr140526_smin_srem_src(%x : _, %y : _, %z : _) -> _ {
  ^bb0(%x : _, %y : _, %z : _):
    %min_c = llvm.icmp "slt" %x, %y : _
    %min = llvm.select %min_c, %x, %y : _
    %res = llvm.srem %min, %z : _
    llvm.return %res : _
  }
  }]

def pr140526_smin_srem_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr140526_smin_srem_tgt(%x : _, %y : _, %z : _) -> _ {
  ^bb0(%x : _, %y : _, %z : _):
    %xz = llvm.srem %x, %z : _
    %yz = llvm.srem %y, %z : _
    %res_c = llvm.icmp "slt" %xz, %yz : _
    %res = llvm.select %res_c, %xz, %yz : _
    llvm.return %res : _
  }
  }]
