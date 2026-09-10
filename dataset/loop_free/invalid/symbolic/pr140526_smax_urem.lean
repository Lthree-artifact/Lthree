import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr140526_smax_urem_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr140526_smax_urem_src(%x : _, %y : _, %z : _) -> _ {
  ^bb0(%x : _, %y : _, %z : _):
    %max_c = llvm.icmp "sgt" %x, %y : _
    %max = llvm.select %max_c, %x, %y : _
    %res = llvm.urem %max, %z : _
    llvm.return %res : _
  }
  }]

def pr140526_smax_urem_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr140526_smax_urem_tgt(%x : _, %y : _, %z : _) -> _ {
  ^bb0(%x : _, %y : _, %z : _):
    %xz = llvm.urem %x, %z : _
    %yz = llvm.urem %y, %z : _
    %res_c = llvm.icmp "sgt" %xz, %yz : _
    %res = llvm.select %res_c, %xz, %yz : _
    llvm.return %res : _
  }
  }]
