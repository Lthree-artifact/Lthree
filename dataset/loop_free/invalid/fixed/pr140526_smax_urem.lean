import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr140526_smax_urem_src :=
  [llvm()| {
  llvm.func @pr140526_smax_urem_src(%x : i64, %y : i64, %z : i64) -> i64 {
  ^bb0(%x : i64, %y : i64, %z : i64):
    %max_c = llvm.icmp "sgt" %x, %y : i64
    %max = llvm.select %max_c, %x, %y : i64
    %res = llvm.urem %max, %z : i64
    llvm.return %res : i64
  }
  }]

def pr140526_smax_urem_tgt :=
  [llvm()| {
  llvm.func @pr140526_smax_urem_tgt(%x : i64, %y : i64, %z : i64) -> i64 {
  ^bb0(%x : i64, %y : i64, %z : i64):
    %xz = llvm.urem %x, %z : i64
    %yz = llvm.urem %y, %z : i64
    %res_c = llvm.icmp "sgt" %xz, %yz : i64
    %res = llvm.select %res_c, %xz, %yz : i64
    llvm.return %res : i64
  }
  }]
