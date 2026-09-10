import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr140526_smin_sdiv_src :=
  [llvm()| {
  llvm.func @pr140526_smin_sdiv_src(%x : i64, %y : i64, %z : i64) -> i64 {
  ^bb0(%x : i64, %y : i64, %z : i64):
    %min_c = llvm.icmp "slt" %x, %y : i64
    %min = llvm.select %min_c, %x, %y : i64
    %res = llvm.sdiv %min, %z : i64
    llvm.return %res : i64
  }
  }]

def pr140526_smin_sdiv_tgt :=
  [llvm()| {
  llvm.func @pr140526_smin_sdiv_tgt(%x : i64, %y : i64, %z : i64) -> i64 {
  ^bb0(%x : i64, %y : i64, %z : i64):
    %xz = llvm.sdiv %x, %z : i64
    %yz = llvm.sdiv %y, %z : i64
    %res_c = llvm.icmp "slt" %xz, %yz : i64
    %res = llvm.select %res_c, %xz, %yz : i64
    llvm.return %res : i64
  }
  }]
