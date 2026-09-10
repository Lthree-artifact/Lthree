import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def A_mul_div__minimal_src :=
  [llvm()| {
  llvm.func @A_mul_div__minimal_src(%x : i32, %C : i32) -> i1 {
  ^bb0(%x : i32, %C : i32):
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %nz = llvm.icmp "ne" %C, %c_i32_0 : i32
    llvm.assume %nz : i1
    %c_i32_m1 = llvm.mlir.constant(-1 : i32) : i32
    %lim = llvm.udiv %c_i32_m1, %C : i32
    %ov = llvm.icmp "ugt" %x, %lim : i32
    llvm.return %ov : i1
  }
  }]

def A_mul_div__minimal_tgt :=
  [llvm()| {
  llvm.func @A_mul_div__minimal_tgt(%x : i32, %C : i32) -> i1 {
  ^bb0(%x : i32, %C : i32):
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %nz = llvm.icmp "ne" %C, %c_i32_0 : i32
    llvm.assume %nz : i1
    %ov_p = llvm.mul %x, %C : i32
    %ov_q = llvm.udiv %ov_p, %C : i32
    %ov = llvm.icmp "ne" %ov_q, %x : i32
    llvm.return %ov : i1
  }
  }]
