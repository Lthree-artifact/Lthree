import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def E_ovf_vs_div__corpus1_src :=
  [llvm()| {
  llvm.func @E_ovf_vs_div__corpus1_src(%v0 : i32, %C1 : i32, %C2 : i32) -> i1 {
  ^bb0(%v0 : i32, %C1 : i32, %C2 : i32):
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %nz = llvm.icmp "ne" %C1, %c_i32_0 : i32
    llvm.assume %nz : i1
    %v3 = llvm.mul %v0, %C1 : i32
    %v4_p = llvm.mul %v0, %C1 : i32
    %v4_q = llvm.udiv %v4_p, %C1 : i32
    %v4 = llvm.icmp "ne" %v4_q, %v0 : i32
    %v5 = llvm.icmp "ugt" %v3, %C2 : i32
    %v6 = llvm.or %v4, %v5 : i1
    llvm.return %v6 : i1
  }
  }]

def E_ovf_vs_div__corpus1_tgt :=
  [llvm()| {
  llvm.func @E_ovf_vs_div__corpus1_tgt(%v0 : i32, %C1 : i32, %C2 : i32) -> i1 {
  ^bb0(%v0 : i32, %C1 : i32, %C2 : i32):
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %nz = llvm.icmp "ne" %C1, %c_i32_0 : i32
    llvm.assume %nz : i1
    %c3 = llvm.udiv %C2, %C1 : i32
    %r = llvm.icmp "ugt" %v0, %c3 : i32
    llvm.return %r : i1
  }
  }]
