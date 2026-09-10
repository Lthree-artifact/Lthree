import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def D_chained_rem__corpus1_src :=
  [llvm()| {
  llvm.func @D_chained_rem__corpus1_src(%x : i32, %C1 : i32, %C2 : i32) -> i32 {
  ^bb0(%x : i32, %C1 : i32, %C2 : i32):
    %rem = llvm.urem %C1, %C2 : i32
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %cond = llvm.icmp "eq" %rem, %c_i32_0 : i32
    llvm.assume %cond : i1
    %v1 = llvm.urem %x, %C1 : i32
    %v2 = llvm.urem %v1, %C2 : i32
    llvm.return %v2 : i32
  }
  }]

def D_chained_rem__corpus1_tgt :=
  [llvm()| {
  llvm.func @D_chained_rem__corpus1_tgt(%x : i32, %C1 : i32, %C2 : i32) -> i32 {
  ^bb0(%x : i32, %C1 : i32, %C2 : i32):
    %rem = llvm.urem %C1, %C2 : i32
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %cond = llvm.icmp "eq" %rem, %c_i32_0 : i32
    llvm.assume %cond : i1
    %v2 = llvm.urem %x, %C2 : i32
    llvm.return %v2 : i32
  }
  }]
