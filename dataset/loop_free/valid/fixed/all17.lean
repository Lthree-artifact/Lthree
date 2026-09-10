import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def all17_src :=
  [llvm()| {
  llvm.func @all17_src(%a : i32, %b : i32, %C_low : i32, %C_high : i32) -> i1 {
  ^bb0(%a : i32, %b : i32, %C_low : i32, %C_high : i32):
    %precond = llvm.icmp "slt" %C_low, %C_high : i32
    llvm.assume %precond : i1
    %v0 = llvm.icmp "sgt" %b, %C_high : i32
    %v1 = llvm.select %v0, %C_high, %b : i32
    %v2 = llvm.icmp "sgt" %v1, %C_low : i32
    %v3 = llvm.select %v2, %v1, %C_low : i32
    %v4 = llvm.icmp "sgt" %a, %C_high : i32
    %v5 = llvm.select %v4, %C_high, %a : i32
    %v6 = llvm.icmp "sgt" %v5, %C_low : i32
    %v7 = llvm.select %v6, %v5, %C_low : i32
    %v8 = llvm.icmp "eq" %v3, %C_high : i32
    %v9 = llvm.icmp "eq" %v7, %C_high : i32
    %v10 = llvm.and %v8, %v9 : i1
    llvm.return %v10 : i1
  }
  }]

def all17_tgt :=
  [llvm()| {
  llvm.func @all17_tgt(%a : i32, %b : i32, %C_low : i32, %C_high : i32) -> i1 {
  ^bb0(%a : i32, %b : i32, %C_low : i32, %C_high : i32):
    %precond = llvm.icmp "slt" %C_low, %C_high : i32
    llvm.assume %precond : i1
    %cmp_a = llvm.icmp "sge" %a, %C_high : i32
    %cmp_b = llvm.icmp "sge" %b, %C_high : i32
    %result = llvm.and %cmp_a, %cmp_b : i1
    llvm.return %result : i1
  }
  }]
