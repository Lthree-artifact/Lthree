import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i115454_InstCombine_src :=
  [llvm()| {
  llvm.func @i115454_InstCombine_src(%x : i32, %y : i32) -> i32 {
  ^bb0(%x : i32, %y : i32):
    %a = llvm.sub %x, %y overflow<nsw> : i32
    %b = llvm.sub %y, %x overflow<nsw,nuw> : i32
    %c_i32_4294967295 = llvm.mlir.constant(4294967295 : i32) : i32
    %cmp = llvm.icmp "sgt" %x, %c_i32_4294967295 : i32
    %cond = llvm.select %cmp, %a, %b : i32
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %sub16 = llvm.sub %c_i32_0, %cond overflow<nsw> : i32
    llvm.return %sub16 : i32
  }
  }]

def i115454_InstCombine_tgt :=
  [llvm()| {
  llvm.func @i115454_InstCombine_tgt(%x : i32, %y : i32) -> i32 {
  ^bb0(%x : i32, %y : i32):
    %a = llvm.sub %x, %y overflow<nsw> : i32
    %b = llvm.sub %y, %x overflow<nsw,nuw> : i32
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %cmp1 = llvm.icmp "slt" %x, %c_i32_0 : i32
    %v1 = llvm.select %cmp1, %a, %b : i32
    llvm.return %v1 : i32
  }
  }]
