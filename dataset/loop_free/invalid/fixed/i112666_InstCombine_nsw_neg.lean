import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i112666_InstCombine_nsw_neg_src :=
  [llvm()| {
  llvm.func @i112666_InstCombine_nsw_neg_src(%x : i8, %y : i8, %c : i1) -> i8 {
  ^bb0(%x : i8, %y : i8, %c : i1):
    %c_i8_0 = llvm.mlir.constant(0 : i8) : i8
    %t0 = llvm.sub %c_i8_0, %x overflow<nsw> : i8
    %t1 = llvm.select %c, %t0, %x : i8
    %t2 = llvm.sub %y, %t1 : i8
    llvm.return %t2 : i8
  }
  }]

def i112666_InstCombine_nsw_neg_tgt :=
  [llvm()| {
  llvm.func @i112666_InstCombine_nsw_neg_tgt(%x : i8, %y : i8, %c : i1) -> i8 {
  ^bb0(%x : i8, %y : i8, %c : i1):
    %c_i8_0 = llvm.mlir.constant(0 : i8) : i8
    %t0 = llvm.sub %c_i8_0, %x overflow<nsw> : i8
    %1 = llvm.select %c, %x, %t0 : i8
    %t2 = llvm.add %1, %y : i8
    llvm.return %t2 : i8
  }
  }]
