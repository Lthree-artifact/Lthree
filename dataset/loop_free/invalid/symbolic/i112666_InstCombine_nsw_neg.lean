import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i112666_InstCombine_nsw_neg_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i112666_InstCombine_nsw_neg_src(%x : _, %y : _, %c : i1) -> _ {
  ^bb0(%x : _, %y : _, %c : i1):
    %c_i8_0 = llvm.mlir.constant(0 : _) : _
    %t0 = llvm.sub %c_i8_0, %x overflow<nsw> : _
    %t1 = llvm.select %c, %t0, %x : _
    %t2 = llvm.sub %y, %t1 : _
    llvm.return %t2 : _
  }
  }]

def i112666_InstCombine_nsw_neg_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i112666_InstCombine_nsw_neg_tgt(%x : _, %y : _, %c : i1) -> _ {
  ^bb0(%x : _, %y : _, %c : i1):
    %c_i8_0 = llvm.mlir.constant(0 : _) : _
    %t0 = llvm.sub %c_i8_0, %x overflow<nsw> : _
    %1 = llvm.select %c, %x, %t0 : _
    %t2 = llvm.add %1, %y : _
    llvm.return %t2 : _
  }
  }]
