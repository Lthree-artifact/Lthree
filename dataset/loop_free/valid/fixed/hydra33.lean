import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def hydra33_src :=
  [llvm()| {
  llvm.func @hydra33_src(%x : i32, %C : i32, %C1 : i32, %C2 : i32) -> i32 {
  ^bb0(%x : i32, %C : i32, %C1 : i32, %C2 : i32):
    %zero = llvm.mlir.constant(0 : i32) : i32
    %uint_max = llvm.mlir.constant(4294967295 : i32) : i32
    %C_not_zero = llvm.icmp "ne" %C, %zero : i32
    llvm.assume %C_not_zero : i1
    %overflow_limit = llvm.udiv %uint_max, %C : i32
    %ov = llvm.icmp "ugt" %x, %overflow_limit : i32
    %mul = llvm.mul %x, %C : i32
    %cmp = llvm.icmp "ugt" %mul, %C1 : i32
    %or = llvm.or %ov, %cmp : i1
    %sel = llvm.select %or, %C2, %mul : i32
    llvm.return %sel : i32
  }
  }]

def hydra33_tgt :=
  [llvm()| {
  llvm.func @hydra33_tgt(%x : i32, %C : i32, %C1 : i32, %C2 : i32) -> i32 {
  ^bb0(%x : i32, %C : i32, %C1 : i32, %C2 : i32):
    %zero = llvm.mlir.constant(0 : i32) : i32
    %C_not_zero = llvm.icmp "ne" %C, %zero : i32
    llvm.assume %C_not_zero : i1
    %limit = llvm.udiv %C1, %C : i32
    %is_bigger = llvm.icmp "ugt" %x, %limit : i32
    %product = llvm.mul %x, %C : i32
    %r = llvm.select %is_bigger, %C2, %product : i32
    llvm.return %r : i32
  }
  }]
