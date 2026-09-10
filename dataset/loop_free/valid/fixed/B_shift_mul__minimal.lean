import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def B_shift_mul__minimal_src :=
  [llvm()| {
  llvm.func @B_shift_mul__minimal_src(%x : i32, %b : i1, %C1 : i32, %C2 : i32, %s : i32) -> i32 {
  ^bb0(%x : i32, %b : i1, %C1 : i32, %C2 : i32, %s : i32):
    %sel = llvm.select %b, %C1, %C2 : i32
    %sh = llvm.shl %x, %s : i32
    %r = llvm.mul %sh, %sel : i32
    llvm.return %r : i32
  }
  }]

def B_shift_mul__minimal_tgt :=
  [llvm()| {
  llvm.func @B_shift_mul__minimal_tgt(%x : i32, %b : i1, %C1 : i32, %C2 : i32, %s : i32) -> i32 {
  ^bb0(%x : i32, %b : i1, %C1 : i32, %C2 : i32, %s : i32):
    %a = llvm.shl %C1, %s : i32
    %c = llvm.shl %C2, %s : i32
    %sel = llvm.select %b, %a, %c : i32
    %r = llvm.mul %x, %sel : i32
    llvm.return %r : i32
  }
  }]
