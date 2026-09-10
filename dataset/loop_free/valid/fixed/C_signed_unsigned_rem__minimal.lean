import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def C_signed_unsigned_rem__minimal_src :=
  [llvm()| {
  llvm.func @C_signed_unsigned_rem__minimal_src(%x : i32, %d : i32) -> i32 {
  ^bb0(%x : i32, %d : i32):
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %p = llvm.icmp "sgt" %d, %c_i32_0 : i32
    llvm.assume %p : i1
    %nn = llvm.icmp "sge" %x, %c_i32_0 : i32
    llvm.assume %nn : i1
    %r = llvm.srem %x, %d : i32
    llvm.return %r : i32
  }
  }]

def C_signed_unsigned_rem__minimal_tgt :=
  [llvm()| {
  llvm.func @C_signed_unsigned_rem__minimal_tgt(%x : i32, %d : i32) -> i32 {
  ^bb0(%x : i32, %d : i32):
    %c_i32_0 = llvm.mlir.constant(0 : i32) : i32
    %p = llvm.icmp "sgt" %d, %c_i32_0 : i32
    llvm.assume %p : i1
    %nn = llvm.icmp "sge" %x, %c_i32_0 : i32
    llvm.assume %nn : i1
    %r = llvm.urem %x, %d : i32
    llvm.return %r : i32
  }
  }]
