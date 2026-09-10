import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i85066_shl_nsw_cttz_to_mul_src :=
  [llvm()| {
  llvm.func @i85066_shl_nsw_cttz_to_mul_src(%x : i64, %y : i64) -> i64 {
  ^bb0(%x : i64, %y : i64):
    %cttz = llvm.cttz %y, false : i64
    %res = llvm.shl %x, %cttz overflow<nsw> : i64
    llvm.return %res : i64
  }
  }]

def i85066_shl_nsw_cttz_to_mul_tgt :=
  [llvm()| {
  llvm.func @i85066_shl_nsw_cttz_to_mul_tgt(%x : i64, %y : i64) -> i64 {
  ^bb0(%x : i64, %y : i64):
    %c_i64_0 = llvm.mlir.constant(0 : i64) : i64
    %0 = llvm.sub %c_i64_0, %y : i64
    %1 = llvm.and %y, %0 : i64
    %2 = llvm.mul %1, %x overflow<nsw> : i64
    llvm.return %2 : i64
  }
  }]
