import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i85066_shl_nsw_cttz_to_mul_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i85066_shl_nsw_cttz_to_mul_src(%x : _, %y : _) -> _ {
  ^bb0(%x : _, %y : _):
    %cttz = llvm.cttz %y, false : _
    %res = llvm.shl %x, %cttz overflow<nsw> : _
    llvm.return %res : _
  }
  }]

def i85066_shl_nsw_cttz_to_mul_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i85066_shl_nsw_cttz_to_mul_tgt(%x : _, %y : _) -> _ {
  ^bb0(%x : _, %y : _):
    %c_i64_0 = llvm.mlir.constant(0 : _) : _
    %0 = llvm.sub %c_i64_0, %y : _
    %1 = llvm.and %y, %0 : _
    %2 = llvm.mul %1, %x overflow<nsw> : _
    llvm.return %2 : _
  }
  }]
