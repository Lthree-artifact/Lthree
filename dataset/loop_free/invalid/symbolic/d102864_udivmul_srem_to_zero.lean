import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def d102864_udivmul_srem_to_zero_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @d102864_udivmul_srem_to_zero_src(%a : _, %y : _) -> _ {
  ^bb0(%a : _, %y : _):
    %x = llvm.udiv %a, %y : _
    %mul = llvm.mul %x, %y : _
    %mod = llvm.srem %mul, %y : _
    llvm.return %mod : _
  }
  }]

def d102864_udivmul_srem_to_zero_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @d102864_udivmul_srem_to_zero_tgt(%a : _, %y : _) -> _ {
  ^bb0(%a : _, %y : _):
    %c_i64_0 = llvm.mlir.constant(0 : _) : _
    llvm.return %c_i64_0 : _
  }
  }]
