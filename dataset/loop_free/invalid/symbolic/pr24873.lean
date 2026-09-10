import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr24873_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr24873_src(%V : _) -> i1 {
  ^bb0(%V : _):
    %c_i64_m4611686018427387904 = llvm.mlir.constant(-4611686018427387904 : _) : _
    %ashr = llvm.ashr %c_i64_m4611686018427387904, %V : _
    %c_i64_m1 = llvm.mlir.constant(-1 : _) : _
    %icmp = llvm.icmp "eq" %ashr, %c_i64_m1 : _
    llvm.return %icmp : i1
  }
  }]

def pr24873_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr24873_tgt(%V : _) -> i1 {
  ^bb0(%V : _):
    %c_i64_62 = llvm.mlir.constant(62 : _) : _
    %icmp = llvm.icmp "eq" %V, %c_i64_62 : _
    llvm.return %icmp : i1
  }
  }]
