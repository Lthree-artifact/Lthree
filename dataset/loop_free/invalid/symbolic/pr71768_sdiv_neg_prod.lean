import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def pr71768_sdiv_neg_prod_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr71768_sdiv_neg_prod_src(%a : _, %b : _) -> _ {
  ^bb0(%a : _, %b : _):
    %mul = llvm.mul %a, %b : _
    %c_i64_0 = llvm.mlir.constant(0 : _) : _
    %neg = llvm.sub %c_i64_0, %mul : _
    %div = llvm.sdiv %neg, %mul : _
    llvm.return %div : _
  }
  }]

def pr71768_sdiv_neg_prod_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @pr71768_sdiv_neg_prod_tgt(%a : _, %b : _) -> _ {
  ^bb0(%a : _, %b : _):
    %c_i64_m1 = llvm.mlir.constant(-1 : _) : _
    llvm.return %c_i64_m1 : _
  }
  }]
