import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i187892_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i187892_src(%p : _, %q : _, %C1 : _) -> _ {
  ^bb0(%p : _, %q : _, %C1 : _):
    %m1 = llvm.mlir.constant(-1 : _) : _
    %not_p = llvm.xor %p, %C1 : _
    %imp = llvm.or %not_p, %q : _
    %cond = llvm.icmp "eq" %imp, %m1 : _
    llvm.assume %cond : i1
    %mask = llvm.xor %C1, %m1 : _
    %p_masked = llvm.xor %p, %mask : _
    %r = llvm.or %p_masked, %q : _
    llvm.return %r : _
  }
  }]

def i187892_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i187892_tgt(%p : _, %q : _, %C1 : _) -> _ {
  ^bb0(%p : _, %q : _, %C1 : _):
    %m1 = llvm.mlir.constant(-1 : _) : _
    %not_p = llvm.xor %p, %C1 : _
    %imp = llvm.or %not_p, %q : _
    %cond = llvm.icmp "eq" %imp, %m1 : _
    llvm.assume %cond : i1
    llvm.return %q : _
  }
  }]
