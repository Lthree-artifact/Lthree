import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i201328_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i201328_src(%x : _, %C1 : _, %C2 : _) -> _ {
  ^bb0(%x : _, %C1 : _, %C2 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %m1 = llvm.mlir.constant(-1 : _) : _
    %c2_not_zero = llvm.icmp "ne" %C2, %zero : _
    %c2_minus_1 = llvm.add %C2, %m1 : _
    %c2_and = llvm.and %C2, %c2_minus_1 : _
    %c2_is_pow2 = llvm.icmp "eq" %c2_and, %zero : _
    %c1_eq = llvm.icmp "eq" %C1, %c2_minus_1 : _
    %cond1 = llvm.and %c2_not_zero, %c2_is_pow2 : i1
    %cond = llvm.and %cond1, %c1_eq : i1
    llvm.assume %cond : i1
    %rem = llvm.and %x, %C1 : _
    %is_zero = llvm.icmp "eq" %rem, %zero : _
    %sel = llvm.select %is_zero, %C2, %rem : _
    %res = llvm.sub %x, %sel : _
    llvm.return %res : _
  }
  }]

def i201328_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i201328_tgt(%x : _, %C1 : _, %C2 : _) -> _ {
  ^bb0(%x : _, %C1 : _, %C2 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %m1 = llvm.mlir.constant(-1 : _) : _
    %c2_not_zero = llvm.icmp "ne" %C2, %zero : _
    %c2_minus_1 = llvm.add %C2, %m1 : _
    %c2_and = llvm.and %C2, %c2_minus_1 : _
    %c2_is_pow2 = llvm.icmp "eq" %c2_and, %zero : _
    %c1_eq = llvm.icmp "eq" %C1, %c2_minus_1 : _
    %cond1 = llvm.and %c2_not_zero, %c2_is_pow2 : i1
    %cond = llvm.and %cond1, %c1_eq : i1
    llvm.assume %cond : i1
    %dec = llvm.add %x, %m1 : _
    %neg_C2 = llvm.sub %zero, %C2 : _
    %res = llvm.and %dec, %neg_C2 : _
    llvm.return %res : _
  }
  }]
