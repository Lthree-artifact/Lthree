import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i199806_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i199806_src(%x : _, %c : _, %max : _) -> _ {
  ^bb0(%x : _, %c : _, %max : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c_ge_0 = llvm.icmp "sge" %c, %zero : _
    llvm.assume %c_ge_0 : i1
    %max_ge_0 = llvm.icmp "sge" %max, %zero : _
    llvm.assume %max_ge_0 : i1
    %ugt = llvm.icmp "ugt" %x, %c : _
    %u = llvm.select %ugt, %x, %c : _
    %sum = llvm.add %u, %x overflow<nsw> : _
    %ov = llvm.icmp "ult" %sum, %x : _
    %ult = llvm.icmp "ult" %sum, %max : _
    %clamp = llvm.select %ult, %sum, %max : _
    %r = llvm.select %ov, %max, %clamp : _
    llvm.return %r : _
  }
  }]

def i199806_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i199806_tgt(%x : _, %c : _, %max : _) -> _ {
  ^bb0(%x : _, %c : _, %max : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c_ge_0 = llvm.icmp "sge" %c, %zero : _
    llvm.assume %c_ge_0 : i1
    %max_ge_0 = llvm.icmp "sge" %max, %zero : _
    llvm.assume %max_ge_0 : i1
    %ugt = llvm.icmp "ugt" %x, %c : _
    %u = llvm.select %ugt, %x, %c : _
    %sum = llvm.add %u, %x : _
    %ult = llvm.icmp "ult" %sum, %max : _
    %clamp = llvm.select %ult, %sum, %max : _
    llvm.return %clamp : _
  }
  }]
