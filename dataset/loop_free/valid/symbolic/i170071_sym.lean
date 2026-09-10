import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i170071_sym_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i170071_sym_src(%C2 : _, %V : _, %v0 : _) -> _ {
  ^bb0(%C2 : _, %V : _, %v0 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c2 = llvm.icmp "sge" %C2, %zero : _
    llvm.assume %c2 : i1
    %xor = llvm.xor %V, %v0 : _
    %same_sign = llvm.icmp "sge" %xor, %zero : _
    llvm.assume %same_sign : i1
    %v2 = llvm.add %V, %v0 overflow<nsw> : _
    %v3 = llvm.icmp "ult" %v2, %v0 : _
    %umin_c = llvm.icmp "ult" %v2, %C2 : _
    %v4 = llvm.select %umin_c, %v2, %C2 : _
    %v5 = llvm.select %v3, %C2, %v4 : _
    llvm.return %v5 : _
  }
  }]

def i170071_sym_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i170071_sym_tgt(%C2 : _, %V : _, %v0 : _) -> _ {
  ^bb0(%C2 : _, %V : _, %v0 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c2 = llvm.icmp "sge" %C2, %zero : _
    llvm.assume %c2 : i1
    %xor = llvm.xor %V, %v0 : _
    %same_sign = llvm.icmp "sge" %xor, %zero : _
    llvm.assume %same_sign : i1
    %v2 = llvm.add %V, %v0 : _
    %umin_c = llvm.icmp "ult" %v2, %C2 : _
    %v4 = llvm.select %umin_c, %v2, %C2 : _
    llvm.return %v4 : _
  }
  }]
