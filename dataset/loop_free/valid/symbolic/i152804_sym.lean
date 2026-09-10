import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i152804_sym_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i152804_sym_src(%V : _, %C1 : _, %C2 : _, %C3 : _) -> _ {
  ^bb0(%V : _, %C1 : _, %C2 : _, %C3 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %negone = llvm.mlir.constant(-1 : _) : _
    %and_V = llvm.and %V, %C1 : _
    %cmp_V = llvm.icmp "eq" %and_V, %V : _
    llvm.assume %cmp_V : i1
    %Y = llvm.sub %zero, %C1 : _
    %Y_not_zero = llvm.icmp "ne" %Y, %zero : _
    %Y_minus_1 = llvm.add %Y, %negone : _
    %and_Y = llvm.and %Y, %Y_minus_1 : _
    %Y_is_power2 = llvm.icmp "eq" %and_Y, %zero : _
    %cond1 = llvm.and %Y_not_zero, %Y_is_power2 : i1
    %cond2_1 = llvm.icmp "sle" %C1, %C2 : _
    %cond2_2 = llvm.icmp "slt" %C2, %zero : _
    %cond2 = llvm.and %cond2_1, %cond2_2 : i1
    %cond3 = llvm.icmp "eq" %C3, %Y : _
    %cond12 = llvm.and %cond1, %cond2 : i1
    %cond = llvm.and %cond12, %cond3 : i1
    llvm.assume %cond : i1
    %v1 = llvm.add %V, %C2 : _
    %v2 = llvm.and %v1, %C1 : _
    %v3 = llvm.add %v2, %C3 : _
    llvm.return %v3 : _
  }
  }]

def i152804_sym_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i152804_sym_tgt(%V : _, %C1 : _, %C2 : _, %C3 : _) -> _ {
  ^bb0(%V : _, %C1 : _, %C2 : _, %C3 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %negone = llvm.mlir.constant(-1 : _) : _
    %and_V = llvm.and %V, %C1 : _
    %cmp_V = llvm.icmp "eq" %and_V, %V : _
    llvm.assume %cmp_V : i1
    %Y = llvm.sub %zero, %C1 : _
    %Y_not_zero = llvm.icmp "ne" %Y, %zero : _
    %Y_minus_1 = llvm.add %Y, %negone : _
    %and_Y = llvm.and %Y, %Y_minus_1 : _
    %Y_is_power2 = llvm.icmp "eq" %and_Y, %zero : _
    %cond1 = llvm.and %Y_not_zero, %Y_is_power2 : i1
    %cond2_1 = llvm.icmp "sle" %C1, %C2 : _
    %cond2_2 = llvm.icmp "slt" %C2, %zero : _
    %cond2 = llvm.and %cond2_1, %cond2_2 : i1
    %cond3 = llvm.icmp "eq" %C3, %Y : _
    %cond12 = llvm.and %cond1, %cond2 : i1
    %cond = llvm.and %cond12, %cond3 : i1
    llvm.assume %cond : i1
    llvm.return %V : _
  }
  }]
