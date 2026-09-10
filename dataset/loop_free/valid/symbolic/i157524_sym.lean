import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i157524_sym_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i157524_sym_src(%arg0 : _, %C : _, %newvar_v0 : _) -> _ {
  ^bb0(%arg0 : _, %C : _, %newvar_v0 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c_pos = llvm.icmp "sge" %C, %zero : _
    %v2 = llvm.add %arg0, %C overflow<nsw> : _
    %cond1 = llvm.icmp "sle" %newvar_v0, %arg0 : _
    %cond2 = llvm.icmp "sge" %newvar_v0, %v2 : _
    %cond = llvm.or %cond1, %cond2 : i1
    %pre = llvm.and %cond, %c_pos : i1
    llvm.assume %pre : i1
    %s1 = llvm.icmp "slt" %arg0, %newvar_v0 : _
    %v1 = llvm.select %s1, %arg0, %newvar_v0 : _
    %s2 = llvm.icmp "slt" %v2, %newvar_v0 : _
    %v3 = llvm.select %s2, %v2, %newvar_v0 : _
    %v4 = llvm.sub %v3, %v1 : _
    llvm.return %v4 : _
  }
  }]

def i157524_sym_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i157524_sym_tgt(%arg0 : _, %C : _, %newvar_v0 : _) -> _ {
  ^bb0(%arg0 : _, %C : _, %newvar_v0 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c_pos = llvm.icmp "sge" %C, %zero : _
    %v2 = llvm.add %arg0, %C : _
    %cond1 = llvm.icmp "sle" %newvar_v0, %arg0 : _
    %cond2 = llvm.icmp "sge" %newvar_v0, %v2 : _
    %cond = llvm.or %cond1, %cond2 : i1
    %pre = llvm.and %cond, %c_pos : i1
    llvm.assume %pre : i1
    %v1 = llvm.icmp "slt" %arg0, %newvar_v0 : _
    %v3 = llvm.select %v1, %C, %zero : _
    llvm.return %v3 : _
  }
  }]
