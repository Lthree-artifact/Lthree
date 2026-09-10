import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i167003_sym_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167003_sym_src(%C : _, %arg1 : _, %newvar_v1 : _) -> _ {
  ^bb0(%C : _, %arg1 : _, %newvar_v1 : _):
    %v0 = llvm.sub %C, %arg1 overflow<nsw> : _
    %v2 = llvm.sub %newvar_v1, %arg1 overflow<nsw> : _
    %c3 = llvm.icmp "slt" %v0, %v2 : _
    %v3 = llvm.select %c3, %v0, %v2 : _
    %v4 = llvm.add %v3, %arg1 : _
    llvm.return %v4 : _
  }
  }]

def i167003_sym_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167003_sym_tgt(%C : _, %arg1 : _, %newvar_v1 : _) -> _ {
  ^bb0(%C : _, %arg1 : _, %newvar_v1 : _):
    %c3 = llvm.icmp "slt" %newvar_v1, %C : _
    %v3 = llvm.select %c3, %newvar_v1, %C : _
    llvm.return %v3 : _
  }
  }]
