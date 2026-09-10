import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def indvars_exitvalue_poison_propagated_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @indvars_exitvalue_poison_propagated_src(%x : _, %n : _) -> _ {
  ^entry(%x : _, %n : _):
    %e_zero = llvm.mlir.constant 0 : _
    llvm.br ^loop(%e_zero : _, %e_zero : _)
  ^loop(%acc : _, %i : _):
    %acc_next = llvm.add %acc, %x : _
    %l_one = llvm.mlir.constant 1 : _
    %i_next = llvm.add %i, %l_one : _
    %cond = llvm.icmp "eq" %i, %n : _
    llvm.cond_br %cond : i1, ^out(%acc : _), ^loop(%acc_next : _, %i_next : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

def indvars_exitvalue_poison_propagated_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @indvars_exitvalue_poison_propagated_tgt(%x : _, %n : _) -> _ {
  ^entry(%x : _, %n : _):
    %prod = llvm.mul %x, %n : _
    llvm.return %prod : _
  }
  }]

end TestLoop
end InstCombine
