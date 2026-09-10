import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def scevexpander_udiv_speculated_straight_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @scevexpander_udiv_speculated_straight_src(%d : _, %g : _) -> _ {
  ^entry(%d : _, %g : _):
    %e_zero = llvm.mlir.constant 0 : _
    %e_guard = llvm.icmp "ne" %g, %e_zero : _
    llvm.cond_br %e_guard : i1, ^out(%e_zero : _), ^loop(%e_zero : _, %e_zero : _)
  ^loop(%k : _, %acc : _):
    %l_one = llvm.mlir.constant 1 : _
    %rem = llvm.udiv %l_one, %d : _
    %acc_next = llvm.add %acc, %rem : _
    %k1 = llvm.add %k, %l_one : _
    %l_two = llvm.mlir.constant 2 : _
    %cond = llvm.icmp "eq" %k1, %l_two : _
    llvm.cond_br %cond : i1, ^out(%acc_next : _), ^loop(%k1 : _, %acc_next : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

def scevexpander_udiv_speculated_straight_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @scevexpander_udiv_speculated_straight_tgt(%d : _, %g : _) -> _ {
  ^entry(%d : _, %g : _):
    %l_one = llvm.mlir.constant 1 : _
    %rem = llvm.udiv %l_one, %d : _
    %r = llvm.add %rem, %rem : _
    llvm.return %r : _
  }
  }]

end TestLoop
end InstCombine
