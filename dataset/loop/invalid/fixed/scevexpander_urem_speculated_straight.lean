import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def scevexpander_urem_speculated_straight_src :=
  [llvm()| {
  llvm.func @scevexpander_urem_speculated_straight_src(%d : i32, %g : i32) -> i32 {
  ^entry(%d : i32, %g : i32):
    %e_zero = llvm.mlir.constant 0 : i32
    %e_guard = llvm.icmp "ne" %g, %e_zero : i32
    llvm.cond_br %e_guard : i1, ^out(%e_zero : i32), ^loop(%e_zero : i32, %e_zero : i32)
  ^loop(%k : i32, %acc : i32):
    %l_one = llvm.mlir.constant 1 : i32
    %rem = llvm.urem %l_one, %d : i32
    %acc_next = llvm.add %acc, %rem : i32
    %k1 = llvm.add %k, %l_one : i32
    %l_two = llvm.mlir.constant 2 : i32
    %cond = llvm.icmp "eq" %k1, %l_two : i32
    llvm.cond_br %cond : i1, ^out(%acc_next : i32), ^loop(%k1 : i32, %acc_next : i32)
  ^out(%res : i32):
    llvm.return %res : i32
  }
  }]

def scevexpander_urem_speculated_straight_tgt :=
  [llvm()| {
  llvm.func @scevexpander_urem_speculated_straight_tgt(%d : i32, %g : i32) -> i32 {
  ^entry(%d : i32, %g : i32):
    %l_one = llvm.mlir.constant 1 : i32
    %rem = llvm.urem %l_one, %d : i32
    %r = llvm.add %rem, %rem : i32
    llvm.return %r : i32
  }
  }]

end TestLoop
end InstCombine
