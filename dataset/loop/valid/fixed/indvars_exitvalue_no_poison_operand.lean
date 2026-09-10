import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def indvars_exitvalue_no_poison_operand_src :=
  [llvm()| {
  llvm.func @indvars_exitvalue_no_poison_operand_src(%x : i32, %n : i32) -> i32 {
  ^entry(%x : i32, %n : i32):
    %e_zero = llvm.mlir.constant 0 : i32
    llvm.br ^loop(%e_zero : i32, %e_zero : i32)
  ^loop(%acc : i32, %i : i32):
    %l_one = llvm.mlir.constant 1 : i32
    %acc_next = llvm.add %acc, %l_one : i32
    %i_next = llvm.add %i, %l_one : i32
    %cond = llvm.icmp "eq" %i, %n : i32
    llvm.cond_br %cond : i1, ^out(%acc : i32), ^loop(%acc_next : i32, %i_next : i32)
  ^out(%res : i32):
    llvm.return %res : i32
  }
  }]

def indvars_exitvalue_no_poison_operand_tgt :=
  [llvm()| {
  llvm.func @indvars_exitvalue_no_poison_operand_tgt(%x : i32, %n : i32) -> i32 {
  ^entry(%x : i32, %n : i32):
    llvm.return %n : i32
  }
  }]

end TestLoop
end InstCombine
