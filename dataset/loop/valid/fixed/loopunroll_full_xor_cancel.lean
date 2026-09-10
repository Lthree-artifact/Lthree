import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def loopunroll_full_xor_cancel_src :=
  [llvm()| {
  llvm.func @loopunroll_full_xor_cancel_src(%m : i32, %x : i32) -> i32 {
  ^entry(%m : i32, %x : i32):
    %e_zero = llvm.mlir.constant 0 : i32
    llvm.br ^loop(%e_zero : i32, %x : i32)
  ^loop(%i : i32, %v : i32):
    %v1 = llvm.xor %v, %m : i32
    %l_one = llvm.mlir.constant 1 : i32
    %i1 = llvm.add %i, %l_one : i32
    %l_two = llvm.mlir.constant 2 : i32
    %cond = llvm.icmp "eq" %i1, %l_two : i32
    llvm.cond_br %cond : i1, ^out(%v1 : i32), ^loop(%i1 : i32, %v1 : i32)
  ^out(%res : i32):
    llvm.return %res : i32
  }
  }]

def loopunroll_full_xor_cancel_tgt :=
  [llvm()| {
  llvm.func @loopunroll_full_xor_cancel_tgt(%m : i32, %x : i32) -> i32 {
  ^entry(%m : i32, %x : i32):
    llvm.return %x : i32
  }
  }]

end TestLoop
end InstCombine
