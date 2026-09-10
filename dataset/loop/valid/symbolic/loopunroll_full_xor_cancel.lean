import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def loopunroll_full_xor_cancel_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @loopunroll_full_xor_cancel_src(%m : _, %x : _) -> _ {
  ^entry(%m : _, %x : _):
    %e_zero = llvm.mlir.constant 0 : _
    llvm.br ^loop(%e_zero : _, %x : _)
  ^loop(%i : _, %v : _):
    %v1 = llvm.xor %v, %m : _
    %l_one = llvm.mlir.constant 1 : _
    %i1 = llvm.add %i, %l_one : _
    %l_two = llvm.mlir.constant 2 : _
    %cond = llvm.icmp "eq" %i1, %l_two : _
    llvm.cond_br %cond : i1, ^out(%v1 : _), ^loop(%i1 : _, %v1 : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

def loopunroll_full_xor_cancel_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @loopunroll_full_xor_cancel_tgt(%m : _, %x : _) -> _ {
  ^entry(%m : _, %x : _):
    llvm.return %x : _
  }
  }]

end TestLoop
end InstCombine
