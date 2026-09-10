import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def lsr_postinc_exitvalue_safe_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @lsr_postinc_exitvalue_safe_src(%step : _) -> _ {
  ^entry(%step : _):
    %e_zero = llvm.mlir.constant 0 : _
    llvm.br ^loop(%e_zero : _, %e_zero : _)
  ^loop(%k : _, %iv : _):
    %iv_next = llvm.add %iv, %step : _
    %l_one = llvm.mlir.constant 1 : _
    %k1 = llvm.add %k, %l_one : _
    %l_two = llvm.mlir.constant 1 : _
    %cond = llvm.icmp "eq" %k1, %l_two : _
    llvm.cond_br %cond : i1, ^out(%iv : _), ^loop(%k1 : _, %iv_next : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

def lsr_postinc_exitvalue_safe_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @lsr_postinc_exitvalue_safe_tgt(%step : _) -> _ {
  ^entry(%step : _):
    %r = llvm.mlir.constant 0 : _
    llvm.return %r : _
  }
  }]

end TestLoop
end InstCombine
