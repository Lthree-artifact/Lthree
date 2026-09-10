import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def lsr_postinc_normalize_poison_straight_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @lsr_postinc_normalize_poison_straight_src(%step : _) -> _ {
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

def lsr_postinc_normalize_poison_straight_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @lsr_postinc_normalize_poison_straight_tgt(%step : _) -> _ {
  ^entry(%step : _):
    %l_zero = llvm.mlir.constant 0 : _
    %neg = llvm.sub %l_zero, %step : _
    %r = llvm.add %neg, %step : _
    llvm.return %r : _
  }
  }]

end TestLoop
end InstCombine
