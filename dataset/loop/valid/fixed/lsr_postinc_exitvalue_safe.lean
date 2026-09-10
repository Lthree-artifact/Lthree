import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def lsr_postinc_exitvalue_safe_src :=
  [llvm()| {
  llvm.func @lsr_postinc_exitvalue_safe_src(%step : i32) -> i32 {
  ^entry(%step : i32):
    %e_zero = llvm.mlir.constant 0 : i32
    llvm.br ^loop(%e_zero : i32, %e_zero : i32)
  ^loop(%k : i32, %iv : i32):
    %iv_next = llvm.add %iv, %step : i32
    %l_one = llvm.mlir.constant 1 : i32
    %k1 = llvm.add %k, %l_one : i32
    %l_two = llvm.mlir.constant 1 : i32
    %cond = llvm.icmp "eq" %k1, %l_two : i32
    llvm.cond_br %cond : i1, ^out(%iv : i32), ^loop(%k1 : i32, %iv_next : i32)
  ^out(%res : i32):
    llvm.return %res : i32
  }
  }]

def lsr_postinc_exitvalue_safe_tgt :=
  [llvm()| {
  llvm.func @lsr_postinc_exitvalue_safe_tgt(%step : i32) -> i32 {
  ^entry(%step : i32):
    %r = llvm.mlir.constant 0 : i32
    llvm.return %r : i32
  }
  }]

end TestLoop
end InstCombine
