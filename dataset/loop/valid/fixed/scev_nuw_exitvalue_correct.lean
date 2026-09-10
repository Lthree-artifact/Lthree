import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def scev_nuw_exitvalue_correct_src :=
  [llvm()| {
  llvm.func @scev_nuw_exitvalue_correct_src(%unused : i32) -> i32 {
  ^entry(%unused : i32):
    %e_index = llvm.mlir.constant 0 : i32
    %e_vec = llvm.mlir.constant -8 : i32
    llvm.br ^loop(%e_index : i32, %e_vec : i32)
  ^loop(%index : i32, %vec : i32):
    %l_four = llvm.mlir.constant 4 : i32
    %index_next = llvm.add %index, %l_four : i32
    %vec_next = llvm.add %vec, %l_four overflow<nuw> : i32
    %l_twelve = llvm.mlir.constant 12 : i32
    %cmp = llvm.icmp "eq" %index_next, %l_twelve : i32
    %l_zero = llvm.mlir.constant 0 : i32
    llvm.cond_br %cmp : i1, ^out(%l_zero : i32), ^loop(%index_next : i32, %vec_next : i32)
  ^out(%res : i32):
    llvm.return %res : i32
  }
  }]

def scev_nuw_exitvalue_correct_tgt :=
  [llvm()| {
  llvm.func @scev_nuw_exitvalue_correct_tgt(%unused : i32) -> i32 {
  ^entry(%unused : i32):
    %r = llvm.mlir.constant 0 : i32
    llvm.return %r : i32
  }
  }]

end TestLoop
end InstCombine
