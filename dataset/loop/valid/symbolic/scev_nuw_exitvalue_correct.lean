import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

def scev_nuw_exitvalue_correct_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @scev_nuw_exitvalue_correct_src(%unused : _) -> _ {
  ^entry(%unused : _):
    %e_index = llvm.mlir.constant 0 : _
    %e_vec = llvm.mlir.constant -8 : _
    llvm.br ^loop(%e_index : _, %e_vec : _)
  ^loop(%index : _, %vec : _):
    %l_four = llvm.mlir.constant 4 : _
    %index_next = llvm.add %index, %l_four : _
    %vec_next = llvm.add %vec, %l_four overflow<nuw> : _
    %l_twelve = llvm.mlir.constant 12 : _
    %cmp = llvm.icmp "eq" %index_next, %l_twelve : _
    %l_zero = llvm.mlir.constant 0 : _
    llvm.cond_br %cmp : i1, ^out(%l_zero : _), ^loop(%index_next : _, %vec_next : _)
  ^out(%res : _):
    llvm.return %res : _
  }
  }]

def scev_nuw_exitvalue_correct_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @scev_nuw_exitvalue_correct_tgt(%unused : _) -> _ {
  ^entry(%unused : _):
    %r = llvm.mlir.constant 0 : _
    llvm.return %r : _
  }
  }]

end TestLoop
end InstCombine
