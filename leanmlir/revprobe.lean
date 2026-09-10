import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

namespace InstCombine
namespace TestLoop

set_option maxHeartbeats 0

def revloop_src :=
  [llvm(8)| {
  llvm.func @revloop_src(%a : i8) -> i8 {
  ^entry(%a : i8):
    %zc = llvm.mlir.constant 0 : i8
    llvm.br ^exit(%zc : i8)
  ^exit(%r : i8):
    llvm.return %r : i8
  }
  }]

def revloop_tgt :=
  [llvm(8)| {
  llvm.func @revloop_tgt(%a : i8) -> i8 {
  ^entry(%a : i8):
    %zero0 = llvm.mlir.constant 0 : i8
    llvm.br ^loop(%a : i8)
  ^loop(%i : i8):
    %zero = llvm.mlir.constant 0 : i8
    %nd = llvm.icmp "ne" %i, %zero : i8
    %one = llvm.mlir.constant 1 : i8
    %inx = llvm.sub %i, %one : i8
    llvm.cond_br %nd : i1, ^loop(%inx : i8), ^exit(%i : i8)
  ^exit(%r : i8):
    llvm.return %r : i8
  }
  }]

-- input valuation: a = 5  (needs ~5 loop trips)
def Vin : InstCombine.InputValuation (Ctxt.ofList [LLVM.Ty.bitvec 8]) :=
  fun _ _ => LLVM.SemVal.value (5 : BitVec _)

-- at fuel = 3 the src (2 block jumps) finishes, the tgt (needs 5 trips) does not
#eval (LLVMMemory.Com.denoteWithMemoryFuel 3 revloop_src
        (V := InstCombine.InputValuation.lift Vin) default).isSome
#eval (LLVMMemory.Com.denoteWithMemoryFuel 3 revloop_tgt
        (V := InstCombine.InputValuation.lift Vin) default).isSome
#eval (LLVMMemory.Com.denoteWithMemoryFuel 20 revloop_tgt
        (V := InstCombine.InputValuation.lift Vin) default).isSome

end TestLoop
end InstCombine

namespace InstCombine
namespace TestLoop
open InstCombine

theorem revloop_not_refined : ¬ (revloop_src ⊑ revloop_tgt) := by
  intro h
  have hh := h Vin default 3
  have ht : (LLVMMemory.Com.denoteWithMemoryFuel 3 revloop_tgt Vin.lift default).isSome = false := by
    decide +kernel
  have hs : (LLVMMemory.Com.denoteWithMemoryFuel 3 revloop_src Vin.lift default).isSome = true := by
    decide +kernel
  cases hh <;> simp_all

end TestLoop
end InstCombine

#print axioms InstCombine.TestLoop.revloop_not_refined
set_option pp.all false in
#check @InstCombine.TestLoop.revloop_not_refined
