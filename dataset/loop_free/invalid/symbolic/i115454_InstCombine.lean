import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i115454_InstCombine_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i115454_InstCombine_src(%x : _, %y : _) -> _ {
  ^bb0(%x : _, %y : _):
    %a = llvm.sub %x, %y overflow<nsw> : _
    %b = llvm.sub %y, %x overflow<nsw,nuw> : _
    %c_i32_4294967295 = llvm.mlir.constant(4294967295 : _) : _
    %cmp = llvm.icmp "sgt" %x, %c_i32_4294967295 : _
    %cond = llvm.select %cmp, %a, %b : _
    %c_i32_0 = llvm.mlir.constant(0 : _) : _
    %sub16 = llvm.sub %c_i32_0, %cond overflow<nsw> : _
    llvm.return %sub16 : _
  }
  }]

def i115454_InstCombine_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i115454_InstCombine_tgt(%x : _, %y : _) -> _ {
  ^bb0(%x : _, %y : _):
    %a = llvm.sub %x, %y overflow<nsw> : _
    %b = llvm.sub %y, %x overflow<nsw,nuw> : _
    %c_i32_0 = llvm.mlir.constant(0 : _) : _
    %cmp1 = llvm.icmp "slt" %x, %c_i32_0 : _
    %v1 = llvm.select %cmp1, %a, %b : _
    llvm.return %v1 : _
  }
  }]
