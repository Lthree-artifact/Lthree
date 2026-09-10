import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i115458_InstCombine_mul_sext_X_Y_se_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i115458_InstCombine_mul_sext_X_Y_se_src(%a : _, %b : i1, %x : _) -> _ {
  ^bb0(%a : _, %b : i1, %x : _):
    %v1 = llvm.sext %b : i1 to _
    %v2 = llvm.mul %a, %v1 overflow<nsw> : _
    %v3 = llvm.select %b, %v2, %a : _
    %v4 = llvm.sub %v1, %v3 : _
    %f = llvm.mul %x, %v1 overflow<nuw> : _
    %r = llvm.add %f, %v4 : _
    llvm.return %r : _
  }
  }]

def i115458_InstCombine_mul_sext_X_Y_se_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i115458_InstCombine_mul_sext_X_Y_se_tgt(%a : _, %b : i1, %x : _) -> _ {
  ^bb0(%a : _, %b : i1, %x : _):
    %c_i8_0 = llvm.mlir.constant(0 : _) : _
    %v1 = llvm.sub %c_i8_0, %a overflow<nsw> : _
    %c_i8_255 = llvm.mlir.constant(255 : _) : _
    %v2 = llvm.xor %x, %c_i8_255 : _
    %v3 = llvm.add %a, %v2 : _
    %r = llvm.select %b, %v3, %v1 : _
    llvm.return %r : _
  }
  }]
