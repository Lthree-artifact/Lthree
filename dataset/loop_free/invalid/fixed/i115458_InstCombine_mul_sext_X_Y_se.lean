import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i115458_InstCombine_mul_sext_X_Y_se_src :=
  [llvm()| {
  llvm.func @i115458_InstCombine_mul_sext_X_Y_se_src(%a : i8, %b : i1, %x : i8) -> i8 {
  ^bb0(%a : i8, %b : i1, %x : i8):
    %v1 = llvm.sext %b : i1 to i8
    %v2 = llvm.mul %a, %v1 overflow<nsw> : i8
    %v3 = llvm.select %b, %v2, %a : i8
    %v4 = llvm.sub %v1, %v3 : i8
    %f = llvm.mul %x, %v1 overflow<nuw> : i8
    %r = llvm.add %f, %v4 : i8
    llvm.return %r : i8
  }
  }]

def i115458_InstCombine_mul_sext_X_Y_se_tgt :=
  [llvm()| {
  llvm.func @i115458_InstCombine_mul_sext_X_Y_se_tgt(%a : i8, %b : i1, %x : i8) -> i8 {
  ^bb0(%a : i8, %b : i1, %x : i8):
    %c_i8_0 = llvm.mlir.constant(0 : i8) : i8
    %v1 = llvm.sub %c_i8_0, %a overflow<nsw> : i8
    %c_i8_255 = llvm.mlir.constant(255 : i8) : i8
    %v2 = llvm.xor %x, %c_i8_255 : i8
    %v3 = llvm.add %a, %v2 : i8
    %r = llvm.select %b, %v3, %v1 : i8
    llvm.return %r : i8
  }
  }]
