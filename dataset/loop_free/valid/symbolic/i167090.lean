import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i167090_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167090_src(%i16arg0 : _, %C1 : _, %C2 : _, %C3 : _) -> _ {
  ^bb0(%i16arg0 : _, %C1 : _, %C2 : _, %C3 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c12 = llvm.add %C1, %C2 : _
    %cond_nuw1 = llvm.icmp "uge" %c12, %C1 : _
    %cond_c2_pos = llvm.icmp "sge" %C2, %zero : _
    %cond_c12_c1 = llvm.icmp "sge" %c12, %C1 : _
    %cond_nsw1 = llvm.icmp "eq" %cond_c2_pos, %cond_c12_c1 : i1
    %a1 = llvm.and %cond_nuw1, %cond_nsw1 : i1
    %c123 = llvm.add %c12, %C3 : _
    %cond_nuw2 = llvm.icmp "uge" %c123, %c12 : _
    %cond_c3_pos = llvm.icmp "sge" %C3, %zero : _
    %cond_c123_c12 = llvm.icmp "sge" %c123, %c12 : _
    %cond_nsw2 = llvm.icmp "eq" %cond_c3_pos, %cond_c123_c12 : i1
    %a2 = llvm.and %cond_nuw2, %cond_nsw2 : i1
    %a3 = llvm.and %a1, %a2 : i1
    llvm.assume %a3 : i1
    %umin0 = llvm.icmp "ult" %i16arg0, %C1 : _
    %v0 = llvm.select %umin0, %i16arg0, %C1 : _
    %v1 = llvm.add %v0, %C2 : _
    %umin1 = llvm.icmp "ult" %i16arg0, %v1 : _
    %v2 = llvm.select %umin1, %i16arg0, %v1 : _
    %v3 = llvm.add %v2, %C3 : _
    %umin2 = llvm.icmp "ult" %i16arg0, %v3 : _
    %v4 = llvm.select %umin2, %i16arg0, %v3 : _
    llvm.return %v4 : _
  }
  }]

def i167090_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i167090_tgt(%i16arg0 : _, %C1 : _, %C2 : _, %C3 : _) -> _ {
  ^bb0(%i16arg0 : _, %C1 : _, %C2 : _, %C3 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %c12 = llvm.add %C1, %C2 : _
    %cond_nuw1 = llvm.icmp "uge" %c12, %C1 : _
    %cond_c2_pos = llvm.icmp "sge" %C2, %zero : _
    %cond_c12_c1 = llvm.icmp "sge" %c12, %C1 : _
    %cond_nsw1 = llvm.icmp "eq" %cond_c2_pos, %cond_c12_c1 : i1
    %a1 = llvm.and %cond_nuw1, %cond_nsw1 : i1
    %c123 = llvm.add %c12, %C3 : _
    %cond_nuw2 = llvm.icmp "uge" %c123, %c12 : _
    %cond_c3_pos = llvm.icmp "sge" %C3, %zero : _
    %cond_c123_c12 = llvm.icmp "sge" %c123, %c12 : _
    %cond_nsw2 = llvm.icmp "eq" %cond_c3_pos, %cond_c123_c12 : i1
    %a2 = llvm.and %cond_nuw2, %cond_nsw2 : i1
    %a3 = llvm.and %a1, %a2 : i1
    llvm.assume %a3 : i1
    %c12_tgt = llvm.add %C1, %C2 : _
    %c123_tgt = llvm.add %c12_tgt, %C3 : _
    %umin0 = llvm.icmp "ult" %i16arg0, %c123_tgt : _
    %v0 = llvm.select %umin0, %i16arg0, %c123_tgt : _
    llvm.return %v0 : _
  }
  }]
