import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

def pow2_mul_shl_log2_src (w : Nat) (_h : 0 < w) :=
  [llvm(w)| {
  llvm.func @pow2_mul_shl_log2_src(%x : _, %C1 : _, %C2 : _, %C3 : _) -> i1 {
  ^bb0(%x : _, %C1 : _, %C2 : _, %C3 : _):
    %is_pow2_c1 = llvm.isPowerOf2 %C1 : _
    llvm.assume %is_pow2_c1 : i1
    %is_pow2_c2 = llvm.isPowerOf2 %C2 : _
    llvm.assume %is_pow2_c2 : i1
    %is_pow2_c3 = llvm.isPowerOf2 %C3 : _
    llvm.assume %is_pow2_c3 : i1
    %c3_mul_c1 = llvm.mul %C3, %C1 : _
    %c2_eq_c3_mul_c1 = llvm.icmp "eq" %C2, %c3_mul_c1 : _
    llvm.assume %c2_eq_c3_mul_c1 : i1
    %c3_shl_x = llvm.shl %C3, %x : _
    %masked = llvm.and %C2, %c3_shl_x : _
    %zero = llvm.mlir.constant(0 : _) : _
    %masked_ne_zero = llvm.icmp "ne" %masked, %zero : _
    llvm.assume %masked_ne_zero : i1
    %log2_c1 = llvm.cttz %C1, false : _
    %r = llvm.icmp "eq" %x, %log2_c1 : _
    llvm.return %r : i1
  }
  }]

def pow2_mul_shl_log2_tgt (w : Nat) (_h : 0 < w) :=
  [llvm(w)| {
  llvm.func @pow2_mul_shl_log2_tgt(%x : _, %C1 : _, %C2 : _, %C3 : _) -> i1 {
  ^bb0(%x : _, %C1 : _, %C2 : _, %C3 : _):
    %is_pow2_c1 = llvm.isPowerOf2 %C1 : _
    llvm.assume %is_pow2_c1 : i1
    %is_pow2_c2 = llvm.isPowerOf2 %C2 : _
    llvm.assume %is_pow2_c2 : i1
    %is_pow2_c3 = llvm.isPowerOf2 %C3 : _
    llvm.assume %is_pow2_c3 : i1
    %c3_mul_c1 = llvm.mul %C3, %C1 : _
    %c2_eq_c3_mul_c1 = llvm.icmp "eq" %C2, %c3_mul_c1 : _
    llvm.assume %c2_eq_c3_mul_c1 : i1
    %c3_shl_x = llvm.shl %C3, %x : _
    %masked = llvm.and %C2, %c3_shl_x : _
    %zero = llvm.mlir.constant(0 : _) : _
    %masked_ne_zero = llvm.icmp "ne" %masked, %zero : _
    llvm.assume %masked_ne_zero : i1
    %true = llvm.mlir.constant(true) : i1
    llvm.return %true : i1
  }
  }]
