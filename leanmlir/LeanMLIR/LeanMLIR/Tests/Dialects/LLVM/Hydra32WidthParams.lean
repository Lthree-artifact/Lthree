import LeanMLIR.Dialects.LLVM

namespace LeanMLIR.Tests

private def hydra32_57381_src_generic (w1 w2 : Nat) :=
  [llvm(w1, w2)| {
    ^bb0(%x : w1, %C1 : w2, %C2 : w1):
      %w = llvm.mlir.constant(w1 : w1) : w1
      %one = llvm.mlir.constant(1 : w1) : w1
      %w_minus_1 = llvm.sub %w, %one : w1
      %is_w_minus_1 = llvm.icmp "eq" %C2, %w_minus_1 : w1
      llvm.assume %is_w_minus_1 : i1
      %zero = llvm.mlir.constant(0 : w2) : w2
      %x_lshr = llvm.lshr %x, %C2 : w1
      %x_lshr_zext = llvm.zext %x_lshr : w1 to w2
      %neg_mask = llvm.sub %zero, %x_lshr_zext : w2
      %x_sext = llvm.sext %x : w1 to w2
      %sub = llvm.sub %C1, %x_sext : w2
      %result = llvm.and %neg_mask, %sub : w2
      llvm.return %result : w2
  }]

private def hydra32_57381_src_8_16 :=
  [llvm| {
    ^bb0(%x : i8, %C1 : i16, %C2 : i8):
      %w = llvm.mlir.constant(8 : i8) : i8
      %one = llvm.mlir.constant(1 : i8) : i8
      %w_minus_1 = llvm.sub %w, %one : i8
      %is_w_minus_1 = llvm.icmp "eq" %C2, %w_minus_1 : i8
      llvm.assume %is_w_minus_1 : i1
      %zero = llvm.mlir.constant(0 : i16) : i16
      %x_lshr = llvm.lshr %x, %C2 : i8
      %x_lshr_zext = llvm.zext %x_lshr : i8 to i16
      %neg_mask = llvm.sub %zero, %x_lshr_zext : i16
      %x_sext = llvm.sext %x : i8 to i16
      %sub = llvm.sub %C1, %x_sext : i16
      %result = llvm.and %neg_mask, %sub : i16
      llvm.return %result : i16
  }]

example : hydra32_57381_src_generic 8 16 = hydra32_57381_src_8_16 := by
  rfl

private def hydra32_57381_tgt_generic (w1 w2 : Nat) :=
  [llvm(w1, w2)| {
    ^bb0(%x : w1, %C1 : w2, %C2 : w1):
      %w = llvm.mlir.constant(w1 : w1) : w1
      %one = llvm.mlir.constant(1 : w1) : w1
      %w_minus_1 = llvm.sub %w, %one : w1
      %is_w_minus_1 = llvm.icmp "eq" %C2, %w_minus_1 : w1
      llvm.assume %is_w_minus_1 : i1
      %zero = llvm.mlir.constant(0 : w2) : w2
      %x_sext = llvm.sext %x : w1 to w2
      %sub = llvm.sub %C1, %x_sext : w2
      %C2_plus_1 = llvm.add %C2, %one : w1
      %threshold = llvm.shl %one, %C2_plus_1 : w1
      %cond = llvm.icmp "slt" %x, %threshold : w1
      %result = llvm.select %cond, %sub, %zero : w2
      llvm.return %result : w2
  }]

private def hydra32_57381_tgt_8_16 :=
  [llvm| {
    ^bb0(%x : i8, %C1 : i16, %C2 : i8):
      %w = llvm.mlir.constant(8 : i8) : i8
      %one = llvm.mlir.constant(1 : i8) : i8
      %w_minus_1 = llvm.sub %w, %one : i8
      %is_w_minus_1 = llvm.icmp "eq" %C2, %w_minus_1 : i8
      llvm.assume %is_w_minus_1 : i1
      %zero = llvm.mlir.constant(0 : i16) : i16
      %x_sext = llvm.sext %x : i8 to i16
      %sub = llvm.sub %C1, %x_sext : i16
      %C2_plus_1 = llvm.add %C2, %one : i8
      %threshold = llvm.shl %one, %C2_plus_1 : i8
      %cond = llvm.icmp "slt" %x, %threshold : i8
      %result = llvm.select %cond, %sub, %zero : i16
      llvm.return %result : i16
  }]

example : hydra32_57381_tgt_generic 8 16 = hydra32_57381_tgt_8_16 := by
  rfl

end LeanMLIR.Tests
