import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def F_wide_symbolic__minimal_src :=
  [llvm()| {
  llvm.func @F_wide_symbolic__minimal_src(%a0 : i32, %a1 : i32, %C0 : i32, %C1 : i32, %C2 : i32, %Ca : i32, %Cu : i32) -> i1 {
  ^bb0(%a0 : i32, %a1 : i32, %C0 : i32, %C1 : i32, %C2 : i32, %Ca : i32, %Cu : i32):
    %p1 = llvm.icmp "sle" %C1, %C2 : i32
    llvm.assume %p1 : i1
    %d = llvm.sub %C0, %C1 : i32
    %p2 = llvm.icmp "eq" %Ca, %d : i32
    llvm.assume %p2 : i1
    %ds = llvm.sub %C2, %C1 : i32
    %c_i32_m1 = llvm.mlir.constant(-1 : i32) : i32
    %p3 = llvm.icmp "ne" %ds, %c_i32_m1 : i32
    llvm.assume %p3 : i1
    %c_i32_1 = llvm.mlir.constant(1 : i32) : i32
    %d1 = llvm.add %ds, %c_i32_1 : i32
    %p4 = llvm.icmp "eq" %Cu, %d1 : i32
    llvm.assume %p4 : i1
    %v0 = llvm.add %a1, %C0 : i32
    %v1 = llvm.add %v0, %a0 : i32
    %c1 = llvm.icmp "sgt" %v1, %C1 : i32
    %m1 = llvm.select %c1, %v1, %C1 : i32
    %c2 = llvm.icmp "slt" %m1, %C2 : i32
    %m2 = llvm.select %c2, %m1, %C2 : i32
    %r = llvm.icmp "eq" %v1, %m2 : i32
    llvm.return %r : i1
  }
  }]

def F_wide_symbolic__minimal_tgt :=
  [llvm()| {
  llvm.func @F_wide_symbolic__minimal_tgt(%a0 : i32, %a1 : i32, %C0 : i32, %C1 : i32, %C2 : i32, %Ca : i32, %Cu : i32) -> i1 {
  ^bb0(%a0 : i32, %a1 : i32, %C0 : i32, %C1 : i32, %C2 : i32, %Ca : i32, %Cu : i32):
    %p1 = llvm.icmp "sle" %C1, %C2 : i32
    llvm.assume %p1 : i1
    %d = llvm.sub %C0, %C1 : i32
    %p2 = llvm.icmp "eq" %Ca, %d : i32
    llvm.assume %p2 : i1
    %ds = llvm.sub %C2, %C1 : i32
    %c_i32_m1 = llvm.mlir.constant(-1 : i32) : i32
    %p3 = llvm.icmp "ne" %ds, %c_i32_m1 : i32
    llvm.assume %p3 : i1
    %c_i32_1 = llvm.mlir.constant(1 : i32) : i32
    %d1 = llvm.add %ds, %c_i32_1 : i32
    %p4 = llvm.icmp "eq" %Cu, %d1 : i32
    llvm.assume %p4 : i1
    %s = llvm.add %a0, %Ca : i32
    %v1 = llvm.add %s, %a1 : i32
    %r = llvm.icmp "ult" %v1, %Cu : i32
    llvm.return %r : i1
  }
  }]
