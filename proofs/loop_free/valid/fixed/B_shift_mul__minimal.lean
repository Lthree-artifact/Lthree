import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def B_shift_mul__minimal_src :=
  [llvm()| {
  llvm.func @B_shift_mul__minimal_src(%x : i32, %b : i1, %C1 : i32, %C2 : i32, %s : i32) -> i32 {
  ^bb0(%x : i32, %b : i1, %C1 : i32, %C2 : i32, %s : i32):
    %sel = llvm.select %b, %C1, %C2 : i32
    %sh = llvm.shl %x, %s : i32
    %r = llvm.mul %sh, %sel : i32
    llvm.return %r : i32
  }
  }]

def B_shift_mul__minimal_tgt :=
  [llvm()| {
  llvm.func @B_shift_mul__minimal_tgt(%x : i32, %b : i1, %C1 : i32, %C2 : i32, %s : i32) -> i32 {
  ^bb0(%x : i32, %b : i1, %C1 : i32, %C2 : i32, %s : i32):
    %a = llvm.shl %C1, %s : i32
    %c = llvm.shl %C2, %s : i32
    %sel = llvm.select %b, %a, %c : i32
    %r = llvm.mul %x, %sel : i32
    llvm.return %r : i32
  }
  }]

abbrev B_shift_mul__minimal_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec 32]
def B_shift_mul__minimal_x (V : InstCombine.InputValuation B_shift_mul__minimal_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := B_shift_mul__minimal_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 4 (by simp [B_shift_mul__minimal_ctx]))
def B_shift_mul__minimal_b (V : InstCombine.InputValuation B_shift_mul__minimal_ctx) : LLVM.IntW 1 :=
  V (Ctxt.Var.mk (Γ := B_shift_mul__minimal_ctx) (t := InstCombine.LLVM.Ty.bitvec 1) 3 (by simp [B_shift_mul__minimal_ctx]))
def B_shift_mul__minimal_C1 (V : InstCombine.InputValuation B_shift_mul__minimal_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := B_shift_mul__minimal_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 2 (by simp [B_shift_mul__minimal_ctx]))
def B_shift_mul__minimal_C2 (V : InstCombine.InputValuation B_shift_mul__minimal_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := B_shift_mul__minimal_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 1 (by simp [B_shift_mul__minimal_ctx]))
def B_shift_mul__minimal_s (V : InstCombine.InputValuation B_shift_mul__minimal_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := B_shift_mul__minimal_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 0 (by simp [B_shift_mul__minimal_ctx]))
def B_shift_mul__minimal_src_sem (V : InstCombine.InputValuation B_shift_mul__minimal_ctx) : LLVM.IntW 32 :=
  (LLVM.mul (LLVM.shl (B_shift_mul__minimal_x V) (B_shift_mul__minimal_s V)) (LLVM.select (B_shift_mul__minimal_b V) (B_shift_mul__minimal_C1 V) (B_shift_mul__minimal_C2 V)))
def B_shift_mul__minimal_tgt_sem (V : InstCombine.InputValuation B_shift_mul__minimal_ctx) : LLVM.IntW 32 :=
  (LLVM.mul (B_shift_mul__minimal_x V) (LLVM.select (B_shift_mul__minimal_b V) (LLVM.shl (B_shift_mul__minimal_C1 V) (B_shift_mul__minimal_s V)) (LLVM.shl (B_shift_mul__minimal_C2 V) (B_shift_mul__minimal_s V))))
def B_shift_mul__minimal_ret (x : LLVM.IntW 32) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 32] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 32)) ::ₕ HVector.nil

theorem B_shift_mul__minimal_value (x : LLVM.IntW 32) (b : LLVM.IntW 1) (C1 : LLVM.IntW 32) (C2 : LLVM.IntW 32) (s : LLVM.IntW 32) :
    (LLVM.mul (LLVM.shl x s) (LLVM.select b C1 C2))
      ⊑ (LLVM.mul x (LLVM.select b (LLVM.shl C1 s) (LLVM.shl C2 s))) := by
  have hshift_mul (a c : BitVec 32) (n : Nat) : (a <<< n) * c = (a * c) <<< n := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_left_comm,
      Nat.mul_comm]
  have hmul_shift (a c : BitVec 32) (n : Nat) : a * (c <<< n) = (a * c) <<< n := by
    rw [BitVec.mul_comm a, hshift_mul, BitVec.mul_comm c]
  cases x <;> cases b <;> cases C1 <;> cases C2 <;> cases s <;>
    simp [LLVM.mul, LLVM.mul?, LLVM.shl, LLVM.shl?, LLVM.select] <;>
    split_ifs <;>
    simp_all

theorem B_shift_mul__minimal_correct : B_shift_mul__minimal_src ⊑ B_shift_mul__minimal_tgt := by
  unfold B_shift_mul__minimal_src B_shift_mul__minimal_tgt
  intro V
  change
    (some (B_shift_mul__minimal_ret (B_shift_mul__minimal_src_sem V)) ⊑ some (B_shift_mul__minimal_ret (B_shift_mul__minimal_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold B_shift_mul__minimal_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [B_shift_mul__minimal_src_sem, B_shift_mul__minimal_tgt_sem] using
        B_shift_mul__minimal_value (B_shift_mul__minimal_x V) (B_shift_mul__minimal_b V) (B_shift_mul__minimal_C1 V) (B_shift_mul__minimal_C2 V) (B_shift_mul__minimal_s V)
  · exact True.intro
