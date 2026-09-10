import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def B_shift_mul__corpus1_src :=
  [llvm()| {
  llvm.func @B_shift_mul__corpus1_src(%v0 : i32, %v1 : i1, %C1 : i32, %C2 : i32, %C3 : i32) -> i32 {
  ^bb0(%v0 : i32, %v1 : i1, %C1 : i32, %C2 : i32, %C3 : i32):
    %v3 = llvm.select %v1, %C1, %C2 : i32
    %v4 = llvm.shl %v0, %C3 : i32
    %v5 = llvm.mul %v4, %v3 : i32
    llvm.return %v5 : i32
  }
  }]

def B_shift_mul__corpus1_tgt :=
  [llvm()| {
  llvm.func @B_shift_mul__corpus1_tgt(%v0 : i32, %v1 : i1, %C1 : i32, %C2 : i32, %C3 : i32) -> i32 {
  ^bb0(%v0 : i32, %v1 : i1, %C1 : i32, %C2 : i32, %C3 : i32):
    %v3 = llvm.shl %C1, %C3 : i32
    %v4 = llvm.shl %C2, %C3 : i32
    %v5 = llvm.select %v1, %v3, %v4 : i32
    %v6 = llvm.mul %v0, %v5 : i32
    llvm.return %v6 : i32
  }
  }]

abbrev B_shift_mul__corpus1_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 1, InstCombine.LLVM.Ty.bitvec 32]
def B_shift_mul__corpus1_v0 (V : InstCombine.InputValuation B_shift_mul__corpus1_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := B_shift_mul__corpus1_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 4 (by simp [B_shift_mul__corpus1_ctx]))
def B_shift_mul__corpus1_v1 (V : InstCombine.InputValuation B_shift_mul__corpus1_ctx) : LLVM.IntW 1 :=
  V (Ctxt.Var.mk (Γ := B_shift_mul__corpus1_ctx) (t := InstCombine.LLVM.Ty.bitvec 1) 3 (by simp [B_shift_mul__corpus1_ctx]))
def B_shift_mul__corpus1_C1 (V : InstCombine.InputValuation B_shift_mul__corpus1_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := B_shift_mul__corpus1_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 2 (by simp [B_shift_mul__corpus1_ctx]))
def B_shift_mul__corpus1_C2 (V : InstCombine.InputValuation B_shift_mul__corpus1_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := B_shift_mul__corpus1_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 1 (by simp [B_shift_mul__corpus1_ctx]))
def B_shift_mul__corpus1_C3 (V : InstCombine.InputValuation B_shift_mul__corpus1_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := B_shift_mul__corpus1_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 0 (by simp [B_shift_mul__corpus1_ctx]))
def B_shift_mul__corpus1_src_sem (V : InstCombine.InputValuation B_shift_mul__corpus1_ctx) : LLVM.IntW 32 :=
  (LLVM.mul (LLVM.shl (B_shift_mul__corpus1_v0 V) (B_shift_mul__corpus1_C3 V)) (LLVM.select (B_shift_mul__corpus1_v1 V) (B_shift_mul__corpus1_C1 V) (B_shift_mul__corpus1_C2 V)))
def B_shift_mul__corpus1_tgt_sem (V : InstCombine.InputValuation B_shift_mul__corpus1_ctx) : LLVM.IntW 32 :=
  (LLVM.mul (B_shift_mul__corpus1_v0 V) (LLVM.select (B_shift_mul__corpus1_v1 V) (LLVM.shl (B_shift_mul__corpus1_C1 V) (B_shift_mul__corpus1_C3 V)) (LLVM.shl (B_shift_mul__corpus1_C2 V) (B_shift_mul__corpus1_C3 V))))
def B_shift_mul__corpus1_ret (x : LLVM.IntW 32) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 32] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 32)) ::ₕ HVector.nil

theorem B_shift_mul__corpus1_value (v0 : LLVM.IntW 32) (v1 : LLVM.IntW 1) (C1 : LLVM.IntW 32) (C2 : LLVM.IntW 32) (C3 : LLVM.IntW 32) :
    (LLVM.mul (LLVM.shl v0 C3) (LLVM.select v1 C1 C2))
      ⊑ (LLVM.mul v0 (LLVM.select v1 (LLVM.shl C1 C3) (LLVM.shl C2 C3))) := by
  have hshift_mul (a b c : BitVec 32) : (a <<< c.toNat) * b = a * (b <<< c.toNat) := by
    have hprod (x y z : BitVec 32) : (x <<< z.toNat) * y = (x * y) <<< z.toNat := by
      rw [BitVec.toNat_eq]
      simp only [BitVec.toNat_mul, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      rw [Nat.mod_mul_mod]
      rw [Nat.mul_assoc]
      rw [Nat.mul_comm (2 ^ z.toNat) y.toNat]
      rw [← Nat.mul_assoc]
      rw [Nat.mod_mul_mod]
    rw [hprod a b c]
    rw [BitVec.mul_comm a (b <<< c.toNat)]
    rw [hprod b a c]
    rw [BitVec.mul_comm b a]
  cases v0 <;> cases v1 <;> cases C1 <;> cases C2 <;> cases C3 <;>
    simp [LLVM.mul, LLVM.shl, LLVM.shl?, LLVM.mul?, LLVM.select] <;>
    split_ifs <;> simp <;>
    exact hshift_mul _ _ _

theorem B_shift_mul__corpus1_correct : B_shift_mul__corpus1_src ⊑ B_shift_mul__corpus1_tgt := by
  unfold B_shift_mul__corpus1_src B_shift_mul__corpus1_tgt
  intro V
  change
    (some (B_shift_mul__corpus1_ret (B_shift_mul__corpus1_src_sem V)) ⊑ some (B_shift_mul__corpus1_ret (B_shift_mul__corpus1_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold B_shift_mul__corpus1_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [B_shift_mul__corpus1_src_sem, B_shift_mul__corpus1_tgt_sem] using
        B_shift_mul__corpus1_value (B_shift_mul__corpus1_v0 V) (B_shift_mul__corpus1_v1 V) (B_shift_mul__corpus1_C1 V) (B_shift_mul__corpus1_C2 V) (B_shift_mul__corpus1_C3 V)
  · exact True.intro
