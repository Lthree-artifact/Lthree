import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def hydra31_issue57531_src :=
  [llvm()| {
  llvm.func @hydra31_issue57531_src(%v0 : i32, %C1 : i32) -> i32 {
  ^bb0(%v0 : i32, %C1 : i32):
    %v0_f = llvm.freeze %v0 : i32
    %C1_f = llvm.freeze %C1 : i32
    %v1 = llvm.sub %C1_f, %v0_f : i32
    %v2 = llvm.or %v0_f, %v1 : i32
    %v3 = llvm.add %v0_f, %v2 : i32
    llvm.return %v3 : i32
  }
  }]

def hydra31_issue57531_tgt :=
  [llvm()| {
  llvm.func @hydra31_issue57531_tgt(%v0 : i32, %C1 : i32) -> i32 {
  ^bb0(%v0 : i32, %C1 : i32):
    %v0_f = llvm.freeze %v0 : i32
    %C1_f = llvm.freeze %C1 : i32
    %v1 = llvm.sub %C1_f, %v0_f : i32
    %v2 = llvm.and %v0_f, %v1 : i32
    %v3 = llvm.add %v0_f, %C1_f : i32
    %v4 = llvm.sub %v3, %v2 : i32
    llvm.return %v4 : i32
  }
  }]

abbrev hydra31_issue57531_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]
def hydra31_issue57531_v0 (V : InstCombine.InputValuation hydra31_issue57531_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := hydra31_issue57531_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 1 (by simp [hydra31_issue57531_ctx]))
def hydra31_issue57531_C1 (V : InstCombine.InputValuation hydra31_issue57531_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := hydra31_issue57531_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 0 (by simp [hydra31_issue57531_ctx]))
def hydra31_issue57531_src_sem (V : InstCombine.InputValuation hydra31_issue57531_ctx) : LLVM.IntW 32 :=
  (LLVM.add (LLVM.freeze (hydra31_issue57531_v0 V)) (LLVM.or (LLVM.freeze (hydra31_issue57531_v0 V)) (LLVM.sub (LLVM.freeze (hydra31_issue57531_C1 V)) (LLVM.freeze (hydra31_issue57531_v0 V)))))
def hydra31_issue57531_tgt_sem (V : InstCombine.InputValuation hydra31_issue57531_ctx) : LLVM.IntW 32 :=
  (LLVM.sub (LLVM.add (LLVM.freeze (hydra31_issue57531_v0 V)) (LLVM.freeze (hydra31_issue57531_C1 V))) (LLVM.and (LLVM.freeze (hydra31_issue57531_v0 V)) (LLVM.sub (LLVM.freeze (hydra31_issue57531_C1 V)) (LLVM.freeze (hydra31_issue57531_v0 V)))))
def hydra31_issue57531_ret (x : LLVM.IntW 32) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 32] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 32)) ::ₕ HVector.nil

theorem hydra31_issue57531_value (v0 : LLVM.IntW 32) (C1 : LLVM.IntW 32) :
    (LLVM.add (LLVM.freeze v0) (LLVM.or (LLVM.freeze v0) (LLVM.sub (LLVM.freeze C1) (LLVM.freeze v0))))
      ⊑ (LLVM.sub (LLVM.add (LLVM.freeze v0) (LLVM.freeze C1)) (LLVM.and (LLVM.freeze v0) (LLVM.sub (LLVM.freeze C1) (LLVM.freeze v0)))) := by
  have nat_or_add_and : ∀ x y : Nat, (x ||| y) + (x &&& y) = x + y := by
    intro x
    induction x using Nat.div2Induction with
    | ind x ih =>
      intro y
      by_cases hx : x = 0
      · simp [hx]
      · by_cases hy : y = 0
        · simp [hy]
        · have hrec := ih (Nat.pos_of_ne_zero hx) (y / 2)
          change Nat.lor (x / 2) (y / 2) + Nat.land (x / 2) (y / 2) =
            x / 2 + y / 2 at hrec
          rw [Nat.lor, Nat.land] at hrec
          change Nat.lor x y + Nat.land x y = x + y
          rw [Nat.lor, Nat.land]
          rw [Nat.bitwise.eq_def (or) x y, Nat.bitwise.eq_def (and) x y]
          by_cases hxm : x % 2 = 1 <;> by_cases hym : y % 2 = 1
          all_goals simp [hxm, hym, hx, hy]
          all_goals omega
  have bv_or_add_and (x y : BitVec 32) : (x ||| y) + (x &&& y) = x + y := by
    apply BitVec.eq_of_toNat_eq
    simp [nat_or_add_and]
  cases v0 with
  | poison =>
      cases C1 <;>
        simp [LLVM.freeze, LLVM.add, LLVM.or, LLVM.sub, LLVM.and, LLVM.and?, LLVM.or?,
          LLVM.add?, LLVM.sub?]
  | value x =>
      cases C1 with
      | poison =>
          simp [LLVM.freeze, LLVM.add, LLVM.or, LLVM.sub, LLVM.and, LLVM.and?, LLVM.or?,
            LLVM.add?, LLVM.sub?]
          rw [BitVec.eq_sub_iff_add_eq]
          rw [BitVec.add_assoc, bv_or_add_and]
          simpa using BitVec.add_right_neg x
      | value c =>
          simp [LLVM.freeze, LLVM.add, LLVM.or, LLVM.sub, LLVM.and, LLVM.and?, LLVM.or?,
            LLVM.add?, LLVM.sub?]
          rw [BitVec.eq_sub_iff_add_eq]
          rw [BitVec.add_assoc, bv_or_add_and]
          rw [show x + (c - x) = c by rw [BitVec.add_comm, BitVec.sub_add_cancel]]

theorem hydra31_issue57531_correct : hydra31_issue57531_src ⊑ hydra31_issue57531_tgt := by
  unfold hydra31_issue57531_src hydra31_issue57531_tgt
  intro V
  change
    (some (hydra31_issue57531_ret (hydra31_issue57531_src_sem V)) ⊑ some (hydra31_issue57531_ret (hydra31_issue57531_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold hydra31_issue57531_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [hydra31_issue57531_src_sem, hydra31_issue57531_tgt_sem] using
        hydra31_issue57531_value (hydra31_issue57531_v0 V) (hydra31_issue57531_C1 V)
  · exact True.intro
