import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i186957_src (w : Nat) (_h : 2 ≤ w) :=
  [llvm(w)| {
  llvm.func @i186957_src(%x : _, %y : _, %z : _) -> i1 {
  ^bb0(%x : _, %y : _, %z : _):
    %px = llvm.ctpop %x : _
    %py = llvm.ctpop %y : _
    %add1 = llvm.add %px, %py : _
    %add2 = llvm.add %add1, %z : _
    %res = llvm.trunc %add2 : _ to i1
    llvm.return %res : i1
  }
  }]

def i186957_tgt (w : Nat) (_h : 2 ≤ w) :=
  [llvm(w)| {
  llvm.func @i186957_tgt(%x : _, %y : _, %z : _) -> i1 {
  ^bb0(%x : _, %y : _, %z : _):
    %xor = llvm.xor %x, %y : _
    %pop = llvm.ctpop %xor : _
    %add = llvm.add %pop, %z : _
    %res = llvm.trunc %add : _ to i1
    llvm.return %res : i1
  }
  }]

abbrev i186957_ctx (w : Nat) : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]
def i186957_x (w : Nat) (V : InstCombine.InputValuation (i186957_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i186957_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 2 (by simp [i186957_ctx]))
def i186957_y (w : Nat) (V : InstCombine.InputValuation (i186957_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i186957_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 1 (by simp [i186957_ctx]))
def i186957_z (w : Nat) (V : InstCombine.InputValuation (i186957_ctx w)) : LLVM.IntW w :=
  V (Ctxt.Var.mk (Γ := i186957_ctx w) (t := InstCombine.LLVM.Ty.bitvec w) 0 (by simp [i186957_ctx]))
def i186957_src_sem (w : Nat) (V : InstCombine.InputValuation (i186957_ctx w)) : LLVM.IntW 1 :=
  (LLVM.trunc 1 (LLVM.add (LLVM.add (LLVM.ctpop (i186957_x w V)) (LLVM.ctpop (i186957_y w V))) (i186957_z w V)))
def i186957_tgt_sem (w : Nat) (V : InstCombine.InputValuation (i186957_ctx w)) : LLVM.IntW 1 :=
  (LLVM.trunc 1 (LLVM.add (LLVM.ctpop (LLVM.xor (i186957_x w V) (i186957_y w V))) (i186957_z w V)))
def i186957_ret (x : LLVM.IntW 1) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) ::ₕ HVector.nil

theorem i186957_value (w : Nat) (_h : 2 ≤ w) (x : LLVM.IntW w) (y : LLVM.IntW w) (z : LLVM.IntW w) :
    (LLVM.trunc 1 (LLVM.add (LLVM.add (LLVM.ctpop x) (LLVM.ctpop y)) z))
      ⊑ (LLVM.trunc 1 (LLVM.add (LLVM.ctpop (LLVM.xor x y)) z)) := by
  cases x with
  | poison =>
      simp [LLVM.trunc, LLVM.add, LLVM.ctpop, LLVM.xor]
  | value a =>
      cases y with
      | poison =>
          simp [LLVM.trunc, LLVM.add, LLVM.ctpop, LLVM.xor, LLVM.trunc?, LLVM.add?,
            LLVM.ctpop?, LLVM.xor?]
      | value b =>
          cases z with
          | poison =>
              simp [LLVM.trunc, LLVM.add, LLVM.ctpop, LLVM.xor, LLVM.trunc?, LLVM.add?,
                LLVM.ctpop?, LLVM.xor?]
          | value c =>
              simp [LLVM.trunc, LLVM.add, LLVM.ctpop, LLVM.xor, LLVM.trunc?, LLVM.add?,
                LLVM.ctpop?, LLVM.xor?]
              have hPop :
                  (decide (LLVM.popCountNatRec a w 0 % 2 = 1) !=
                    decide (LLVM.popCountNatRec b w 0 % 2 = 1)) =
                  decide (LLVM.popCountNatRec (a ^^^ b) w 0 % 2 = 1) := by
                have hParity : ∀ n accx accy accxy,
                    (LLVM.popCountNatRec (a ^^^ b) n accxy +
                      LLVM.popCountNatRec a n accx + LLVM.popCountNatRec b n accy) % 2 =
                    (accxy + accx + accy) % 2 := by
                  intro n
                  induction n with
                  | zero =>
                      intro accx accy accxy
                      simp [LLVM.popCountNatRec]
                  | succ n ih =>
                      intro accx accy accxy
                      simp [LLVM.popCountNatRec, BitVec.getLsbD_xor]
                      rw [ih]
                      cases a.getLsbD n <;> cases b.getLsbD n <;> simp <;> omega
                have h0 := hParity w 0 0 0
                simp at h0
                rcases Nat.mod_two_eq_zero_or_one (LLVM.popCountNatRec a w 0) with ha | ha <;>
                rcases Nat.mod_two_eq_zero_or_one (LLVM.popCountNatRec b w 0) with hb | hb <;>
                rcases Nat.mod_two_eq_zero_or_one (LLVM.popCountNatRec (a ^^^ b) w 0) with hc | hc <;>
                  simp [ha, hb, hc, Nat.add_mod] at *
              apply BitVec.eq_of_getLsbD_eq
              intro i hi
              have hi0 : i = 0 := by omega
              subst i
              rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
              simp
              rw [BitVec.getLsbD_add (by omega : 0 < w)]
              rw [BitVec.getLsbD_add (by omega : 0 < w)]
              rw [BitVec.getLsbD_add (by omega : 0 < w)]
              have hw0 : decide (0 < w) = true := by simp [show 0 < w by omega]
              simp [BitVec.getLsbD_ofNat, hw0]
              rw [← hPop]
              cases decide (LLVM.popCountNatRec a w 0 % 2 = 1) <;>
              cases decide (LLVM.popCountNatRec b w 0 % 2 = 1) <;>
              cases c.getLsbD 0 <;> simp

theorem i186957_correct (w : Nat) (_h : 2 ≤ w) : i186957_src w _h ⊑ i186957_tgt w _h := by
  unfold i186957_src i186957_tgt
  intro V
  change
    (some (i186957_ret (i186957_src_sem w V)) ⊑ some (i186957_ret (i186957_tgt_sem w V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i186957_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i186957_src_sem, i186957_tgt_sem] using
        i186957_value w _h (i186957_x w V) (i186957_y w V) (i186957_z w V)
  · exact True.intro
