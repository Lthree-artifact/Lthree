import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def i143630_a2n_src :=
  [llvm()| {
  llvm.func @i143630_a2n_src(%arg0 : i32, %arg1 : i32) -> i1 {
  ^bb0(%arg0 : i32, %arg1 : i32):
    %c_32_31 = llvm.mlir.constant(31 : i32) : i32
    %1 = llvm.ashr %arg0, %c_32_31 : i32
    %c_32_1 = llvm.mlir.constant(1 : i32) : i32
    %2 = llvm.lshr %1, %c_32_1 : i32
    %3 = llvm.xor %2, %arg0 : i32
    %4 = llvm.ashr %arg1, %c_32_31 : i32
    %5 = llvm.lshr %4, %c_32_1 : i32
    %6 = llvm.xor %5, %arg1 : i32
    %7 = llvm.icmp "eq" %3, %6 : i32
    llvm.return %7 : i1
  }
  }]

def i143630_a2n_tgt :=
  [llvm()| {
  llvm.func @i143630_a2n_tgt(%arg0 : i32, %arg1 : i32) -> i1 {
  ^bb0(%arg0 : i32, %arg1 : i32):
    %1 = llvm.icmp "eq" %arg0, %arg1 : i32
    llvm.return %1 : i1
  }
  }]

abbrev i143630_a2n_ctx : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec 32, InstCombine.LLVM.Ty.bitvec 32]
def i143630_a2n_arg0 (V : InstCombine.InputValuation i143630_a2n_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := i143630_a2n_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 1 (by simp [i143630_a2n_ctx]))
def i143630_a2n_arg1 (V : InstCombine.InputValuation i143630_a2n_ctx) : LLVM.IntW 32 :=
  V (Ctxt.Var.mk (Γ := i143630_a2n_ctx) (t := InstCombine.LLVM.Ty.bitvec 32) 0 (by simp [i143630_a2n_ctx]))
def i143630_a2n_src_sem (V : InstCombine.InputValuation i143630_a2n_ctx) : LLVM.IntW 1 :=
  (LLVM.icmp LLVM.IntPred.eq (LLVM.xor (LLVM.lshr (LLVM.ashr (i143630_a2n_arg0 V) (LLVM.const? 32 31)) (LLVM.const? 32 1)) (i143630_a2n_arg0 V)) (LLVM.xor (LLVM.lshr (LLVM.ashr (i143630_a2n_arg1 V) (LLVM.const? 32 31)) (LLVM.const? 32 1)) (i143630_a2n_arg1 V)))
def i143630_a2n_tgt_sem (V : InstCombine.InputValuation i143630_a2n_ctx) : LLVM.IntW 1 :=
  (LLVM.icmp LLVM.IntPred.eq (i143630_a2n_arg0 V) (i143630_a2n_arg1 V))
def i143630_a2n_ret (x : LLVM.IntW 1) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec 1] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec 1)) ::ₕ HVector.nil

theorem i143630_a2n_value (arg0 : LLVM.IntW 32) (arg1 : LLVM.IntW 32) :
    (LLVM.icmp LLVM.IntPred.eq (LLVM.xor (LLVM.lshr (LLVM.ashr arg0 (LLVM.const? 32 31)) (LLVM.const? 32 1)) arg0) (LLVM.xor (LLVM.lshr (LLVM.ashr arg1 (LLVM.const? 32 31)) (LLVM.const? 32 1)) arg1))
      ⊑ (LLVM.icmp LLVM.IntPred.eq arg0 arg1) := by
  cases arg0 with
  | poison =>
      simp [LLVM.icmp, LLVM.xor, LLVM.lshr, LLVM.ashr, LLVM.const?, LLVM.icmp?, LLVM.xor?,
        LLVM.lshr?, LLVM.ashr?, LLVM.icmp']
  | value a =>
      cases arg1 with
      | poison =>
          simp [LLVM.icmp, LLVM.xor, LLVM.lshr, LLVM.ashr, LLVM.const?, LLVM.icmp?, LLVM.xor?,
            LLVM.lshr?, LLVM.ashr?, LLVM.icmp']
      | value b =>
          simp [LLVM.icmp, LLVM.xor, LLVM.lshr, LLVM.ashr, LLVM.const?, LLVM.icmp?, LLVM.xor?,
            LLVM.lshr?, LLVM.ashr?, LLVM.icmp']
          apply congrArg BitVec.ofBool
          apply Bool.eq_iff_iff.mpr
          constructor
          · intro h
            apply beq_iff_eq.mpr
            apply BitVec.eq_of_getElem_eq
            intro i hi
            by_cases h31 : i = 31
            · subst i
              have hg := congrArg (fun x : BitVec 32 => x[31]) ((beq_iff_eq).mp h)
              simpa [BitVec.getElem_xor, BitVec.getElem_ushiftRight, BitVec.getLsbD_of_ge]
                using hg
            · have hi31 : i < 31 := by omega
              have hsign : a[31] = b[31] := by
                have hg := congrArg (fun x : BitVec 32 => x[31]) ((beq_iff_eq).mp h)
                simpa [BitVec.getElem_xor, BitVec.getElem_ushiftRight, BitVec.getLsbD_of_ge]
                  using hg
              have hma : (a.sshiftRight 31).getLsbD (1 + i) = a[31] := by
                have hlt : 1 + i < 32 := by omega
                simp [BitVec.getLsbD_eq_getElem, BitVec.getElem_sshiftRight,
                  BitVec.msb_eq_getLsbD_last, hlt, show ¬(31 + (1 + i) < 32) by omega]
              have hmb : (b.sshiftRight 31).getLsbD (1 + i) = b[31] := by
                have hlt : 1 + i < 32 := by omega
                simp [BitVec.getLsbD_eq_getElem, BitVec.getElem_sshiftRight,
                  BitVec.msb_eq_getLsbD_last, hlt, show ¬(31 + (1 + i) < 32) by omega]
              have hg := congrArg (fun x : BitVec 32 => x[i]) ((beq_iff_eq).mp h)
              have hxor : (a[31] ^^ a[i]) = (a[31] ^^ b[i]) := by
                simpa [BitVec.getElem_xor, BitVec.getElem_ushiftRight, hma, hmb, ← hsign]
                  using hg
              exact (Bool.xor_right_inj (x := a[31]) (y := a[i]) (z := b[i])).mp hxor
          · intro h
            apply beq_iff_eq.mpr
            have hab : a = b := (beq_iff_eq).mp h
            subst b
            rfl

theorem i143630_a2n_correct : i143630_a2n_src ⊑ i143630_a2n_tgt := by
  unfold i143630_a2n_src i143630_a2n_tgt
  intro V
  change
    (some (i143630_a2n_ret (i143630_a2n_src_sem V)) ⊑ some (i143630_a2n_ret (i143630_a2n_tgt_sem V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i143630_a2n_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i143630_a2n_src_sem, i143630_a2n_tgt_sem] using
        i143630_a2n_value (i143630_a2n_arg0 V) (i143630_a2n_arg1 V)
  · exact True.intro
