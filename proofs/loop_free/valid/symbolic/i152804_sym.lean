import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def i152804_sym_src (w : Nat) :=
  [llvm(w)| {
  llvm.func @i152804_sym_src(%V : _, %C1 : _, %C2 : _, %C3 : _) -> _ {
  ^bb0(%V : _, %C1 : _, %C2 : _, %C3 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %negone = llvm.mlir.constant(-1 : _) : _
    %and_V = llvm.and %V, %C1 : _
    %cmp_V = llvm.icmp "eq" %and_V, %V : _
    llvm.assume %cmp_V : i1
    %Y = llvm.sub %zero, %C1 : _
    %Y_not_zero = llvm.icmp "ne" %Y, %zero : _
    %Y_minus_1 = llvm.add %Y, %negone : _
    %and_Y = llvm.and %Y, %Y_minus_1 : _
    %Y_is_power2 = llvm.icmp "eq" %and_Y, %zero : _
    %cond1 = llvm.and %Y_not_zero, %Y_is_power2 : i1
    %cond2_1 = llvm.icmp "sle" %C1, %C2 : _
    %cond2_2 = llvm.icmp "slt" %C2, %zero : _
    %cond2 = llvm.and %cond2_1, %cond2_2 : i1
    %cond3 = llvm.icmp "eq" %C3, %Y : _
    %cond12 = llvm.and %cond1, %cond2 : i1
    %cond = llvm.and %cond12, %cond3 : i1
    llvm.assume %cond : i1
    %v1 = llvm.add %V, %C2 : _
    %v2 = llvm.and %v1, %C1 : _
    %v3 = llvm.add %v2, %C3 : _
    llvm.return %v3 : _
  }
  }]

def i152804_sym_tgt (w : Nat) :=
  [llvm(w)| {
  llvm.func @i152804_sym_tgt(%V : _, %C1 : _, %C2 : _, %C3 : _) -> _ {
  ^bb0(%V : _, %C1 : _, %C2 : _, %C3 : _):
    %zero = llvm.mlir.constant(0 : _) : _
    %negone = llvm.mlir.constant(-1 : _) : _
    %and_V = llvm.and %V, %C1 : _
    %cmp_V = llvm.icmp "eq" %and_V, %V : _
    llvm.assume %cmp_V : i1
    %Y = llvm.sub %zero, %C1 : _
    %Y_not_zero = llvm.icmp "ne" %Y, %zero : _
    %Y_minus_1 = llvm.add %Y, %negone : _
    %and_Y = llvm.and %Y, %Y_minus_1 : _
    %Y_is_power2 = llvm.icmp "eq" %and_Y, %zero : _
    %cond1 = llvm.and %Y_not_zero, %Y_is_power2 : i1
    %cond2_1 = llvm.icmp "sle" %C1, %C2 : _
    %cond2_2 = llvm.icmp "slt" %C2, %zero : _
    %cond2 = llvm.and %cond2_1, %cond2_2 : i1
    %cond3 = llvm.icmp "eq" %C3, %Y : _
    %cond12 = llvm.and %cond1, %cond2 : i1
    %cond = llvm.and %cond12, %cond3 : i1
    llvm.assume %cond : i1
    llvm.return %V : _
  }
  }]

private theorem i152804_sym_value {w : Nat} (Vv : BitVec w) (C1 : BitVec w) (C2 : BitVec w) (C3 : BitVec w)
    (hpre1 : ((Vv &&& C1) == Vv) = true)
    (hpre2 : ((((-C1 != 0#w) && ((-C1 &&& (-C1 + (BitVec.ofInt w (-1)))) == 0#w)) && ((C1 ≤ₛ C2) && (C2 <ₛ 0#w))) && (C3 == -C1)) = true) :
    (((Vv + C2) &&& C1) + C3) = Vv := by
  have nat_power : ∀ n : Nat, n ≠ 0 → n &&& (n - 1) = 0 → Nat.isPowerOfTwo n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hne hland
      rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
      · by_cases hn1 : n = 1
        · subst n
          exact Nat.isPowerOfTwo_one
        · have hhalf_ne : n / 2 ≠ 0 := by omega
          have hhalf_land : n / 2 &&& (n / 2 - 1) = 0 := by
            have hdiv : (n &&& (n - 1)) / 2 ^ 1 = n / 2 ^ 1 &&& (n - 1) / 2 ^ 1 := by
              exact Nat.and_div_two_pow
            rw [hland] at hdiv
            have hnsub : (n - 1) / 2 = n / 2 - 1 := by omega
            simpa [hnsub] using hdiv.symm
          have hlt : n / 2 < n := by omega
          rcases ih (n / 2) hlt hhalf_ne hhalf_land with ⟨k, hk⟩
          refine ⟨k + 1, ?_⟩
          calc
            n = 2 * (n / 2) := by omega
            _ = 2 * 2 ^ k := by rw [hk]
            _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
      · have hnle : n ≤ 1 := by
          have hdiv : (n &&& (n - 1)) / 2 ^ 1 = n / 2 ^ 1 &&& (n - 1) / 2 ^ 1 := by
            exact Nat.and_div_two_pow
          rw [hland] at hdiv
          have hnsub : (n - 1) / 2 = n / 2 := by omega
          have hz : n / 2 = 0 := by
            simpa [hnsub, Nat.and_self] using hdiv.symm
          omega
        have hn : n = 1 := by omega
        subst n
        exact Nat.isPowerOfTwo_one
  have ofInt_neg_one_toNat : (BitVec.ofInt w (-1)).toNat = 2 ^ w - 1 := by
    rw [BitVec.toNat_ofInt]
    by_cases hpow1 : 2 ^ w = 1
    · have hw : w = 0 := by
        cases w with
        | zero => rfl
        | succ w =>
          have : 1 < 2 ^ Nat.succ w := Nat.one_lt_two_pow (Nat.succ_ne_zero w)
          omega
      subst w
      decide
    · have hNge1Nat : 1 ≤ 2 ^ w := Nat.one_le_two_pow
      have hNgt1Nat : 1 < 2 ^ w := lt_of_le_of_ne hNge1Nat (Ne.symm hpow1)
      have hNgt1Int : (1 : Int) < (2 ^ w : Nat) := by exact_mod_cast hNgt1Nat
      have hdiv : ¬(↑(2 ^ w) : Int) ∣ (1 : Int) := by
        intro hd
        have hdNat : 2 ^ w ∣ 1 := by exact_mod_cast hd
        have hle : 2 ^ w ≤ 1 := Nat.le_of_dvd (by omega) hdNat
        omega
      rw [show (-1 : Int) = -(1 : Int) by rfl]
      rw [Int.neg_emod]
      simp [hdiv]
      have hone : (1 : Int) % ↑(2 ^ w) = 1 := by
        apply Int.emod_eq_of_lt
        · omega
        · exact hNgt1Int
      rw [hone]
      have hnonneg : 0 ≤ ((2 ^ w : Nat) : Int) - 1 := by omega
      have hcast : (((((2 ^ w : Nat) : Int) - 1).toNat : Int) = ((2 ^ w : Nat) : Int) - 1) :=
        Int.toNat_of_nonneg hnonneg
      exact_mod_cast hcast
  have mask_formula : ∀ {k x : Nat}, k < w → x < 2 ^ w →
      x &&& (2 ^ w - 2 ^ k) = x - x % 2 ^ k := by
    intro k x hk hx
    let M := 2 ^ k
    have hMpos : 0 < M := Nat.two_pow_pos k
    have hmask_mod : (2 ^ w - 2 ^ k) % M = 0 := by
      have hdvd1 : M ∣ 2 ^ w := Nat.pow_dvd_pow 2 (Nat.le_of_lt hk)
      have hdvd2 : M ∣ 2 ^ k := dvd_refl M
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_sub hdvd1 hdvd2)
    have hmask_div : (2 ^ w - 2 ^ k) / M = 2 ^ (w - k) - 1 := by
      have hmask_eq : 2 ^ w - 2 ^ k = (2 ^ (w - k) - 1) * M := by
        have hkw : k ≤ w := Nat.le_of_lt hk
        have hp : 2 ^ (w - k) * M = 2 ^ w := Nat.pow_sub_mul_pow 2 hkw
        calc
          2 ^ w - 2 ^ k = 2 ^ (w - k) * M - M := by rw [hp]
          _ = (2 ^ (w - k) - 1) * M := by rw [Nat.sub_one_mul]
      rw [hmask_eq]
      exact Nat.mul_div_left (2 ^ (w - k) - 1) hMpos
    have hxdiv_lt : x / M < 2 ^ (w - k) := by
      have hkw : k ≤ w := Nat.le_of_lt hk
      have hp : 2 ^ (w - k) * M = 2 ^ w := Nat.pow_sub_mul_pow 2 hkw
      have hmul : x / M * M ≤ x := Nat.div_mul_le_self x M
      by_contra hnot
      have hge : 2 ^ (w - k) ≤ x / M := Nat.le_of_not_gt hnot
      have : 2 ^ w ≤ x / M * M := by
        rw [← hp]
        exact Nat.mul_le_mul_right M hge
      omega
    have hdiv : (x &&& (2 ^ w - 2 ^ k)) / M = (x - x % M) / M := by
      rw [Nat.and_div_two_pow, hmask_div]
      rw [Nat.and_two_pow_sub_one_of_lt_two_pow hxdiv_lt]
      have hxdecomp := Nat.div_add_mod' x M
      have hxmodlt : x % M < M := Nat.mod_lt x hMpos
      have hsub : x - x % M = x / M * M := by omega
      rw [hsub]
      exact (Nat.mul_div_left (x / M) hMpos).symm
    have hmod : (x &&& (2 ^ w - 2 ^ k)) % M = (x - x % M) % M := by
      rw [Nat.and_mod_two_pow, hmask_mod, Nat.and_zero]
      have hxdecomp := Nat.div_add_mod' x M
      have hxmodlt : x % M < M := Nat.mod_lt x hMpos
      have hsub : x - x % M = x / M * M := by omega
      rw [hsub]
      exact (Nat.mul_mod_left (x / M) M).symm
    calc
      x &&& (2 ^ w - 2 ^ k) = (x &&& (2 ^ w - 2 ^ k)) / M * M + (x &&& (2 ^ w - 2 ^ k)) % M := by
        rw [Nat.div_add_mod']
      _ = (x - x % M) / M * M + (x - x % M) % M := by rw [hdiv, hmod]
      _ = x - x % M := Nat.div_add_mod' (x - x % M) M
  have finish_nat : ∀ {k V C2n : Nat}, k < w → V < 2 ^ w → C2n < 2 ^ w →
      V % 2 ^ k = 0 → 2 ^ w - 2 ^ k ≤ C2n →
      (((((V + C2n) % (2 ^ w)) - (((V + C2n) % (2 ^ w)) % (2 ^ k))) + (2 ^ k)) % (2 ^ w) = V) := by
    intro k V C2n hk hVlt hC2lt hVmod hC2ge
    let N := 2 ^ w
    let M := 2 ^ k
    let B := N - M
    change (((((V + C2n) % N) - (((V + C2n) % N) % M)) + M) % N = V)
    have hVltN : V < N := hVlt
    have hC2ltN : C2n < N := hC2lt
    have hVmodM : V % M = 0 := hVmod
    have hC2geB : B ≤ C2n := hC2ge
    have hMpos : 0 < M := Nat.two_pow_pos k
    have hNpos : 0 < N := Nat.two_pow_pos w
    have hMleN : M ≤ N := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.le_of_lt hk)
    have hMdvdN : M ∣ N := Nat.pow_dvd_pow 2 (Nat.le_of_lt hk)
    have hBmod : B % M = 0 := by
      have hdvd2 : M ∣ 2 ^ k := dvd_refl M
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_sub hMdvdN hdvd2)
    let r := C2n - B
    have hC2eq : C2n = B + r := by omega
    have hrlt : r < M := by omega
    have hC2mod : C2n % M = r := by
      rw [hC2eq, Nat.add_mod, hBmod]
      simp [Nat.mod_eq_of_lt hrlt]
    have hsumlow : ((V + C2n) % N) % M = r := by
      rw [Nat.mod_mod_of_dvd (V + C2n) hMdvdN]
      rw [Nat.add_mod, hVmodM, hC2mod, Nat.zero_add]
      exact Nat.mod_eq_of_lt hrlt
    by_cases hVzero : V = 0
    · subst V
      have hsum : (0 + C2n) % N = C2n := by simpa using Nat.mod_eq_of_lt hC2ltN
      rw [hsum, hC2mod]
      have hBM : B + M = N := by dsimp [B]; omega
      have hmain : C2n - r + M = N := by
        calc
          C2n - r + M = B + r - r + M := by rw [hC2eq]
          _ = B + M := by omega
          _ = N := hBM
      rw [hmain]
      exact Nat.mod_self N
    · have hVpos : 0 < V := Nat.pos_iff_ne_zero.mpr hVzero
      have hMleV : M ≤ V := by
        have hdvdV : M ∣ V := Nat.dvd_of_mod_eq_zero hVmodM
        exact Nat.le_of_dvd hVpos hdvdV
      have hwrap : N ≤ V + C2n := by omega
      have hsumlt : V + C2n < 2 * N := by omega
      have hsum : (V + C2n) % N = V + C2n - N := by
        rw [Nat.add_mod_eq_ite]
        rw [Nat.mod_eq_of_lt hVltN, Nat.mod_eq_of_lt hC2ltN]
        split
        · rfl
        · omega
      have hsumlow' : (V + C2n - N) % M = r := by
        rw [← hsum]
        exact hsumlow
      rw [hsum, hsumlow']
      have hmain : V + C2n - N - r + M = V := by omega
      rw [hmain]
      exact Nat.mod_eq_of_lt hVltN
  simp_all
  rcases hpre2 with ⟨⟨⟨hneg_ne, hpow⟩, hle, hlt⟩, hC3⟩
  have hYne : -C1 ≠ 0#w := by
    intro h
    apply hneg_ne
    rw [← BitVec.neg_eq_zero_iff]
    exact h
  have hminus : ((-C1) + BitVec.ofInt w (-1)).toNat = (-C1).toNat - 1 := by
    rw [BitVec.toNat_add]
    rw [show (BitVec.ofInt w (-1)).toNat = 2 ^ w - 1 by exact ofInt_neg_one_toNat]
    have hYlt : (-C1).toNat < 2 ^ w := (-C1).isLt
    have hYpos : 0 < (-C1).toNat := BitVec.toNat_pos_of_ne_zero hYne
    have hNpos : 0 < 2 ^ w := Nat.two_pow_pos w
    rw [Nat.add_mod_eq_ite]
    rw [Nat.mod_eq_of_lt hYlt]
    have hNm1lt : 2 ^ w - 1 < 2 ^ w := by omega
    rw [Nat.mod_eq_of_lt hNm1lt]
    split <;> omega
  have hpowNat : (-C1).toNat &&& ((-C1).toNat - 1) = 0 := by
    have h := congrArg BitVec.toNat hpow
    simpa [BitVec.toNat_and, hminus, BitVec.toNat_zero] using h
  rcases nat_power (-C1).toNat (by exact BitVec.toNat_ne.mp hYne) hpowNat with ⟨k, hYnat⟩
  have hk : k < w := by
    have hYlt : (-C1).toNat < 2 ^ w := (-C1).isLt
    rw [hYnat] at hYlt
    exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hYlt
  have hYposBV : 0#w < -C1 := by
    rw [BitVec.lt_def]
    exact BitVec.toNat_pos_of_ne_zero hYne
  have hC1nat : C1.toNat = 2 ^ w - 2 ^ k := by
    have h := BitVec.toNat_neg_of_pos (x := -C1) hYposBV
    simpa [BitVec.neg_neg, hYnat] using h
  have hleInt : C1.toInt ≤ C2.toInt := (BitVec.sle_iff_toInt_le).mp hle
  have hltInt : C2.toInt < 0 := by
    have h := (BitVec.slt_iff_toInt_lt).mp hlt
    simpa [BitVec.toInt_zero] using h
  have hC1lt : C1.toInt < 0 := lt_of_le_of_lt hleInt hltInt
  have hC1msb : C1.msb = true := by
    rw [BitVec.msb_eq_toInt]
    simp [hC1lt]
  have hC2msb : C2.msb = true := by
    rw [BitVec.msb_eq_toInt]
    simp [hltInt]
  have hmsbeq : C1.msb = C2.msb := by rw [hC1msb, hC2msb]
  have hleu : (C1 ≤ᵤ C2) = true := by
    simpa [BitVec.sle_eq_ule_of_msb_eq hmsbeq] using hle
  have hC2ge : 2 ^ w - 2 ^ k ≤ C2.toNat := by
    have h := (BitVec.ule_iff_toNat_le).mp hleu
    rwa [← hC1nat]
  have hpreNat := congrArg BitVec.toNat hpre1
  rw [BitVec.toNat_and, hC1nat] at hpreNat
  have hVmask := mask_formula (k := k) (x := Vv.toNat) hk Vv.isLt
  rw [hVmask] at hpreNat
  have hVmod_le : Vv.toNat % 2 ^ k ≤ Vv.toNat := Nat.mod_le _ _
  have hVmod : Vv.toNat % 2 ^ k = 0 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_add, hC1nat, hYnat]
  rw [mask_formula (k := k) (x := (Vv.toNat + C2.toNat) % 2 ^ w) hk (Nat.mod_lt _ (Nat.two_pow_pos w))]
  exact finish_nat (k := k) (V := Vv.toNat) (C2n := C2.toNat) hk Vv.isLt C2.isLt hVmod (by omega)

set_option maxHeartbeats 4000000 in
theorem i152804_sym_correct (w : Nat) : i152804_sym_src w ⊑ i152804_sym_tgt w := by
  intro V
  let VVar : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨3, by simp⟩
  let C1Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨2, by simp⟩
  let C2Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) := ⟨1, by simp⟩
  let C3Var : (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]).Var (InstCombine.LLVM.Ty.bitvec w) :=
    Ctxt.Var.last (Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w, InstCombine.LLVM.Ty.bitvec w]) (InstCombine.LLVM.Ty.bitvec w)
  cases hV : V VVar
  case poison =>
    simp [i152804_sym_src, i152804_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, VVar, hV, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.sub, LLVM.sub?, LLVM.assume_]
    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  case value Vv =>
    change BitVec w at Vv
    cases hC1 : V C1Var
    case poison =>
      simp [i152804_sym_src, i152804_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, VVar, C1Var, hV, hC1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.sub, LLVM.sub?, LLVM.assume_]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
    case value C1 =>
      change BitVec w at C1
      cases hcond1 : ((Vv &&& C1) == Vv)
      · simp [i152804_sym_src, i152804_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, VVar, C1Var, hV, hC1, hcond1, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.sub, LLVM.sub?, LLVM.assume_]
        exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
      ·
        cases hC2 : V C2Var
        case poison =>
          simp [i152804_sym_src, i152804_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, VVar, C1Var, C2Var, hV, hC1, hcond1, hC2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.sub, LLVM.sub?, LLVM.assume_]
          exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
        case value C2 =>
          change BitVec w at C2
          cases hC3 : V C3Var
          case poison =>
            simp [i152804_sym_src, i152804_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, VVar, C1Var, C2Var, C3Var, hV, hC1, hcond1, hC2, hC3, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.sub, LLVM.sub?, LLVM.assume_]
            exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
          case value C3 =>
            change BitVec w at C3
            cases hcond2 : ((((-C1 != 0#w) && ((-C1 &&& (-C1 + (BitVec.ofInt w (-1)))) == 0#w)) && ((C1 ≤ₛ C2) && (C2 <ₛ 0#w))) && (C3 == -C1))
            · simp [i152804_sym_src, i152804_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, VVar, C1Var, C2Var, C3Var, hV, hC1, hcond1, hC2, hC3, hcond2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.sub, LLVM.sub?, LLVM.assume_]
              exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
            ·
              simp [i152804_sym_src, i152804_sym_tgt, Expr.denote_unfold, Expr.denoteOp, DialectDenote.denote, InstCombine.Op.denoteVec, InstCombine.Op.denote, Ctxt.Valuation.cons_eval, VVar, C1Var, C2Var, C3Var, hV, hC1, hcond1, hC2, hC3, hcond2, ImmediateUBOr.immediateUB, ImmediateUBOr.value, LLVM.const?, LLVM.icmp, LLVM.icmp?, LLVM.icmp', LLVM.add, LLVM.add?, LLVM.and, LLVM.and?, LLVM.sub, LLVM.sub?, LLVM.assume_]
              have hv := i152804_sym_value (w := w) Vv C1 C2 C3 hcond1 hcond2
              exact ImmediateUBOr.IsRefinedBy.bothValues (by
                constructor
                · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv] <;> rfl)
                · exact HVector.nil_isRefinedBy_nil)
