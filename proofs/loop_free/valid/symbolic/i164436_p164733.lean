import SSA.Projects.InstCombine.Refinement
import LeanMLIR.Dialects.LLVM.Syntax

open scoped InstCombine
open BitVec

def ctlz_and_not_x_x_sub_1_src (w1 : Nat)(_h : 0 < w1) :=
  [llvm(w1)| {
  llvm.func @ctlz_and_not_x_x_sub_1_src(%x : _) -> _ {
  ^bb0(%x : _):
    %minus_one = llvm.mlir.constant(-1 : _) : _
    %one = llvm.mlir.constant(1 : _) : _
    %not_x = llvm.xor %x, %minus_one
    %x_sub_1 = llvm.sub %x, %one
    %masked = llvm.and %not_x, %x_sub_1
    %r = llvm.ctlz %masked, false : _
    llvm.return %r
  }
  }]

def ctlz_and_not_x_x_sub_1_tgt (w1 : Nat)(_h : 0 < w1) :=
  [llvm(w1)| {
  llvm.func @ctlz_and_not_x_x_sub_1_tgt(%x : _) -> _ {
  ^bb0(%x : _):
    %bitwidth = llvm.mlir.constant(w1 : w1) : w1
    %count = llvm.cttz %x, false : _
    %r = llvm.sub %bitwidth, %count
    llvm.return %r
  }
  }]

abbrev i164436_p164733_ctx (w1 : Nat) : Ctxt InstCombine.LLVM.Ty :=
  Ctxt.ofList [InstCombine.LLVM.Ty.bitvec w1]
def i164436_p164733_x (w1 : Nat) (V : InstCombine.InputValuation (i164436_p164733_ctx w1)) : LLVM.IntW w1 :=
  V (Ctxt.Var.mk (Γ := i164436_p164733_ctx w1) (t := InstCombine.LLVM.Ty.bitvec w1) 0 (by simp [i164436_p164733_ctx]))
def i164436_p164733_src_sem (w1 : Nat) (V : InstCombine.InputValuation (i164436_p164733_ctx w1)) : LLVM.IntW w1 :=
  (LLVM.ctlz (LLVM.and (LLVM.xor (i164436_p164733_x w1 V) (LLVM.const? w1 (-1))) (LLVM.sub (i164436_p164733_x w1 V) (LLVM.const? w1 1))) {is_zero_poison := false})
def i164436_p164733_tgt_sem (w1 : Nat) (V : InstCombine.InputValuation (i164436_p164733_ctx w1)) : LLVM.IntW w1 :=
  (LLVM.sub (LLVM.const? w1 (w1 : Int)) (LLVM.cttz (i164436_p164733_x w1 V) {is_zero_poison := false}))
def i164436_p164733_ret (x : LLVM.IntW w1) :
    HVector TyDenote.toType [InstCombine.LLVM.Ty.bitvec w1] :=
  (some x : TyDenote.toType (InstCombine.LLVM.Ty.bitvec w1)) ::ₕ HVector.nil

theorem i164436_p164733_value (w1 : Nat) (_h : 0 < w1) (x : LLVM.IntW w1) :
    (LLVM.ctlz (LLVM.and (LLVM.xor x (LLVM.const? w1 (-1))) (LLVM.sub x (LLVM.const? w1 1))) {is_zero_poison := false})
      ⊑ (LLVM.sub (LLVM.const? w1 (w1 : Int)) (LLVM.cttz x {is_zero_poison := false})) := by
  cases x with
  | poison =>
      simp [LLVM.ctlz, LLVM.and, LLVM.xor, LLVM.sub, LLVM.cttz]
  | value x =>
      simp [LLVM.ctlz, LLVM.and, LLVM.xor, LLVM.sub, LLVM.cttz, LLVM.ctlz?, LLVM.cttz?,
        LLVM.const?, LLVM.and?, LLVM.xor?, LLVM.sub?]
      have hofInt : BitVec.ofInt w1 (-1) = BitVec.allOnes w1 := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_ofInt, BitVec.allOnes]
        rw [show (-1 : Int) = Int.negSucc 0 by rfl]
        rw [Int.negSucc_emod]
        · change ((↑(2 ^ w1) : Int) - 1 - ((0 : Int) % (↑(2 ^ w1) : Int))).toNat =
            2 ^ w1 - 1
          have h0 : ((0 : Int) % (↑(2 ^ w1) : Int)) = 0 := by
            exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast Nat.two_pow_pos w1)
          rw [h0]
          rw [sub_zero]
          rw [show (1 : Int) = ↑(1 : Nat) by rfl]
          exact Int.toNat_sub (2 ^ w1) 1
        · exact_mod_cast Nat.two_pow_pos w1
      have hxornot : x ^^^ BitVec.ofInt w1 (-1) = ~~~x := by
        rw [hofInt]
        exact BitVec.xor_allOnes
      have hneg : (-1#w1 : BitVec w1) = BitVec.allOnes w1 := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_neg, BitVec.allOnes]
        have h2 : 1 < 2 ^ w1 := by
          exact Nat.one_lt_two_pow (ne_of_gt _h)
        have h1mod : 1 % 2 ^ w1 = 1 := Nat.mod_eq_of_lt h2
        rw [h1mod]
        have hlt : 2 ^ w1 - 1 < 2 ^ w1 := by
          exact Nat.sub_one_lt (ne_of_gt (Nat.two_pow_pos w1))
        exact Nat.mod_eq_of_lt hlt
      have hsub : x - 1#w1 = x + BitVec.allOnes w1 := by
        rw [BitVec.sub_eq_add_neg]
        rw [hneg]
      have hcarry : ∀ i, i ≤ w1 →
          BitVec.carry i x (BitVec.allOnes w1) false =
            decide (∃ j, j < i ∧ x.getLsbD j = true) := by
        intro i
        induction i with
        | zero =>
            intro hi
            simp [BitVec.carry_zero]
        | succ i ih =>
            intro hi
            rw [BitVec.carry_succ]
            have hiw : i < w1 := Nat.lt_of_succ_le hi
            rw [BitVec.getLsbD_allOnes]
            simp [hiw, ih (Nat.le_of_succ_le hi), Bool.atLeastTwo]
            by_cases hxi : x[i] = true
            · simp [hxi]
              exact ⟨i, by omega, by simpa [BitVec.getLsbD_eq_getElem hiw] using hxi⟩
            · have hxi_false : x[i] = false := Bool.eq_false_of_not_eq_true hxi
              simp [hxi_false]
              constructor
              · intro h
                rcases h with ⟨j, hj, hxj⟩
                exact ⟨j, by omega, hxj⟩
              · intro h
                rcases h with ⟨j, hj, hxj⟩
                by_cases hji : j = i
                · have : x[i] = true := by
                    have hxgi : x.getLsbD i = true := by simpa [hji] using hxj
                    simpa [BitVec.getLsbD_eq_getElem hiw] using hxgi
                  contradiction
                · exact ⟨j, by omega, hxj⟩
      have hmask_not : ∀ i, i < w1 →
          (((~~~x) &&& (x - 1#w1)).getLsbD i =
            decide (∀ j, j ≤ i → x.getLsbD j = false)) := by
        intro i hi
        rw [hsub]
        simp
        rw [BitVec.getLsbD_add hi x (BitVec.allOnes w1)]
        rw [BitVec.getLsbD_allOnes, hcarry i (Nat.le_of_lt hi)]
        simp [hi]
        by_cases hxi : x[i] = true
        · simp [hxi]
          exact ⟨i, by omega, by simpa [BitVec.getLsbD_eq_getElem hi] using hxi⟩
        · have hxi_false : x[i] = false := Bool.eq_false_of_not_eq_true hxi
          simp [hxi_false]
          by_cases hlow : ∃ j, j < i ∧ x.getLsbD j = true
          · simp [hlow]
            rcases hlow with ⟨j, hj, hxj⟩
            exact ⟨j, by omega, hxj⟩
          · simp [hlow]
            intro j hj
            by_cases hji : j = i
            · have hxgi : x.getLsbD i = false := by
                simpa [BitVec.getLsbD_eq_getElem hi] using hxi_false
              simpa [hji] using hxgi
            · by_contra hxjfalse
              have hxj : x.getLsbD j = true := Bool.eq_true_of_not_eq_false hxjfalse
              exact hlow ⟨j, by omega, hxj⟩
      have hmask : ∀ i, i < w1 →
          (((x ^^^ BitVec.ofInt w1 (-1)) &&& (x - 1#w1)).getLsbD i =
            decide (∀ j, j ≤ i → x.getLsbD j = false)) := by
        intro i hi
        rw [hxornot]
        exact hmask_not i hi
      have hctz_le : ∀ rem acc, LLVM.countTrailingZerosNatRec x rem acc ≤ acc + rem := by
        intro rem
        induction rem with
        | zero =>
            intro acc
            simp [LLVM.countTrailingZerosNatRec]
        | succ n ih =>
            intro acc
            rw [LLVM.countTrailingZerosNatRec]
            by_cases h : x.getLsbD acc
            · simp [h]
            · simp [h]
              have := ih (acc + 1)
              omega
      have hctz_false : ∀ rem acc i, acc ≤ i →
          i < LLVM.countTrailingZerosNatRec x rem acc → x.getLsbD i = false := by
        intro rem
        induction rem with
        | zero =>
            intro acc i hacc hi
            simp [LLVM.countTrailingZerosNatRec] at hi
            omega
        | succ n ih =>
            intro acc i hacc hi
            rw [LLVM.countTrailingZerosNatRec] at hi
            by_cases h : x.getLsbD acc
            · simp [h] at hi
              omega
            · simp [h] at hi
              by_cases hiacc : i = acc
              · simp [hiacc, Bool.eq_false_of_not_eq_true h]
              · exact ih (acc + 1) i (by omega) hi
      have hctz_true : ∀ rem acc,
          LLVM.countTrailingZerosNatRec x rem acc < acc + rem →
            x.getLsbD (LLVM.countTrailingZerosNatRec x rem acc) = true := by
        intro rem
        induction rem with
        | zero =>
            intro acc hlt
            simp [LLVM.countTrailingZerosNatRec] at hlt
        | succ n ih =>
            intro acc hlt
            rw [LLVM.countTrailingZerosNatRec] at hlt ⊢
            by_cases h : x.getLsbD acc
            · simp [h]
            · simp [h] at hlt ⊢
              exact ih (acc + 1) (by omega)
      have hlead_threshold : ∀ (y : BitVec w1) rem acc t, t ≤ rem →
          (∀ i, t ≤ i → i < rem → y.getLsbD i = false) →
          (∀ i, i < t → y.getLsbD i = true) →
          LLVM.countLeadingZerosNatRec y rem acc = acc + (rem - t) := by
        intro y rem
        induction rem with
        | zero =>
            intro acc t ht hfalse htrue
            have ht0 : t = 0 := by omega
            simp [LLVM.countLeadingZerosNatRec, ht0]
        | succ n ih =>
            intro acc t ht hfalse htrue
            rw [LLVM.countLeadingZerosNatRec]
            by_cases htn : t = n + 1
            · have hbit : y.getLsbD n = true := htrue n (by omega)
              simp [hbit, htn]
            · have htle : t ≤ n := by omega
              have hbit : y.getLsbD n = false := hfalse n (by omega) (by omega)
              simp [hbit]
              rw [ih (acc + 1) t htle]
              · omega
              · intro i hti hin
                exact hfalse i hti (by omega)
              · intro i hit
                exact htrue i hit
      let t := LLVM.countTrailingZerosNatRec x w1 0
      have ht_le : t ≤ w1 := by
        dsimp [t]
        simpa using hctz_le w1 0
      have hlead :
          LLVM.countLeadingZerosNatRec ((x ^^^ BitVec.ofInt w1 (-1)) &&& (x - 1#w1)) w1 0 =
            w1 - t := by
        rw [hlead_threshold (((x ^^^ BitVec.ofInt w1 (-1)) &&& (x - 1#w1)) : BitVec w1)
          w1 0 t ht_le]
        · simp
        · intro i hti hiw
          rw [hmask i hiw]
          simp
          have htt : t < w1 := by omega
          have hxt : x.getLsbD t = true := by
            dsimp [t]
            exact hctz_true w1 0 (by simpa [t] using htt)
          exact ⟨t, hti, hxt⟩
        · intro i hit
          rw [hmask i (lt_of_lt_of_le hit ht_le)]
          simp
          intro j hji
          exact hctz_false w1 0 j (by omega) (by simpa [t] using lt_of_le_of_lt hji hit)
      rw [hlead]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, BitVec.toNat_sub]
      have htlt2 : t < 2 ^ w1 := lt_of_le_of_lt ht_le Nat.lt_two_pow_self
      have hwlt2 : w1 < 2 ^ w1 := Nat.lt_two_pow_self
      have hsub_lt : w1 - t < 2 ^ w1 := lt_of_le_of_lt (Nat.sub_le w1 t) hwlt2
      rw [Nat.mod_eq_of_lt hsub_lt]
      have hmodt : LLVM.countTrailingZerosNatRec x w1 0 % 2 ^ w1 = t := by
        dsimp [t]
        exact Nat.mod_eq_of_lt htlt2
      rw [hmodt]
      have hsum : 2 ^ w1 - t + w1 = 2 ^ w1 + (w1 - t) := by omega
      rw [hsum, Nat.add_mod_left]
      exact (Nat.mod_eq_of_lt hsub_lt).symm

theorem i164436_p164733_correct (w1 : Nat) (_h : 0 < w1) : ctlz_and_not_x_x_sub_1_src w1 _h ⊑ ctlz_and_not_x_x_sub_1_tgt w1 _h := by
  unfold ctlz_and_not_x_x_sub_1_src ctlz_and_not_x_x_sub_1_tgt
  intro V
  change
    (some (i164436_p164733_ret (i164436_p164733_src_sem w1 V)) ⊑ some (i164436_p164733_ret (i164436_p164733_tgt_sem w1 V)))
  apply ImmediateUBOr.IsRefinedBy.bothValues
  unfold i164436_p164733_ret
  constructor
  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by
      simpa [i164436_p164733_src_sem, i164436_p164733_tgt_sem] using
        i164436_p164733_value w1 _h (i164436_p164733_x w1 V)
  · exact True.intro
