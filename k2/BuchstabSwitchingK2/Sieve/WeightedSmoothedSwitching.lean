import BuchstabSwitchingK2.Sieve.ChenSwitching
import BuchstabSwitchingK2.Sieve.BSetSieveBridge
import Mathlib.Tactic

/-!
# Weighted Combinatorial Switching & Role-Reversed `B`-Set Sieve Bridge (`1 + 2`)

Generalizes the combinatorial `1 + 2` switching inequality from constant indicator weight `1`
to an arbitrary non-negative prime-shift weight `w : ℕ → ℚ`:
1. `weightedSwitchingBalance1p2` & `weightedSwitchingBalance1p2WithS4`: weighted `1 + 2`
   combinatorial balance (with optional three-divisor mid-prime bonus `s4Shifted`);
2. `weightedSwitchingBalance1p2_eq_unweighted` & `weightedSwitchingBalance1p2WithS4_eq_of_le`:
   exact specialization identities recovering unweighted `switchingBalance1p2` and `1`-step forms;
3. `smallPrimes_sum_eq_zero_of_supp` & `weightedSwitchingBalance1p2_of_supp`: identical vanishing
   of the `smallPrimes N y` defect whenever `w` vanishes below `y`;
4. `weightedSwitchingBalance1p2_le_sum_good`, `weightedSwitchingBalance1p2WithS4_le_sum_good`,
   `exists_prime_add_omegaMult_le_two_of_weighted_switching_pos`, and
   `exists_prime_add_omegaMult_le_two_of_weighted_switchingWithS4_pos`: deterministic `Ω(N - p) ≤ 2`
   pinch from any positive weighted balance;
5. `sum_bSet_eq_sum_bTriples`, `sum_bSetDivisible_eq_sum_bTriples_dvd`, `weightedRemBSet`,
   `sum_sievedBSet_le_of_weight_dominance`, and `weightedBSide_upper_of_unit_weights_and_supp`:
   exact role-reversed `B`-set decomposition and `3^ω₀`-free upper bound.
-/

namespace BuchstabSwitchingK2

/-! ### Part 1: Weighted Combinatorial `1 + 2` Switching -/

/-- Rational weighted `1 + 2` switching balance for an arbitrary prime-shift weight `w : ℕ → ℚ`.
Specializing `w = fun _ => 1` recovers `switchingBalance1p2 N z y`; choosing a non-negative
weight vanishing on `[0, y)` eliminates the `smallPrimes N y` defect identically. -/
def weightedSwitchingBalance1p2 (w : ℕ → ℚ) (N z y : ℕ) : ℚ :=
  (∑ p ∈ sievedShifted N z, w p) -
    (1 / 2 : ℚ) * ∑ q ∈ midPrimes N z y,
      ((∑ p ∈ divisibleSievedShifted N z q, w p) + (∑ p ∈ squareDivisibleShifted N q, w p)) -
    (1 / 2 : ℚ) * ((∑ p ∈ sievedBSet N z y, w p) + (∑ p ∈ smallPrimes N y, w p))

/-- Constant unit weight `w = fun _ => 1` recovers the unweighted `switchingBalance1p2`. -/
theorem weightedSwitchingBalance1p2_eq_unweighted (N z y : ℕ) :
    weightedSwitchingBalance1p2 (fun _ => (1 : ℚ)) N z y = switchingBalance1p2 N z y := by
  simp [weightedSwitchingBalance1p2, switchingBalance1p2]

/-- If `w` vanishes on `[0, y)`, then the `smallPrimes N y` defect sum vanishes identically. -/
theorem smallPrimes_sum_eq_zero_of_supp (w : ℕ → ℚ) (N y : ℕ)
    (hsupp : ∀ p < y, w p = 0) :
    ∑ p ∈ smallPrimes N y, w p = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpy : p < y := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
  exact hsupp p hpy

/-- Simplified form of `weightedSwitchingBalance1p2` when `w` vanishes below `y`. -/
theorem weightedSwitchingBalance1p2_of_supp (w : ℕ → ℚ) (N z y : ℕ)
    (hsupp : ∀ p < y, w p = 0) :
    weightedSwitchingBalance1p2 w N z y =
      (∑ p ∈ sievedShifted N z, w p) -
        (1 / 2 : ℚ) * ∑ q ∈ midPrimes N z y,
          ((∑ p ∈ divisibleSievedShifted N z q, w p) + (∑ p ∈ squareDivisibleShifted N q, w p)) -
        (1 / 2 : ℚ) * (∑ p ∈ sievedBSet N z y, w p) := by
  rw [weightedSwitchingBalance1p2, smallPrimes_sum_eq_zero_of_supp w N y hsupp, add_zero]

/-- Pointwise divisor and `B`-set multiplicity attached to `p` in the `1 + 2` switching identity. -/
def pointwiseChenCount (N z y p : ℕ) : ℕ :=
  ((midPrimes N z y).filter (fun q => q ∣ N - p)).card +
    ((midPrimes N z y).filter (fun q => q ^ 2 ∣ N - p)).card +
    ((if p ∈ sievedBSet N z y then 1 else 0) + (if p ∈ smallPrimes N y then 1 else 0))

/-- Weighted Fubini upper bound summing `(pointwiseChenCount N z y p : ℚ) * w p` over
`sievedShifted N z` for any non-negative `w : ℕ → ℚ`. -/
theorem sum_pointwise_weighted_le (w : ℕ → ℚ) (N z y : ℕ) (hw : ∀ n : ℕ, 0 ≤ w n) :
    ∑ p ∈ sievedShifted N z, (pointwiseChenCount N z y p : ℚ) * w p ≤
      (∑ q ∈ midPrimes N z y,
        ((∑ p ∈ divisibleSievedShifted N z q, w p) + (∑ p ∈ squareDivisibleShifted N q, w p))) +
        ((∑ p ∈ sievedBSet N z y, w p) + (∑ p ∈ smallPrimes N y, w p)) := by
  set A := sievedShifted N z
  set M := midPrimes N z y
  have hcomm1 :
      ∑ p ∈ A, (((M.filter (fun q => q ∣ N - p)).card : ℚ) * w p) =
        ∑ q ∈ M, ∑ p ∈ divisibleSievedShifted N z q, w p := by
    have hcard : ∀ p ∈ A,
        (((M.filter (fun q => q ∣ N - p)).card : ℚ) * w p) =
          ∑ q ∈ M, if q ∣ N - p then w p else 0 := by
      intro p _
      rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hcard, Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [divisibleSievedShifted, Finset.sum_filter]
  have hcomm2 :
      ∑ p ∈ A, (((M.filter (fun q => q ^ 2 ∣ N - p)).card : ℚ) * w p) ≤
        ∑ q ∈ M, ∑ p ∈ squareDivisibleShifted N q, w p := by
    have hcard : ∀ p ∈ A,
        (((M.filter (fun q => q ^ 2 ∣ N - p)).card : ℚ) * w p) =
          ∑ q ∈ M, if q ^ 2 ∣ N - p then w p else 0 := by
      intro p _
      rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hcard, Finset.sum_comm]
    refine Finset.sum_le_sum fun q _ => ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => hw p)
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp'.1).1, hp'.2⟩
  have hB :
      ∑ p ∈ A, ((if p ∈ sievedBSet N z y then (1 : ℚ) else 0) * w p) ≤
        ∑ p ∈ sievedBSet N z y, w p := by
    have hite : ∀ p ∈ A,
        ((if p ∈ sievedBSet N z y then (1 : ℚ) else 0) * w p) =
          if p ∈ sievedBSet N z y then w p else 0 := by
      intro p _
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => (Finset.mem_filter.mp hx).2) (fun x _ _ => hw x)
  have hS :
      ∑ p ∈ A, ((if p ∈ smallPrimes N y then (1 : ℚ) else 0) * w p) ≤
        ∑ p ∈ smallPrimes N y, w p := by
    have hite : ∀ p ∈ A,
        ((if p ∈ smallPrimes N y then (1 : ℚ) else 0) * w p) =
          if p ∈ smallPrimes N y then w p else 0 := by
      intro p _
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => (Finset.mem_filter.mp hx).2) (fun x _ _ => hw x)
  have hexpand :
      ∑ p ∈ A, (pointwiseChenCount N z y p : ℚ) * w p =
        ((∑ p ∈ A, (((M.filter (fun q => q ∣ N - p)).card : ℚ) * w p)) +
          (∑ p ∈ A, (((M.filter (fun q => q ^ 2 ∣ N - p)).card : ℚ) * w p))) +
        ((∑ p ∈ A, ((if p ∈ sievedBSet N z y then (1 : ℚ) else 0) * w p)) +
          (∑ p ∈ A, ((if p ∈ smallPrimes N y then (1 : ℚ) else 0) * w p))) := by
    simp only [pointwiseChenCount, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      add_mul, Finset.sum_add_distrib]
    rfl
  rw [hexpand, hcomm1, Finset.sum_add_distrib]
  linarith

/-- Deterministic weighted `1 + 2` lower bound: for any non-negative weight `w : ℕ → ℚ`
and admissible cutoffs `2 ≤ z ≤ y` with `N ≤ y^3`, `weightedSwitchingBalance1p2 w N z y` is a
lower bound for `∑ p ∈ goodRepresentations2 N, w p`. -/
theorem weightedSwitchingBalance1p2_le_sum_good (w : ℕ → ℚ) (N z y : ℕ)
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hy3 : N ≤ y ^ 3)
    (hw : ∀ n : ℕ, 0 ≤ w n) :
    weightedSwitchingBalance1p2 w N z y ≤ ∑ p ∈ goodRepresentations2 N, w p := by
  set A := sievedShifted N z
  set Agood := A.filter (fun p => omegaMult (N - p) ≤ 2)
  set Abad := A.filter (fun p => ¬ omegaMult (N - p) ≤ 2)
  have hsplit : (∑ p ∈ Agood, w p) + (∑ p ∈ Abad, w p) = ∑ p ∈ A, w p :=
    Finset.sum_filter_add_sum_filter_not A (fun p => omegaMult (N - p) ≤ 2) w
  have hAgood_sub : Agood ⊆ goodRepresentations2 N := by
    intro p hp
    have hpA : p ∈ A := (Finset.mem_filter.mp hp).1
    have hp_le : omegaMult (N - p) ≤ 2 := (Finset.mem_filter.mp hp).2
    have hp_cop : p ∈ shiftedCoprimePrimes N := (Finset.mem_filter.mp hpA).1
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hp_cop).1, (Finset.mem_filter.mp hp_cop).2.1, hp_le⟩
  have hgood_le : ∑ p ∈ Agood, w p ≤ ∑ p ∈ goodRepresentations2 N, w p :=
    Finset.sum_le_sum_of_subset_of_nonneg hAgood_sub (fun p _ _ => hw p)
  have hbad_pt : ∀ p ∈ Abad, (2 : ℚ) * w p ≤ (pointwiseChenCount N z y p : ℚ) * w p := by
    intro p hp
    have h2 : (2 : ℚ) ≤ (pointwiseChenCount N z y p : ℚ) := by
      exact_mod_cast bad_pointwise_weight_ge_two hz2 hzy hy3 hp
    exact mul_le_mul_of_nonneg_right h2 (hw p)
  have hbad_sum :
      (2 : ℚ) * ∑ p ∈ Abad, w p ≤ ∑ p ∈ A, (pointwiseChenCount N z y p : ℚ) * w p := by
    calc
      (2 : ℚ) * ∑ p ∈ Abad, w p = ∑ p ∈ Abad, (2 : ℚ) * w p := by rw [Finset.mul_sum]
      _ ≤ ∑ p ∈ Abad, (pointwiseChenCount N z y p : ℚ) * w p := Finset.sum_le_sum hbad_pt
      _ ≤ ∑ p ∈ A, (pointwiseChenCount N z y p : ℚ) * w p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (hw p))
  have htot := le_trans hbad_sum (sum_pointwise_weighted_le w N z y hw)
  unfold weightedSwitchingBalance1p2
  linarith

/-- Strictly positive weighted switching balance yields a representation `p + m = N`
with `p.Prime`, `omegaMult m ≤ 2`, and `0 < w p`. -/
theorem exists_good_pos_weight_of_weighted_switching_pos
    (w : ℕ → ℚ) (N z y : ℕ)
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hy3 : N ≤ y ^ 3)
    (hw : ∀ n : ℕ, 0 ≤ w n)
    (hpos : 0 < weightedSwitchingBalance1p2 w N z y) :
    ∃ p ∈ goodRepresentations2 N, 0 < w p := by
  have hle := weightedSwitchingBalance1p2_le_sum_good w N z y hz2 hzy hy3 hw
  have hsum_pos : (0 : ℚ) < ∑ p ∈ goodRepresentations2 N, w p := lt_of_lt_of_le hpos hle
  by_contra hall
  push Not at hall
  have hsum_nonpos : ∑ p ∈ goodRepresentations2 N, w p ≤ 0 :=
    Finset.sum_nonpos hall
  linarith

/-- Strictly positive weighted switching balance yields a representation `p + m = N`
with `p` prime and `omegaMult m ≤ 2`. -/
theorem exists_prime_add_omegaMult_le_two_of_weighted_switching_pos
    (w : ℕ → ℚ) (N z y : ℕ)
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hy3 : N ≤ y ^ 3)
    (hw : ∀ n : ℕ, 0 ≤ w n)
    (hpos : 0 < weightedSwitchingBalance1p2 w N z y) :
    ∃ p m : ℕ, p.Prime ∧ omegaMult m ≤ 2 ∧ p + m = N := by
  rcases exists_good_pos_weight_of_weighted_switching_pos w N z y hz2 hzy hy3 hw hpos with
    ⟨p, hp, _⟩
  have hp' := Finset.mem_filter.mp hp
  have hpN : p < N := Finset.mem_range.mp hp'.1
  exact ⟨p, N - p, hp'.2.1, hp'.2.2, Nat.add_sub_cancel' (le_of_lt hpN)⟩

/-- Weighted `1 + 2` balance augmented with the `(1 / 2) * ∑_{p ∈ S₄} w p` three-divisor bonus. -/
def weightedSwitchingBalance1p2WithS4 (w : ℕ → ℚ) (N z y w_cut : ℕ) : ℚ :=
  weightedSwitchingBalance1p2 w N z y + (1 / 2 : ℚ) * ∑ p ∈ s4Shifted N z w_cut, w p

/-- When `w_cut ≤ z`, `s4Shifted N z w_cut` is empty and `weightedSwitchingBalance1p2WithS4`
reduces identically to `weightedSwitchingBalance1p2`. -/
theorem weightedSwitchingBalance1p2WithS4_eq_of_le
    (w : ℕ → ℚ) (N z y w_cut : ℕ) (hwz : w_cut ≤ z) :
    weightedSwitchingBalance1p2WithS4 w N z y w_cut = weightedSwitchingBalance1p2 w N z y := by
  have hempty : s4Shifted N z w_cut = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    have hcard : 3 ≤ ((midPrimes N z w_cut).filter (fun q => q ∣ N - p)).card :=
      (Finset.mem_filter.mp hp).2
    have hmid : midPrimes N z w_cut = ∅ := by
      simp [midPrimes, Finset.Ico_eq_empty (by lia : ¬ z < w_cut)]
    rw [hmid] at hcard
    simp at hcard
  simp [weightedSwitchingBalance1p2WithS4, hempty]

/-- Strengthened weighted `1 + 2` lower bound incorporating the weighted `S₄` bonus. -/
theorem weightedSwitchingBalance1p2WithS4_le_sum_good (w : ℕ → ℚ) (N z y w_cut : ℕ)
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hwy : w_cut ≤ y) (hy3 : N ≤ y ^ 3)
    (hw : ∀ n : ℕ, 0 ≤ w n) :
    weightedSwitchingBalance1p2WithS4 w N z y w_cut ≤ ∑ p ∈ goodRepresentations2 N, w p := by
  set A := sievedShifted N z
  set Agood := A.filter (fun p => omegaMult (N - p) ≤ 2)
  set Abad := A.filter (fun p => ¬ omegaMult (N - p) ≤ 2)
  have hsplit : (∑ p ∈ Agood, w p) + (∑ p ∈ Abad, w p) = ∑ p ∈ A, w p :=
    Finset.sum_filter_add_sum_filter_not A (fun p => omegaMult (N - p) ≤ 2) w
  have hAgood_sub : Agood ⊆ goodRepresentations2 N := by
    intro p hp
    have hpA : p ∈ A := (Finset.mem_filter.mp hp).1
    have hp_le : omegaMult (N - p) ≤ 2 := (Finset.mem_filter.mp hp).2
    have hp_cop : p ∈ shiftedCoprimePrimes N := (Finset.mem_filter.mp hpA).1
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hp_cop).1, (Finset.mem_filter.mp hp_cop).2.1, hp_le⟩
  have hgood_le : ∑ p ∈ Agood, w p ≤ ∑ p ∈ goodRepresentations2 N, w p :=
    Finset.sum_le_sum_of_subset_of_nonneg hAgood_sub (fun p _ _ => hw p)
  have hmid_sub : midPrimes N z w_cut ⊆ midPrimes N z y :=
    Finset.filter_subset_filter _ (Finset.Ico_subset_Ico_right hwy)
  have hbad_pt : ∀ p ∈ Abad,
      ((2 : ℚ) + if p ∈ s4Shifted N z w_cut then 1 else 0) * w p ≤
        (pointwiseChenCount N z y p : ℚ) * w p := by
    intro p hp
    have hnat :
        (if p ∈ s4Shifted N z w_cut then 3 else 2) ≤ pointwiseChenCount N z y p := by
      by_cases hp4 : p ∈ s4Shifted N z w_cut
      · have hcard_w : 3 ≤ ((midPrimes N z w_cut).filter (fun q => q ∣ N - p)).card :=
          (Finset.mem_filter.mp hp4).2
        have hcard_y : 3 ≤ ((midPrimes N z y).filter (fun q => q ∣ N - p)).card :=
          le_trans hcard_w (Finset.card_le_card (Finset.filter_subset_filter _ hmid_sub))
        rw [if_pos hp4]
        unfold pointwiseChenCount
        lia
      · rw [if_neg hp4]
        exact bad_pointwise_weight_ge_two hz2 hzy hy3 hp
    have hq :
        ((2 : ℚ) + if p ∈ s4Shifted N z w_cut then 1 else 0) ≤
          (pointwiseChenCount N z y p : ℚ) := by
      by_cases hp4 : p ∈ s4Shifted N z w_cut
      · rw [if_pos hp4]
        rw [if_pos hp4] at hnat
        norm_num
        exact_mod_cast hnat
      · rw [if_neg hp4]
        rw [if_neg hp4] at hnat
        norm_num
        exact_mod_cast hnat
    exact mul_le_mul_of_nonneg_right hq (hw p)
  have hs4_eq :
      ∑ p ∈ Abad, (if p ∈ s4Shifted N z w_cut then (1 : ℚ) else 0) * w p =
        ∑ p ∈ s4Shifted N z w_cut, w p := by
    have hite : ∀ p ∈ Abad,
        (if p ∈ s4Shifted N z w_cut then (1 : ℚ) else 0) * w p =
          if p ∈ s4Shifted N z w_cut then w p else 0 := by
      intro p _
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
    have hfilt : Abad.filter (· ∈ s4Shifted N z w_cut) = s4Shifted N z w_cut := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨s4Shifted_subset_bad N z w_cut h, h⟩⟩
    rw [hfilt]
  have hbad_sum :
      (2 : ℚ) * (∑ p ∈ Abad, w p) + (∑ p ∈ s4Shifted N z w_cut, w p) ≤
        ∑ p ∈ A, (pointwiseChenCount N z y p : ℚ) * w p := by
    calc
      (2 : ℚ) * (∑ p ∈ Abad, w p) + (∑ p ∈ s4Shifted N z w_cut, w p)
          = ∑ p ∈ Abad, ((2 : ℚ) + if p ∈ s4Shifted N z w_cut then 1 else 0) * w p := by
            rw [← hs4_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p _ => by ring
      _ ≤ ∑ p ∈ Abad, (pointwiseChenCount N z y p : ℚ) * w p := Finset.sum_le_sum hbad_pt
      _ ≤ ∑ p ∈ A, (pointwiseChenCount N z y p : ℚ) * w p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (hw p))
  have htot := le_trans hbad_sum (sum_pointwise_weighted_le w N z y hw)
  unfold weightedSwitchingBalance1p2WithS4 weightedSwitchingBalance1p2
  linarith

/-- Strictly positive `S₄`-augmented weighted switching balance yields a representation
`p + m = N` with `p` prime and `omegaMult m ≤ 2`. -/
theorem exists_prime_add_omegaMult_le_two_of_weighted_switchingWithS4_pos
    (w : ℕ → ℚ) (N z y w_cut : ℕ)
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hwy : w_cut ≤ y) (hy3 : N ≤ y ^ 3)
    (hw : ∀ n : ℕ, 0 ≤ w n)
    (hpos : 0 < weightedSwitchingBalance1p2WithS4 w N z y w_cut) :
    ∃ p m : ℕ, p.Prime ∧ omegaMult m ≤ 2 ∧ p + m = N := by
  have hle := weightedSwitchingBalance1p2WithS4_le_sum_good w N z y w_cut hz2 hzy hwy hy3 hw
  have hsum_pos : (0 : ℚ) < ∑ p ∈ goodRepresentations2 N, w p := lt_of_lt_of_le hpos hle
  have hex : ∃ p ∈ goodRepresentations2 N, 0 < w p := by
    by_contra hall
    push Not at hall
    have hsum_nonpos : ∑ p ∈ goodRepresentations2 N, w p ≤ 0 := Finset.sum_nonpos hall
    linarith
  rcases hex with ⟨p, hp, _⟩
  have hp' := Finset.mem_filter.mp hp
  have hpN : p < N := Finset.mem_range.mp hp'.1
  exact ⟨p, N - p, hp'.2.1, hp'.2.2, Nat.add_sub_cancel' (le_of_lt hpN)⟩

/-! ### Part 2: Weighted `B`-Set Role-Reversal & Unit-Weight Sieve Bridge -/

/-- Exact weighted role-reversal identity on `bSet N z y` via `bTriples_injOn`: summing any
shift weight `W` over `b ∈ bSet N z y` equals summing `W(N - p₁ p₂ p₃)` over ordered triples
`(p₁, p₂, p₃) ∈ bTriples N z y`. -/
theorem sum_bSet_eq_sum_bTriples {α : Type*} [AddCommMonoid α]
    (W : ℕ → α) (N z y : ℕ) :
    ∑ b ∈ bSet N z y, W b =
      ∑ t ∈ bTriples N z y, W (N - t.1 * t.2.1 * t.2.2) := by
  rw [bSet, Finset.sum_image]
  intro t₁ ht₁ t₂ ht₂ hEq
  exact bTriples_injOn N z y ht₁ ht₂ hEq

/-- Exact weighted divisibility sum on `bSetDivisible N z y d` pulled back to `bTriples N z y`. -/
theorem sum_bSetDivisible_eq_sum_bTriples_dvd {α : Type*} [AddCommMonoid α]
    (W : ℕ → α) (N z y d : ℕ) :
    ∑ b ∈ bSetDivisible N z y d, W b =
      ∑ t ∈ (bTriples N z y).filter (fun t => d ∣ N - t.1 * t.2.1 * t.2.2),
        W (N - t.1 * t.2.1 * t.2.2) := by
  have himg : bSetDivisible N z y d =
      ((bTriples N z y).filter (fun t => d ∣ N - t.1 * t.2.1 * t.2.2)).image
        (fun t => N - t.1 * t.2.1 * t.2.2) := by
    ext b
    simp only [bSetDivisible, bSet, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hdb⟩
      exact ⟨t, ⟨ht, hdb⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hdt⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, hdt⟩
  rw [himg, Finset.sum_image]
  intro t₁ ht₁ t₂ ht₂ hEq
  exact bTriples_injOn N z y (Finset.mem_filter.mp ht₁).1 (Finset.mem_filter.mp ht₂).1 hEq

/-- Signed weighted bilinear divisor discrepancy on `bSet N z y`. -/
noncomputable def weightedRemBSet (W : ℕ → ℝ) (N z y d : ℕ) : ℝ :=
  (∑ b ∈ bSetDivisible N z y d, W b) -
    (∑ b ∈ bSet N z y, W b) / (Nat.totient d : ℝ)

/-- Upper-sieve decomposition of `∑ b ∈ sievedBSet N z y, W b` for any non-negative prime
weight `W : ℕ → ℝ` and upper-sieve divisor weights `lam : ℕ → ℝ` on `Dset`. -/
theorem sum_sievedBSet_le_of_weight_dominance
    (W : ℕ → ℝ) (N z y : ℕ) (Dset : Finset ℕ) (lam : ℕ → ℝ)
    (hW : ∀ n : ℕ, 0 ≤ W n)
    (hdom : ∀ b ∈ bSet N z y,
      (if (∀ r ∈ Finset.range y, r.Prime → ¬ r ∣ N → ¬ r ∣ b) then (1 : ℝ) else 0) ≤
        ∑ d ∈ Dset, if d ∣ b then lam d else 0) :
    ∑ b ∈ sievedBSet N z y, W b ≤
      (∑ t ∈ bTriples N z y, W (N - t.1 * t.2.1 * t.2.2)) *
        (∑ d ∈ Dset, lam d / (Nat.totient d : ℝ)) +
        ∑ d ∈ Dset, lam d * weightedRemBSet W N z y d := by
  have hcount :
      ∑ b ∈ sievedBSet N z y, W b =
        ∑ b ∈ bSet N z y,
          W b * if (∀ r ∈ Finset.range y, r.Prime → ¬ r ∣ N → ¬ r ∣ b) then (1 : ℝ) else 0 := by
    rw [sievedBSet, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  have hle_sum :
      ∑ b ∈ sievedBSet N z y, W b ≤
        ∑ b ∈ bSet N z y, W b * (∑ d ∈ Dset, if d ∣ b then lam d else 0) := by
    rw [hcount]
    exact Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left (hdom b hb) (hW b)
  have hswap :
      (∑ b ∈ bSet N z y, W b * (∑ d ∈ Dset, if d ∣ b then lam d else 0)) =
        ∑ d ∈ Dset, lam d * (∑ b ∈ bSetDivisible N z y d, W b) := by
    have hexp : ∀ b ∈ bSet N z y,
        W b * (∑ d ∈ Dset, if d ∣ b then lam d else 0) =
          ∑ d ∈ Dset, if d ∣ b then lam d * W b else 0 := by
      intro b _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [bSetDivisible, ← Finset.sum_filter, Finset.mul_sum]
  have hdecomp :
      (∑ d ∈ Dset, lam d * (∑ b ∈ bSetDivisible N z y d, W b)) =
        (∑ b ∈ bSet N z y, W b) * (∑ d ∈ Dset, lam d / (Nat.totient d : ℝ)) +
          ∑ d ∈ Dset, lam d * weightedRemBSet W N z y d := by
    have hterm : ∀ d ∈ Dset,
        lam d * (∑ b ∈ bSetDivisible N z y d, W b) =
          (∑ b ∈ bSet N z y, W b) * (lam d / (Nat.totient d : ℝ)) +
            lam d * weightedRemBSet W N z y d := by
      intro d _
      unfold weightedRemBSet
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← sum_bSet_eq_sum_bTriples W N z y]
  linarith

/-- Divisor-multiplicity-free and `smallPrimes`-free weighted `B`-side upper bound: when `0 ≤ W`,
`W` vanishes below `y`, and upper-sieve weights satisfy `|lam d| ≤ 1`, both the `3^ω₀` penalty
and the `+ y` small-prime defect disappear completely. -/
theorem weightedBSide_upper_of_unit_weights_and_supp
    (W : ℕ → ℝ) (N z y : ℕ) (Dset : Finset ℕ) (lam : ℕ → ℝ)
    (hW : ∀ n : ℕ, 0 ≤ W n)
    (hsupp : ∀ p < y, W p = 0)
    (hdom : ∀ b ∈ bSet N z y,
      (if (∀ r ∈ Finset.range y, r.Prime → ¬ r ∣ N → ¬ r ∣ b) then (1 : ℝ) else 0) ≤
        ∑ d ∈ Dset, if d ∣ b then lam d else 0)
    (hlam_abs : ∀ d ∈ Dset, |lam d| ≤ 1) :
    (∑ b ∈ sievedBSet N z y, W b) + (∑ p ∈ smallPrimes N y, W p) ≤
      (∑ t ∈ bTriples N z y, W (N - t.1 * t.2.1 * t.2.2)) *
        (∑ d ∈ Dset, lam d / (Nat.totient d : ℝ)) +
        ∑ d ∈ Dset, |weightedRemBSet W N z y d| := by
  have hB := sum_sievedBSet_le_of_weight_dominance W N z y Dset lam hW hdom
  have hsm : ∑ p ∈ smallPrimes N y, W p = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    exact hsupp p (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
  have hrem :
      ∑ d ∈ Dset, lam d * weightedRemBSet W N z y d ≤
        ∑ d ∈ Dset, |weightedRemBSet W N z y d| := by
    calc
      ∑ d ∈ Dset, lam d * weightedRemBSet W N z y d
          ≤ |∑ d ∈ Dset, lam d * weightedRemBSet W N z y d| := le_abs_self _
      _ ≤ ∑ d ∈ Dset, |lam d * weightedRemBSet W N z y d| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ d ∈ Dset, |lam d| * |weightedRemBSet W N z y d| :=
          Finset.sum_congr rfl fun d _ => abs_mul (lam d) _
      _ ≤ ∑ d ∈ Dset, 1 * |weightedRemBSet W N z y d| :=
          Finset.sum_le_sum fun d hd =>
            mul_le_mul_of_nonneg_right (hlam_abs d hd) (abs_nonneg _)
      _ = ∑ d ∈ Dset, |weightedRemBSet W N z y d| := by simp
  linarith

end BuchstabSwitchingK2
