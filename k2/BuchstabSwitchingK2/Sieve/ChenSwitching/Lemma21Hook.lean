import BuchstabSwitchingK2.Sieve.ChenSwitching.Soundness
import Mathlib.Algebra.BigOperators.Associated

/-!
# Lemma 2.1 `S₄` Bonus Hook for Chen Switching

Defines `s4Shifted N z w`, the subset of `sievedShifted N z` whose shifts `N - p` have at least
`3` distinct prime divisors in `[z, w)`. Every `p ∈ s4Shifted N z w` automatically satisfies
`3 ≤ omegaMult (N - p)` and receives weight at least `3` (instead of `2`) in the `[z, y)`
switching inequality when `w ≤ y`, yielding the strengthened balance `switchingBalance1p2WithS4`.
-/

namespace BuchstabSwitchingK2

private theorem omegaMult_prod_primes (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) :
    omegaMult (∏ q ∈ T, q) = T.card := by
  induction T using Finset.induction_on with
  | empty =>
    have h_one : omegaMult 1 = 0 := by
      have h := omegaMult_mul one_ne_zero one_ne_zero
      rw [mul_one] at h
      omega
    simp [h_one]
  | @insert a s has ih =>
    have ha : a.Prime := hT a (Finset.mem_insert_self a s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hT q (Finset.mem_insert_of_mem hq)
    have hprod_pos : 0 < ∏ q ∈ s, q := Finset.prod_pos fun q hq => (hs q hq).pos
    rw [Finset.prod_insert has, Finset.card_insert_of_notMem has,
      omegaMult_mul ha.ne_zero hprod_pos.ne', omegaMult_prime ha, ih hs]
    omega

/-- Sieved shifted primes `p ∈ sievedShifted N z` with at least `3` distinct prime divisors
of `N - p` in `[z, w)`. -/
def s4Shifted (N z w : ℕ) : Finset ℕ :=
  (sievedShifted N z).filter (fun p => 3 ≤ ((midPrimes N z w).filter (fun q => q ∣ N - p)).card)

/-- Chen switching balance augmented by the `(1 / 2) * |S₄|` Lemma 2.1 bonus term. -/
def switchingBalance1p2WithS4 (N z y w : ℕ) : ℚ :=
  switchingBalance1p2 N z y + (1 / 2 : ℚ) * ((s4Shifted N z w).card : ℚ)

/-- Every `p ∈ s4Shifted N z w` satisfies `¬ omegaMult (N - p) ≤ 2`. -/
theorem s4Shifted_subset_bad (N z w : ℕ) :
    s4Shifted N z w ⊆ (sievedShifted N z).filter (fun p => ¬ omegaMult (N - p) ≤ 2) := by
  intro p hp
  have hpA : p ∈ sievedShifted N z := (Finset.mem_filter.mp hp).1
  have hcard3 : 3 ≤ ((midPrimes N z w).filter (fun q => q ∣ N - p)).card :=
    (Finset.mem_filter.mp hp).2
  refine Finset.mem_filter.mpr ⟨hpA, ?_⟩
  set S := (midPrimes N z w).filter (fun q => q ∣ N - p)
  have hp_cop : p ∈ shiftedCoprimePrimes N := (Finset.mem_filter.mp hpA).1
  have hpN : p < N := Finset.mem_range.mp (Finset.mem_filter.mp hp_cop).1
  have hm_pos : 0 < N - p := Nat.sub_pos_of_lt hpN
  have hS_prime : ∀ q ∈ S, q.Prime := fun q hq =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
  have hS_dvd : ∀ q ∈ S, q ∣ N - p := fun q hq => (Finset.mem_filter.mp hq).2
  have hprod_dvd : (∏ q ∈ S, q) ∣ N - p :=
    Finset.prod_primes_dvd (N - p) (fun q hq => (hS_prime q hq).prime) hS_dvd
  rcases hprod_dvd with ⟨u, hu_eq⟩
  have hprod_pos : 0 < ∏ q ∈ S, q := Finset.prod_pos fun q hq => (hS_prime q hq).pos
  have hu_pos : 0 < u := Nat.pos_of_ne_zero (fun h => by subst h; simp at hu_eq; omega)
  have homega : omegaMult (N - p) = S.card + omegaMult u := by
    rw [hu_eq, omegaMult_mul hprod_pos.ne' hu_pos.ne', omegaMult_prod_primes S hS_prime]
  omega

/-- Strengthened double-counting bound incorporating the extra weight `1` on `s4Shifted N z w`. -/
theorem card_sieved_sub_good2_with_s4_le (N z y w : ℕ)
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hwy : w ≤ y) (hy3 : N ≤ y ^ 3) :
    2 * ((sievedShifted N z).filter (fun p => ¬ omegaMult (N - p) ≤ 2)).card +
        (s4Shifted N z w).card ≤
      (∑ q ∈ midPrimes N z y,
        ((divisibleSievedShifted N z q).card + (squareDivisibleShifted N q).card)) +
        ((sievedBSet N z y).card + (smallPrimes N y).card) := by
  set A := sievedShifted N z
  set Abad := A.filter (fun p => ¬ omegaMult (N - p) ≤ 2)
  set M := midPrimes N z y
  have hmid_sub : midPrimes N z w ⊆ M :=
    Finset.filter_subset_filter _ (Finset.Ico_subset_Ico_right hwy)
  have hpoint : ∀ p ∈ Abad,
      (if p ∈ s4Shifted N z w then 3 else 2) ≤
        (M.filter (fun q => q ∣ N - p)).card + (M.filter (fun q => q ^ 2 ∣ N - p)).card +
          ((if p ∈ sievedBSet N z y then 1 else 0) + (if p ∈ smallPrimes N y then 1 else 0)) := by
    intro p hp
    by_cases hp4 : p ∈ s4Shifted N z w
    · have hcard_w : 3 ≤ ((midPrimes N z w).filter (fun q => q ∣ N - p)).card :=
        (Finset.mem_filter.mp hp4).2
      have hcard_y : 3 ≤ (M.filter (fun q => q ∣ N - p)).card :=
        le_trans hcard_w (Finset.card_le_card (Finset.filter_subset_filter _ hmid_sub))
      rw [if_pos hp4]
      omega
    · rw [if_neg hp4]
      exact bad_pointwise_weight_ge_two hz2 hzy hy3 hp
  have hAbad_sum :
      2 * Abad.card + (s4Shifted N z w).card =
        ∑ p ∈ Abad, (if p ∈ s4Shifted N z w then 3 else 2) := by
    have hsplit_ite :
        ∑ p ∈ Abad, (if p ∈ s4Shifted N z w then 3 else 2) =
          ∑ p ∈ Abad, (2 + if p ∈ s4Shifted N z w then 1 else 0) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : p ∈ s4Shifted N z w <;> simp [hp]
    rw [hsplit_ite, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm,
      ← Finset.card_filter, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr (s4Shifted_subset_bad N z w)]
  have hsub : Abad ⊆ A := Finset.filter_subset _ _
  calc 2 * Abad.card + (s4Shifted N z w).card
    _ = ∑ p ∈ Abad, (if p ∈ s4Shifted N z w then 3 else 2) := hAbad_sum
    _ ≤ ∑ p ∈ Abad,
          ((M.filter (fun q => q ∣ N - p)).card + (M.filter (fun q => q ^ 2 ∣ N - p)).card +
            ((if p ∈ sievedBSet N z y then 1 else 0) + (if p ∈ smallPrimes N y then 1 else 0))) :=
        Finset.sum_le_sum hpoint
    _ ≤ ∑ p ∈ A,
          ((M.filter (fun q => q ∣ N - p)).card + (M.filter (fun q => q ^ 2 ∣ N - p)).card +
            ((if p ∈ sievedBSet N z y then 1 else 0) + (if p ∈ smallPrimes N y then 1 else 0))) :=
        Finset.sum_le_sum_of_subset hsub
    _ ≤ (∑ q ∈ M, ((divisibleSievedShifted N z q).card + (squareDivisibleShifted N q).card)) +
          ((sievedBSet N z y).card + (smallPrimes N y).card) :=
        sum_pointwise_weight_le N z y

/-- Deterministic Chen switching lower bound over `ℚ` with the `S₄` Lemma 2.1 bonus term. -/
theorem switchingBalance1p2WithS4_le_card_good (N z y w : ℕ)
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hwy : w ≤ y) (hy3 : N ≤ y ^ 3) :
    switchingBalance1p2WithS4 N z y w ≤ (goodRepresentations2 N).card := by
  have hsplit := card_sieved_le_good_add_bad N z
  have hbad := card_sieved_sub_good2_with_s4_le N z y w hz2 hzy hwy hy3
  have hnat : 2 * (sievedShifted N z).card + (s4Shifted N z w).card ≤
      2 * (goodRepresentations2 N).card +
        ((∑ q ∈ midPrimes N z y,
            ((divisibleSievedShifted N z q).card + (squareDivisibleShifted N q).card)) +
          ((sievedBSet N z y).card + (smallPrimes N y).card)) := by
    omega
  have hq : (2 : ℚ) * ((sievedShifted N z).card : ℚ) + ((s4Shifted N z w).card : ℚ) ≤
      (2 : ℚ) * ((goodRepresentations2 N).card : ℚ) +
        ((∑ q ∈ midPrimes N z y,
            (((divisibleSievedShifted N z q).card : ℚ) + ((squareDivisibleShifted N q).card : ℚ))) +
          (((sievedBSet N z y).card : ℚ) + ((smallPrimes N y).card : ℚ))) := by
    exact_mod_cast hnat
  unfold switchingBalance1p2WithS4 switchingBalance1p2
  linarith

/-- Strictly positive `S₄`-augmented Chen switching balance yields a representation `p + m = N`
with `p` prime and `omegaMult m ≤ 2`. -/
theorem exists_prime_add_omegaMult_le_two_of_switchingWithS4_pos (N z y w : ℕ)
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hwy : w ≤ y) (hy3 : N ≤ y ^ 3)
    (hpos : 0 < switchingBalance1p2WithS4 N z y w) :
    ∃ p m : ℕ, p.Prime ∧ omegaMult m ≤ 2 ∧ p + m = N := by
  have hle := switchingBalance1p2WithS4_le_card_good N z y w hz2 hzy hwy hy3
  have hcard_q : (0 : ℚ) < ((goodRepresentations2 N).card : ℚ) := lt_of_lt_of_le hpos hle
  have hcard : 0 < (goodRepresentations2 N).card := by exact_mod_cast hcard_q
  rcases Finset.card_pos.mp hcard with ⟨p, hp⟩
  have hp' := Finset.mem_filter.mp hp
  refine ⟨p, N - p, hp'.2.1, hp'.2.2, ?_⟩
  have hpN : p < N := Finset.mem_range.mp hp'.1
  exact Nat.add_sub_cancel' (le_of_lt hpN)

end BuchstabSwitchingK2
