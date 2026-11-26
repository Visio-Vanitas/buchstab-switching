import BuchstabSwitching.Core.ShiftedPrimes
import Mathlib.Algebra.Order.Field.Basic

/-!
# One-Step Buchstab–Richert Weighted Sieve Switching

Proves the deterministic combinatorial weighted-sieve inequality for `Ω(N - p) ≤ 3`
over `ℚ` (using `Finset` indicator/sum identities) and derives the existence of a shifted
representation `p + m = N` with `Nat.Prime p` and `omegaMult m ≤ 3` whenever the net
switching balance is strictly positive.
-/

namespace BuchstabSwitching

/-- Shifted primes `p < N` coprime to `N` whose shift `N - p` has no prime divisor `< z`. -/
def sievedShifted (N z : ℕ) : Finset ℕ :=
  (shiftedCoprimePrimes N).filter (fun p => ∀ r ∈ Finset.range z, r.Prime → ¬ r ∣ N - p)

/-- Subset of `sievedShifted N z` with a prescribed divisor `q ∣ N - p`. -/
def divisibleSievedShifted (N z q : ℕ) : Finset ℕ :=
  (sievedShifted N z).filter (fun p => q ∣ N - p)

/-- Primes `p ∈ shiftedCoprimePrimes N` with `q ^ 2 ∣ N - p`. -/
def squareDivisibleShifted (N q : ℕ) : Finset ℕ :=
  (shiftedCoprimePrimes N).filter (fun p => q ^ 2 ∣ N - p)

/-- Target good prime shifts `p < N` such that `omegaMult (N - p) ≤ 3`. -/
def goodRepresentations (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p => p.Prime ∧ omegaMult (N - p) ≤ 3)

/-- Exact rational switching balance for the one-step Richert/Buchstab inequality. -/
def switchingBalance (N z y : ℕ) : ℚ :=
  ((sievedShifted N z).card : ℚ) -
    (1 / 2 : ℚ) * ∑ q ∈ midPrimes N z y,
      (((divisibleSievedShifted N z q).card : ℚ) + ((squareDivisibleShifted N q).card : ℚ))

/-- Pointwise weighted inequality: every bad `p ∈ sievedShifted N z \ goodRepresentations N`
is counted with multiplicity at least `2` inside the `[z, y)` divisor + square sum. -/
theorem card_sieved_sub_good_le (N z y : ℕ)
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hy4 : N ≤ y ^ 4) (hzy3 : N ≤ z * y ^ 3) :
    2 * ((sievedShifted N z).filter (fun p => ¬ omegaMult (N - p) ≤ 3)).card ≤
      ∑ q ∈ midPrimes N z y,
        ((divisibleSievedShifted N z q).card + (squareDivisibleShifted N q).card) := by
  set A := sievedShifted N z
  set Abad := A.filter (fun p => ¬ omegaMult (N - p) ≤ 3)
  set M := midPrimes N z y
  have hbad_weight : ∀ p ∈ Abad,
      2 ≤ (M.filter (fun q => q ∣ N - p)).card + (M.filter (fun q => q ^ 2 ∣ N - p)).card := by
    intro p hp
    have hpA : p ∈ A := (Finset.mem_filter.mp hp).1
    have hp_not_le : ¬ omegaMult (N - p) ≤ 3 := (Finset.mem_filter.mp hp).2
    have hpA' := Finset.mem_filter.mp hpA
    have hp_cop : p ∈ shiftedCoprimePrimes N := hpA'.1
    have hp_rough : ∀ r : ℕ, r.Prime → r < z → ¬ r ∣ N - p :=
      fun r hr hrz => hpA'.2 r (Finset.mem_range.mpr hrz) hr
    have hpN : p < N := Finset.mem_range.mp (Finset.mem_filter.mp hp_cop).1
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp_cop).2.1
    have hp_ndvd : ¬ p ∣ N := (Finset.mem_filter.mp hp_cop).2.2
    by_cases hsq : ∀ q ∈ M, ¬ q ^ 2 ∣ N - p
    · -- No `q^2 ∣ N - p` in `M`, so at least `2` distinct primes `q ∈ M` must divide `N - p`.
      have hge2 : 2 ≤ (M.filter (fun q => q ∣ N - p)).card := by
        by_contra hlt
        push Not at hlt
        have hle1 : (M.filter (fun q => q ∣ N - p)).card ≤ 1 := Nat.lt_succ_iff.mp hlt
        exact hp_not_le (omegaMult_le_three_of_sieve_pinch hz2 hzy hy4 hzy3
          hpN hp_prime hp_ndvd hp_rough hsq hle1)
      omega
    · -- Some `q ∈ M` satisfies `q^2 ∣ N - p`, hence `q ∣ N - p` as well, contributing `≥ 1 + 1 = 2`.
      push Not at hsq
      rcases hsq with ⟨q, hqM, hq2⟩
      have hq1 : q ∣ N - p := dvd_trans (dvd_pow_self q (by norm_num : 2 ≠ 0)) hq2
      have hc1 : 1 ≤ (M.filter (fun r => r ∣ N - p)).card :=
        Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hqM, hq1⟩⟩
      have hc2 : 1 ≤ (M.filter (fun r => r ^ 2 ∣ N - p)).card :=
        Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hqM, hq2⟩⟩
      omega
  have hcomm1 : ∑ q ∈ M, (divisibleSievedShifted N z q).card =
      ∑ p ∈ A, (M.filter (fun q => q ∣ N - p)).card := by
    simp only [divisibleSievedShifted, Finset.card_filter]
    exact Finset.sum_comm
  have hcomm2 : ∑ p ∈ A, (M.filter (fun q => q ^ 2 ∣ N - p)).card ≤
      ∑ q ∈ M, (squareDivisibleShifted N q).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun q _ => ?_
    simp only [squareDivisibleShifted, Finset.card_filter]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hsub : Abad ⊆ A := Finset.filter_subset _ _
  calc 2 * Abad.card
    _ = ∑ _p ∈ Abad, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ p ∈ Abad,
          ((M.filter (fun q => q ∣ N - p)).card + (M.filter (fun q => q ^ 2 ∣ N - p)).card) :=
        Finset.sum_le_sum hbad_weight
    _ ≤ ∑ p ∈ A,
          ((M.filter (fun q => q ∣ N - p)).card + (M.filter (fun q => q ^ 2 ∣ N - p)).card) :=
        Finset.sum_le_sum_of_subset hsub
    _ = (∑ p ∈ A, (M.filter (fun q => q ∣ N - p)).card) +
          (∑ p ∈ A, (M.filter (fun q => q ^ 2 ∣ N - p)).card) :=
        Finset.sum_add_distrib
    _ ≤ (∑ q ∈ M, (divisibleSievedShifted N z q).card) +
          (∑ q ∈ M, (squareDivisibleShifted N q).card) := by
        rw [← hcomm1]
        exact Nat.add_le_add_left hcomm2 _
    _ = ∑ q ∈ M, ((divisibleSievedShifted N z q).card + (squareDivisibleShifted N q).card) := by
        rw [Finset.sum_add_distrib]

/-- Deterministic one-step switching lower bound over `ℚ`. -/
theorem switchingBalance_le_card_good (N z y : ℕ)
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hy4 : N ≤ y ^ 4) (hzy3 : N ≤ z * y ^ 3) :
    switchingBalance N z y ≤ (goodRepresentations N).card := by
  set A := sievedShifted N z
  set Agood := A.filter (fun p => omegaMult (N - p) ≤ 3)
  set Abad := A.filter (fun p => ¬ omegaMult (N - p) ≤ 3)
  have hsplit : Agood.card + Abad.card = A.card := by
    simp only [Agood, Abad, Finset.card_filter, ← Finset.sum_add_distrib]
    trans ∑ _p ∈ A, 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : omegaMult (N - p) ≤ 3 <;> simp [hp]
    · simp
  have hAgood_sub : Agood ⊆ goodRepresentations N := by
    intro p hp
    have hpA : p ∈ A := (Finset.mem_filter.mp hp).1
    have hp_le : omegaMult (N - p) ≤ 3 := (Finset.mem_filter.mp hp).2
    have hp_cop : p ∈ shiftedCoprimePrimes N := (Finset.mem_filter.mp hpA).1
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hp_cop).1, (Finset.mem_filter.mp hp_cop).2.1, hp_le⟩
  have hAgood_le : Agood.card ≤ (goodRepresentations N).card :=
    Finset.card_le_card hAgood_sub
  have hbad := card_sieved_sub_good_le N z y hz2 hzy hy4 hzy3
  have hnat : 2 * A.card ≤ 2 * (goodRepresentations N).card +
      ∑ q ∈ midPrimes N z y,
        ((divisibleSievedShifted N z q).card + (squareDivisibleShifted N q).card) := by
    calc 2 * A.card
      _ = 2 * (Agood.card + Abad.card) := by rw [hsplit]
      _ = 2 * Agood.card + 2 * Abad.card := by ring
      _ ≤ 2 * (goodRepresentations N).card +
            ∑ q ∈ midPrimes N z y,
              ((divisibleSievedShifted N z q).card + (squareDivisibleShifted N q).card) :=
          Nat.add_le_add (Nat.mul_le_mul_left 2 hAgood_le) hbad
  have hq : (2 : ℚ) * (A.card : ℚ) ≤ (2 : ℚ) * ((goodRepresentations N).card : ℚ) +
      ∑ q ∈ midPrimes N z y,
        (((divisibleSievedShifted N z q).card : ℚ) + ((squareDivisibleShifted N q).card : ℚ)) := by
    exact_mod_cast hnat
  unfold switchingBalance
  linarith

/-- Strictly positive switching balance yields a representation `p + m = N` with `p` prime
and `omegaMult m ≤ 3`. -/
theorem exists_prime_add_omegaMult_le_three_of_switching_pos (N z y : ℕ)
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hy4 : N ≤ y ^ 4) (hzy3 : N ≤ z * y ^ 3)
    (hpos : 0 < switchingBalance N z y) :
    ∃ p m : ℕ, p.Prime ∧ omegaMult m ≤ 3 ∧ p + m = N := by
  have hle := switchingBalance_le_card_good N z y hz2 hzy hy4 hzy3
  have hcard_q : (0 : ℚ) < ((goodRepresentations N).card : ℚ) := lt_of_lt_of_le hpos hle
  have hcard : 0 < (goodRepresentations N).card := by exact_mod_cast hcard_q
  rcases Finset.card_pos.mp hcard with ⟨p, hp⟩
  have hp' := Finset.mem_filter.mp hp
  refine ⟨p, N - p, hp'.2.1, hp'.2.2, ?_⟩
  have hpN : p < N := Finset.mem_range.mp hp'.1
  exact Nat.add_sub_cancel' (le_of_lt hpN)

end BuchstabSwitching
