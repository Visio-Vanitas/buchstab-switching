import BuchstabSwitchingK2.Sieve.ChenSwitching.Defs

/-!
# Soundness of Chen Switching for `Ω(N - p) ≤ 2`

Proves the deterministic combinatorial weighted-sieve inequality for `Ω(N - p) ≤ 2`
over `ℚ` and deduces the existence of a representation `p + m = N` with `p.Prime`
and `omegaMult m ≤ 2` whenever `0 < switchingBalance1p2 N z y`.
-/

namespace BuchstabSwitchingK2

/-- Pointwise lower bound: every bad `p ∈ sievedShifted N z` with `¬ omegaMult (N - p) ≤ 2`
contributes total weight at least `2` across `[z, y)` prime divisors, prime squares,
`sievedBSet N z y`, and `smallPrimes N y`. -/
theorem bad_pointwise_weight_ge_two {N z y p : ℕ}
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hy3 : N ≤ y ^ 3)
    (hp : p ∈ (sievedShifted N z).filter (fun p => ¬ omegaMult (N - p) ≤ 2)) :
    2 ≤ ((midPrimes N z y).filter (fun q => q ∣ N - p)).card +
      ((midPrimes N z y).filter (fun q => q ^ 2 ∣ N - p)).card +
      ((if p ∈ sievedBSet N z y then 1 else 0) + (if p ∈ smallPrimes N y then 1 else 0)) := by
  set M := midPrimes N z y
  have hpA : p ∈ sievedShifted N z := (Finset.mem_filter.mp hp).1
  have hp_not_le : ¬ omegaMult (N - p) ≤ 2 := (Finset.mem_filter.mp hp).2
  have hpA' := Finset.mem_filter.mp hpA
  have hp_cop : p ∈ shiftedCoprimePrimes N := hpA'.1
  have hp_rough : ∀ r : ℕ, r.Prime → r < z → ¬ r ∣ N - p :=
    fun r hr hrz => hpA'.2 r (Finset.mem_range.mpr hrz) hr
  have hpN : p < N := Finset.mem_range.mp (Finset.mem_filter.mp hp_cop).1
  have hp_prime : p.Prime := (Finset.mem_filter.mp hp_cop).2.1
  have hp_ndvd : ¬ p ∣ N := (Finset.mem_filter.mp hp_cop).2.2
  by_cases hsq : ∀ q ∈ M, ¬ q ^ 2 ∣ N - p
  · by_cases hge2 : 2 ≤ (M.filter (fun q => q ∣ N - p)).card
    · omega
    · have hle1 : (M.filter (fun q => q ∣ N - p)).card ≤ 1 := by omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
      · -- No prime divisor in `[z, y)`: all prime factors of `N - p` are `≥ y`, so `Ω(N - p) ≤ 2`.
        exfalso
        apply hp_not_le
        set m := N - p
        have hm_pos : 0 < m := Nat.sub_pos_of_lt hpN
        have hm_lt : m < N := Nat.sub_lt (lt_trans hp_prime.pos hpN) hp_prime.pos
        have hm_lt_y3 : m < y ^ 3 := lt_of_lt_of_le hm_lt hy3
        have hall : ∀ r : ℕ, r.Prime → r ∣ m → y ≤ r := by
          intro r hr hrm
          by_contra hlt
          push Not at hlt
          have hrz : z ≤ r := by
            by_contra hltz
            push Not at hltz
            exact hp_rough r hr hltz hrm
          have hrN : ¬ r ∣ N := by
            intro hrN
            have hrp : r ∣ p := by
              have hsub : N - m = p := Nat.sub_sub_self (le_of_lt hpN)
              rw [← hsub]
              exact Nat.dvd_sub hrN hrm
            have heq : r = p := (Nat.prime_dvd_prime_iff_eq hr hp_prime).mp hrp
            subst heq
            exact hp_ndvd hrN
          have hr_mem : r ∈ M.filter (fun q => q ∣ m) := by
            simp only [M, midPrimes, Finset.mem_filter, Finset.mem_Ico]
            exact ⟨⟨⟨hrz, hlt⟩, hr, hrN⟩, hrm⟩
          rw [Finset.card_eq_zero] at h0
          simp [h0] at hr_mem
        have hy1 : 1 ≤ y := le_trans (by omega) (le_trans hz2 hzy)
        have hlt3 := omegaMult_lt_of_lt_pow hm_pos hy1 hm_lt_y3 hall
        omega
      · -- Exactly one prime divisor in `[z, y)`: Chen pinch forces `p ∈ sievedBSet ∪ smallPrimes`.
        rcases omegaMult_le_two_of_chen_pinch hz2 hzy hy3 hpN hp_prime hp_ndvd hp_rough hsq hle1
          with hle2 | hp_mem
        · exact absurd hle2 hp_not_le
        · rw [Finset.mem_union] at hp_mem
          rcases hp_mem with hpB | hpS
          · have hB1 : (if p ∈ sievedBSet N z y then 1 else 0) = 1 := by simp [hpB]
            omega
          · have hS1 : (if p ∈ smallPrimes N y then 1 else 0) = 1 := by simp [hpS]
            omega
  · push Not at hsq
    rcases hsq with ⟨q, hqM, hq2⟩
    have hq1 : q ∣ N - p := dvd_trans (dvd_pow_self q (by norm_num : 2 ≠ 0)) hq2
    have hc1 : 1 ≤ (M.filter (fun r => r ∣ N - p)).card :=
      Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hqM, hq1⟩⟩
    have hc2 : 1 ≤ (M.filter (fun r => r ^ 2 ∣ N - p)).card :=
      Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hqM, hq2⟩⟩
    omega

/-- Upper bound for the total pointwise weight summed over `sievedShifted N z`. -/
theorem sum_pointwise_weight_le (N z y : ℕ) :
    ∑ p ∈ sievedShifted N z,
      (((midPrimes N z y).filter (fun q => q ∣ N - p)).card +
        ((midPrimes N z y).filter (fun q => q ^ 2 ∣ N - p)).card +
        ((if p ∈ sievedBSet N z y then 1 else 0) + (if p ∈ smallPrimes N y then 1 else 0))) ≤
      (∑ q ∈ midPrimes N z y,
        ((divisibleSievedShifted N z q).card + (squareDivisibleShifted N q).card)) +
        ((sievedBSet N z y).card + (smallPrimes N y).card) := by
  set A := sievedShifted N z
  set M := midPrimes N z y
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
  have hB : ∑ p ∈ A, (if p ∈ sievedBSet N z y then 1 else 0) ≤ (sievedBSet N z y).card := by
    rw [← Finset.card_filter]
    exact Finset.card_le_card fun x hx => (Finset.mem_filter.mp hx).2
  have hS : ∑ p ∈ A, (if p ∈ smallPrimes N y then 1 else 0) ≤ (smallPrimes N y).card := by
    rw [← Finset.card_filter]
    exact Finset.card_le_card fun x hx => (Finset.mem_filter.mp hx).2
  calc ∑ p ∈ A,
        ((M.filter (fun q => q ∣ N - p)).card + (M.filter (fun q => q ^ 2 ∣ N - p)).card +
          ((if p ∈ sievedBSet N z y then 1 else 0) + (if p ∈ smallPrimes N y then 1 else 0)))
    _ = ((∑ p ∈ A, (M.filter (fun q => q ∣ N - p)).card) +
          (∑ p ∈ A, (M.filter (fun q => q ^ 2 ∣ N - p)).card)) +
          ((∑ p ∈ A, (if p ∈ sievedBSet N z y then 1 else 0)) +
            (∑ p ∈ A, (if p ∈ smallPrimes N y then 1 else 0))) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ ((∑ q ∈ M, (divisibleSievedShifted N z q).card) +
          (∑ q ∈ M, (squareDivisibleShifted N q).card)) +
          ((sievedBSet N z y).card + (smallPrimes N y).card) := by
        rw [← hcomm1]
        exact Nat.add_le_add (Nat.add_le_add_left hcomm2 _) (Nat.add_le_add hB hS)
    _ = (∑ q ∈ M, ((divisibleSievedShifted N z q).card + (squareDivisibleShifted N q).card)) +
          ((sievedBSet N z y).card + (smallPrimes N y).card) := by
        rw [Finset.sum_add_distrib]

/-- Combinatorial double-counting bound on bad shifted primes `p ∈ sievedShifted N z`
with `¬ omegaMult (N - p) ≤ 2`. -/
theorem card_sieved_sub_good2_le (N z y : ℕ)
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hy3 : N ≤ y ^ 3) :
    2 * ((sievedShifted N z).filter (fun p => ¬ omegaMult (N - p) ≤ 2)).card ≤
      (∑ q ∈ midPrimes N z y,
        ((divisibleSievedShifted N z q).card + (squareDivisibleShifted N q).card)) +
        ((sievedBSet N z y).card + (smallPrimes N y).card) := by
  set A := sievedShifted N z
  set Abad := A.filter (fun p => ¬ omegaMult (N - p) ≤ 2)
  set M := midPrimes N z y
  have hsub : Abad ⊆ A := Finset.filter_subset _ _
  calc 2 * Abad.card
    _ = ∑ _p ∈ Abad, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ p ∈ Abad,
          ((M.filter (fun q => q ∣ N - p)).card + (M.filter (fun q => q ^ 2 ∣ N - p)).card +
            ((if p ∈ sievedBSet N z y then 1 else 0) + (if p ∈ smallPrimes N y then 1 else 0))) :=
        Finset.sum_le_sum fun p hp => bad_pointwise_weight_ge_two hz2 hzy hy3 hp
    _ ≤ ∑ p ∈ A,
          ((M.filter (fun q => q ∣ N - p)).card + (M.filter (fun q => q ^ 2 ∣ N - p)).card +
            ((if p ∈ sievedBSet N z y then 1 else 0) + (if p ∈ smallPrimes N y then 1 else 0))) :=
        Finset.sum_le_sum_of_subset hsub
    _ ≤ (∑ q ∈ M, ((divisibleSievedShifted N z q).card + (squareDivisibleShifted N q).card)) +
          ((sievedBSet N z y).card + (smallPrimes N y).card) :=
        sum_pointwise_weight_le N z y

/-- Splits `sievedShifted N z` into good representations (`≤ 2`) and bad shifts. -/
theorem card_sieved_le_good_add_bad (N z : ℕ) :
    (sievedShifted N z).card ≤
      (goodRepresentations2 N).card +
        ((sievedShifted N z).filter (fun p => ¬ omegaMult (N - p) ≤ 2)).card := by
  set A := sievedShifted N z
  set Agood := A.filter (fun p => omegaMult (N - p) ≤ 2)
  set Abad := A.filter (fun p => ¬ omegaMult (N - p) ≤ 2)
  have hsplit : Agood.card + Abad.card = A.card := by
    simp only [Agood, Abad, Finset.card_filter, ← Finset.sum_add_distrib]
    trans ∑ _p ∈ A, 1
    · refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : omegaMult (N - p) ≤ 2 <;> simp [hp]
    · simp
  have hAgood_sub : Agood ⊆ goodRepresentations2 N := by
    intro p hp
    have hpA : p ∈ A := (Finset.mem_filter.mp hp).1
    have hp_le : omegaMult (N - p) ≤ 2 := (Finset.mem_filter.mp hp).2
    have hp_cop : p ∈ shiftedCoprimePrimes N := (Finset.mem_filter.mp hpA).1
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hp_cop).1, (Finset.mem_filter.mp hp_cop).2.1, hp_le⟩
  have hAgood_le : Agood.card ≤ (goodRepresentations2 N).card :=
    Finset.card_le_card hAgood_sub
  omega

/-- Deterministic Chen switching lower bound over `ℚ`. -/
theorem switchingBalance1p2_le_card_good (N z y : ℕ)
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hy3 : N ≤ y ^ 3) :
    switchingBalance1p2 N z y ≤ (goodRepresentations2 N).card := by
  have hsplit := card_sieved_le_good_add_bad N z
  have hbad := card_sieved_sub_good2_le N z y hz2 hzy hy3
  have hnat : 2 * (sievedShifted N z).card ≤ 2 * (goodRepresentations2 N).card +
      ((∑ q ∈ midPrimes N z y,
          ((divisibleSievedShifted N z q).card + (squareDivisibleShifted N q).card)) +
        ((sievedBSet N z y).card + (smallPrimes N y).card)) := by
    omega
  have hq : (2 : ℚ) * ((sievedShifted N z).card : ℚ) ≤ (2 : ℚ) * ((goodRepresentations2 N).card : ℚ) +
      ((∑ q ∈ midPrimes N z y,
          (((divisibleSievedShifted N z q).card : ℚ) + ((squareDivisibleShifted N q).card : ℚ))) +
        (((sievedBSet N z y).card : ℚ) + ((smallPrimes N y).card : ℚ))) := by
    exact_mod_cast hnat
  unfold switchingBalance1p2
  linarith

/-- Strictly positive Chen switching balance yields a representation `p + m = N` with `p` prime
and `omegaMult m ≤ 2`. -/
theorem exists_prime_add_omegaMult_le_two_of_switching_pos (N z y : ℕ)
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hy3 : N ≤ y ^ 3)
    (hpos : 0 < switchingBalance1p2 N z y) :
    ∃ p m : ℕ, p.Prime ∧ omegaMult m ≤ 2 ∧ p + m = N := by
  have hle := switchingBalance1p2_le_card_good N z y hz2 hzy hy3
  have hcard_q : (0 : ℚ) < ((goodRepresentations2 N).card : ℚ) := lt_of_lt_of_le hpos hle
  have hcard : 0 < (goodRepresentations2 N).card := by exact_mod_cast hcard_q
  rcases Finset.card_pos.mp hcard with ⟨p, hp⟩
  have hp' := Finset.mem_filter.mp hp
  refine ⟨p, N - p, hp'.2.1, hp'.2.2, ?_⟩
  have hpN : p < N := Finset.mem_range.mp hp'.1
  exact Nat.add_sub_cancel' (le_of_lt hpN)

end BuchstabSwitchingK2
