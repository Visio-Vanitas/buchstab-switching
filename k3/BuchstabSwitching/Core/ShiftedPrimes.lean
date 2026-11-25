import BuchstabSwitching.Core.MultiplicativeOmega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card

/-!
# Shifted Coprime Primes & Sieve-Pinch Criterion for `Ω(m) ≤ 3`

Connects the combinatorial sieve conditions (`z`-roughness, at most one prime divisor
in `[z, y)`, no prime square `q^2` in `[z, y)` dividing `N - p`) to `Ω(N - p) ≤ 3`.
-/

namespace BuchstabSwitching

/-- Odd/coprime primes `p < N` strictly below `N` not dividing `N`. -/
def shiftedCoprimePrimes (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p => p.Prime ∧ ¬ p ∣ N)

/-- Candidate prime divisors in `[z, y)` coprime to `N`. -/
def midPrimes (N z y : ℕ) : Finset ℕ :=
  (Finset.Ico z y).filter (fun q => q.Prime ∧ ¬ q ∣ N)

/-- If `p < N` is prime with `¬ p ∣ N`, then every prime factor `r ∣ N - p` satisfies `¬ r ∣ N`. -/
theorem not_dvd_of_dvd_sub {N p r : ℕ} (hpN : p < N) (hp_prime : p.Prime)
    (hp_ndvd : ¬ p ∣ N) (hr_prime : r.Prime) (hr_sub : r ∣ N - p) :
    ¬ r ∣ N := by
  intro hrN
  have hr_le : p ≤ N := le_of_lt hpN
  have hrp : r ∣ p := by
    have h1 : N - (N - p) = p := Nat.sub_sub_self hr_le
    rw [← h1]
    exact Nat.dvd_sub hrN hr_sub
  have heq : r = p := (Nat.prime_dvd_prime_iff_eq hr_prime hp_prime).mp hrp
  subst heq
  exact hp_ndvd hrN

/--
Core combinatorial sieve-pinch lemma for `Ω(N - p) ≤ 3`:
Suppose `2 ≤ z ≤ y`, `N ≤ y^4`, `N ≤ z * y^3`, `p < N` is prime with `¬ p ∣ N`, and `N - p` has:
1. No prime divisor `r < z` coprime to `N` (hence no prime divisor `< z` at all);
2. Either no prime `q ∈ [z, y)` with `q ^ 2 ∣ N - p`;
3. And at most one prime `q ∈ [z, y)` dividing `N - p`.
Then `omegaMult (N - p) ≤ 3`.
-/
theorem omegaMult_le_three_of_sieve_pinch {N z y p : ℕ}
    (hz2 : 2 ≤ z) (hzy : z ≤ y) (hy4 : N ≤ y ^ 4) (hzy3 : N ≤ z * y ^ 3)
    (hpN : p < N) (hp_prime : p.Prime) (hp_ndvd : ¬ p ∣ N)
    (hrough : ∀ r : ℕ, r.Prime → r < z → ¬ r ∣ N - p)
    (hsq : ∀ q ∈ midPrimes N z y, ¬ q ^ 2 ∣ N - p)
    (hmid : ((midPrimes N z y).filter (fun q => q ∣ N - p)).card ≤ 1) :
    omegaMult (N - p) ≤ 3 := by
  set m := N - p
  have hm_pos : 0 < m := Nat.sub_pos_of_lt hpN
  have hm_lt : m < N := Nat.sub_lt (lt_trans hp_prime.pos hpN) hp_prime.pos
  have hy1 : 1 ≤ y := le_trans (by omega) (le_trans hz2 hzy)
  set S := (midPrimes N z y).filter (fun q => q ∣ m)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hmid with h0 | h1
  · -- Zero prime divisors of `m` in `[z, y)`: all prime factors of `m` are `≥ y`.
    have hall : ∀ r : ℕ, r.Prime → r ∣ m → y ≤ r := by
      intro r hr hrm
      by_contra hlt
      push_neg at hlt
      have hrz : z ≤ r := by
        by_contra hltz
        push_neg at hltz
        exact hrough r hr hltz hrm
      have hrN : ¬ r ∣ N := not_dvd_of_dvd_sub hpN hp_prime hp_ndvd hr hrm
      have hr_mem : r ∈ S := by
        simp only [S, midPrimes, Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨⟨hrz, hlt⟩, hr, hrN⟩, hrm⟩
      rw [Finset.card_eq_zero] at h0
      simp [h0] at hr_mem
    have hm_lt_y4 : m < y ^ 4 := lt_of_lt_of_le hm_lt hy4
    have hlt4 := omegaMult_lt_of_lt_pow hm_pos hy1 hm_lt_y4 hall
    omega
  · -- Exactly one prime divisor `q ∈ [z, y)` of `m`, with `¬ q^2 ∣ m`.
    rcases Finset.card_eq_one.mp h1 with ⟨q, hSq⟩
    have hq_mem : q ∈ S := by
      rw [hSq]
      exact Finset.mem_singleton_self q
    have hq_mid : q ∈ midPrimes N z y := (Finset.mem_filter.mp hq_mem).1
    have hqm : q ∣ m := (Finset.mem_filter.mp hq_mem).2
    have hq_bounds : z ≤ q ∧ q < y := Finset.mem_Ico.mp (Finset.mem_filter.mp hq_mid).1
    have hq_prime : q.Prime := (Finset.mem_filter.mp hq_mid).2.1
    have hq_sq : ¬ q ^ 2 ∣ m := hsq q hq_mid
    rcases hqm with ⟨m', hm_eq⟩
    have hm'_pos : 0 < m' := by
      rcases Nat.eq_zero_or_pos m' with rfl | hpos
      · simp at hm_eq
        omega
      · exact hpos
    have hq_ndvd_m' : ¬ q ∣ m' := by
      intro hqm'
      apply hq_sq
      rcases hqm' with ⟨k, rfl⟩
      exact ⟨k, by rw [hm_eq]; ring⟩
    have hm'_ge_y : ∀ r : ℕ, r.Prime → r ∣ m' → y ≤ r := by
      intro r hr hrm'
      have hrm : r ∣ m := hm_eq ▸ dvd_mul_of_dvd_right hrm' q
      by_contra hlt
      push_neg at hlt
      have hrz : z ≤ r := by
        by_contra hltz
        push_neg at hltz
        exact hrough r hr hltz hrm
      have hrN : ¬ r ∣ N := not_dvd_of_dvd_sub hpN hp_prime hp_ndvd hr hrm
      have hrS : r ∈ S := by
        simp only [S, midPrimes, Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨⟨hrz, hlt⟩, hr, hrN⟩, hrm⟩
      rw [hSq, Finset.mem_singleton] at hrS
      subst hrS
      exact hq_ndvd_m' hrm'
    have hm_lt_zy3 : q * m' < q * y ^ 3 := by
      have h1 : q * m' < N := hm_eq ▸ hm_lt
      have h2 : z * y ^ 3 ≤ q * y ^ 3 := Nat.mul_le_mul_right (y ^ 3) hq_bounds.1
      exact lt_of_lt_of_le (lt_of_lt_of_le h1 hzy3) h2
    have hm'_lt_y3 : m' < y ^ 3 := (Nat.mul_lt_mul_left hq_prime.pos).mp hm_lt_zy3
    have hlt3 := omegaMult_lt_of_lt_pow hm'_pos hy1 hm'_lt_y3 hm'_ge_y
    rw [hm_eq, omegaMult_mul hq_prime.ne_zero hm'_pos.ne', omegaMult_prime hq_prime]
    omega

end BuchstabSwitching
