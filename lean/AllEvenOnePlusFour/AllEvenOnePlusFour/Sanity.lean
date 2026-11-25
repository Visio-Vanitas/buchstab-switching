import AllEvenOnePlusFour.Statement

/-!
# Sanity checks on the statement

These lemmas check that `AllEvenPrimePlusAlmostPrime` says what it is meant to say:

* it is monotone in `K`;
* it can be phrased with `Nat.primeFactorsList.length` or with Mathlib's
  `Nat.IsAtMostAlmostPrime`;
* `m = 1` is allowed (so `4 = 3 + 1` is a witness with `Ω m = 0`), yet the case `K = 0` is
  false (`10 - 1 = 9` is not prime);
* the bounded statement with `K = 1` (Goldbach) holds for `4 ≤ N ≤ 40`, with explicit witnesses.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.Omega

namespace AllEvenOnePlusFour

/-- `AllEvenPrimePlusAlmostPrime` is monotone in `K`. -/
theorem AllEvenPrimePlusAlmostPrime.mono {K L : ℕ} (hKL : K ≤ L)
    (h : AllEvenPrimePlusAlmostPrime K) : AllEvenPrimePlusAlmostPrime L := by
  intro N hN hev
  obtain ⟨p, m, hp, hm, hNpm, hΩ⟩ := h N hN hev
  exact ⟨p, m, hp, hm, hNpm, hΩ.trans hKL⟩

/-- The statement with `Ω m` spelled as the length of the list of prime factors. -/
theorem allEvenPrimePlusAlmostPrime_iff_primeFactorsList {K : ℕ} :
    AllEvenPrimePlusAlmostPrime K ↔ ∀ N : ℕ, 4 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ m.primeFactorsList.length ≤ K := by
  simp only [AllEvenPrimePlusAlmostPrime, cardFactors_apply]

/-- The statement with Mathlib's predicate `Nat.IsAtMostAlmostPrime K m`
(`m ≠ 0 ∧ Ω m ≤ K`). -/
theorem allEvenPrimePlusAlmostPrime_iff_isAtMostAlmostPrime {K : ℕ} :
    AllEvenPrimePlusAlmostPrime K ↔ ∀ N : ℕ, 4 ≤ N → Even N →
      ∃ p m : ℕ, p.Prime ∧ Nat.IsAtMostAlmostPrime K m ∧ N = p + m := by
  constructor
  · intro h N hN hev
    obtain ⟨p, m, hp, hm, hNpm, hΩ⟩ := h N hN hev
    exact ⟨p, m, hp, ⟨hm.ne', hΩ⟩, hNpm⟩
  · intro h N hN hev
    obtain ⟨p, m, hp, ⟨hm, hΩ⟩, hNpm⟩ := h N hN hev
    exact ⟨p, m, hp, Nat.pos_of_ne_zero hm, hNpm, hΩ⟩

/-- The subtlety `m = 1`: `4 = 3 + 1` is an admissible decomposition with `Ω 1 = 0`. -/
theorem four_eq_prime_add_one :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ 4 = p + m ∧ Ω m ≤ 0 :=
  ⟨3, 1, by norm_num, by norm_num, rfl, by simp⟩

/-- The case `K = 0` is false: it would force `10 = p + 1`, but `9` is not prime.
So the definition is not vacuous. -/
theorem not_allEvenPrimePlusAlmostPrime_zero : ¬ AllEvenPrimePlusAlmostPrime 0 := by
  intro h
  obtain ⟨p, m, hp, hm, h10, hΩ⟩ := h 10 (by norm_num) ⟨5, rfl⟩
  have hm01 : m = 0 ∨ m = 1 := cardFactors_eq_zero_iff_eq_zero_or_one.mp (Nat.le_zero.mp hΩ)
  have hm1 : m = 1 := by omega
  subst hm1
  have hp9 : p = 9 := by omega
  subst hp9
  norm_num at hp

/-- Goldbach for `4 ≤ N ≤ 40`, with explicit witnesses checked by `norm_num`. -/
theorem goldbach_of_le_forty : ∀ N : ℕ, 4 ≤ N → N ≤ 40 → Even N →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N = p + q := by
  intro N h4 h40 hev
  obtain ⟨k, rfl⟩ := hev
  have hk2 : 2 ≤ k := by omega
  have hk20 : k ≤ 20 := by omega
  interval_cases k
  · exact ⟨2, 2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 3, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 5, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 7, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 7, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 11, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 13, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 13, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 17, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 19, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 19, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 23, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 23, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 23, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 29, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 31, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 31, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 31, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 37, by norm_num, by norm_num, by norm_num⟩

/-- The bounded form of `AllEvenPrimePlusAlmostPrime 1` for `4 ≤ N ≤ 40`. -/
theorem primePlusAlmostPrime_one_of_le_forty : ∀ N : ℕ, 4 ≤ N → N ≤ 40 → Even N →
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ N = p + m ∧ Ω m ≤ 1 := by
  intro N h4 h40 hev
  obtain ⟨p, q, hp, hq, hN⟩ := goldbach_of_le_forty N h4 h40 hev
  exact ⟨p, q, hp, hq.pos, hN, (cardFactors_apply_prime hq).le⟩

end AllEvenOnePlusFour
