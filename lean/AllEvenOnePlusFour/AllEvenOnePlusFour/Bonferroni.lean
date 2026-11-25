import Mathlib

/-!
# Truncated inclusion–exclusion (the note, §2, Lemma 1)

The proof of Lemma 1 of the note is the identity, for `k ≥ 1`,

  `∑_{j ≤ m} (-1)^j C(k, j) = (-1)^m C(k - 1, m)`,

which is in Mathlib as `Int.alternating_sum_range_choose_eq_choose` (stated for `k = n + 1`).
From it we get the Bonferroni signs: the truncated sum is `≤ 1[k = 0]` for `m` odd and
`≥ 1[k = 0]` for `m` even. Applied with `k = ω_{P₂'}(n)` this is exactly the statement
"`∑_{d ∣ n} λ_d` is `≤ 1[(n, P(z)) = 1]` for `m` odd and `≥` for `m` even" of Lemma 1.

The passage from the Möbius-weight sum `∑_{d ∣ n} μ(d) 1[ω_{P₂'}(d) ≤ m]` to the binomial sum
(counting subsets of the prime divisors of `n` by size) is not formalised here: the reduction
in `Reduction.lean` takes the positivity of the weighted sum as its hypothesis, so it does not
depend on this file. This file certifies the sign lemma that the certificate script relies on.
-/

open Finset

namespace AllEvenOnePlusFour

/-- Truncated alternating binomial sum, in the form of the note:
for `k ≥ 1`, `∑_{j ≤ m} (-1)^j C(k, j) = (-1)^m C(k - 1, m)`.
This is Mathlib's `Int.alternating_sum_range_choose_eq_choose`. -/
theorem truncated_alternating_sum_choose {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    ∑ j ∈ range (m + 1), ((-1) ^ j * k.choose j : ℤ) = (-1) ^ m * ((k - 1).choose m : ℤ) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact Int.alternating_sum_range_choose_eq_choose

/-- The truncated sum for `k = 0` is `1`. -/
theorem truncated_alternating_sum_choose_zero (m : ℕ) :
    ∑ j ∈ range (m + 1), ((-1) ^ j * (0 : ℕ).choose j : ℤ) = 1 := by
  rw [sum_range_succ']
  simp

/-- **Bonferroni, odd order.** For `m` odd, `∑_{j ≤ m} (-1)^j C(k, j) ≤ 1[k = 0]`. -/
theorem truncated_alternating_sum_choose_le_of_odd (k : ℕ) {m : ℕ} (hm : Odd m) :
    ∑ j ∈ range (m + 1), ((-1) ^ j * k.choose j : ℤ) ≤ if k = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact (truncated_alternating_sum_choose_zero m).le.trans (by simp)
  · rw [truncated_alternating_sum_choose hk, hm.neg_one_pow, if_neg hk.ne']
    have h0 : (0 : ℤ) ≤ ((k - 1).choose m : ℤ) := Nat.cast_nonneg _
    linarith

/-- **Bonferroni, even order.** For `m` even, `1[k = 0] ≤ ∑_{j ≤ m} (-1)^j C(k, j)`. -/
theorem le_truncated_alternating_sum_choose_of_even (k : ℕ) {m : ℕ} (hm : Even m) :
    (if k = 0 then 1 else 0) ≤ ∑ j ∈ range (m + 1), ((-1) ^ j * k.choose j : ℤ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact (by simp : (if (0 : ℕ) = 0 then (1 : ℤ) else 0) ≤ 1).trans
      (truncated_alternating_sum_choose_zero m).ge
  · rw [truncated_alternating_sum_choose hk, hm.neg_one_pow, if_neg hk.ne']
    have h0 : (0 : ℤ) ≤ ((k - 1).choose m : ℤ) := Nat.cast_nonneg _
    linarith

end AllEvenOnePlusFour
