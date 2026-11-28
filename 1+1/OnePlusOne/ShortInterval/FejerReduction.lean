import OnePlusOne.Core.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Fejér Short-Interval Reduction (`OnePlusOne.ShortInterval.FejerReduction`)

Complete Mathlib proofs of:
1. `short_interval_small_range`: for every `X ∈ [4, 4 * 10^18)`, the interval `[X, X + 6281 * (log X)^2]`
   contains an even integer `N ∈ [4, 4 * 10^18]` (since `log 4 > 1`, so `6281 * (log X)^2 ≥ 2`),
   hence `IsGoldbachEven N` follows directly from `EmpiricalGoldbachBase`.
2. `exists_goldbach_of_fejer_pos`: if a nonnegatively weighted sum of Goldbach prime-pair counts
   over `N ∈ [⌈X⌉₊, ⌊X + H⌋₊]` is strictly positive, then `[X, X + H]` contains an `IsGoldbachEven N`.
3. `short_interval_all_range`: seamless union of `[4, 4 * 10^18)` and `[4 * 10^18, ∞)`.
-/

namespace OnePlusOne.ShortInterval

open scoped BigOperators

/-- Unconditional lower bound `1 < Real.log 4`, giving `6281 * (log X)^2 ≥ 2` for `X ≥ 4`. -/
theorem one_lt_log_four : (1 : ℝ) < Real.log 4 := by
  have he : Real.exp 1 < 4 := (Real.exp_one_lt_d9).trans (by norm_num)
  exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr he

/-- Every `X ∈ [4, 4 * 10^18)` has an even Goldbach integer in `[X, X + C₁ (log X)^2]` whenever `C₁ ≥ 2`. -/
theorem short_interval_small_range
    (hbase : EmpiricalGoldbachBase) {C₁ : ℝ} (hC₁ : 2 ≤ C₁)
    {X : ℝ} (hX4 : 4 ≤ X) (hXlt : X < ((4 * 10 ^ 18 : ℕ) : ℝ)) :
    ∃ N : ℕ, X ≤ (N : ℝ) ∧ (N : ℝ) ≤ X + C₁ * (Real.log X) ^ 2 ∧ IsGoldbachEven N := by
  have hlog : 1 < Real.log X := one_lt_log_four.trans_le (Real.log_le_log (by norm_num) hX4)
  have hlen : 2 ≤ C₁ * (Real.log X) ^ 2 := by
    have hsq : 1 ≤ (Real.log X) ^ 2 := by nlinarith
    nlinarith
  let m : ℕ := Nat.ceil X
  have hm_ge : X ≤ (m : ℝ) := Nat.le_ceil X
  have hm_lt : (m : ℝ) < X + 1 := Nat.ceil_lt_add_one (by linarith)
  have hm_ge4 : 4 ≤ m := by exact_mod_cast (hX4.trans hm_ge)
  by_cases hm_ev : Even m
  · refine ⟨m, hm_ge, by linarith, hbase m hm_ge4 ?_ hm_ev⟩
    by_cases hcap : m ≤ 4 * 10 ^ 18
    · exact hcap
    · exfalso
      have hle : 4 * 10 ^ 18 < m := Nat.lt_of_not_ge hcap
      -- Actually since `X < 4 * 10^18` (an integer!), `⌈X⌉₊ ≤ 4 * 10^18` ALWAYS!
      have hceil_le : m ≤ 4 * 10 ^ 18 := Nat.ceil_le.mpr hXlt.le
      omega
  · let N : ℕ := m + 1
    have hN_ev : Even N := by
      rw [Nat.even_iff] at hm_ev ⊢
      omega
    have hN_ge : X ≤ (N : ℝ) := by push_cast [N]; linarith
    have hN_le : (N : ℝ) ≤ X + C₁ * (Real.log X) ^ 2 := by push_cast [N]; linarith
    have hN_ge4 : 4 ≤ N := by omega
    have hm_le_bound : m ≤ 4 * 10 ^ 18 := Nat.ceil_le.mpr hXlt.le
    have hN_le_bound : N ≤ 4 * 10 ^ 18 := by
      -- Since `m ≤ 4 * 10^18` and `¬ Even m` while `Even (4 * 10^18)`, `m < 4 * 10^18`!
      have hEvenTop : Even (4 * 10 ^ 18 : ℕ) := by decide
      have hm_ne : m ≠ 4 * 10 ^ 18 := fun he => hm_ev (he ▸ hEvenTop)
      omega
    exact ⟨N, hN_ge, hN_le, hbase N hN_ge4 hN_le_bound hN_ev⟩

/-- Existence of an even Goldbach integer in `[X, X + H]` from positivity of any nonnegative
weighted sum over `[⌈X⌉₊, ⌊X + H⌋₊]`. -/
theorem exists_goldbach_of_weighted_pos
    {X H : ℝ} (hX : 4 ≤ X) (_hH : 0 ≤ H)
    (W : ℕ → ℝ) (_hW : ∀ N, 0 ≤ W N)
    (hpos : 0 < ∑ N ∈ Finset.Icc (Nat.ceil X) (Nat.floor (X + H)),
      W N * goldbachIndicator N) :
    ∃ N : ℕ, X ≤ (N : ℝ) ∧ (N : ℝ) ≤ X + H ∧ IsGoldbachEven N := by
  obtain ⟨N, hNmem, hNne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  rw [Finset.mem_Icc] at hNmem
  have hG : IsGoldbachEven N := by
    by_contra hng
    apply hNne
    rw [goldbachIndicator_eq_zero_of_not hng, mul_zero]
  have hNX : X ≤ (N : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast hNmem.1)
  have hNXH : (N : ℝ) ≤ X + H := (by exact_mod_cast hNmem.2 : (N : ℝ) ≤ Nat.floor (X + H)).trans
    (Nat.floor_le (by linarith))
  exact ⟨N, hNX, hNXH, hG⟩

/-- **All-Range Short-Interval Goldbach Theorem** (`[X, X + 6281 * (log X)^2]`, `∀ X ≥ 4`). -/
theorem short_interval_all_range
    (hbase : EmpiricalGoldbachBase)
    (hlarge : ∀ X : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ X →
      ∃ N : ℕ, X ≤ (N : ℝ) ∧ (N : ℝ) ≤ X + 6281 * (Real.log X) ^ 2 ∧ IsGoldbachEven N) :
    ShortIntervalProp 6281 2 := by
  intro X hX4
  by_cases hsmall : X < ((4 * 10 ^ 18 : ℕ) : ℝ)
  · exact short_interval_small_range hbase (by norm_num) hX4 hsmall
  · exact hlarge X (le_of_not_gt hsmall)

end OnePlusOne.ShortInterval
