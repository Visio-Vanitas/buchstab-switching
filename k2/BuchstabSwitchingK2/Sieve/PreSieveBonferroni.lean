import BuchstabSwitching.Sieve.BonferroniHybrid
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Bilinear Bonferroni Pre-Sieve Indicator Bounds for `1 + 2`

Formalizes the hybrid pre-sieve indicator inequality combining Bonferroni-truncated
pre-sieving on `Q₀` (`α⁻ ≤ I₀ ≤ α⁺`) with linear sieve weights on `P'` (`β⁻ ≤ I₁ ≤ β⁺`):
- Pointwise lower and upper real bilinear inequalities (`bonf_bilinear_lower_real`,
  `bonf_bilinear_upper_real`),
- Summed indicator decomposition over a finite sifted set `I` with disjoint support sets
  `Q₀` and `P'` (`bilinear_presieve_sum_lower`, `bilinear_presieve_sum_upper`),
- Divisor-level multiplication bound `d₀ * d₁ ≤ D₀ * D₁` (`presieve_level_mul_le`).
-/

namespace BuchstabSwitchingK2

section PreSieveBonferroni

/-- Pointwise bilinear Bonferroni lower bound: for real numbers bounded above and below around
non-negative indicators `0 ≤ I₀, I₁`,
`α⁺ β⁻ + α⁻ β⁺ - α⁺ β⁺ ≤ I₀ I₁`. -/
theorem bonf_bilinear_lower_real
    {αm I₀ αp βm I₁ βp : ℝ}
    (hI₀_nn : 0 ≤ I₀) (hI₁_nn : 0 ≤ I₁)
    (hα_lo : αm ≤ I₀) (hα_hi : I₀ ≤ αp)
    (hβ_lo : βm ≤ I₁) (hβ_hi : I₁ ≤ βp) :
    αp * βm + αm * βp - αp * βp ≤ I₀ * I₁ := by
  have hαp_nn : 0 ≤ αp := le_trans hI₀_nn hα_hi
  have hβp_nn : 0 ≤ βp := le_trans hI₁_nn hβ_hi
  have hprod : 0 ≤ (αp - I₀) * (βp - I₁) :=
    mul_nonneg (sub_nonneg.mpr hα_hi) (sub_nonneg.mpr hβ_hi)
  have h1 : 0 ≤ αp * (I₁ - βm) := mul_nonneg hαp_nn (sub_nonneg.mpr hβ_lo)
  have h2 : 0 ≤ (I₀ - αm) * βp := mul_nonneg (sub_nonneg.mpr hα_lo) hβp_nn
  linarith

/-- Pointwise bilinear upper bound for non-negative indicators bounded above by `α⁺, β⁺`. -/
theorem bonf_bilinear_upper_real
    {I₀ αp I₁ βp : ℝ}
    (hI₀_nn : 0 ≤ I₀) (hI₁_nn : 0 ≤ I₁)
    (hα_hi : I₀ ≤ αp) (hβ_hi : I₁ ≤ βp) :
    I₀ * I₁ ≤ αp * βp := by
  exact mul_le_mul hα_hi hβ_hi hI₁_nn (le_trans hI₀_nn hα_hi)

/-- Bilinear weighted lower bound on a finite index set `I` with non-negative weights `a n`:
if `α⁻ n ≤ I₀ n ≤ α⁺ n` and `β⁻ n ≤ I₁ n ≤ β⁺ n` pointwise on `I`, then summing
`α⁺ β⁻ + α⁻ β⁺ - α⁺ β⁺` against `a` bounds `∑_{n ∈ I} a n * (I₀ n * I₁ n)` from below. -/
theorem bilinear_presieve_sum_lower
    (I : Finset ℕ) (a αm I₀ αp βm I₁ βp : ℕ → ℝ)
    (ha : ∀ n ∈ I, 0 ≤ a n)
    (hI₀_nn : ∀ n ∈ I, 0 ≤ I₀ n) (hI₁_nn : ∀ n ∈ I, 0 ≤ I₁ n)
    (hα_lo : ∀ n ∈ I, αm n ≤ I₀ n) (hα_hi : ∀ n ∈ I, I₀ n ≤ αp n)
    (hβ_lo : ∀ n ∈ I, βm n ≤ I₁ n) (hβ_hi : ∀ n ∈ I, I₁ n ≤ βp n) :
    ∑ n ∈ I, a n * (αp n * βm n + αm n * βp n - αp n * βp n) ≤
      ∑ n ∈ I, a n * (I₀ n * I₁ n) := by
  refine Finset.sum_le_sum fun n hn => ?_
  exact mul_le_mul_of_nonneg_left
    (bonf_bilinear_lower_real (hI₀_nn n hn) (hI₁_nn n hn)
      (hα_lo n hn) (hα_hi n hn) (hβ_lo n hn) (hβ_hi n hn))
    (ha n hn)

/-- Bilinear weighted upper bound on a finite index set `I` with non-negative weights `a n`. -/
theorem bilinear_presieve_sum_upper
    (I : Finset ℕ) (a I₀ αp I₁ βp : ℕ → ℝ)
    (ha : ∀ n ∈ I, 0 ≤ a n)
    (hI₀_nn : ∀ n ∈ I, 0 ≤ I₀ n) (hI₁_nn : ∀ n ∈ I, 0 ≤ I₁ n)
    (hα_hi : ∀ n ∈ I, I₀ n ≤ αp n) (hβ_hi : ∀ n ∈ I, I₁ n ≤ βp n) :
    ∑ n ∈ I, a n * (I₀ n * I₁ n) ≤ ∑ n ∈ I, a n * (αp n * βp n) := by
  refine Finset.sum_le_sum fun n hn => ?_
  exact mul_le_mul_of_nonneg_left
    (bonf_bilinear_upper_real (hI₀_nn n hn) (hI₁_nn n hn) (hα_hi n hn) (hβ_hi n hn))
    (ha n hn)

/-- Divisor-level multiplication bound for Bonferroni pre-sieved supports:
any `d₀ ≤ D₀` and `d₁ ≤ D₁` satisfy `d₀ * d₁ ≤ D₀ * D₁`. -/
theorem presieve_level_mul_le {d₀ D₀ d₁ D₁ : ℕ} (h₀ : d₀ ≤ D₀) (h₁ : d₁ ≤ D₁) :
    d₀ * d₁ ≤ D₀ * D₁ :=
  Nat.mul_le_mul h₀ h₁

end PreSieveBonferroni

end BuchstabSwitchingK2
