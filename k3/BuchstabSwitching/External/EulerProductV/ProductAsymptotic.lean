import BuchstabSwitching.External.CharacterSums.DirichletGRH
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Asymptotic Euler-Product Estimate for `V_N(z)`

Defines the shifted-prime Euler product `VN N z`, the relative-error envelopes `deltaV_bjs`
(unconditional, Bordignon–Johnston–Starichkova `arXiv:2207.09452v6`, Lemma 38 `vjlem`) and
`deltaV_bs` (under GRH, Bordignon–Starichkova `arXiv:2211.08844v1`, Lemma 11 `vjlem`, matching
`k3/scripts/sieve_cert/regime_asymptotic.py` lines 76–81), the divisor-adjustment product
`UN_ratio U_c N`, and the corresponding premise interfaces `EulerProductVPremise` and
`EulerProductVGRHPremise`.

## Notes on Conventions
* `U_c` denotes `2 * ∏_{p > 2} (1 - 1 / (p - 1)^2)` (`U_CONST` in `constants.py`), and
  `eNegGamma` denotes `exp (-γ)` (`E_NEG_GAMMA` in `constants.py`), so `eNegGamma * UN_ratio U_c N`
  is `U_N` in BJS Lemma 38 / BS Lemma 11 (using the corrected `2 e^{-γ}` factor, fixing BS v1
  Lemma 11's `2 e^γ` typo).
* `Even N` (`2 ∣ N`) is required in the asymptotic premises because `VN` filters `¬ p ∣ N`; for
  odd `N` and `z > 2`, the prime `p = 2` enters the product with factor `1 - 1 / (2 - 1) = 0`,
  forcing `VN N z = 0`.
-/

namespace BuchstabSwitching.External

/-- Shifted-prime Euler product `V_N(z) = ∏_{p < z, p ∤ N} (1 - 1 / (p - 1))`. -/
noncomputable def VN (N z : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range z).filter (fun p => p.Prime ∧ ¬ p ∣ N),
    (1 - 1 / ((p : ℝ) - 1))

/-- Unconditional relative error envelope `δ_V(N, x)` from BJS (`arXiv:2207.09452v6`, Lemma 38
`vjlem`) for `x ≥ 285` and `N ≥ 3`:
`(1 + θ₁ f₁)(1 + θ₂ f₂)(1 + θ₃ f₃)` with `|θᵢ| ≤ 1`, bounded symmetrically by
`max (1 - (1 - f₁)(1 - f₂)(1 - f₃)) ((1 + f₁)(1 + f₂)(1 + f₃) - 1)`. -/
noncomputable def deltaV_bjs (N : ℕ) (x : ℝ) : ℝ :=
  let f1 := (1.45 : ℝ) * (Real.log N / (x - 1)) * (1 + 10 * Real.log (Real.log N) / Real.log N)
  let f2 := (1.002 : ℝ) / (x - 3)
  let f3 := (1 : ℝ) / (2 * (Real.log x) ^ 2)
  let d_lo := 1 - (1 - f1) * (1 - f2) * (1 - f3)
  let d_hi := (1 + f1) * (1 + f2) * (1 + f3) - 1
  max d_lo d_hi

/-- GRH relative error envelope `δ_V(N, x)` from BS (`arXiv:2211.08844v1`, Lemma 11 `vjlem`,
implemented in `k3/scripts/sieve_cert/regime_asymptotic.py` lines 76–81) for `x ≥ 8` and `N ≥ 3`:
`(1 + θ₁ f₁)(1 + θ₂ f₂)(1 + θ₃ f₃)(1 + θ₄ f₄)` with `|θᵢ| ≤ 1`, where
`f₁ = (3 log x + 5) / (8 π √x)`, `f₂ = 2 / x`, `f₃ = 8 log N / x`, `f₄ = 1 / (x - 1)`. -/
noncomputable def deltaV_bs (N : ℕ) (x : ℝ) : ℝ :=
  let f1 := (3 * Real.log x + 5) / (8 * Real.pi * Real.sqrt x)
  let f2 := (2 : ℝ) / x
  let f3 := (8 * Real.log N) / x
  let f4 := (1 : ℝ) / (x - 1)
  let d_lo := 1 - (1 - f1) * (1 - f2) * (1 - f3) * (1 - f4)
  let d_hi := (1 + f1) * (1 + f2) * (1 + f3) * (1 + f4) - 1
  max d_lo d_hi

/-- Divisor-adjusted constant `U_c * ∏_{p > 2, p ∣ N} (p - 1) / (p - 2)`. When `U_c = 2 * C₂`,
`eNegGamma * UN_ratio U_c N` equals `U_N` in BJS Lemma 38 / BS Lemma 11. -/
noncomputable def UN_ratio (U_c : ℝ) (N : ℕ) : ℝ :=
  U_c * ∏ p ∈ N.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2)

/-- Unconditional Euler-product asymptotic premise for `V_N(⌈x⌉)` (BJS Lemma 38):
for all even `N ≥ 3` and all `x ≥ 285`, `V_N(⌈x⌉)` lies within relative error `deltaV_bjs N x` of
`eNegGamma * UN_ratio U_c N / log x`. -/
def EulerProductVPremise (U_c eNegGamma : ℝ) : Prop :=
  ∀ (N : ℕ), Even N → 3 ≤ N → ∀ (x : ℝ), 285 ≤ x →
    (1 - deltaV_bjs N x) * (eNegGamma * UN_ratio U_c N) / Real.log x ≤ VN N (Nat.ceil x) ∧
      VN N (Nat.ceil x) ≤ (1 + deltaV_bjs N x) * (eNegGamma * UN_ratio U_c N) / Real.log x

/-- GRH Euler-product asymptotic premise for `V_N(⌈x⌉)` (BS Lemma 11 / `regime_asymptotic.py`):
under `DirichletLNonvanishingRightOfHalf`, for all even `N ≥ 3` and all `x ≥ 8`, `V_N(⌈x⌉)` lies
within relative error `deltaV_bs N x` of `eNegGamma * UN_ratio U_c N / log x` (where
`eNegGamma * UN_ratio U_c N` explicitly uses the corrected factor `2 e^{-γ}`, fixing BS v1
Lemma 11's `2 e^γ` typo). -/
def EulerProductVGRHPremise (U_c eNegGamma : ℝ) : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ (N : ℕ), Even N → 3 ≤ N → ∀ (x : ℝ), 8 ≤ x →
      (1 - deltaV_bs N x) * (eNegGamma * UN_ratio U_c N) / Real.log x ≤ VN N (Nat.ceil x) ∧
        VN N (Nat.ceil x) ≤ (1 + deltaV_bs N x) * (eNegGamma * UN_ratio U_c N) / Real.log x

/-- For `0 < U_c`, the divisor adjustment never decreases `U_c`, i.e., `U_c ≤ UN_ratio U_c N`. -/
theorem UN_ratio_ge_Uc {U_c : ℝ} {N : ℕ} (hUc : 0 < U_c) :
    U_c ≤ UN_ratio U_c N := by
  unfold UN_ratio
  have hprod : (1 : ℝ) ≤ ∏ p ∈ N.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    refine Finset.one_le_prod₀ ?_
    intro p hp
    have hp2 : 2 < p := (Finset.mem_filter.mp hp).2
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp2
    have hden_pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    rw [one_le_div hden_pos]
    linarith
  exact le_mul_of_one_le_right hUc.le hprod

private lemma factor_mem_Icc {p : ℕ} (hp : p.Prime) :
    0 ≤ 1 - 1 / ((p : ℝ) - 1) ∧ 1 - 1 / ((p : ℝ) - 1) ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hden_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hnonneg : 0 ≤ 1 / ((p : ℝ) - 1) := div_nonneg zero_le_one hden_pos.le
  have hle : 1 / ((p : ℝ) - 1) ≤ 1 := by
    rw [div_le_one hden_pos]
    linarith
  exact ⟨by linarith, by linarith⟩

/-- Every factor in `VN N z` lies in `[0, 1]`, so `0 ≤ VN N z`. -/
theorem VN_nonneg (N z : ℕ) : 0 ≤ VN N z :=
  Finset.prod_nonneg fun _ hp => (factor_mem_Icc ((Finset.mem_filter.mp hp).2).1).1

/-- For even `N`, `p = 2` is excluded from `VN N z`, so `0 < VN N z`. -/
theorem VN_pos_of_even {N : ℕ} (z : ℕ) (hN : Even N) : 0 < VN N z := by
  unfold VN
  refine Finset.prod_pos fun p hp => ?_
  have hmem := (Finset.mem_filter.mp hp).2
  have hp_ne_two : p ≠ 2 := by
    rintro rfl
    exact hmem.2 (even_iff_two_dvd.mp hN)
  have hp3 : (3 : ℝ) ≤ p := by
    exact_mod_cast lt_of_le_of_ne hmem.1.two_le hp_ne_two.symm
  have hden_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hlt : 1 / ((p : ℝ) - 1) < 1 := by
    rw [div_lt_one hden_pos]
    linarith
  linarith

/-- Every factor in `VN N z` is at most `1`, so `VN N z ≤ 1`. -/
theorem VN_le_one (N z : ℕ) : VN N z ≤ 1 :=
  Finset.prod_le_one₀
    (fun _ hp => (factor_mem_Icc ((Finset.mem_filter.mp hp).2).1).1)
    (fun _ hp => (factor_mem_Icc ((Finset.mem_filter.mp hp).2).1).2)

end BuchstabSwitching.External
