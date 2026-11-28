import OnePlusOne.Core.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Isolated External Analytic Premises for `OnePlusOne`

All external analytic inputs sit here explicitly as `Prop` structures (zero `axiom` declarations),
matching the convention of `k3/`, `k2/`, and `1+a/` and mirrored verbatim in `comparator/`.
-/

namespace OnePlusOne.External

/-- **Theorem 1A Parseval–Laplace Input (GRH-conditional):**
Under `DirichletLNonvanishingRightOfHalf`, the Laplace-smoothed circle-method decomposition at
`Q₀ = ⌊(1/2)√Y⌋` certifies `E(Y) - E(Y/2) ≤ 3728.72 * √Y * (log Y)^3` for all `Y ≥ 4 * 10^18`
(verified across `[4 * 10^18, 10^10000]` + asymptotic tail in `scripts/certify_exceptional_short.py`). -/
def DyadicLaplaceCirclePremise : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ Y : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ Y →
      (exceptionalCount Y : ℝ) - (exceptionalCount (Y / 2) : ℝ) ≤
        (372872 / 100 : ℝ) * Real.sqrt Y * (Real.log Y) ^ 3

/-- **Theorem 1B Fejér–Mellin Short-Interval Input (RH-conditional):**
Under `RiemannHypothesis`, the Fejér triangle weight `W(n)` and Laplace sum `S(α)` on
`[X, X + 6281 * (log X)^2]` satisfy strict positivity of the Goldbach weighted sum for all
`X ≥ 4 * 10^18` (via `C_Sel ≤ 78.04`, verified in `scripts/certify_exceptional_short.py`). -/
def FejerShortIntervalPositivityPremise : Prop :=
  RiemannHypothesis →
    ∀ X : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ X →
      ∃ W : ℕ → ℝ, (∀ N, 0 ≤ W N) ∧
        0 < ∑ N ∈ Finset.Icc (Nat.ceil X) (Nat.floor (X + 6281 * (Real.log X) ^ 2)),
          W N * goldbachIndicator N

/-- **Theorem 3 Circle-Method Input above the Binary Goldbach Bridge (GRH-conditional):**
Under `DirichletLNonvanishingRightOfHalf`, for every even `N > (2^23 - 2) * 2^61 + 4 * 10^18`
(`≈ 1.93428e25`), the smoothed circle-method representation integral at `r = 22` is strictly positive,
hence `HasExactPosLinnikRep 22 N` holds (verified across `L ∈ [79, 139]` + uniform tail `L ≥ 140`
with Bessel growth/step `0.910613 < 1` in `scripts/certify_linnik_r.py`). -/
def LinnikCircleAboveBridgePremise : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ N : ℕ, ((2 ^ 23 - 2) * 2 ^ 61 + 4 * 10 ^ 18) < N → Even N →
      HasExactPosLinnikRep 22 N

/-- Combined analytic premises for `1+1/` Theorems 1A, 1B, and 3. -/
structure OnePlusOnePremises : Prop where
  empirical : EmpiricalGoldbachBase
  dyadicLaplace : DyadicLaplaceCirclePremise
  fejerShort : FejerShortIntervalPositivityPremise
  linnikCircle : LinnikCircleAboveBridgePremise

end OnePlusOne.External
