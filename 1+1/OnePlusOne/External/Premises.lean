import OnePlusOne.Core.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Isolated External Analytic Premises for `OnePlusOne`

All external analytic inputs sit here explicitly as `Prop` structures (zero `axiom` declarations),
matching the convention of `k3/`, `k2/`, and `1+a/` and mirrored verbatim in `comparator/`.
-/

namespace OnePlusOne.External

/-- **Theorem 1A v2 Parseval–Laplace 4-adic Input (GRH-conditional):**
Under `DirichletLNonvanishingRightOfHalf`, the v2 Laplace-smoothed circle-method decomposition
on 4-adic shells `(Y/4, Y]` (with `κ = 11/20`, `Q₀ = ⌊3 Z^{1/4}⌋`, `Q_D = ⌊√Z⌋`, BMOR zero-counting,
Binet vertical contour shift, and zero-black-box `C_E2 ≤ 28.0916`) certifies
`E(Y) - E(Y/4) ≤ (777 / 100) * √Y * (log Y)^3` for all `Y ≥ 4 * 10^18`
(verified across `[4 * 10^18, 10^10000]` + asymptotic tail in `scripts/certify_exceptional_short.py`). -/
def FouradicLaplaceCirclePremise : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ Y : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ Y →
      (exceptionalCount Y : ℝ) - (exceptionalCount (Y / 4) : ℝ) ≤
        (777 / 100 : ℝ) * Real.sqrt Y * (Real.log Y) ^ 3

/-- **Theorem 1B v2 Averaged Fejér–Mellin Short-Interval Input (RH-conditional):**
Under `RiemannHypothesis`, the averaged sharp-cutoff Fejér weight `W̃(n)` on
`[X, X + 8 * (log X)^2]` (at `ε = 1/4`, Bochner-optimal zero-density kernel, exact closed-form
Mellin moments, and Fatou's Lemma with zero black-box buffers) satisfies strict positivity of the
Goldbach weighted sum for all `X ≥ 4 * 10^18` (`C_J ≤ 1.76`, verified in
`scripts/certify_exceptional_short.py`). -/
def FejerShortIntervalPositivityPremise : Prop :=
  RiemannHypothesis →
    ∀ X : ℝ, ((4 * 10 ^ 18 : ℕ) : ℝ) ≤ X →
      ∃ W : ℕ → ℝ, (∀ N, 0 ≤ W N) ∧
        0 < ∑ N ∈ Finset.Icc (Nat.ceil X) (Nat.floor (X + 8 * (Real.log X) ^ 2)),
          W N * goldbachIndicator N

/-- **Theorem 3 v2 Circle-Method Input above the Binary Goldbach Bridge (GRH-conditional):**
Under `DirichletLNonvanishingRightOfHalf`, for every even `N > (2^19 - 2) * 2^61 + 4 * 10^18`
(`≈ 1.208925e24`), the v2 `sin^2(πt/N)` circle-method representation integral at `K = 18`
(zero black-box buffers, `C_E2 ≤ 31.3259`, 16-direction transfer automaton + Abel layer-cake)
is strictly positive, hence `HasExactPosLinnikRep 18 N` holds (verified across `L ∈ [76, 119]` +
pure Collatz–Wielandt uniform tail `L ≥ 120` in `scripts/certify_linnik_r.py`). -/
def LinnikCircleAboveBridgePremise : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ N : ℕ, ((2 ^ 19 - 2) * 2 ^ 61 + 4 * 10 ^ 18) < N → Even N →
      HasExactPosLinnikRep 18 N

/-- Combined analytic premises for `1+1/` Theorems 1A (v2), 1B (v2), and 3 (v2). -/
structure OnePlusOnePremises : Prop where
  empirical : EmpiricalGoldbachBase
  fouradicLaplace : FouradicLaplaceCirclePremise
  fejerShort : FejerShortIntervalPositivityPremise
  linnikCircle : LinnikCircleAboveBridgePremise

end OnePlusOne.External
