import BuchstabSwitching.Sieve.BuchstabFunctions
import BuchstabSwitching.Sieve.LinearSieveInduction
import Mathlib.Tactic

/-!
# Buchstab Series Identities for `F(s)` and `f(s)` (`DelayDiffEqIdentity`)

Defines `BuchstabSeriesPremise`, the external analytic premise asserting the infinite series
representations of the Buchstab upper and lower functions `buchstabF cBuchstab s` (`F(s)`) and
`buchstabf cBuchstab s` (`f(s)`) in terms of the Jurkat–Richert iterated error integrals
`BuchstabSwitching.fHat n s`:

- `F(s) = 1 + ∑_{k = 0}^∞ fHat (2k + 1) s` for `s ≥ 1`
- `f(s) = 1 - ∑_{k = 0}^∞ fHat (2(k + 1)) s` for `s ≥ 2`

Literature references:
- M. B. Nathanson, *Additive Number Theory: The Classical Bases*, Graduate Texts in Mathematics
  164, Springer, 1996, Chapter 9, Theorem 9.4.
- M. Bordignon, D. R. Johnston, V. Starichkova, *An explicit version of Chen's theorem and the
  linear sieve*, Int. J. Number Theory 21 (2025), no. 10, 2497–2572 (`arXiv:2207.09452v6`), §2.1,
  formulas `bigFdeffn` and `lilFdeffn` (noting that the printed `n odd` in `lilFdeffn` line 461
  of `arXiv:2207.09452v6` is a TeX typo for `n even`, as used in Proposition 13 `theo:G`).

Also provides finite-truncation corollaries bridging `BuchstabSeriesPremise` directly to the
hypotheses of `LinearSieveInduction.finite_buchstab_lower_bound` and
`LinearSieveInduction.finite_buchstab_upper_bound`.
-/

namespace BuchstabSwitching.External

/-- External analytic premise for the Buchstab delay-differential series identities
(Nathanson Ch. 9 Theorem 9.4; Bordignon–Johnston–Starichkova `arXiv:2207.09452v6` §2.1,
`bigFdeffn` and `lilFdeffn`):
- For `1 ≤ s`, `∑_{k=0}^∞ fHat (2 * k + 1) s = buchstabF cBuchstab s - 1`;
- For `2 ≤ s`, `∑_{k=0}^∞ fHat (2 * (k + 1)) s = 1 - buchstabf cBuchstab s`. -/
def BuchstabSeriesPremise : Prop :=
  (∀ s : ℝ, 1 ≤ s →
    HasSum (fun k : ℕ => BuchstabSwitching.fHat (2 * k + 1) s)
      (BuchstabSwitching.buchstabF BuchstabSwitching.cBuchstab s - 1)) ∧
  (∀ s : ℝ, 2 ≤ s →
    HasSum (fun k : ℕ => BuchstabSwitching.fHat (2 * (k + 1)) s)
      (1 - BuchstabSwitching.buchstabf BuchstabSwitching.cBuchstab s))

/-- Odd-index `HasSum` identity for `buchstabF cBuchstab s - 1` when `1 ≤ s`. -/
theorem BuchstabSeriesPremise.hasSum_odd (h : BuchstabSeriesPremise) {s : ℝ} (hs : 1 ≤ s) :
    HasSum (fun k : ℕ => BuchstabSwitching.fHat (2 * k + 1) s)
      (BuchstabSwitching.buchstabF BuchstabSwitching.cBuchstab s - 1) :=
  h.1 s hs

/-- Even-index `HasSum` identity for `1 - buchstabf cBuchstab s` when `2 ≤ s`. -/
theorem BuchstabSeriesPremise.hasSum_even (h : BuchstabSeriesPremise) {s : ℝ} (hs : 2 ≤ s) :
    HasSum (fun k : ℕ => BuchstabSwitching.fHat (2 * (k + 1)) s)
      (1 - BuchstabSwitching.buchstabf BuchstabSwitching.cBuchstab s) :=
  h.2 s hs

/-- Finite-truncation lower bridge: for `2 ≤ s` and any `K_even : ℕ`,
`buchstabf cBuchstab s ≤ 1 - ∑ k ∈ Finset.Icc 1 K_even, fHat (2 * k) s`. -/
theorem BuchstabSeriesPremise.buchstabf_le_one_sub_sum (h : BuchstabSeriesPremise)
    {s : ℝ} (hs : 2 ≤ s) (K_even : ℕ) :
    BuchstabSwitching.buchstabf BuchstabSwitching.cBuchstab s ≤
      1 - ∑ k ∈ Finset.Icc 1 K_even, BuchstabSwitching.fHat (2 * k) s :=
  BuchstabSwitching.buchstabf_le_one_sub_sum_fHat_of_hasSum (h.hasSum_even hs)

/-- Finite-truncation upper bridge: for `1 ≤ s` and any `K_odd : ℕ`,
`1 + ∑ k ∈ Finset.range K_odd, fHat (2 * k + 1) s ≤ buchstabF cBuchstab s`. -/
theorem BuchstabSeriesPremise.one_add_sum_le_buchstabF (h : BuchstabSeriesPremise)
    {s : ℝ} (hs : 1 ≤ s) (K_odd : ℕ) :
    1 + ∑ k ∈ Finset.range K_odd, BuchstabSwitching.fHat (2 * k + 1) s ≤
      BuchstabSwitching.buchstabF BuchstabSwitching.cBuchstab s :=
  BuchstabSwitching.one_add_sum_fHat_le_buchstabF_of_hasSum (h.hasSum_odd hs)

end BuchstabSwitching.External
