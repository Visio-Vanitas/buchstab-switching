import BuchstabSwitching.External.RobinOmega.Basic
import BuchstabSwitching.External.RobinOmega.Reduction
import BuchstabSwitching.External.RobinOmega.ChebyshevLower
import BuchstabSwitching.External.RobinOmega.Asymptotic
import BuchstabSwitching.External.RobinOmega.FiniteCheck

/-!
# Robin's Upper Bound on `ω(N)` (`robinOmegaBound_holds`)

Re-exports the interface and monotonicity lemmas from `RobinOmega.Basic` and discharges
`RobinOmegaBound` unconditionally (`theorem robinOmegaBound_holds : RobinOmegaBound`,
Guy Robin, *Acta Arithmetica* **42** (1983), Théorème 11): for every natural number `N ≥ 3`,
`ω(N) = N.primeFactors.card < 1.3841 * log N / log (log N)`.

Proof architecture across `External/RobinOmega/`:
- `Basic.lean`: `RobinOmegaBound`, `omegaUpperFn`, `3 < omegaUpperFn N` for `N ≥ 3`,
  monotonicity on `[e^e, ∞)` (`omegaUpperFn_monoOn_sixteen`), and antitonicity of `log x / x`.
- `Reduction.lean`: reduces `RobinOmegaBound` for arbitrary `N ≥ 3` (`ω(N) ≤ 3` directly;
  `ω(N) ≥ 4` via primorial minimization) to primes `p ≥ 7`.
- `ChebyshevLower.lean`: elementary Mod-30 Chebyshev binomial divisibility and Costa-Pereira
  lower bound `(84 / 100) * m ≤ θ m` for `m ≥ 13000`.
- `Asymptotic.lean`: Abel partial summation (`Chebyshev.primeCounting_eq_theta_div_log_add_integral`)
  closing all `m ≥ 13000`.
- `FiniteCheck.lean`: pure-kernel (`by decide`) Q64 lower-bound verification of all `1,547`
  primes `p < 13000` (`7 ≤ p < 13000`), including the global maximum at `k = 9, p_9 = 23`.
-/

namespace BuchstabSwitching.External

/-- Unconditional prime-counting bound for all primes `p ≥ 7` combining the Q64 kernel
verification on `[7, 13000)` (`FiniteCheck`) with the Mod-30 Chebyshev + Abel partial-summation
asymptotic closure on `[13000, ∞)` (`ChebyshevLower`, `Asymptotic`). -/
theorem robin_primeCounting_lt_theta {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    (Nat.primeCounting p : ℝ) <
      (1.3841 : ℝ) * Chebyshev.theta (p : ℝ) / Real.log (Chebyshev.theta (p : ℝ)) := by
  rcases lt_or_ge p 13000 with hp_lt | hp_ge
  · exact robin_primeCounting_lt_of_lt_13000 hp hp7 hp_lt
  · exact robin_primeCounting_lt_of_ge_13000 log_two_gt_nine_div_thirteen log_two_lt_25_div_36
      (fun _ hm => chebyshev_theta_ge_linear hm) hp_ge

/-- Unconditional proof of Guy Robin's explicit prime-divisor bound (`RobinOmegaBound`,
*Acta Arithmetica* **42** (1983), Théorème 11): for all `N ≥ 3`,
`ω(N) < 1.3841 * log N / log (log N)`. -/
theorem robinOmegaBound_holds : RobinOmegaBound :=
  robinOmegaBound_of_prime_theta_bound (fun _ hp hp7 => robin_primeCounting_lt_theta hp hp7)

/-- Direct unconditional bound `(N.primeFactors.card : ℝ) < omegaUpperFn N` for `N ≥ 3`. -/
theorem card_primeFactors_lt_omegaUpperFn {N : ℕ} (hN : 3 ≤ N) :
    (N.primeFactors.card : ℝ) < omegaUpperFn (N : ℝ) :=
  robinOmegaBound_holds N hN

end BuchstabSwitching.External
