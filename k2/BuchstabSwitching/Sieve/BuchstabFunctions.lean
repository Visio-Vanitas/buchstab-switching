import BuchstabSwitching.Sieve.BuchstabFunctions.BJSWeight
import BuchstabSwitching.Sieve.BuchstabFunctions.DelayEquation
import BuchstabSwitching.Sieve.BuchstabFunctions.Monotonicity
import BuchstabSwitching.Sieve.BuchstabFunctions.FHat
import BuchstabSwitching.Sieve.BuchstabFunctions.Quadrature

/-!
# Linear Sieve Functions: Buchstab `F, f`, BJS Error Weight `h`, Jurkat–Richert `fHat`, and Quadrature Bounds

This module formalizes the analytic linear-sieve toolkit required by the BJS linear sieve
(`arXiv:2207.09452`) and the `f(s)` quadrature certificate in `linear_sieve.py`:

1. **BJS error weight `h_bjs`**: positivity, antitonicity, continuity, and explicit integral
   comparison bounds on `[s, M]` for `s⁻¹ ∫_s^M h_bjs (t - 1) dt`.
2. **Buchstab functions `buchstabF` and `buchstabf`**: stepwise recursive definition on `(k, k + 1]`,
   continuity on `(0, ∞)`, delay integral equations for `2 ≤ a ≤ s`, exact closed forms on
   `[2, 4]`, `[3, 5]`, `[4, 6]` (BJS Lemma 19 / Cai Lemma 2), strict separation `f < F` via the
   Dickman-type integral equation for `s * (F(s) - f(s))`, and global monotonicity (`F` antitone,
   `f` monotone) for any `c > 0`.
3. **Jurkat–Richert iterated error integrals `fHat`**: recursive finite-support construction,
   nonnegativity, compact support (`s ≥ n + 2 → fHat n s = 0`), continuity and antitonicity on
   `[1, ∞)`, and comparison bounds with `h_bjs`.
4. **Quadrature second-derivative bounds**: `|(d²/dt²)(log (t - 1) / t)| ≤ 13 / 10` on `[2, 4]`
   and `|(d²/dt²)((1 / t) ∫_2^(t-1) (log (u - 1) / u) du)| ≤ 3 / 10` on `[3, 5]`.
-/
