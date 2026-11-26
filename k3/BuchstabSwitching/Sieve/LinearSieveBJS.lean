import BuchstabSwitching.Sieve.LinearSieveBJS.ExpEnclosures
import BuchstabSwitching.Sieve.LinearSieveBJS.Contraction
import BuchstabSwitching.Sieve.LinearSieveBJS.FHatDecay
import BuchstabSwitching.Sieve.LinearSieveBJS.Lyapunov
import BuchstabSwitching.Sieve.LinearSieveBJS.TailConstants
import BuchstabSwitching.Sieve.LinearSieveBJS.Theorem6

/-!
# Explicit BJS v6 Linear Sieve Constants, Lyapunov Bounds, and Theorem 6

This module formalizes the analytic-combinatorial explicit linear sieve bounds from
Bordignon–Johnston–Starichkova (`arXiv:2207.09452v6`, Lemmas 8–12, 14, and Theorem 6),
building on the all-levels two-variable induction in `LinearSieveInduction`:

1. **Contraction of `h_bjs` (BJS v6 Lemmas 9 & 10)**:
   - Pointwise shift bounds `h_bjs (s - 1) ≤ γ_{s₀} * h_bjs s` on `[2, s₀ + 0.2]` (`γ_{s₀} = e^{s₀ - 1.8}`)
     and `s ≥ 3` (`γ_3 = 4e/3`), plus `(3 / s) * h_bjs 2 ≤ 3 * h_bjs s` on `[1, 3]`.
   - Tail-integral bounds `∫ t in s..M, h_bjs (t - 1) ≤ κ_{s₀} * s * h_bjs s` for
     `s₀ ∈ {2, 2.2, 2.4, 2.6, 2.8, 3}` and `H(3) ≤ 0.9214 * s * h_bjs s` on `[1, 3]`.
2. **Universal Exponential Decay of `fHat` (BJS v6 Lemma 8 / Nathanson Lemma 9.7)**:
   - `fHat_le_bjs_universal`: `fHat n s ≤ 2 * e^2 * (9607 / 10000) ^ (n - 1) * h_bjs s` for all
     `n ≥ 1`, `s ≥ 1`, and `ValidDecaySeq constDecaySeq`.
3. **Lyapunov Recurrences `τ_n`, `τ'_n` and Tail Bounds `C₁(ε), C₂(ε)` (BJS v6 Lemmas 11, 12, 14)**:
   - `E_bjs_le_tauBJS`: `E_bjs (1 + ε) n s ≤ ε * tauBJS c_seq ε n * e^2 * h_bjs s`.
   - `tauBJS_le_tauPrimeBJS` and `tauPrimeBJS_summable` for `0 < ε ≤ 1 / 74`.
   - `C1_bjs_le_tail` and `C2_bjs_le_tail`: explicit finite prefix + geometric `J_bjs` tail bounds.
4. **All-Levels BJS Explicit Linear Sieve Theorem (Theorem 6)**:
   - `bjs_linear_sieve_upper_fHat`, `bjs_linear_sieve_lower_fHat` (unconditional on Buchstab series).
   - `bjs_linear_sieve_upper`, `bjs_linear_sieve_lower` (accepting `HasSum` hypotheses for
     `buchstabF` and `buchstabf`).
-/
