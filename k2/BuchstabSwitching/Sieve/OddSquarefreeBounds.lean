import BuchstabSwitching.Sieve.OddSquarefreeBounds.OddHarmonic
import BuchstabSwitching.Sieve.OddSquarefreeBounds.SquarefreeCount
import BuchstabSwitching.Sieve.OddSquarefreeBounds.ThreePowOmega
import BuchstabSwitching.Sieve.OddSquarefreeBounds.InvTotient
import BuchstabSwitching.Sieve.OddSquarefreeBounds.JOddConvolution
import BuchstabSwitching.Sieve.OddSquarefreeBounds.JOddAsymptotic

/-!
# Explicit Odd Squarefree Counting and Divisor-Sum Bounds

Provides verified real-analytic upper and asymptotic bounds over odd squarefree integers used
throughout the `k3` sieve certificates (`constants.py`, `selberg_weights.py`, `regime_slabs.py`):

1. `odd_squarefree_count_le`: `#{1 ≤ d ≤ X : Odd d ∧ Squarefree d} ≤ (4 / π²) * X + √X`.
2. `odd_squarefree_three_pow_omega_le`: `∑_{1 ≤ L ≤ X, Odd L, Sqf L} 3^{ω(L)} ≤ (1/16) * X * (log X + 6)²`.
3. `odd_squarefree_inv_totient_le`: `∑_{1 ≤ d ≤ X, Odd d, Sqf d} 1/φ(d) ≤ H_tilde * ((1/2) * log X + α₀ + C_{f₀}/X)`.
4. `J_odd_asymptotic_enclosure`: `|J_odd X - H₀ * ((1/2) * log X + α₀)| ≤ C_J * X^{-1/4}`.
-/
