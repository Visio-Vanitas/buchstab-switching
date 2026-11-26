import BuchstabSwitching.Sieve.SelbergAsymptoticBridge.CouplingAndJOdd
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge.TwoPrimePartition
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge.DiscreteJFull
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge.MonotoneVJ
import BuchstabSwitching.Sieve.SelbergAsymptoticBridge.UniformRayVJ

/-!
# Selberg Asymptotic Bridge: `V_N · J_N ≥ V_full · J_full`, `j_full_lb_z3`, and Monotone `V · J`

Connects the combinatorial Selberg normalizer `SelbergDiagonalization.selbergJ` for
`g(p) = 1 / (p - 1)` on odd primes `< z` to `OddSquarefreeBounds.J_odd` and
`External.VN`, and re-exports:

1. **Prime-omission coupling (`CouplingAndJOdd`)**:
   for every even `N`, `z : ℕ`, and `xi : ℝ`,
   `External.VN N z * J_N N z xi ≥ External.VN 2 z * J_full z xi`.
2. **2-prime inclusion-exclusion and partition bounds (`TwoPrimePartition`)**:
   `J_full_two_prime_ie_ge`, `sum_Ico_partition`, and Mertens `1 / (p - 2)` box bounds.
3. **Discrete 2-prime inclusion-exclusion (`DiscreteJFull`)**:
   for `3 ≤ z`, `1 ≤ xi < z^3`, and any strictly disjoint partition
   `z = w_0 < w_1 < ... < w_{k₁} = xi` together with a disjoint 2-prime box grid
   `[a_i, a_{i+1}) × [b_{i,j}, b_{i,j+1})`, an explicit lower bound `j_full_lb_z3_ge` on `J_full z xi`.
4. **Continuous-partition monotone asymptotic bound (`MonotoneVJ`, `UniformRayVJ`)**:
   for `Real.exp 10 < z`, `0 < r < 3` (both `0 < r < 1` and `1 < r < 3`), any
   partition `1 = t_0 < t_1 < ... < t_{k₁} = r` and 2-prime exponential grid,
   proves `vj_monotone_lb ≤ External.VN 2 (Nat.ceil z) * J_full (Nat.ceil z) (z ^ r)`
   and `≤ External.VN 2 (Nat.floor z) * J_full (Nat.floor z) (z ^ r)`, proves
   monotonicity of `vj_monotone_lb` in `N ≥ X_LS` (for `z = N^{1/M}` or `⌊N^{1/M}⌋`
   and constant or antitone `δ_V`), and deduces a uniform bound for all even `N ≥ X_LS`.
-/
