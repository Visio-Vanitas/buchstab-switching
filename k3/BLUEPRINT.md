# Blueprint for Discharging External Analytic Inputs

This blueprint describes the modular architecture of `BuchstabSwitching` and provides a
roadmap for proving the remaining assumptions in `BuchstabSwitching/External/` inside Lean 4 /
Mathlib so that `even_eq_prime_add_omegaMult_le_three` rests only on
`External.DirichletLNonvanishingRightOfHalf`.

## Proof Dependency Graph

```
Core/MultiplicativeOmega.lean       Core/ShiftedPrimes.lean
             \                               /
              v                             v
         Sieve/OneStepSwitching.lean   Sieve/{BonferroniHybrid, SelbergLambdaSq}.lean
                      \
                       v
Certificates/{Types, Data, Soundness}.lean  +  External/Bridge.lean
                                  \               /
                                   v             v
                            BuchstabSwitching/Main.lean
```

All combinatorial, multiplicative, and rational-certificate modules (`Core/`, `Sieve/`,
`Certificates/`, `Main.lean`) are **fully verified with zero `sorry` and zero custom axioms**.

## Contributor Roadmap (`BuchstabSwitching/External/`)

### Track 1: Finite Binary Verification (`External/FiniteVerification/SmallEven.lean`)
- **Goal**: Establish `SmallEvenPremise` for even integers `4 ≤ N < 4 * 10^18`.
- **Strategy**: Verified certificate replay (e.g., segmented prime-gap tables or bounded
  bitmask verification up to `4 * 10^18`, following Oliveira e Silva, Herzog & Pardi,
  *Math. Comp.* **83** (2014), 2033–2060).

### Track 2: Explicit GRH Prime-Counting in APs (`External/CharacterSums/DirichletGRH.lean`)
- **Goal**: Derive `ExplicitPrimeInAPPremise` from `DirichletLNonvanishingRightOfHalf` and
  `Mathlib.NumberTheory.LSeries.DirichletContinuation`.
- **Sub-lemmas**:
  1. Explicit von Mangoldt smoothed Perron formula (`ψ(x, χ)`) under zero-free strip
     `Re(s) > 1/2`.
  2. Partial summation from `ψ(x; d, a)` to `π(x; d, a) = li(x) / φ(d) + O*(c_π(x) √x ln x)`
     following Grenié–Molteni (*Ramanujan J.* **49** (2019), 535–548).
  3. Schoenfeld explicit `|π(x) - li(x)| ≤ (√x ln x) / (8π)` and Robin explicit `ω(N)` bound.

### Track 3: Finite-Slab Sieve Enclosures (`External/MultiplicativeBounds/SlabSieveEnclosure.lean`)
- **Goal**: Prove `SlabSieveEnclosurePremise` linking each `c ∈ allSlabs` over
  `[4 * 10^18, 10^600)` to `switchingBalance N c.z c.y` (normalized by `|A_N|` on `2a/2b`
  and `|A_N| * V_N(z)` on `2c`).
- **Sub-lemmas**:
  1. Explicit Mertens sums `∑_{p < x} 1/p` (`Rosser–Schoenfeld 1962`, `Johnston–Starichkova arXiv:2208.01229v3`).
  2. Odd squarefree counting `∑_{d ≤ X, 2 ∤ d} μ²(d) ≤ (4/π²) X + √X` and Selberg collision
     bound `∑_{L ≤ X, 2 ∤ L} μ²(L) 3^{ω(L)} ≤ (1/16) X (ln X + 6)²`.
  3. Exact finite-terminating Buchstab recursion (`n < n_term` where `q_3^3 ∏_{j=4}^{n_term} q_j > D`),
     prime-omission monotonicity across sub-cutoffs `z_sub ≤ z`, and two-prime inclusion-exclusion
     `J_full(z, ξ)`.

### Track 4: Asymptotic Ray Closure (`External/LinearSieve/AsymptoticRayEnclosure.lean`)
- **Goal**: Prove `AsymptoticRayEnclosurePremise` uniformly for all even `N ≥ 10^600`.
- **Sub-lemmas**:
  1. Order-respecting two-variable pre-sieve error `ε_sup(251) ≤ 0.0100583` (`k = 99`, `C₂ = 345`,
     break-even `C₂ ≤ 417.1`) and BJS linear-sieve inequality (`arXiv:2207.09452`, Theorem 6).
  2. Quadrature enclosure of Buchstab's lower sieve function `f(s)` on `4 ≤ s ≤ 6`.
  3. Monotone pre-sieve-free Selberg `Λ²` bound `V_N(z) * J_full(z, z^r)`.
