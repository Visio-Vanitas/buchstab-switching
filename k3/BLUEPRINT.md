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
  3. Brun combinatorial block lower sieve parity rule (`χ⁻ ≤ 1`), block remainder `E⁻`,
     modbound `∏ z_i^{m_i - m_{i-1}}`, prime-omission monotonicity across sub-cutoffs `z_sub ≤ z`,
     and two-prime inclusion-exclusion `J_full(z, ξ)`.

### Track 4: Asymptotic Ray Closure (`External/LinearSieve/AsymptoticRayEnclosure.lean`)
- **Goal**: Prove `AsymptoticRayEnclosurePremise` uniformly for all even `N ≥ 10^600`.
- **Sub-lemmas**:
  1. Closed-interval two-variable pre-sieve error `(H*)` on `Q0_100` (`ε_* < 1/100`, certified
     `100:old` `C₂ ≤ 348.365883` and cross-checked `100:new` `C₂ ≤ 235.091291`, break-even
     `C₂ ≤ 1854.3`).
  2. Explicit Jurkat–Richert / linear-sieve enclosure of Buchstab's lower sieve function `f(s)`
     and error `h(s)` with integer cutoff rounding `z = ⌊N^{1/16}⌋`, `y = ⌈(N/z)^{1/3}⌉`.
  3. Monotone pre-sieve-free Selberg `Λ²` bound `V_N(z) * J_full(z, z^r)`.
