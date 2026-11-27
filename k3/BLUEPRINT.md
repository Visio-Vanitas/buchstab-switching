# Blueprint for Discharging External Analytic Inputs

This blueprint describes the modular architecture of `BuchstabSwitching` and provides a
roadmap for proving the five remaining classical literature assumptions in `External.ClassicalBasicLemmas`
inside Lean 4 / Mathlib so that `all_even_one_plus_three_of_classical` (and
`even_eq_prime_add_omegaMult_le_three`) rests only on
`External.DirichletLNonvanishingRightOfHalf` (pinned to
`https://github.com/lsernau/grh-lean@72fead102f663d5c7a407964a13dc0cf9d977207`,
`grh-compact/src/Statements.lean`, where `src/Main.lean` proves `LFunction_ne_zero_of_half_lt_re`).

## Proof Dependency Graph

```
Core/{MultiplicativeOmega, ShiftedPrimes}.lean
                 |
                 v
Sieve/{OneStepSwitching, BonferroniHybrid, BrunBlockSieve, SelbergLambdaSq, ...}.lean
                 |
       +---------+-------------------------------+
       |                                         |
       v                                         v
Sieve/Regime2SlabBridge/SlabCertInst*.lean   Sieve/Regime3RayBridge/RayCertInst*.lean
(127/127 slabs, binary Dyadic reflection)    (Q0_100 closed (H*), C₂ ≤ 494, 120 strips,
       |                                      + BuchstabSeries.buchstabSeriesPremise_proved)
       v                                         |
External/SlabSieveEnclosure.lean                 v
       \                                External/AsymptoticRayEnclosure.lean
        \                                       /
         v                                     v
      External/Bridge.lean (ClassicalBasicLemmas → externalPremises_of_classical)
                              |
                              v
      BuchstabSwitching/Main.lean (all_even_one_plus_three_of_classical)
```

## 1. Already Discharged Inside Lean 4 (`0 sorry`, `0` custom axioms, `0 native_decide`)

All combinatorial, multiplicative, linear-sieve, and numerical-certificate engines are **fully
proved in Lean 4** depending solely on `[propext, Classical.choice, Quot.sound]`:

1. **Combinatorial One-Step Switching & Sieve Engines (`Core/`, `Sieve/`)**:
   - Multiplicative $\Omega(m)$ pinch (`omegaMult_le_three_of_sieve_pinch`, `switchingBalance_le_card_good`).
   - Hybrid `Q₁ × P₂` Bonferroni identities and prime-omission monotonicity (`BonferroniHybrid`, `BonferroniEstimates`).
   - Brun combinatorial block lower sieve parity rule ($\chi^- \le \mathbf{1}$), remainder $E^-$, level bound $\prod z_i^{m_i - m_{i-1}}$, and prime-omission monotonicity (`BrunBlockSieve`).
   - Selberg $\Lambda^2$ quadratic upper sieve, diagonalization, `V_N(z) J_N(z, ξ) ≥ V_full(z) J_full(z, ξ)` coupling, disjoint two-prime inclusion-exclusion `J_full(z, ξ)`, odd squarefree bound $\sum_{d \le X, 2\nmid d} \mu^2(d) \le \frac{4}{\pi^2} X + \sqrt{X}$, and collision sum $\sum_{L \le X, 2\nmid L} \mu^2(L) 3^{\omega(L)} \le \frac{1}{16} X (\ln X + 6)^2$ (`SelbergLambdaSq`, `SelbergDiagonalization`, `OddSquarefreeBounds`).
2. **Buchstab Delay-Differential Series & Robin `ω(N)` Bound (`External/BuchstabSeries/`, `External/RobinOmega/`)**:
   - Unconditional theorem `buchstabSeriesPremise_proved` establishing $F(s) = 1 + \sum_{n \text{ odd}} f_n(s)$ and $f(s) = 1 - \sum_{n \text{ even}} f_n(s)$.
   - Unconditional theorem `robinOmegaBound_holds` establishing $\omega(N) < 1.3841 \ln N / \ln \ln N$ for all $N \ge 3$ via primorial reduction, Mod-30 Chebyshev + Abel summation ($p \ge 13000$), and Q64 `by decide` verification ($p < 13000$).
3. **Regime 2 Finite-Slab Enclosure (`SlabSieveEnclosurePremise` via `SlabCertInst*`)**:
   - `slabSieveEnclosurePremise_of_sieveBridge` + `allSlabs_bridges_inst` verify all `127` contiguous slabs on $[4 \cdot 10^{18}, 10^{600})$ (`21` in `2a`, `40` in `2b`, `66` in `2c`, `6,448` slices total) via binary `Dyadic` proof-by-reflection (`m * 2^e / 2^8192`), depth-6 `OddPrimeTree` (`2,960` odd primes $< 27{,}000$), and non-deterministic algebraic/transcendental witnesses (`by decide`).
4. **Regime 3 Asymptotic Ray Enclosure (`AsymptoticRayEnclosurePremise` via `RayCertInst*`)**:
   - `asymptoticRayEnclosurePremise_of_sieveBridge` + `ray_cert_data_inst` verify all even $N \ge 10^{600}$ via closed-interval `(H*)` on `Q0_100` (`closedHStarCond_Q0_100`, $\varepsilon_* < 1/100$), kernel-certified `C2_bjs certifiedDecaySeq (1/100) ≤ 494` (Python cap `495`, break-even $C_2 \le 1853.2$), integer cutoffs $z = \lfloor N^{1/16} \rfloor$, $y = \lceil (N/z)^{1/3} \rceil$, and `L = 120` monotone Selberg `Λ²` strips.

---

## 2. Contributor Roadmap on `on-dev`: 4 Remaining Analytic Lemmas (+ `CertifiedConstants`)

`External.externalPremises_of_classical` reduces `ExternalPremises` to `SmallEvenPremise`
(retained as an external computational premise) plus constructing a `CertifiedConstants` witness
and proving the **four remaining classical analytic lemmas** below on the **`on-dev`** branch:

### Retained External Computational Input (Out of Scope for `on-dev` PRs)
- **`SmallEvenPremise` (`External/FiniteVerification/SmallEven.lean`)**: Binary prime
  representations on the finite initial range `4 ≤ N < 4 * 10^18` (Oliveira e Silva, Herzog &
  Pardi, *Math. Comp.* **83** (2014), 2033–2060). Retained as an external finite-verification
  premise rather than re-tabulated inside Lean.

### Track 1 (Open PR Target): Explicit GRH / RH Prime-Counting (`CharacterSums/DirichletGRH.lean` & `SchoenfeldRH/PrimeCountingRH.lean`)
- **Targets**: `JSLemma51Premise consts.li2` and `SchoenfeldPrimePremise consts.li2` from
  `DirichletLNonvanishingRightOfHalf` (`lsernau/grh-lean@72fead1`) and
  `Mathlib.NumberTheory.LSeries.DirichletContinuation`.
- **Sub-lemmas**:
  1. Explicit von Mangoldt smoothed Perron formula (`ψ(x, χ)`) under zero-free half-plane
     `Re(s) > 1/2`.
  2. Partial summation to `|π(x; d, a) - li(x) / φ(d)| ≤ c_π(X₂) √x ln x` (`x ≥ X₂ ≥ 4 * 10^18`,
     `3 ≤ d ≤ √x`) following Grenié–Molteni (*J. Number Theory* **200** (2019), Cor. 1;
     *Ramanujan J.* **49** (2019), 535–548) and Johnston–Starichkova (`arXiv:2208.01229v3`, Lemma 5.1).
  3. Schoenfeld explicit RH bound `|π(x) - li(x)| ≤ (√x ln x) / (8π)` for `x ≥ 2657`
     (*Math. Comp.* **30** (1976), Cor. 1) and unconditional Rosser–Schoenfeld fallback.

### Track 2 (Open PR Target): Explicit Mertens Reciprocal-Prime Bounds (`MertensSums/`)
- **Target**: `MertensPrimeSumPremise consts.M0` (`RobinOmegaBound` is already discharged via `robinOmegaBound_holds`).
- **Sub-lemmas**:
  1. Explicit Mertens reciprocal-prime bounds `∑_{p < x} 1/p = ln ln x + M₀ + O*(...)`
     following Johnston–Starichkova (`arXiv:2208.01229v3`, Lemma 3.2) and
     Bordignon–Johnston–Starichkova (`arXiv:2207.09452v6`, Lemmas 16–17).

### Track 3 (Open PR Target): Unconditional Euler Product Asymptotic & Constants (`EulerProductV/` & `NumericalConstants/`)
- **Targets**: `EulerProductVPremise consts.U_c consts.eNegGamma` and `CertifiedConstants`.
- **Sub-lemmas**:
  1. Unconditional shifted-prime Euler product asymptotic `V_N(x) = (U_N / ln x) (1 + O*(δ_V))`
     for `x ≥ 285` following Bordignon–Johnston–Starichkova (`arXiv:2207.09452v6`, Lemma 38 `vjlem`).
  2. Rational interval enclosures in `CertifiedConstants` for `li(2)`, Meissel–Mertens `M₀`,
     `U_c = 2 C₂ e^{-γ}`, and `e^{-γ}` via convergent series and finite prime products with integral tails.
