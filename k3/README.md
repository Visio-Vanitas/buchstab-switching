# Buchstab–Richert One-Step Weighted Sieve Switching in Lean 4 (`k3/`)

A modular Lean 4 formalization of one-step Buchstab–Richert weighted sieve switching paired
with a zero-float arbitrary-precision Python interval certifier for shifted $\Omega(m) \le 3$
representations across all even integers $N \ge 4$:

> **Main Conditional Theorem (`BuchstabSwitching.even_eq_prime_add_omegaMult_le_three`)**
> Assuming `DirichletLNonvanishingRightOfHalf` (generalized half-plane non-vanishing for
> Dirichlet $L$-functions, matching `https://github.com/lsernau/grh-lean` at commit
> `72fead102f663d5c7a407964a13dc0cf9d977207`, `grh-compact/src/Statements.lean`) together
> with the external analytic bridges isolated in `BuchstabSwitching/External/`, every even
> integer $N \ge 4$ satisfies
> $$N = p + m \qquad (p \text{ prime},\; \Omega(m) \le 3),$$
> where $\Omega(m)$ counts the prime divisors of $m$ with multiplicity.

For full mathematical derivations, closed-interval `(H*)` certification (`certify_closed_hstar_q0`),
Brun block lower sieving (`brun_block_sieve.py`), parameter meanings, and robustness margins, see
[NOTES_K3_DERIVATION.md](NOTES_K3_DERIVATION.md) and
[BLUEPRINT.md](BLUEPRINT.md).

---

## Verified Scope & Key Margins (`127` Contiguous Slabs + Asymptotic Ray)

| Regime | Interval | Normalization Scale | Certified Margin |
| :--- | :--- | :--- | :--- |
| **1** | `[4, 4 * 10^18)` | Exact binary prime verification (`K = 1 <= 3`) | `exact` |
| **2a** | `[4 * 10^18, 2 * 10^23)` (21 slabs) | `|A_N|` | `net >= 0.00402`, `sieve_net >= 0.0176` |
| **2b** | `[2 * 10^23, 10^84)` (40 slabs) | `|A_N|` | `net >= 0.00183`, `sieve_net >= 0.0251` |
| **2c** | `[10^84, 10^600)` (66 slabs) | `|A_N| * V_N(z)` | `net = sieve_net >= 0.00989`, `tol >= 1.9x` |
| **3** | `[10^600, ∞)` (uniform ray) | `16 * U_N * N / ln^2 N` | `net >= 0.046862`, `tot_err <= 0.000078`, `C_2 <= 1854.3` (Lean `C_2 ≤ 494`, cap `495`; cross-checks `100:old` `0.051917` / `100:new` `0.055822`), `tol = 609.2x` |

---

## Kernel-Verified Modules vs. External Contributor Modules

### Verified in Lean 4 (`zero sorry`, `zero axiom` declarations, `#print axioms` = `[propext, Quot.sound, Classical.choice]`)
- **`BuchstabSwitching/Core/`**:
  - `MultiplicativeOmega.lean`: Formal `omegaMult m := m.primeFactorsList.length`,
    multiplicativity, and rough-integer bounds (`m < y ^ k` implies `omegaMult m < k`).
  - `ShiftedPrimes.lean`: Coprimality of shifted divisors and `omegaMult_le_three_of_sieve_pinch`.
- **`BuchstabSwitching/Sieve/`**:
  - `OneStepSwitching.lean`, `BonferroniHybrid.lean`, `SelbergLambdaSq.lean`, `AbstractSieve.lean`:
    Deterministic one-step switching inequality (`switchingBalance_le_card_good`), hybrid
    `Q₁ × P₂` Bonferroni identities, and Selberg `Λ²` quadratic upper-bound sieve.
  - `BonferroniEstimates.lean`, `BrunBlockSieve.lean` (+ `BrunBlockSieve/`),
    `OddSquarefreeBounds.lean` (+ `OddSquarefreeBounds/`), `ShiftedPrimeRemainder.lean` (+ `ShiftedPrimeRemainder/`),
    `RosserIwaniecComb.lean` (+ `RosserIwaniecComb/`): Combinatorial Brun/Bonferroni bounds and
    GRH remainder estimates.
  - `BuchstabFunctions.lean` (+ `BuchstabFunctions/`), `LinearSieveInduction.lean` (+ `LinearSieveInduction/`),
    `LinearSieveBJS.lean` (+ `LinearSieveBJS/`), `MertensTwoVar.lean`: Two-variable closed `(H*)`
    Mertens bounds and explicit BJS linear sieve.
  - `SelbergDiagonalization.lean` (+ `SelbergDiagonalization/`),
    `SelbergAsymptoticBridge.lean` (+ `SelbergAsymptoticBridge/`),
    `Regime2SlabBridge.lean` (+ `Regime2SlabBridge/`),
    `Regime3RayBridge.lean` (+ `Regime3RayBridge/`), `AxiomsAudit.lean`: Regime 2 & Regime 3
    formal bridges and kernel axiom audit.
- **`BuchstabSwitching/Certificates/`**:
  - `Types.lean`, `Data.lean`, `Soundness.lean`: Kernel-decidable (`by decide`, zero
    `native_decide`) check of all `127` contiguous slabs over `[4 * 10^18, 10^600)` plus
    asymptotic ray `X_LS = 10^600` (`DENOM = 10^10`).
- **`BuchstabSwitching/Main.lean`**:
  - Top-level conditional theorem `even_eq_prime_add_omegaMult_le_three` and challenge-aligned
    `all_even_one_plus_three_of_premises : AllEvenPrimePlusAlmostPrime 3` (matching
    `0 < m` and Mathlib `Ω := ArithmeticFunction.cardFactors`).

### Isolated External Bridges (`BuchstabSwitching/External/`)
Unformalized inputs are grouped into independent topic subfolders (`8` classical lemma folders,
`2` sieve-enclosure bridges, and `Bridge.lean` providing `ClassicalBasicLemmas` and
`externalPremises_of_classical`, see [BuchstabSwitching/External/README.md](BuchstabSwitching/External/README.md))
so contributors can discharge them individually without `axiom` declarations:
- `External/FiniteVerification/SmallEven.lean`: `SmallEvenPremise` (`4 ≤ N < 4 * 10^18`).
- `External/CharacterSums/DirichletGRH.lean`: `DirichletLNonvanishingRightOfHalf` and
  explicit AP prime-counting bounds.
- `External/SchoenfeldRH/PrimeCountingRH.lean`, `External/RobinOmega/PrimeFactorCount.lean`,
  `External/MertensSums/ReciprocalPrimeSums.lean`, `External/EulerProductV/ProductAsymptotic.lean`,
  `External/BuchstabSeries/DelayDiffEqIdentity.lean`, `External/NumericalConstants/ExplicitConstants.lean`:
  Classical analytic prime-number bounds and explicit numerical certificate constants.
- `External/MultiplicativeBounds/SlabSieveEnclosure.lean`: Finite-slab bridge over
  `c ∈ allSlabs` (`slabSieveEnclosurePremise_of_sieveBridge`).
- `External/LinearSieve/AsymptoticRayEnclosure.lean`: Asymptotic linear-sieve closure
  via closed `(H*)` pre-sieve `Q0_100` (`certifiedDecaySeq` with `C_2 ≤ 494`, Python cap `495`;
  `100:old` / `100:new` SHA-256 provenance cross-checks in `../shared/data/linear_sieve_inputs/`) +
  Selberg `Λ²` for `N ≥ X_LS`.
- `External/Bridge.lean`: Top-level `ExternalPremises`, `ClassicalBasicLemmas`, and
  `externalPremises_of_classical`.

---

## Building & Verifying (Inside `k3/`)

```bash
cd k3

# 1. Verify Lean 4 library, kernel certificates, and axiom whitelist
lake exe cache get
lake build BuchstabSwitching
lake env lean AxiomsCheckK3.lean

# 2. Fast (~40s) AST zero-float, active Decimal-trap, slab, Data.lean & Lean hygiene verification
python3 scripts/quick_verify.py

# 3. Full outward-rounded Decimal/Fraction/int certification (PREC = 90)
python3 scripts/certify_omega_le_3.py

# 4. Comparator independent kernel export check (leanchecker-paranoid & nanoda_bin)
bash comparator/run_comparator.sh
```

---

## Key References

- **Finite Range**: T. Oliveira e Silva, S. Herzog, S. Pardi, *Math. Comp.* **83** (2014), no. 288, 2033–2060.
- **GRH Explicit AP & Mertens Bounds**: L. Grenié, G. Molteni, *Ramanujan J.* **49** (2019), 535–548; D. R. Johnston, V. V. Starichkova, `arXiv:2208.01229v3`; J. B. Rosser, L. Schoenfeld, *Illinois J. Math.* **6** (1962), 64–94.
- **Explicit Linear Sieve Error (`C₁, C₂`)**: M. Bordignon, D. R. Johnston, V. V. Starichkova, `arXiv:2207.09452`.
