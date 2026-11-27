# Buchstab–Richert One-Step Weighted Sieve Switching in Lean 4 (`k3/`)

A modular Lean 4 formalization of one-step Buchstab–Richert weighted sieve switching paired
with a zero-float arbitrary-precision Python interval certifier for shifted $\Omega(m) \le 3$
representations across all even integers $N \ge 4$:

> **Main Conditional Theorems (`BuchstabSwitching.all_even_one_plus_three_of_classical` & `even_eq_prime_add_omegaMult_le_three`)**
> Assuming `DirichletLNonvanishingRightOfHalf` (generalized half-plane non-vanishing for
> Dirichlet $L$-functions, matching `https://github.com/lsernau/grh-lean` at commit
> `72fead102f663d5c7a407964a13dc0cf9d977207`, `grh-compact/src/Statements.lean`) together
> with the six classical literature premises bundled in `External.ClassicalBasicLemmas`
> (`SmallEvenPremise`, `JSLemma51Premise`, `SchoenfeldPrimePremise`, `RobinOmegaBound`,
> `MertensPrimeSumPremise`, and unconditional BJS v6 Lemma 38 `EulerProductVPremise`), every
> even integer $N \ge 4$ satisfies
> $$N = p + m \qquad (p \text{ prime},\; 0 < m,\; \Omega(m) \le 3),$$
> where $\Omega(m)$ counts the prime divisors of $m$ with multiplicity. All `127` finite-slab
> sieve enclosures, `BuchstabSeries`, closed-interval `(H*)` on `Q0_100`, Lean `C_2 ≤ 494`, and
> all `120` asymptotic ray strips are proved inside Lean 4 (`0 sorry`, `0` custom axioms).

For full mathematical derivations, closed-interval `(H*)` certification (`certify_closed_hstar_q0`),
Brun block lower sieving (`brun_block_sieve.py`), the binary `Dyadic` proof-by-reflection
architecture, parameter meanings, and robustness margins, see
[NOTES_K3_DERIVATION.md](NOTES_K3_DERIVATION.md) and
[BLUEPRINT.md](BLUEPRINT.md).

---

## Verified Scope & Key Margins (`127` Contiguous Slabs + Asymptotic Ray)

| Regime | Interval | Normalization Scale | Certified Margin & Bottleneck |
| :--- | :--- | :--- | :--- |
| **1** | `[4, 4 * 10^18)` | Exact binary prime verification (`K = 1 <= 3`) | `exact` |
| **2a** | `[4 * 10^18, 2 * 10^23)` (21 slabs) | `\|A_N\|` | `net >= 0.001832` (`2a-03`: `[5.0e18, 7.0e18)`), `sieve_net >= 0.008025`, `tol >= 1.04x` |
| **2b** | `[2 * 10^23, 10^84)` (40 slabs) | `\|A_N\|` | `net >= 0.001763` (`2b-40`: `[10^82, 10^84)`), `sieve_net >= 0.024224`, `tol >= 2.30x` |
| **2c** | `[10^84, 10^600)` (66 slabs) | `\|A_N\| * V_N(z)` | `net = sieve_net >= 0.003969` (`2c-07`: `[10^96, 10^98)`), `tol >= 1.41x` |
| **3** | `[10^600, ∞)` (uniform ray) | `16 * U_N * N / ln^2 N` | `main_coeff >= 0.046903`, `tot_err <= 0.000078`, `net >= 0.046825`, `C_2 <= 1853.2` (Lean `C_2 ≤ 494`, cap `495`; cross-checks `100:old` `0.051880` / `100:new` `0.055785`), `tol = 608.7x` |

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
    `Regime3RayBridge.lean` (+ `Regime3RayBridge/`), `AxiomsAudit.lean`:
    - **Regime 2 Binary Proof-by-Reflection (`Regime2SlabBridge/SlabCertInst*.lean`, 41 modules, all `<= 750` lines)**: Biased binary `Dyadic` (`m * 2^e / 2^8192`), non-deterministic algebraic/transcendental witnesses (`SlabCertInstData2a1..2c6`, `2,433` lines), depth-6 `OddPrimeTree` segment tree over `2,960` odd primes `< 27,000`, literal-folded 11-step `jOddStepTableFast` staircase (`d <= 1024`), memoized slice checker `checkSlices2abMemo`, and 6-way `2c` sharding (`SlabCertInst2c1..6`, 11 slabs/shard, `< 500 MB` RAM/process) discharging `allSlabs_bridges_inst` across all `127/127` slabs via `by decide`.
    - **Regime 3 Ray Certificate (`Regime3RayBridge/RayCertInst*.lean`, `LinearSieveBJS/CertifiedC2.lean`)**: Kernel-proved closed-interval `(H*)` on `Q0_100` (`closedHStarCond_Q0_100`), parity-split `C_2 ≤ 494` (`certifiedDecaySeq`), unconditional `buchstabSeriesPremise_proved` (`External/BuchstabSeries/`), and `L = 120` ray strips (`ray_cert_data_inst`).
- **`BuchstabSwitching/Certificates/`**:
  - `Types.lean`, `Data.lean`, `Soundness.lean`: Kernel-decidable (`by decide`, zero
    `native_decide`) contiguity, switching-geometry, and margin check of all `127` slabs over
    `[4 * 10^18, 10^600)` plus asymptotic ray `X_LS = 10^600` (`DENOM = 10^10`).
- **`BuchstabSwitching/Main.lean`**:
  - Top-level conditional theorems `all_even_one_plus_three_of_classical` (directly from GRH +
    `ClassicalBasicLemmas`), `all_even_one_plus_three_of_premises : AllEvenPrimePlusAlmostPrime 3`
    (matching `0 < m` and Mathlib `Ω := ArithmeticFunction.cardFactors`), and
    `even_eq_prime_add_omegaMult_le_three`.

### Isolated External Bridges (`BuchstabSwitching/External/`)
`External/Bridge.lean` reduces `ExternalPremises` (`externalPremises_of_classical`) to strictly
**6 classical/computational premises** bundled in `ClassicalBasicLemmas` (`8` classical topic
folders, `2` proved sieve-enclosure bridges, and `Bridge.lean`; see
[BuchstabSwitching/External/README.md](BuchstabSwitching/External/README.md))
so contributors can discharge them individually without `axiom` declarations:
- `External/FiniteVerification/SmallEven.lean`: `SmallEvenPremise` (`4 ≤ N < 4 * 10^18`).
- `External/CharacterSums/DirichletGRH.lean`: `DirichletLNonvanishingRightOfHalf` and
  explicit AP prime-counting bound `JSLemma51Premise`.
- `External/SchoenfeldRH/PrimeCountingRH.lean`, `External/RobinOmega/PrimeFactorCount.lean`,
  `External/MertensSums/ReciprocalPrimeSums.lean`, `External/EulerProductV/ProductAsymptotic.lean`,
  `External/NumericalConstants/ExplicitConstants.lean`:
  Classical analytic prime-number bounds (`SchoenfeldPrimePremise`, `RobinOmegaBound`,
  `MertensPrimeSumPremise`, unconditional BJS v6 Lemma 38 `EulerProductVPremise`) and explicit
  numerical certificate constants (`CertifiedConstants`). (Note `External/BuchstabSeries/` is
  already unconditionally proved via `buchstabSeriesPremise_proved`.)
- `External/MultiplicativeBounds/SlabSieveEnclosure.lean` & `SlabSieveEngineWiring.lean`:
  Proved finite-slab reduction `slabSieveEnclosurePremise_of_sieveBridge` instantiated across all
  `127/127` slabs (`allSlabs_bridges_inst`).
- `External/LinearSieve/AsymptoticRayEnclosure.lean`: Proved asymptotic linear-sieve reduction
  `asymptoticRayEnclosurePremise_of_sieveBridge` via closed `(H*)` pre-sieve `Q0_100`
  (`certifiedDecaySeq` with `C_2 ≤ 494`, Python cap `495`; `100:old` / `100:new` SHA-256
  provenance cross-checks in `../shared/data/linear_sieve_inputs/`) + Selberg `Λ²` (`L = 120`
  strips, `ray_cert_data_inst`) for `N ≥ X_LS`.
- `External/Bridge.lean`: Top-level `ExternalPremises`, `ClassicalBasicLemmas`, and
  `externalPremises_of_classical`.

---

## Building & Verifying (Inside `k3/`)

```bash
cd k3

# 1. Verify Lean 4 library (~9–11m parallel cold build, ~2.5 GB peak RAM; 8,211 jobs),
#    binary Dyadic slab reflection, ray certificates, and 3-axiom whitelist
lake exe cache get
lake build BuchstabSwitching
lake env lean BuchstabSwitching/Sieve/AxiomsAudit.lean
lake env lean AxiomsCheckK3.lean

# 2. Fast (~40s) AST zero-float, active Decimal-trap, slab, Data.lean & Lean hygiene verification
python3 scripts/quick_verify.py

# 3. Full outward-rounded Decimal/Fraction/int certification (PREC = 90) & Lean codegen
python3 scripts/certify_omega_le_3.py              # regenerates certified_bounds.txt & certified_slabs.json
python3 scripts/generate_lean_data.py              # regenerates Certificates/Data.lean
python3 -m scripts.sieve_cert.slab_witness_export  # regenerates 12 binary Dyadic witness shards SlabCertInstData*.lean

# 4. Comparator independent kernel export check (leanchecker-paranoid & nanoda_bin)
bash comparator/run_comparator.sh
```

---

## Key References

- **Finite Range**: T. Oliveira e Silva, S. Herzog, S. Pardi, *Math. Comp.* **83** (2014), no. 288, 2033–2060.
- **GRH Explicit AP & Mertens Bounds**: L. Grenié, G. Molteni, *Ramanujan J.* **49** (2019), 535–548; D. R. Johnston, V. V. Starichkova, `arXiv:2208.01229v3`; J. B. Rosser, L. Schoenfeld, *Illinois J. Math.* **6** (1962), 64–94.
- **Explicit Linear Sieve Error (`C₁, C₂`)**: M. Bordignon, D. R. Johnston, V. V. Starichkova, `arXiv:2207.09452`.
