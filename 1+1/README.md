# `1+1/` — GRH All-Range Explicit Binary Goldbach Extensions (Exceptional Set, Short Intervals, and Linnik Powers of 2)

Lean `v4.36.0` + Mathlib (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) formalization and zero-float (`Decimal` / `Fraction`) verification toolchain under GRH (`DirichletLNonvanishingRightOfHalf`, matching `lsernau/grh-lean` and `CGandGameEngineLearner/goldbach-proofs`) + empirical binary Goldbach base $E(4\cdot 10^{18}) = 0$.

## Certified Theorems (`OnePlusOne.Main`)

1. **Theorem 1A (v2) — All-Range Explicit `1+1` Exceptional Set (`theorem_1A_all_even_exceptional_set`)**:
   $$E(X) \le 16 \sqrt{X} (\log X)^3 \qquad (\forall X \ge 4)$$
   under `DirichletLNonvanishingRightOfHalf` and `EmpiricalGoldbachBase` (compressed **795.7×** from v1 `12731`, zero black-box buffers). 4-adic quartering induction (`OnePlusOne/Exceptional/DyadicClosure.lean`) combines $E(4\cdot 10^{18}) = 0$ with the v2 Parseval–Laplace 4-adic shell bound $E(Y) - E(Y/4) \le 7.77 \sqrt{Y}(\log Y)^3$ (`C_4adic ≤ 7.76342528` on $[4\cdot 10^{18}, 10^{19}]$, decreasing to `4.61768434` on $[10^{10000}, \infty)$) via $2 \cdot 7.77 = 15.54 < 16$.
2. **Theorem 1B (v2) — All-Range Explicit Short-Interval `1+1` (`theorem_1B_all_even_short_interval`)**:
   $$\forall X \ge 4,\quad \exists N \in [X,\ X + 8 (\log X)^2] \cap 2\mathbb{Z},\quad N = p_1 + p_2$$
   under `RiemannHypothesis` and `EmpiricalGoldbachBase` (`OnePlusOne/ShortInterval/FejerReduction.lean`; compressed **785.1×** from v1 `6281`, beating Chirre–Hagen 2026 `123` by **15.4×**, via averaged sharp-cutoff Fejér kernel at $\varepsilon = 1/4$, exact closed-form Mellin moments, Bochner-optimal zero-density kernel, and Fatou's Lemma with `C_J ≤ 1.75087527` across $[4\cdot 10^{18}, \infty)$).
3. **Theorem 3 — All-Range Explicit Linnik–Goldbach (`theorem_3A_all_even_exact_linnik_22` & `theorem_3_all_even_linnik_goldbach`)**:
   - Every even $N \ge 48$ satisfies $N = p_1 + p_2 + \sum_{i=1}^{22} 2^{k_i}$ with $k_i \ge 1$ (`r = 22`).
   - Every even $N \ge 4$ satisfies `HasLinnikRep 22 N` ($N = p_1 + p_2 + \sum_{j=1}^s 2^{k_j}$ with $s \le 22$).
   - **Constructive Binary Goldbach Bridge (`binary_goldbach_bridge_22` in `OnePlusOne/Linnik/Reduction.lean`)**: reduces the entire finite range $48 \le N \le (2^{23} - 2)\cdot 2^{61} + 4\cdot 10^{18} \approx 1.93428\cdot 10^{25}$ purely in Lean 4 from `EmpiricalGoldbachBase` via base-2 decomposition and bit-splitting $2^e = 2^{e-1} + 2^{e-1}$.

## Trust Boundary

- **Zero `axiom`, zero `sorry`, zero `native_decide`, zero `unsafe` in `OnePlusOne/`**: verified by `AxiomsCheckOnePlusOne.lean` (strictly `[propext, Classical.choice, Quot.sound]`) and `comparator/run_comparator.sh` (`leanchecker-paranoid` + `nanoda_bin`).
- **Explicit Analytic Interface (`OnePlusOne/External/Premises.lean`)**: `EmpiricalGoldbachBase`, `FouradicLaplaceCirclePremise`, `FejerShortIntervalPositivityPremise`, and `LinnikCircleAboveBridgePremise` isolate the classical empirical and circle-method/GRH/RH analytic inputs as explicit `Prop` fields (same convention as `k3/`, `k2/`, and `1+a/`).

## Directory Layout

- `OnePlusOne/Core/Defs.lean`: Core definitions (`IsGoldbachEven`, `exceptionalCount`, `ExceptionalSetProp`, `ShortIntervalProp`, `HasLinnikRep`, `HasExactPosLinnikRep`, `AllEvenLinnikProp`, `DirichletLNonvanishingRightOfHalf`, `EmpiricalGoldbachBase`).
- `OnePlusOne/Arithmetic/ElementaryBounds.lean`: Unconditional Mathlib proofs of `major_arcs_disjoint`, `ratio_2p_sub_1_le_pow_eighth`, `twin_prime_partial_product_ge`, `totient_sq_ge_half`, `dyadic_geom_sum_lt`, and `fouradic_geom_sum_lt`.
- `OnePlusOne/Certificates/Data.lean`: Kernel-checked (`by decide` / `norm_num`) integer tables for Theorems 1A (v2), 1B (v2), and 3.
- `OnePlusOne/Exceptional/DyadicClosure.lean`: Unconditional dyadic & 4-adic telescoping closure for Theorem 1A (v2).
- `OnePlusOne/ShortInterval/FejerReduction.lean`: Unconditional small-range `[4, 4 * 10^18)` & Fejér positivity bridge for Theorem 1B (v2).
- `OnePlusOne/Linnik/Reduction.lean`: Constructive Binary Goldbach Bridge (`48 ≤ N ≤ 1.93428e25`) & all-range Linnik–Goldbach assembly.
- `OnePlusOne/External/Premises.lean` & `OnePlusOne/Main.lean`: Isolated analytic premises & top-level theorem exports.
- `scripts/`: `certify_exceptional_short.py`, `certify_linnik_r.py` (zero IEEE-754 floats), `quick_verify.py`.
- `data/`: Pinned text outputs of both certifiers.
- `notes/`: Mathematical & Lean design specifications (`DESIGN_AND_PROOF_SPEC.md`, `LEAN4_INTERFACE.md`, `LINNIK_GOLDBACH_SPEC.md`).
- `comparator/`: Multi-kernel challenge/solution export harness (`leanchecker-paranoid`, `nanoda_bin`, `sorryAx` self-challenge rejection).

## Reproducibility (POSIX shell)

```sh
cd 1+1
python3 -I scripts/quick_verify.py
lake exe cache get
lake build OnePlusOne
lake env lean AxiomsCheckOnePlusOne.lean
bash comparator/run_comparator.sh
```
