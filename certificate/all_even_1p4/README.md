# all_even_1p4: certificate package

**Status.** This certificate checks arithmetic given the cited theorems; it does not prove the cited theorems. Regime 2 (`4·10^18 <= N < 10^170`) is the established part. The tail regime (`N >= 10^170`) is computed as in the note, but the note's use of the explicit linear sieve there is under repair (see the repository README), so the tail numbers are not a proof.

## Purpose

`notes/all-even-1p4-under-grh.md` reduces "every even N is p + eta with Omega(eta) <= 4" (under GRH) to finitely many explicit inequalities. This package checks them in exact integer and outward-rounded 90-digit decimal interval arithmetic: no floats, every rounding directed, `Inexact`/`Rounded` trapped outside directed contexts, every cited bound validated against its stated range at call time, every inequality recorded as a named check with its margin.

## How to run

Run everything from `certificate`. You need Python 3.10 or later and the standard library only.

```
python -m all_even_1p4                          # full certificate, about 3 minutes
python -m all_even_1p4 --json out.json --table out.md
python -m all_even_1p4 --quick                  # everything except the tail (about 20 s)
python -m all_even_1p4 --slab 22 [--slab 1]     # only the given slabs
python -m unittest discover -s all_even_1p4/tests -t .                 # fast tests (about 30 s)
ALL_EVEN_1P4_FULL=1 python -m unittest discover -s all_even_1p4/tests -t .   # plus the full regression
```

The exit status is 0 when every check of the parts that were run holds. A failed check raises `CertificationError`. A cited result used outside its range raises `HypothesisError`. Neither depends on `assert`, so `python -O` does not switch them off. A partial run (`--quick`, `--slab`) says so in the log, in the JSON (`"complete_run": false`) and in the table.

## Architecture

```
                 interval.py   Iv: outward-rounded Decimal intervals, PREC = 90, rounding audit
                     |
                elementary.py  ln, exp, x^y, arctan(1/m) enclosures (series + explicit tails)
                     |
   primes.py --- constants.py  pi, gamma, e^gamma, C_2, M_0, U_c, li(2), li(e^5)
                     |
                  cited.py     every imported theorem: Citation record + range-checked accessor
                 /   |    \
   prime_bounds.py  remainder.py  sieve_functions.py
   (Mertens sums,   ((*) per      (F, f, h one-sided
    pi(x) bound)     modulus)      bounds)
          \          |      \         |
           \     weights.py  \        |
            \    ((1.1),      \       |
             \   Bonferroni)   \      |
              regime2.py      regime3.py      benchmark.py
              (30 slabs)      (tail)          ([JS] reproduction)
                     \            |            /
                   checks.py (CheckList: named, recorded inequalities)
                              |
                       certificate.py   (runs the parts in order -> CertificateRun)
                              |
                        report.py       (formatting only, directed display rounding)
                              |
                   cli.py / __main__.py
```

Data flow:

1. Every certified inequality goes through `CheckList.require(name, note_ref, lhs, relation, rhs, **inputs)`. It compares the correct one-sided bounds (for `lhs > rhs` it compares lhs.lo with rhs.hi) and records a `Check`: name, note section, the two bounds compared, a certified lower bound for the margin, and the inputs.
2. A full run records 387 checks. All of them appear in `summary.json`.
3. Results are frozen dataclasses (`SlabResult`, `TailResult`, `BenchmarkResult`) that hold every intermediate bound shown in the parameter table.

## Module to note mapping

| Module | Note section | Content |
|---|---|---|
| `interval.py` | 5 | Interval type. Each operation states its rounding direction. Sets the Inexact/Rounded traps. Holds the `sqrt` fix. |
| `elementary.py` | 5 | log, exp, real powers, arctan series, with tail bounds stated. |
| `constants.py` | 0.4, 0.5, 5 | pi (Machin), gamma (Euler-Maclaurin), C_2, M_0, U_c = 2e^-gamma C_2, li(2), li(e^5). |
| `primes.py` | - | Primes up to P_CUT = 30000. Exact integer helpers. |
| `cited.py` | 0.1-0.6 | All cited results (list below). |
| `prime_bounds.py` | 0.2, 0.3, 0.4, 3 item 4 | E_<(x) bounds, sum of 1/p bounds, pi(x) <= x/(log x - 2) + sqrt(x) log x/(8 pi). |
| `remainder.py` | 1, (*) | Per-modulus remainder bound (*), the omega(N) bound. |
| `weights.py` | 1 (1.1), 2 Lemma 1 | Weight conditions z y^4 >= X, y^5 > X. Elementary symmetric functions, Bonferroni truncations. |
| `regime2.py` | 2, 3 | Slab schedule, choice of z and y, q-sums, exact and analytic sieve branches, moduli range checks, main term, err_A, err_Aq, err_q2, net. |
| `sieve_functions.py` | 0.1 (Lemma 19), 4.3 | One-sided bounds for F, f, h, uniform for s' >= s. |
| `regime3.py` | 4.1-4.4 | alpha, z_0, H, the epsilon bound and table row, delta_V, the 200-slice q-sum, R1, R2, rq, q2, net. |
| `benchmark.py` | 5 (Benchmark 0), 0.2 | [JS] Theorem 1.4 ranges and the Theorem 5.9 coefficient. |
| `checks.py`, `certificate.py`, `report.py`, `cli.py` | - | Infrastructure. `report.py` only formats. |

## Cited results (provenance; all in `cited.py`)

| Key | Source | Statement used | Range validated at call time |
|---|---|---|---|
| OeSHP | Oliveira e Silva, Herzog, Pardi (2014), as quoted in [BJS] s1 and [JS] s1 | Goldbach holds for N <= 4e18 | Regime 1 only; nothing computed |
| JS-L5.1 | [JS] arXiv:2208.01229v3, Lemma 5.1 (label `epilem`), GRH | \|pi(x;q,a) - li(x)/phi(q)\| <= c_pi(X2) sqrt(x) log x | X2 >= 4e18. The moduli condition 3 <= d <= sqrt(X_lo) is a named check per slab. |
| BS-L1 | [BS] arXiv:2211.08844v1, Lemma 1 (Schoenfeld 1976, Cor. 1), RH | \|pi(x) - li(x)\| <= sqrt(x) log x/(8 pi) | x >= 2657 (see Issues found, item 3) |
| BS-L4 | [BS] Lemma 4 (Robin) | omega(N) < 1.3841 log N/log log N | N >= 3 |
| BS-L5 | [BS] Lemma 5 (Buthe) | sum mu^2 <= 0.608x; sum mu^2/phi <= 1.1 log x | x >= 1e9, as log H > log 1e9 |
| JS-L3.1 | [JS] Lemma 3.1 (label `Alem`) | \|A\| > N/log N | N >= 71 |
| JS-L3.2 | [JS] Lemma 3.2 (label `mertenlem`), (3.1)-(3.3) | Mertens bounds with 2.964e-6, 1.614e-3, 6.836e-6 | x >= 2; x > e^8.9; x > 1e12 |
| BJS-L16 | [BJS] arXiv:2207.09452v6, Lemma 16 | sum_{p<=x} 1/p < log log x + M + 2/(sqrt(x) log x) | 2 <= x <= 1e12 |
| BJS-T6 | [BJS] v6, Theorem 6 (label `theo:JR`) and Table 1 (24 rows, data in `BJS_TABLE_1`) | Explicit linear sieve, upper with C_1, lower with C_2 | 1/eps >= 74; eps < eps' = 1/k; s >= 2 (D >= z^2); s_min >= 1 (D/q >= z) |
| BJS-L19 | [BJS] v6, Lemma 19 (= Cai Lemma 2); monotonicity from [JS] s2 | Explicit F on (0, 4], f on (0, 4] | Domains enforced in `sieve_functions.py`. F is extended to [3, 5] via the delay equation (note 0.1). |
| BJS-L38 | [BJS] v6, Lemma 38 (label `vjlem`), j = 0 | V(x) = U_N/log x [...] with constants 1.45, 10, 1.002 | x >= 285 |
| BJS-L23 | [BJS] v6, Lemma 23 | sum mu^2 <= 0.65x | Benchmark only |
| JS-L5.7/5.8/T5.9 | [JS] Lemmas 5.7, 5.8, Theorem 5.9, Lemmas 3.3, 3.4 | p_G, c_4G, the 1.48 coefficient | Benchmark only |

The elementary facts that the note proves itself (note section 0.4) are not citations, so they live where they are used:

- li(x) < x/(log x - 2) for x >= e^5. The run checks li(e^5) < e^5/3.
- log(t-1)/t is increasing on [2, 4].
- -log(1-x) <= x + x^2/(2(1-x)).

## Regression reference

`tests/data/original_reference.json` freezes, to all 90 digits, every bound produced by an earlier single-file implementation of the same certificate (10 constants; z, y, main, err, net for all 30 slabs; 18 interval fields of the tail). The regression tests require every bound of this package to agree with it, allowing a difference only in the conservative direction and of at most 1e-80. The current run agrees in all digits.

## Tests (`tests/`, run with `python -m unittest`)

- **`test_interval.py`.** Outwardness on 400 randomised rational inputs, compared with exact `Fraction`s:
  - +, -, *, / at all endpoint pairs; negation; integer powers;
  - sqrt, checked as lo^2 <= a <= hi^2;
  - exact squares; division by an interval containing 0 is refused; immutability; the rounding audit is active; consistency of exp(ln x).
  - A test also shows why sqrt needs care: `Decimal.sqrt` gives the same half-even result under ROUND_FLOOR and ROUND_CEILING, and that result is above sqrt(3).
- **`test_cited.py`.** Every accessor refuses out-of-range use: X2 < 4e18, x < 2657, N < 3, x < 1e9, N < 71, each Mertens range, 1/eps < 74, x < 285. The table has 24 rows, increasing in 1/eps, with C1 and C2 non-increasing. Every citation has provenance.
- **`test_no_float.py`.**
  - An AST scan of every package module rejects float/complex literals, `float`/`complex`/`round`, imports of math/cmath/random/statistics/numpy, float-valued clocks, and int-literal / int-literal.
  - A self-test makes sure the scanner catches six planted violations.
  - A runtime check confirms the JSON summary contains no float.
- **`test_regression.py`.**
  - The constants are checked.
  - A fast regression covers slab 1 (exact branch) and slab 22 (analytic branch, the minimum margin).
  - The full regression (`ALL_EVEN_1P4_FULL=1`) covers all slabs, the tail and the benchmark.

## Reproducibility

Python >= 3.10, standard library only. A full run takes about 3 minutes on one core. Outputs are written by

```
python -m all_even_1p4 --json ../tables/summary.json --table ../tables/parameter_table.md > ../tables/run_log.txt
```

`summary.json` and `parameter_table.md` contain no timestamps or platform data and are reproducible byte for byte; `run_log.txt` ends with the measured run time.

## Known limitations

1. **Tail regime.** The code checks the product hypothesis of [BJS] Theorem 6 at the sieving level z only. The proof of that theorem uses it at all lower levels, where these parameters violate it (eps >= 0.0164 on [97, 113)). The tail numbers are therefore not a proof; see the repository README.
2. **0.608 versus 0.65.** The squarefree-count constant 0.608 ([BS] Lemma 5, attributed to Buthe) is used; [BJS] Lemma 23 has 0.65, with which the tail net would be about 0.00141.
3. **Schoenfeld's bound** is validated for x >= 2657, the range usually attributed to Schoenfeld (primary paper not read); every use has x >= 30000.
4. **Conservative choices.** f(s) >= f(4) and F(s) <= F(5) are used beyond those arguments, which costs about 0.02 of the tail bracket.
5. **Primary sources not read first-hand:** Grenie-Molteni beyond the quoted corollary, Schoenfeld, Buthe, Robin, Oliveira e Silva-Herzog-Pardi, Cai, Halberstam-Richert, Nathanson.
6. **Static float scan.** It cannot detect int/int division between two variables, only between literals; the runtime `Inexact`/`Rounded` traps cover the Decimal paths.
