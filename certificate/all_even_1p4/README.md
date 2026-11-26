# all_even_1p4: certificate for note X26 as an auditable package

**Status.** This certificate checks arithmetic given the cited theorems; it does not prove the cited theorems. The tail regime (N >= 10^170) depends on the hypothesis scope of the explicit linear sieve theorem ([BJS] Theorem 6): review R18 (`notes/R18-review-X26-repaired.md`) leaves open whether its product hypothesis is needed only at the sieving level z, as the note assumes, or also at levels below z. Under the second reading, Regime 3 fails. The claim of note X26 stays at level `conjecture`.

## Purpose

Note `notes/X26-all-even-1p4-under-grh.md` claims that, under GRH, every even N >= 4 is p + eta with p prime and Omega(eta) <= 4. The note splits this into three regimes:

| Regime | Range | How it is covered |
|---|---|---|
| 1 | 4 <= N <= 4e18 | Cited Goldbach verification (Oliveira e Silva, Herzog, Pardi). Nothing is computed. |
| 2 | 4e18 <= N < 10^170 | 30 slabs, each with a Bonferroni sieve plus switching (note sections 2-3). |
| 3 | N >= 10^170 | Explicit linear sieve [BJS] Theorem 6 with a pre-sieve (note section 4). |

This package is a restructured version of `scripts/certify_all_even_1p4.py`. The mathematics is unchanged: same parameters, same lemmas, same order of every interval operation. The original script is still in place and was not modified. The package adds:

- named, recorded checks;
- explicit hypothesis checks for every cited result;
- a JSON summary and a Markdown parameter table;
- tests;
- the fixes for the minor defects found in review R18.

## How to run

Run everything from `research/goldbach/scripts`. You need Python 3.10 or later and the standard library only.

```
python -m all_even_1p4                          # full certificate, about 3 minutes
python -m all_even_1p4 --json out.json --table out.md
python -m all_even_1p4 --quick                  # everything except the tail (about 20 s)
python -m all_even_1p4 --slab 22 [--slab 1]     # only the given slabs
python -m unittest discover -s all_even_1p4/tests -t .                 # fast tests (about 30 s)
ALL_EVEN_1P4_FULL=1 python -m unittest discover -s all_even_1p4/tests -t .   # plus the full regression
python -m all_even_1p4.tests.make_original_reference   # rebuild the reference from the original script
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

| Module | Note X26 section | Content |
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

## Equivalence with the original script

Evidence for equivalence:

1. **Reference file.** `tests/make_original_reference.py` imports the unmodified original by path and calls its own functions. It writes every bound those functions return to `tests/data/original_reference.json` as an exact 90-digit Decimal string:
   - for each slab: z, y, main.lo, err.hi, net.lo;
   - every field of the Regime 3 result;
   - all constants;
   - the benchmark output.
2. **Consistency check.** `test_reference_matches_original_output` confirms that this reference agrees with the committed text output `data/certify_all_even_1p4_output.txt` to its 6 printed decimals.
3. **Comparison.** The full regression test runs the package and compares every one of these values.

**Result of the comparison.** Every returned value is identical in all 90 digits, in both directions of every interval. This covers:

- the 10 constants;
- z, y, main, err and net of all 30 slabs;
- the 18 interval fields of Regime 3.

The original does not return its benchmark values, so the benchmark K values and the two coefficients are compared with its printed output: K exactly, the coefficients to 4 decimals.

Headline numbers, original and package:

| Quantity | Original script | This package (90-digit lower bound, shown to 21 digits) |
|---|---|---|
| Minimum slab margin (slab 22) | net >= 0.000331 | net >= 0.000331115585209829503 |
| Tail net coefficient | NET COEFF >= 0.001489 | net >= 0.00148936701796414746 |

**Why the sqrt fix changes no digit.** The fix does change some intermediate endpoints, by one unit in the 90th digit:

- `sqrt(10^33)` and `sqrt(10^45)` had a lower endpoint above the true root;
- other roots had an upper endpoint below it.

In this run none of these changes survives the outward rounding of the operations that follow. The test would accept a difference only in the conservative direction (lower bounds lower, upper bounds higher) and of at most 1e-80.

**Printed numbers do differ.** Display rounding is now directed (Issues found, item 2). As a result, 38 of the 90 six-decimal slab numbers printed by the original change by 1e-6 in the conservative direction. Some Regime 3 numbers change too:

| Quantity | Original printed | Package printed |
|---|---|---|
| f(s) - eps' C2 e^2 h(s) | >= 0.975815 | >= 0.975814 |
| 1/2 sum_q | <= 0.973127 | <= 0.973128 |
| tot_err | <= 0.001194 | <= 0.001195 |
| R1 | | <= 0.000016 |
| R2 | | <= 0.001091 |
| q2 | | <= 8.81e-5 |

The minimum slab margin (0.000331) and the tail net (0.001489) print the same.

## Tests (`tests/`, run with `python -m unittest`)

- **`test_interval.py`.** Outwardness on 400 randomised rational inputs, compared with exact `Fraction`s:
  - +, -, *, / at all endpoint pairs; negation; integer powers;
  - sqrt, checked as lo^2 <= a <= hi^2;
  - exact squares; division by an interval containing 0 is refused; immutability; the rounding audit is active; consistency of exp(ln x).
  - A test also shows the original leak: `Decimal.sqrt` gives the same half-even result under ROUND_FLOOR and ROUND_CEILING, and that result is above sqrt(3).
- **`test_cited.py`.** Every accessor refuses out-of-range use: X2 < 4e18, x < 2657, N < 3, x < 1e9, N < 71, each Mertens range, 1/eps < 74, x < 285. The table has 24 rows, increasing in 1/eps, with C1 and C2 non-increasing. Every citation has provenance.
- **`test_no_float.py`.**
  - An AST scan of every package module rejects float/complex literals, `float`/`complex`/`round`, imports of math/cmath/random/statistics/numpy, float-valued clocks, and int-literal / int-literal.
  - A self-test makes sure the scanner catches six planted violations.
  - A runtime check confirms the JSON summary contains no float.
- **`test_regression.py`.**
  - The reference file is checked against the original's text output.
  - The constants are checked.
  - A fast regression covers slab 1 (exact branch) and slab 22 (analytic branch, the minimum margin).
  - The full regression (`ALL_EVEN_1P4_FULL=1`) covers all slabs, the tail and the benchmark.

## Reproducibility

- Python 3.13.18, standard library only, on Linux with 4 cores. Another job was running at the same time.
- Full run: 177 s wall clock, including the module-level constants (most of the time is the 200-slice tail sum). On the same machine the original took about 217 s (18 s import, 7 s Regime 2, 192 s Regime 3).
- Outputs, written by `python -m all_even_1p4 --json ../data/all_even_1p4/summary.json --table ../data/all_even_1p4/parameter_table.md > ../data/all_even_1p4/run_log.txt`:

| File | SHA-256 |
|---|---|
| `data/all_even_1p4/summary.json` | `8aa72886b57ca03709453ee8beeb5524db30b7c1c9a2f6b26c910c7cc633bbb3` |
| `data/all_even_1p4/parameter_table.md` | `802861702e9961b591af0f4548c3e63c4aa8b8fbb9a62ca5f3524151e1c1084d` |
| `data/all_even_1p4/run_log.txt` | `73b223ffd3e805869c53f28e860f90b872b5e01f5a4b8a19a83b2797370ccaae` |

`summary.json` and `parameter_table.md` contain no timestamps or platform data. `run_log.txt` ends with the measured run time, so its hash changes from run to run.

## Issues found

### Defects fixed here, as review R18 asked (X26r_v2 findings 1, 2, 3, 5)

1. **Rounding leak in `_sqrt` / `Iv.sqrt`.**
   - `Decimal.sqrt` always rounds half-even, whatever the context's rounding. The original's "floor" and "ceiling" square roots could therefore be off by half an ulp in the wrong direction.
   - Fix: `interval.sqrt_down` and `interval.sqrt_up` take that result as a candidate and step it with `next_minus` / `next_plus` until an exact square comparison holds, i.e. lo^2 <= a <= hi^2. The square is computed at 2·PREC+4 digits with the Inexact trap on, so its exactness is checked mechanically.
   - The leak is real but numerically irrelevant here: no certified value changed.
2. **Display rounding was not directed.** f-strings round half-even, so 38 printed slab bounds and several Regime 3 bounds were not true bounds at their printed precision. Example: slab 30 printed `err<=0.000000`, but its err bound is 4.26e-7. `report.py` now rounds lower bounds down and upper bounds up. The original also printed slab ends through float formatting (`{X_lo:.0e}`); they are now printed exactly.
3. **False comment "M0 cancels identically".** In interval arithmetic the width of the M_0 enclosure (about 3.3e-5) is added to the sum of 1/(q-1), which is conservative. The docstring of `regime2.q_sums` now says this.
4. **False comment in `omega_ub_iv`.** It said callers pass the slab's upper end. They pass X_lo, which is correct because omega(N) log N/N decreases. `remainder.omega_upper` now documents this.

### Recorded, behaviour unchanged

1. **Decisive, Regime 3 only (R18).** Which reading of the product hypothesis of [BJS] Theorem 6 is correct is still open: upper endpoint fixed at z, or also levels p_1 < z inside the induction. The code checks the fixed-z reading. Under the other reading, eps >= 0.0164 > 1/74 on [97, 113) and the theorem does not apply. This package cannot decide it.
2. **0.608 versus 0.65 (R18 finding 1).** The squarefree density 0.608 ([BS] Lemma 5, attributed to Buthe) is used as in the original. The attached [BJS] Lemma 23 has 0.65. Per R18, the net would fall to about 0.00141, which is still positive. Not changed.
3. **Schoenfeld range (R18 finding 2).** [BS] Lemma 1 is quoted "for x >= 3", which is false at x = 3. The accessor validates x >= 2657 instead, the range usually attributed to Schoenfeld; this was not checked in the primary paper. Every use has x >= 30000, so behaviour is identical.
4. **Note section 3 is inaccurate about the q^2 branch.**
   - The note says the branch with (*) for d = q^2 "is used only in slab 1".
   - Like the original, the code uses it whenever y^4 <= X_lo. That holds in slabs 1-6, 23-28 and 30; see the `q^2` column of the parameter table.
   - The branch is valid wherever its condition holds, and the condition is checked exactly, so only the note's description is wrong.
5. **Numbers quoted in the note.** The note quotes the original's half-even display values, which are not certified at 6 decimals. Use these instead:

   | Note value | Corrected |
   |---|---|
   | >= 0.975815 | >= 0.975814 |
   | <= 0.973127 | <= 0.973128 |
   | tot_err <= 0.001194 | <= 0.001195 |
   | slab 22 main >= 0.000734 | >= 0.000733 |
6. **Hypothesis never checked explicitly in the original.** [JS] Lemma 3.1 (N >= 71) is now validated. It holds trivially.
7. **Dead code removed.** The exact-count branch of `pi_ub_iv` (z <= P_CUT) was unreachable: every call has x > P_CUT. The unused `verbose` parameter of `regime3` was also removed.
8. **Conservative choices kept as they are (R18 finding 3).**
   - f(s) >= f(4) at s = 8.01 and F(s) <= F(5) for s > 5.
   - Regime 3 is very sensitive to C1(1/100): C1 >= 280 would make the net negative.
   - It also depends on the computational Mertens bound [BJS] Lemma 16.
9. **Unread primary sources (R18 finding 6).** Grenie-Molteni beyond the quoted corollary, Schoenfeld, Buthe, Robin, Oliveira e Silva-Herzog-Pardi, Cai, Halberstam-Richert, and Nathanson (Lemma 9.8, Theorems 9.5 and 9.7, on which the pre-sieved form of Theorem 6 rests).

I found no new mathematical error in the arithmetic of the original while restructuring it.
