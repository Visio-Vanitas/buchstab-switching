# buchstab-switching

Explicit Chen-type results for **every** even integer, conditional on GRH for Dirichlet L-functions: representations `N = p + P_K` with no "sufficiently large" threshold, obtained from explicit weighted linear sieves and certified numerics. The name refers to the two devices the programme is organised around, Buchstab iteration and Chen's switching (role reversal).

## Statement currently on the table

> **(GRH)** Every even `N >= 4` is `p + η` with `p` prime and `Ω(η) <= 4`.

Prior explicit all-`N` results: `Ω(η) <= 31` under GRH and `Ω(η) <= 395` unconditionally (Johnston–Starichkova, arXiv:2208.01229), from the explicit Chen theorem of Bordignon–Johnston–Starichkova (arXiv:2207.09452). They remark that their method cannot go below `K = 4`.

GRH enters only through an explicit bound for `π(x; q, a)` (Johnston–Starichkova Lemma 5.1, from Grenié–Molteni), i.e. level of distribution `1/2` with explicit constants for each modulus. The premise is pinned to the Lean formalisation at `leanprover-community/riemann-hypothesis@91b273530883b723ef4422436e0dc3557749325a` (`src/Challenge.lean`, Mathlib-only statements).

## Method

Sifted set `A = {N − p : p ≤ N, p ∤ N}`, density `g(p) = 1/(p−1)` on `p ∤ N`, linear sieve. Kuhn–Richert type weights on `z ≤ q < y` with `z·y^4 ≥ N`, `y^5 > N` (in the tail `z = N^{1/22}`, `y = N^{21/88}`; per-slab integers below `10^170`):

`w(a) = 1 − ½·#{z ≤ q < y : q | a} − ½·#{z ≤ q < y : q² | a}`,

and `w(a) > 0`, `(a, P(z)) = 1` force `Ω(a) <= 4`. No switching term is needed at `K = 4`.

Three regimes:

| Range | Argument | Margin |
|---|---|---|
| `4 <= N <= 4·10^18` | numerical verification of Goldbach (Oliveira e Silva–Herzog–Pardi) | n/a |
| `4·10^18 <= N < 10^170` | 30 contiguous slabs; exact pre-sieve by small primes, hybrid Bonferroni truncation, monotonicity in the primes dividing `N` so that one evaluation covers every `N` in a slab | min. net `3.31·10^-4` |
| `N >= 10^170` | explicit Jurkat–Richert linear sieve (arXiv:2207.09452v6, Thm 6, Table 1 at `ε' = 1/100`, `C_1 = 276`, `C_2 = 277`), pre-sieve by primes `< 41`, monotonicity in `N` of every `N`-dependent term | net `1.489·10^-3` |

All inequalities are checked by a single stdlib-only Python certificate: integers and directed-rounding decimals at 90 digits, no floats, `Inexact`/`Rounded` trapped outside directed contexts. Runtime about 3.5 minutes.

## Status (read this before citing)

- Two rounds of independent refereeing found no arithmetic or logical error in the derivations. Every imported statement was compared with the TeX source of the cited papers.
- The range `N < 10^170` has drawn no substantive objection.
- **Open point, tail regime.** Theorem 6 of arXiv:2207.09452v6 assumes `∏_{u ≤ p < z} (1 − g(p))^{-1} ≤ (1+ε) log z / log u` "for all `1 < u < z`". We verify it with the top endpoint fixed at the sieving level (`ε ≤ 8.526·10^-3`), as the published `K = 31` application does. Whether the Jurkat–Richert induction behind the theorem also needs the condition at intermediate levels `w < z` is being settled by an independent derivation; if it does, short intervals just above the pre-sieve (e.g. `[41, 47)`) push `ε` above the table row used and the tail must be redone with a larger pre-sieve. Until that is closed the all-`N` statement should be read as conditional on that theorem exactly as stated.
- The tail margin is thin and sensitive to `C_1` (it dies at `C_1 = 280`); widening it by using `F(s)`, `f(s)` at the true arguments instead of `F(5)`, `f(4)` is in progress.
- Primary sources not yet read first-hand: Schoenfeld, Büthe, Robin, Cai, Halberstam–Richert (monotonicity of `F`, `f`), Nathanson Ch. 9.
- `K = 3` for all even `N >= 4` is work in progress and is **not** claimed.

## Contents

To be added: the note, the certificate script and its output, a per-slab parameter table, a Lean statement file (`Challenge.lean`, Mathlib only) with `#print axioms` and comparator output.

## What we ask of readers

1. Does the quantifier in the linear-sieve hypothesis need intermediate levels (Nathanson, Lemma 9.8, Thms 9.5 and 9.7)?
2. Any missing error term in the tail, given the size of the margin.
3. Once posted: does `Challenge.lean` say what the sentence above says?

Derivations and scripts were produced largely by AI agents under human direction and refereed by independent readers; treat every claim here as unrefereed in the journal sense.
