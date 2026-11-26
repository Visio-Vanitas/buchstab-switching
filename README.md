# buchstab-switching

Explicit Chen-type results for **every** even integer, conditional on GRH for Dirichlet L-functions: representations `N = p + P_K` with no "sufficiently large" threshold, obtained from explicit weighted linear sieves and certified numerics. The name refers to the two devices the programme is organised around, Buchstab iteration and Chen's switching (role reversal).

## Target statement

> **(GRH)** Every even `N >= 4` is `p + η` with `p` prime and `Ω(η) <= 4`.

Prior explicit all-`N` results: D. R. Johnston (2026) reports `Ω(η) <= 16` under GRH (thesis summary, Bull. Aust. Math. Soc. 113 (2026), 372–374, Theorem 2), improving `Ω(η) <= 31` under GRH and `Ω(η) <= 395` unconditionally (Johnston–Starichkova, arXiv:2208.01229), from the explicit Chen theorem of Bordignon–Johnston–Starichkova (arXiv:2207.09452). They remark that their method cannot go below `K = 4`.

GRH enters only through an explicit bound for `π(x; q, a)` (Johnston–Starichkova Lemma 5.1, from Grenié–Molteni), i.e. level of distribution `1/2` with explicit constants for each modulus. The premise is pinned to the Lean formalisation at `leanprover-community/riemann-hypothesis@91b273530883b723ef4422436e0dc3557749325a` (`src/Challenge.lean`, Mathlib-only statements).

## Method

Sifted set `A = {N − p : p ≤ N, p ∤ N}`, density `g(p) = 1/(p−1)` on `p ∤ N`, linear sieve. Kuhn–Richert type weights on `z ≤ q < y` with `z·y^4 ≥ N`, `y^5 > N` (per-slab integers below `10^500`):

`w(a) = 1 − ½·#{z ≤ q < y : q | a} − ½·#{z ≤ q < y : q² | a}`,

and `w(a) > 0`, `(a, P(z)) = 1` force `Ω(a) <= 4`. No switching term is needed at `K = 4`.

Three ranges:

| Range | Argument | Margin |
|---|---|---|
| `4 <= N <= 4·10^18` | numerical verification of Goldbach (Oliveira e Silva–Herzog–Pardi) | n/a |
| `4·10^18 <= N < 10^500` | 58 contiguous slabs, each certified with a Brun block sieve (blocks of primes with caps on the number of prime factors; parity rule for lower/upper bounds), monotonicity in the primes dividing `N` so that one evaluation covers every `N` in a slab | min. net `> 1.6796·10^-3` |
| `N >= 10^500` | explicit Jurkat–Richert linear sieve with an arbitrary pre-sieve set, proved here under the hypothesis on all closed prime intervals with `ε = 1/80` (`C_1 = 391.82`, `C_2 = 390.69`); pre-sieve by the odd primes `<= 82` and `103, 107, 191, 223` | net `> 0.07522` (`> 0.03909` with the classical recursion constants) |

All inequalities are checked by a stdlib-only Python certificate: integers and directed-rounding decimals, no floats. Every certified number has been reproduced by an independent replay from the recorded parameters.

## Status (read this before citing)

- **The argument covers every even `N >= 4`.** Each part (the weighted inequality, the block sieve, the corrected linear sieve and its constants, the certificate code for both computed ranges) was read by several independent readers, each part at least twice, with no error found.
- **Correction to the literature.** Theorem 6 of Bordignon–Johnston–Starichkova (arXiv:2207.09452v6) states its product hypothesis only at the theorem's own `z`; its Jurkat–Richert induction uses it on all closed prime intervals, and under the fixed-`z` condition alone the key lemma fails (explicit profile at `n = 3`, `s = 1.5`). Its Table 1 is not reproduced by its own recursion. We prove the theorem under the all-intervals hypothesis with an arbitrary pre-sieve and recompute the constants.
- Quoted without a first-hand check of the source: the Goldbach verification to `4·10^18`; Nathanson, *Additive Number Theory: The Classical Bases*, Thm 9.4 (identification of the sieve functions `F`, `f`); Johnston–Starichkova Lemmas 3.1, 5.1, (3.1)–(3.3) and the monotonicity of `F`, `f`; Schoenfeld; Robin.
- `K = 3` for all even `N >= 4` is work in progress and is **not** claimed.

## Contents

| Path | What |
|---|---|
| `notes/proof-map.md` | **start here**: the theorem, the three ranges with final parameters, what is quoted |
| `notes/frame-weighted-inequality.md` | sources quoted verbatim, the weighted inequality, the worst case over the primes dividing `N` (§0–§2) |
| `notes/linear-sieve/` | the explicit linear sieve with pre-sieve under the closed-interval hypothesis (S1–S4), and why weaker hypotheses do not suffice (S5–S6) |
| `notes/block-sieve/` | the Brun block sieve used for `4·10^18 <= N < 10^500` |
| `certificate/` | stdlib-only Python: `all_even_1p4/` (interval layer, cited bounds, remainders, tests), `all_even_1p4_ext/` (block-sieve slabs, linear-sieve tail, replay), `linear_sieve/` (certification of the pre-sieve hypothesis and of the constants `C_1`, `C_2`) |
| `data/` | certified ladder and tail (`certificate/`), pre-sieve and constant certificates (`linear_sieve_inputs/`, `linear_sieve_constants/`), replay logs |
| `lean/AllEvenOnePlusFour/` | Lake project (Lean `v4.37.0-rc1`, Mathlib `31ce06ea`): `Challenge.lean` (Mathlib-only statement), kernel-checked weight lemma (`w(a) > 0 ⟹ Ω(a) ≤ 4`), and the reduction of the theorem to explicit analytic hypotheses (stated with the earlier split point `10^170`). `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`. The analytic number theory is not formalised. |

Labels such as `X26`, `X31`, `X32` in code comments and raw logs refer to the frame note, the linear-sieve notes and the block-sieve note respectively.

## Reproduce

```
cd certificate
python3 -m pytest -q all_even_1p4/tests
python3 -I all_even_1p4_ext/replay.py ../data/certificate/ladder_4e18_500_all.json ../data/certificate/tail/tail_at_500.json
```

The replay re-certifies all 58 slabs and the tail from the recorded parameters (a few minutes) and ends with `ALL PASS`.

## What we ask of readers

1. Does `lean/AllEvenOnePlusFour/Challenge.lean` say what the target statement says (note `η = 1` is allowed, `Ω(1) = 0`)?
2. The explicit linear sieve with pre-sieve under the closed-interval hypothesis, and its constants.
3. Any missing remainder term in either computed range.

Derivations and scripts were produced largely by AI agents under human direction and refereed by independent readers; treat every claim here as unrefereed in the journal sense.
