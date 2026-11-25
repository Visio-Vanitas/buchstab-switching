# buchstab-switching

Explicit Chen-type results for **every** even integer, conditional on GRH for Dirichlet L-functions: representations `N = p + P_K` with no "sufficiently large" threshold, obtained from explicit weighted linear sieves and certified numerics. The name refers to the two devices the programme is organised around, Buchstab iteration and Chen's switching (role reversal).

## Target statement

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

- **Established, with no substantive objection after two rounds of independent refereeing:** under GRH every even `4 <= N < 10^170` is `p + η`, `Ω(η) <= 4`. Every imported statement was compared with the TeX source of the cited papers; the certificate reruns byte-identically.
- **Tail regime `N >= 10^170`: not established, under repair.** Theorem 6 of arXiv:2207.09452v6 states its hypothesis `∏_{u ≤ p < z} (1 − g(p))^{-1} ≤ (1+ε) log z / log u` "for all `1 < u < z`" at the theorem's own `z`. An independent derivation, confirmed by three referees, shows that the Jurkat–Richert induction behind it (Lemma on `T_n`, in particular the case `n` odd, `1 <= s < 3`, which passes through the level `D^{1/3}`) uses the condition at all lower levels, including real ones, i.e. on closed prime intervals `[u, v]`; under the fixed-`z` condition alone the lemma fails (explicit profile at `n = 3`, `s = 1.5`). With a pre-sieve below 41 our data violate the all-levels condition (`ε ≈ 0.0165` on `[97, 113)`), so the tail as written is outside the theorem as proved. A corrected statement (all-levels hypothesis, arbitrary pre-sieve set, recomputed `C_1`, `C_2`) and a redesigned tail with the slab method pushed beyond `10^170` are in progress. The all-`N` statement above is therefore a target, not a claim.
- Primary sources not yet read first-hand: Schoenfeld, Büthe, Robin, Cai, Halberstam–Richert (monotonicity of `F`, `f`), Nathanson Ch. 9.
- `K = 3` for all even `N >= 4` is work in progress and is **not** claimed.

## Contents

| Path | What |
|---|---|
| `notes/all-even-1p4-under-grh.md` | the argument, with quoted imports (internal review labels R17/R18 refer to refereeing rounds) |
| `certificate/` | stdlib-only certificate script and its output |
| `tables/` | per-slab parameter table (A), Lean output table (B), raw rerun data |
| `lean/AllEvenOnePlusFour/` | Lake project (Lean `v4.37.0-rc1`, Mathlib `31ce06ea`): `Challenge.lean` (Mathlib-only statement), kernel-checked weight lemma (`w(a) > 0 ⟹ Ω(a) ≤ 4`), Bonferroni signs, and the reduction of the theorem to explicit analytic hypotheses, one per regime. `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` only; `sorryAx` only for the challenge statement. The analytic number theory is hypothesis there, not proof. |

## What we ask of readers

1. The scope of the product hypothesis in the explicit linear sieve (Nathanson, Lemma 9.8, Thms 9.5 and 9.7): is there a formulation weaker than all levels that the induction supports?
2. Any missing error term in the tail, given the size of the margin.
3. Does `lean/AllEvenOnePlusFour/Challenge.lean` say what the target statement says (note `η = 1` is allowed, `Ω(1) = 0`)?

Derivations and scripts were produced largely by AI agents under human direction and refereed by independent readers; treat every claim here as unrefereed in the journal sense.
