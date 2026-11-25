# AllEvenOnePlusFour

A Lean 4 / Mathlib formalisation skeleton for note X26:

> Under GRH for Dirichlet L-functions, every even N ≥ 4 is p + η with p prime and
> Ω(η) ≤ 4, where Ω counts prime factors with multiplicity.

Mathematical source: `research/goldbach/notes/X26-all-even-1p4-under-grh.md`.
Review: `research/goldbach/notes/R18-review-X26-repaired.md`.
R18's verdict is "not refuted, not proved for all N": Regime 3 depends on how the
hypothesis of [BJS] Theorem 6 is read, and that question is still open. This project does not
hide this. Every analytic or computational input is an explicit `Prop` hypothesis. None is an
`axiom`.

## Status: compiled (2026-11-25)

`lake build` completes (18313 jobs, 0 errors) with `leanprover/lean4:v4.37.0-rc1` and Mathlib
`31ce06ea`. `lake env lean AxiomsCheck.lean` exits with status 0. Every library theorem
depends only on `propext`, `Classical.choice` and `Quot.sound`. `sorryAx` appears only for
`all_even_one_plus_four` in `Challenge.lean`. The analytic inputs remain explicit hypotheses
(see below), so this checks the reduction, not the analytic number theory.

One statement was corrected for the build. In `Sanity.lean`,
`allEvenPrimePlusAlmostPrime_iff_isAtMostAlmostPrime` had `m.IsAtMostAlmostPrime K`. Mathlib's
signature is `Nat.IsAtMostAlmostPrime (k n : ℕ)`, so dot notation made that
`IsAtMostAlmostPrime m K`, and the proof did not typecheck. It now reads
`Nat.IsAtMostAlmostPrime K m`, which is what the docstring and this README always said. No
other file was changed.

## Toolchain

| | |
|---|---|
| Lean | `leanprover/lean4:v4.37.0-rc1` (`lean-toolchain`) |
| Mathlib | `31ce06eaadf4a200c0e1407c5f10953cf606b8f8` (`lakefile.toml`, pinned in `lake-manifest.json`) |

These are the versions of the upstream `riemann-hypothesis` formalisation at commit
`91b273530883b723ef4422436e0dc3557749325a`, so `Challenge.lean` is checked against the same
Mathlib as the upstream GRH statements. `lake-manifest.json` came from a `lake update` that
resolved all dependencies. No build was run.

## Build

```sh
lake exe cache get   # prebuilt Mathlib; do not build Mathlib from source
lake build 2>&1 | tee build_log.txt
lake env lean AxiomsCheck.lean
```

## Files

| File | Content | Status |
|---|---|---|
| `Challenge.lean` | Mathlib only. It holds the four upstream GRH `Prop`s (copied verbatim), `AllEvenPrimePlusAlmostPrime K` and the challenge `theorem all_even_one_plus_four (hGRH : DirichletLNonvanishingRightOfHalf) : AllEvenPrimePlusAlmostPrime 4 := by sorry`. | **Statement only.** Its `sorry` follows the challenge-file convention and is not a proof. |
| `AllEvenOnePlusFour/Statement.lean` | Namespaced copies of `DirichletLNonvanishingRightOfHalf` and `AllEvenPrimePlusAlmostPrime`, so the library never imports the `sorry`. | definitions |
| `AllEvenOnePlusFour/Sanity.lean` | Checks that the statement is not vacuous: monotone in K; equivalent to the `primeFactorsList.length` form and to Mathlib's `Nat.IsAtMostAlmostPrime`; `4 = 3 + 1` (m = 1 is allowed); `K = 0` is false (N = 10); Goldbach for 4 ≤ N ≤ 40 with explicit witnesses. | proved (no sorry) |
| `AllEvenOnePlusFour/Weights.lean` | Note §1: if a ≥ 1, every prime factor of a is ≥ z, N ≤ z·y⁴, N < y⁵, a < N and w(a) > 0, then Ω(a) ≤ 4. | proved (no sorry) |
| `AllEvenOnePlusFour/Bonferroni.lean` | Note §2 Lemma 1: Σ_{j≤m} (−1)^j C(k,j) = (−1)^m C(k−1,m) for k ≥ 1. This is Mathlib's `Int.alternating_sum_range_choose_eq_choose`. Also the Bonferroni signs (≤ 1[k=0] for m odd, ≥ 1[k=0] for m even). | proved (no sorry) |
| `AllEvenOnePlusFour/Reduction.lean` | The sifted set, the weighted sum Σ_{a∈A,(a,P(z))=1} w(a), the hypotheses, and the main theorems. | proved (no sorry), **from explicit hypotheses** |
| `AllEvenOnePlusFour/GRHInterface.lean` | [JS] Lemma 5.1, written as a `Prop` (`PrimesInAPBound`, `JSLemma51`). | statement only; not used or assumed anywhere |
| `AxiomsCheck.lean` | Checks by `Iff.rfl` that the library copies agree with `Challenge.lean`, then runs `#print axioms` on every main theorem. | |

## Proved in Lean (kernel-checked, from the explicit hypotheses)


- `AllEvenOnePlusFour.cardFactors_le_four_of_weight_pos`. This is the weight lemma of note
  §1, and the combinatorial heart of inequality (1.1).
- `AllEvenOnePlusFour.exists_prime_add_of_weightedSum_pos`. If the weighted sum is positive
  for some admissible (z, y), then N = p + m with Ω m ≤ 4.
- `AllEvenOnePlusFour.prime_add_of_lt_tailStart`. Regimes 1 and 2 give every even
  4 ≤ N < 10¹⁷⁰. This theorem does not use the disputed Regime 3.
- `AllEvenOnePlusFour.all_even_one_plus_four_of_inputs : AnalyticInputs → AllEvenPrimePlusAlmostPrime 4`.
- `AllEvenOnePlusFour.all_even_one_plus_four_of_conditionalInputs : ConditionalInputs → DirichletLNonvanishingRightOfHalf → AllEvenPrimePlusAlmostPrime 4`.
  In `AxiomsCheck.lean` the same theorem is restated with the challenge file's own definitions
  (`all_even_one_plus_four_of_conditionalInputs'`).
- The Bonferroni identity and its signs, and the sanity lemmas.

## Explicit hypotheses (not proved in Lean)

| Field | Regime | Statement | Source |
|---|---|---|---|
| `regime1 : GoldbachUpTo (4·10¹⁸)` | 1, 4 ≤ N ≤ 4·10¹⁸ | Goldbach for even N in that range | Oliveira e Silva–Herzog–Pardi, a computation (quoted via [BJS] §1 and [JS] §1; the primary paper was not read) |
| `regime2 : WeightedSievePositiveOn (Set.Ico (4·10¹⁸) (10¹⁷⁰))` | 2 | For every even N in the range there are z, y with N ≤ z·y⁴, N < y⁵ and Σ_{a sifted} w(a) > 0 | The certificate script `certify_all_even_1p4.py` (30 Bonferroni slabs), with [JS] Lemma 5.1 (GRH), Schoenfeld under RH as quoted in [BS] Lemma 1, [JS] Lemmas 3.1 and 3.2, and [BJS] Lemma 16 |
| `regime3 : WeightedSievePositiveOn (Set.Ici (10¹⁷⁰))` | 3 | The same statement for N ≥ 10¹⁷⁰ | [BJS] Theorem 6 (arXiv:2207.09452v6, explicit linear sieve, Table 1 row 100), with [BJS] Lemma 38, [BS] Lemmas 4 and 5, and [JS] Lemma 5.1. **Open after R18**: the hypothesis scope of [BJS] Theorem 6 (fixed upper endpoint z, or all subintervals) is undecided. |

In `ConditionalInputs`, `regime2` and `regime3` take the form
`DirichletLNonvanishingRightOfHalf → …`, so the role of GRH is visible in the statement.

How the hypotheses match the sieve. Exchanging the order of summation gives
Σ_{a sifted} w(a) = S(A,P(z)) − ½ Σ_q S(A_q,P(z)) − ½ Σ_q #{a sifted : q² ∣ a}.
This is at least the right-hand side of (1.1), the quantity the sieve bounds from below.
That exchange is described in a docstring and is not formalised. It is not needed in Lean,
because the hypotheses are stated directly about the weighted sum.

Not formalised. The passage from the Möbius weights λ_d of Lemma 1 to the binomial sum is not
formalised; only the binomial identity and its signs are. Lemma 2 (removing the primes that
divide N) is not formalised either, and none of the numerics are.

## Is the challenge statement faithful?

`AllEvenPrimePlusAlmostPrime 4` says: for every N with 4 ≤ N and N even, there exist p and m
with p prime, 0 < m, N = p + m and Ω m ≤ 4. Ω is `ArithmeticFunction.cardFactors`, the number
of prime factors counted with multiplicity. Some subtleties:

- m = 1 is allowed, and Ω 1 = 0. So "at most 4 prime factors" includes η = 1, which happens
  when N − 1 is prime. The note does the same ("η = 1 needs no exclusion"). Requiring
  m ≥ 2 would give a different, stronger statement, which neither the note nor this project
  proves. The condition 0 < m excludes m = 0, for which Mathlib sets Ω 0 = 0. For even N ≥ 4 it
  is in fact redundant, since m = 0 would force N = p to be prime. It is kept so that Ω is
  only ever applied to positive integers.
- The statement is equivalent to the `m.primeFactorsList.length ≤ 4` form and to
  `Nat.IsAtMostAlmostPrime 4 m` (see `Sanity.lean`).
- The premise is `DirichletLNonvanishingRightOfHalf`, taken from upstream. It ranges over all
  moduli and all characters, primitive or not. The trivial character at s = 1 is excluded.

## Build log

The full output is in `build_log.txt`. Summary: `Build completed successfully (18313 jobs).`
All warnings are of four kinds:
- the "imports `Mathlib` … module system" notice on every file;
- `push_neg` deprecated (prefer `push Not`), in `Weights.lean` ×4 and `Reduction.lean` ×2;
- `if_neg` deprecated, in `Bonferroni.lean` ×2;
- `declaration uses sorry` at `Challenge.lean:58`, which is the challenge statement.

## `#print axioms` output

Verbatim output of `lake env lean AxiomsCheck.lean`, with the module-system notices dropped:

```
'allEvenPrimePlusAlmostPrime_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
'dirichletLNonvanishingRightOfHalf_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
'all_even_one_plus_four_of_conditionalInputs'' depends on axioms: [propext, Classical.choice, Quot.sound]
'AllEvenOnePlusFour.pow_cardFactors_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AllEvenOnePlusFour.cardFactors_lt_of_lt_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'AllEvenOnePlusFour.cardFactors_le_four_of_weight_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'AllEvenOnePlusFour.truncated_alternating_sum_choose' depends on axioms: [propext, Classical.choice, Quot.sound]
'AllEvenOnePlusFour.truncated_alternating_sum_choose_le_of_odd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AllEvenOnePlusFour.le_truncated_alternating_sum_choose_of_even' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AllEvenOnePlusFour.rough_of_mem_siftedPrimes' depends on axioms: [propext, Classical.choice, Quot.sound]
'AllEvenOnePlusFour.exists_prime_add_of_weightedSum_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'AllEvenOnePlusFour.prime_add_of_lt_tailStart' depends on axioms: [propext, Classical.choice, Quot.sound]
'AllEvenOnePlusFour.all_even_one_plus_four_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'AllEvenOnePlusFour.all_even_one_plus_four_of_conditionalInputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AllEvenOnePlusFour.AllEvenPrimePlusAlmostPrime.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'AllEvenOnePlusFour.allEvenPrimePlusAlmostPrime_iff_primeFactorsList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AllEvenOnePlusFour.allEvenPrimePlusAlmostPrime_iff_isAtMostAlmostPrime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AllEvenOnePlusFour.four_eq_prime_add_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AllEvenOnePlusFour.not_allEvenPrimePlusAlmostPrime_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AllEvenOnePlusFour.goldbach_of_le_forty' depends on axioms: [propext, Classical.choice, Quot.sound]
'AllEvenOnePlusFour.primePlusAlmostPrime_one_of_le_forty' depends on axioms: [propext, Classical.choice, Quot.sound]
'all_even_one_plus_four' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## References (as quoted in note X26)

- [BJS] Bordignon, Johnston, Starichkova, arXiv:2207.09452v6.
- [JS] Johnston, Starichkova, arXiv:2208.01229v3.
- [BS] Bordignon, Starichkova, arXiv:2211.08844v1.
