# Explicit β = 2 linear sieve under the all-levels hypothesis

- **Date:** 2026-11-25
- **Subject:** a self-contained replacement for [BJS] Theorem 6 (arXiv 2207.09452v6, label `theo:JR`), written after an independent derivation showed that the published proof needs the product condition at all lower levels.
- **Standing premise:** GRH is treated as a theorem; it plays no role in this note.

## 0. Summary

1. **Theorem (S1).** Let `g` be multiplicative on a set of primes 𝐏 with `0 ≤ g(p) < 1`, and suppose
   `∏_{u ≤ p < w} (1 − g(p))^{-1} ≤ K · log w / log u` for all real `1 < u < w ≤ z`, with `K < 1 + ε`
   (equivalently: the same on all closed intervals of consecutive primes of 𝐏 below `z`). Then for the β = 2 Rosser weights of level `D`, with `s = log D / log z`,
   `G(z, λ⁺) < V(z)(F(s) + ε C₁ e² h(s))` for `s ≥ 1`, and `G(z, λ⁻) > V(z)(f(s) − ε C₂ e² h(s))` for `s ≥ 2`,
   where `C₁ = Σ_{n odd} τ_n`, `C₂ = Σ_{n even} τ_n` and `τ_n` is the recursion of [BJS] (eq. `eq:tau`) with one correction (item 3). The proof is written out in `this note-sections/S1-core-theorem-and-induction.md`. One external input remains: the identification of `1 ± Σ f_n` with the classical `F`, `f` (Nathanson, Theorem 9.4).
2. **Sieve theorem with a pre-sieve (S2).** `this note-sections/S2-presieve-and-fundamental-identity.md` proves the properties of the weights, the fundamental identity, and the passage to `S(A, 𝐏, z)` with an arbitrary pre-sieve set ℚ; the hypothesis is then needed for 𝐏∖ℚ only.
3. **Corrections to [BJS] found on the way.**
   - Lemma `lem:hsm1`: `γ_{s₀} = e^{s₀−2}` must be `e^{s₀−1.8}` (the paper's own remark uses `γ₂ = e^{0.2}`).
   - Case `n` odd, `s < 3`: `(c_n)^{n−2}` must be `(c_{n−1})^{n−2}`; in the proof of Lemma `lemma:forg`, `e^{−s}H(s)` must be `e^{s}H(s)`; in (`lilFdeffn`) "n odd" must be "n even".
   - **Tables `tab:tau` and `tab:fF` are not reproduced by the recursion (`eq:tau`).** For `n = 2` the maximum contains `ξ₃`, which forces `τ₂ ≥ 3κ₃ + 2γ₃ > 9.75`; the table prints 8.
4. **Constants recomputed (rigorous rational arithmetic, `certificate/linear_sieve/tau_constants.py`).** With the `c_n` of [BJS] Table `tab:cn1` as input:

   | 1/ε | C₁ | C₂ | printed in [BJS] |
   |---|---|---|---|
   | 74 | 801.38 | 802.33 | 631, 630 |
   | 80 | 584.76 | 586.53 | 461, 461 |
   | 90 | 426.15 | 428.50 | 336, 337 |
   | 100 | 349.85 | 352.49 | 276, 277 |
   | 120 | 275.49 | 278.40 | 218, 219 |
   | 200 | 192.92 | 196.13 | 153, 154 |
   | 1000 | 141.50 | 144.90 | 113, 114 |

   The ratio to the printed values is about 1.27 throughout. With only the proved bound `c_n ≤ 0.9607` the constants are about twelve times larger (4221 at 1/ε = 100), so **the table of `c_n` is an essential input and is not certified here**. Full output: `data/linear_sieve_constants/tau_constants_output.txt`. A float scouting run suggests the printed 276 arises if `ξ₃` is dropped from the even step and the uncorrected `γ` is used; this is an observation, not a claim about the authors' code.
5. **Hypothesis in the application (S3).** For `g(p) = 1/(p−1)` and worst case over `N` (any subset of odd primes outside ℚ) a single sifting prime `p` forces `ε ≥ 1/(p−2)`. `certificate/linear_sieve/hstar_certify.py` builds a pre-sieve set and certifies the closed-interval supremum; e.g. target 1/100 passes with ℚ = {odd p ≤ 102} ∪ {107, 109, 137, 149, 191, 227}, `log ∏ℚ ≤ 117.62`, certified `ε* ≤ 0.009941` (run log in `data/linear_sieve_constants/`).
6. **Consequence for the frame note.** No pre-sieve admissible at `ε ≤ 1/74` lets Regime 3 start at `10^170` (S3, Proposition F). The start `N₃` of a valid tail was estimated at `10^420`–`10^480` with the printed constants; with the constants of item 4 it will be higher. This estimate is heuristic. Closing all `N` now needs either Regime 2 extended to `N₃`, or a sharper theorem (level-dependent ε, or avoiding the real level `D^{1/3}`); both are being worked on.

## 1. What is and is not established

- Established before this note and unaffected: `4 ≤ N < 10^170` (the earlier slab certificate, after review).
- Not established: any statement for `N ≥ 10^170`.
- The three sections S1–S3 were written independently from the same source material and later reviewed against each other. Section S1's and S3's scripts were run once (outputs in `data/linear_sieve_constants/`); the outputs agree with the independent script of item 4 where they overlap (`τ₂ = 10.4803…` at ε = 1/200; partial sums 349.84 and 352.48 at ε = 1/100).

## 2. Open items

1. Certify `c_n` (Lemma `lemma:fsmall` of [BJS]) by an independent rigorous computation of `f_n`.
2. External input: Nathanson Theorem 9.4 (`3F̃(3) = 2e^γ`, `f̃(2) = 0`).
3. Referee pass on S1–S3.
4. A theorem with level-dependent ε, so that the small clusters just above the pre-sieve do not dictate the constant.
5. Redo the the frame note tail with the final theorem and constants, and meet it from below with Regime 2.

## 3. Files

- `notes/linear-sieve/S1-core-theorem-and-induction.md`, `S2-presieve-and-fundamental-identity.md`, `S3-hypothesis-for-application.md`
- `certificate/linear_sieve/tau_constants.py` (constants), `core_checks.py` (from S1), `hstar_certify.py` (from S3)
- `data/linear_sieve_constants/*.txt` (run logs)

## 4. Update after the second round (2026-11-25, see after review)

1. **Review.** One independent reader per section: the induction of S1, the weights and pre-sieve passage of S2, and Theorems A, D, Propositions C, F of S3 were checked and found correct; the errors found are in side remarks and are listed after review. The corrections to [BJS] of item 3 above were confirmed against the TeX.
2. **`c_n` certified (S4, `certificate/linear_sieve/cn_certify.py`).** Upper Riemann sums on a mesh 1/1000 with outward rounding give certified `c_n` for `2 ≤ n ≤ 500`. The [BJS] table is confirmed except at five indices where the certified 4-decimal value exceeds the 2-decimal table entry by less than 0.001 (a mesh effect, first at `n = 33`: 0.6905 against 0.69). With the certified values the recursion of item 4 gives `C₁(1/100) ≤ 345.72`, `C₂(1/100) ≤ 348.37`.
3. **Sharper recursion (S4, Theorem 3).** Replacing the majorants `c^{n−2}`, `c^{n−1}` in each branch by the exact suprema of `f_{n−1}(s−1)/(2e²h(s))` and `f_n(s)/(2e²h(s))` on that branch's range gives

   | 1/ε | C₁ | C₂ |
   |---|---|---|
   | 74 | 535.85 | 534.17 |
   | 100 | 235.64 | 235.10 |
   | 200 | 131.13 | 130.99 |

   These are below the values printed in [BJS]. They depend on Theorem 3 of S4, whose proof assumes that the induction uses `f_{n−1}`, `f_n` only through four inequalities; this has to be checked against S1 step by step before the values are used.
4. **Weaker hypotheses do not work (S5, S6).** The half-open prime-interval hypothesis alone is insufficient (explicit profile). A two-tier, level-dependent constant gives only a polynomially small gain. The closed-interval hypothesis with a large pre-sieve is the route.

Additional files: `notes/linear-sieve/S4-…`, `S5-…`, `S6-…`; `certificate/linear_sieve/cn_certify.py`; `data/linear_sieve_constants/cn_certify_output.txt`; `notes/after review-review-this note-explicit-linear-sieve.md`.
