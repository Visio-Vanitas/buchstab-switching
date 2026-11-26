# Shared Literature Directory & Formalization Reference (`shared/references/`)

Single source of truth for primary literature, verified explicit inequalities, arXiv TeX sources,
and explicit analytic constants shared across `k3/`, `k4/`, and `shared/`.

## Directory Layout

| Path | Purpose | Git status |
| :--- | :--- | :--- |
| [`README.md`](README.md) | Master bibliography and document map | Tracked |
| [`selberg-and-mertens.md`](selberg-and-mertens.md) | Verified Selberg `Λ²` (`J_odd`, `H₀`, `α₀`, `C_{f₀}`, `H_{1/4}`, `C_J`, `H̃`) and two-variable Mertens (`JS25`, `BJV22`, `GM19`, `Schoenfeld`, `Robin`) reference | Tracked |
| [`bjs-linear-sieve-and-vj.md`](bjs-linear-sieve-and-vj.md) | Verified BJS v6 Theorem 6 / Lemma 38 (`fHat`, `F`, `h`, `C₁(ε)`, `C₂(ε)`, `δ_V`), version comparison (`v2` vs `v6`), and BS v1 Lemma 11 erratum (`2 e^γ` typo) | Tracked |
| `sources/JS2025_arXiv_2208.01229v3/` | Upstream TeX (`main.tex`, `references.bib`, `main.bbl`) for Johnston–Starichkova (2025) | Gitignored |
| `sources/BJS2025_arXiv_2207.09452v6/` | Upstream TeX (`main.tex`, etc.) for Bordignon–Johnston–Starichkova (2025, v6) | Gitignored |
| `sources/BS2022_arXiv_2211.08844v1/` | Upstream TeX for Bordignon–Starichkova (2024, arXiv:2211.08844v1) | Gitignored |

See also the derivation notes in [`../notes/linear-sieve/README.md`](../notes/linear-sieve/README.md),
[`../notes/block-sieve/brun-block-sieve.md`](../notes/block-sieve/brun-block-sieve.md), and
[`../../k3/NOTES_K3_DERIVATION.md`](../../k3/NOTES_K3_DERIVATION.md).

## Primary Bibliography

1. **BJS25 (`arXiv:2207.09452v6`, *Int. J. Number Theory* **21** (2025), 2497–2572)** — M. Bordignon, D. R. Johnston, V. Starichkova, *An explicit version of Chen's theorem*.
   - **Used for**: Theorem 6 (arbitrary pre-sieve `Q₀` linear sieve under closed-interval `(H*)`), Lemma 38 (`vjlem`, unconditional `δ_V(N, x)` for `x ≥ 285`), and Table 1 (`C₁(1/k), C₂(1/k)` for `k ≥ 74`).
   - **Local source**: `sources/BJS2025_arXiv_2207.09452v6/`.
2. **JS25 (`arXiv:2208.01229v3`, *Acta Math. Hungar.* **177** (2025), 163–192)** — D. R. Johnston, V. Starichkova, *Some explicit results on the sum of a prime and an almost prime*.
   - **Used for**: Lemma 3.2 (two-sided Mertens `1/p` error functions `2.964e-6 / log x`, `6.836e-6 / log x` for `x > 10^12`, `1.614e-3` for `x > exp(8.9)`), Lemma 5.1 (Grenié–Molteni AP prime counting with `li(2)` term), and Lemma 5.7/5.8 (`c_π(X)`).
   - **Local source**: `sources/JS2025_arXiv_2208.01229v3/main.tex`.
3. **BS24 (`arXiv:2211.08844v1`, *Ramanujan J.* **64** (2024), 1213–1242)** — M. Bordignon, V. Starichkova, *An explicit version of Chen's theorem assuming the Generalized Riemann Hypothesis*.
   - **Warning (Verified Errata)**: Lemma 1 contains `x ≥ 3` typo for Schoenfeld's `x ≥ 2657` bound (fails at `x = 3, 4`); Lemma 11 contains a `2 e^γ` typo instead of `2 e^{-γ}` and we intentionally avoid BS v1 Lemma 11 in favor of unconditional **BJS v6 Lemma 38 (`deltaV_bjs`)**.
   - **Local source**: `sources/BS2022_arXiv_2211.08844v1/`.
4. **BJV22 (`arXiv:2207.09452v2` / *Ramanujan J.* / pre-v6)** & **RI80** — H. Iwaniec, *A new form of the error term in the linear sieve* (1980), closed-interval `(H*)` formulation detailed in [`../notes/linear-sieve/`](../notes/linear-sieve/README.md).
5. **Schoenfeld (1976, *Math. Comp.* **30**, 337–360, Corollary 1)** & **Rosser–Schoenfeld (1962, *Illinois J. Math.* **6**, 64–94, Theorem 1 / Corollary 1)**:
   - Under RH, `|π(x) - li(x)| ≤ √x log x / (8π)` for **`x ≥ 2657`** (never apply for `x < 2657`).
   - Unconditional Chebyshev bound `π(x) < 1.25506 x / log x` for `x > 1` (`x ≥ 17` for RS Corollary 1 eq. (3.6)).
6. **Grenié–Molteni (2019, *J. Number Theory* **200**, Corollary 1 & *Ramanujan J.* **49**, 535–548)** — Explicit GRH Brun–Titchmarsh / AP remainder bound for `|π(x; d, a) - Li(x) / φ(d)|`.
7. **Robin (1983, *Acta Arith.* **42**, Théorème 11)** — `ω(N) < 1.3841 log N / log(log N)` for `N ≥ 3`.
8. **BJV22 Lemma 16 (`exp(10) < x ≤ 10^12`)** — `∑_{p < x} 1/p ≤ log(log x) + M₀ + 2 / (√x log x)`.
9. **Broadbent, Kadiri, Lumley, Ng, Wilk (2021, *Math. Comp.* **90**, 2281–2315)** & **Oliveira e Silva, Herzog, Pardi (2014, *Math. Comp.* **83**, 2033–2060)** (`4 ≤ N ≤ 4 · 10^18`).
