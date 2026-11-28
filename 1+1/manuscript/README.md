# Manuscript: Explicit All-Range Linnik–Goldbach Reduction (`K = 18`, v2)

- **LaTeX Source**: [`linnik_goldbach_all_range.tex`](linnik_goldbach_all_range.tex)
- **Compiled PDF**: [`linnik_goldbach_all_range.pdf`](linnik_goldbach_all_range.pdf)
- **Pinned Verified Source Snapshot**: `Visio-Vanitas/buchstab-switching` (`feat/one-plus-one-v436`), commit `d5081e7a2dae5d8067c43d92cf35403ce12f0ee4`

## Build Command

```sh
cd 1+1/manuscript
pdflatex -interaction=nonstopmode linnik_goldbach_all_range.tex
pdflatex -interaction=nonstopmode linnik_goldbach_all_range.tex
```

## Summary of v2 Upgrades Reflected in This Manuscript (vs. v1 `K = 22` Draft)

1. All-range explicit Linnik–Goldbach reduced from **`K = 22`** (`N ≥ 48` exact) to **`K = 18`** (`N ≥ 40` exact, `N ≥ 4` with `0 ≤ s ≤ 18` and `k_j ≥ 1`); bridge threshold `N_br(18) = (2^19 - 2) * 2^61 + 4 * 10^18 ≈ 1.208925e24`.
2. Strengthened Lean predicate `HasLinnikRep` directly enforces `(∀ k ∈ ks, 1 ≤ k)` in `OnePlusOne/Core/Defs.lean` and `comparator/ChallengeOnePlusOneDefs.lean`.
3. Eliminated BOTH additive safety allowances from v1 (`+0.06` in `avg_S2_pintz_ruzsa_bound` and `+4.00` in `proved_C_E2_const`), replaced by exact unit-interval Bochner–Hadamard `C_E2 ≤ 31.3259`, exact Parseval prime-power bound, exact `gcd` and major-arc `U ≤ U_q` vertical contour bounds, and self-contained odd squarefree `q ≤ 105` Ramanujan sums + `D_1 = 2000` tail + prefix sums up to `1,800,000`.
4. Added pure effective asymptotic GRH `K = 6` (`C_1 = 8.0`, no Siegel theorem, margin `≥ 0.0798`) and zero-float reproduction of Li–Liu's Lichtman `K = 5` (`C_1 = 6.7814`, margin `≥ 0.0044`).
5. Fixed Reference `[4]` LaTeX formatting (`4 \cdot 10^{18}`).
