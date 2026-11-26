# buchstab-switching

Explicit conditional Chen-type representations $N = p + m$ for **every** even integer $N \ge 4$
under the Generalized Riemann Hypothesis (GRH) for Dirichlet $L$-functions, with no "sufficiently
large" threshold. The repository is split symmetrically into two verified packages plus shared
analytic sieve infrastructure:

- [`k4/`](k4/README.md): **`1 + 4` ($\Omega(\eta) \le 4$ for all even $N \ge 4$)** — Brun block sieve on $[4 \cdot 10^{18}, 10^{500})$ + closed-interval `(H*)` linear sieve on $[10^{500}, \infty)$, stdlib-only Python interval certificates, and Lean 4 reduction (`k4/lean/AllEvenOnePlusFour/`).
- [`k3/`](k3/README.md): **`1 + 3` ($\Omega(m) \le 3$ for all even $N \ge 4$)** — One-step Buchstab–Richert weighted sieve switching across `127` finite slabs on $[4 \cdot 10^{18}, 10^{600})$ (`2a`/`2b`/`2c`, Bonferroni + Brun block + adaptive Selberg $\Lambda^2$) + closed-interval `(H*)` linear sieve + Selberg $\Lambda^2$ on $[10^{600}, \infty)$, outward-rounded Python certifier (`PREC = 90`), and Lean 4 formalization (`k3/BuchstabSwitching/`) discharging `BuchstabSeries`, finite closed-interval `(H*)`, Lean kernel `C₂ ≤ 494`, and Regime 2/3 sieve engines.
- [`shared/`](shared/README.md): **Shared linear-sieve and block-sieve foundations** — notes `S1`–`S6`, Brun block sieve proof, linear-sieve `(H*)`/`C₁, C₂` Python certifiers, and SHA-256-verified provenance inputs.

## Pinned GRH Statement & Toolchain

Both Lean 4 formalizations (`k4/lean/AllEvenOnePlusFour/` and `k3/`) use:

- **Toolchain**: `leanprover/lean4:v4.37.0-rc1` with Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8` (`propext`, `Classical.choice`, `Quot.sound` only; zero custom `axiom` declarations, zero `native_decide`).
- **GRH Statement Source**: `DirichletLNonvanishingRightOfHalf` matches verbatim the Mathlib-only statement in [`lsernau/grh-lean`](https://github.com/lsernau/grh-lean) at commit `72fead102f663d5c7a407964a13dc0cf9d977207` (`grh-compact/src/Statements.lean` and `grh/src/Statements.lean`, where `src/Main.lean` proves `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`).

GRH enters both certificates only through the explicit AP prime-counting bound of Grenié–Molteni / Johnston–Starichkova (`arXiv:2208.01229v3`, Lemma 5.1). Both packages use the closed-interval `(H*)` correction replacing Bordignon–Johnston–Starichkova (`arXiv:2207.09452v6`, Theorem 6).

## Summary of Certified Results

| Package | Target ($\forall$ even $N \ge 4$) | Finite Range | Tail Range | Lean 4 Project |
| :--- | :--- | :--- | :--- | :--- |
| [`k4/`](k4/README.md) | $\Omega(\eta) \le 4$ | `[4·10^18, 10^500)`: `58` Brun block slabs (`min net > 1.6796e-3`) | `[10^500, ∞)`: linear sieve `ε = 1/80` (`net > 0.07522`) | [`k4/lean/AllEvenOnePlusFour/`](k4/lean/AllEvenOnePlusFour/README.md) (`Challenge.lean` reduction + `comparator`) |
| [`k3/`](k3/README.md) | $\Omega(m) \le 3$ | `[4·10^18, 10^600)`: `127` slabs (`min net >= 0.001833`, `min sieve_net >= 0.009891`) | `[10^600, ∞)`: closed `(H*)` `Q0_100` + Lean `C₂ ≤ 494` (`cap 495`, `net >= 0.046862`, `tol = 609.2x`; `100:old` `0.051917`, `100:new` `0.055822`) | [`k3/`](k3/README.md) (one-step switching, Brun/Bonferroni/Selberg/BJS engines, `by decide` certs + `comparator`) |

## Reproduce

### `k4/` (`1 + 4`)
```bash
cd k4/certificate
python3 -m pytest -q all_even_1p4/tests
python3 -I all_even_1p4_ext/replay.py ../data/certificate/ladder_4e18_500_all.json ../data/certificate/tail/tail_at_500.json

cd ../lean/AllEvenOnePlusFour
lake exe cache get
lake build Challenge AllEvenOnePlusFour
lake env lean AxiomsCheck.lean
bash comparator/run_comparator.sh
```

### `k3/` (`1 + 3`)
```bash
cd k3
lake exe cache get
lake build
lake env lean BuchstabSwitching/Sieve/AxiomsAudit.lean
lake env lean AxiomsCheckK3.lean
python3 scripts/quick_verify.py
python3 scripts/certify_omega_le_3.py   # regenerates certified_bounds.txt, certified_slabs.json, Data.lean
bash comparator/run_comparator.sh
```
