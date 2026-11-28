<p align="center">
  <img src="assets/logo.svg" alt="buchstab-switching logo" width="128" />
</p>

# buchstab-switching

Explicit conditional Chen-type representations $N = p + m$ for **every** even integer $N \ge 4$
under the Generalized Riemann Hypothesis (GRH) for Dirichlet $L$-functions, with no "sufficiently
large" threshold. The repository is split symmetrically into two verified packages plus shared
analytic sieve infrastructure:

- [`k4/`](k4/README.md): **`1 + 4` ($\Omega(\eta) \le 4$ for all even $N \ge 4$)** — Brun block sieve on $[4 \cdot 10^{18}, 10^{500})$ + closed-interval `(H*)` linear sieve on $[10^{500}, \infty)$, stdlib-only Python interval certificates, and Lean 4 reduction (`k4/lean/AllEvenOnePlusFour/`).
- [`k3/`](k3/README.md): **`1 + 3` ($\Omega(m) \le 3$ for all even $N \ge 4$)** — One-step Buchstab–Richert weighted sieve switching across `127` finite slabs on $[4 \cdot 10^{18}, 10^{600})$ (`2a`/`2b`/`2c`, Bonferroni + Brun block + adaptive Selberg $\Lambda^2$) + closed-interval `(H*)` linear sieve + Selberg $\Lambda^2$ on $[10^{600}, \infty)$, outward-rounded Python certifier (`PREC = 90`), and Lean 4 formalization (`k3/BuchstabSwitching/`) reducing `AllEvenPrimePlusAlmostPrime 3` (`all_even_one_plus_three_of_classical`) to GRH + 4 classical literature premises by discharging `RobinOmegaBound` (`robinOmegaBound_holds`), `CertifiedConstants` (`canonicalConstants`), `EulerProductVPremise` (`eulerProductVPremise_of_schoenfeld_and_mertens`), `BuchstabSeries`, closed-interval `(H*)` (`Q0_100`), Lean kernel `C₂ ≤ 494`, all `127` Regime 2 slabs via binary `Dyadic` proof-by-reflection (`SlabCertInst*`), and all `120` Regime 3 ray strips (`RayCertInst*`).
- [`shared/`](shared/README.md): **Shared linear-sieve and block-sieve foundations** — notes `S1`–`S6`, Brun block sieve proof, linear-sieve `(H*)`/`C₁, C₂` Python certifiers, and SHA-256-verified provenance inputs.

## Pinned GRH Statement & Toolchain

Both Lean 4 formalizations (`k4/lean/AllEvenOnePlusFour/` and `k3/`) use:

- **Toolchain**: `leanprover/lean4:v4.36.0` with Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (`propext`, `Classical.choice`, `Quot.sound` only; zero custom `axiom` declarations, zero `native_decide`).
- **GRH Statement Source**: `DirichletLNonvanishingRightOfHalf` matches verbatim the Mathlib-only statement in [`lsernau/grh-lean`](https://github.com/lsernau/grh-lean) at commit `72fead102f663d5c7a407964a13dc0cf9d977207` (`grh-compact/src/Statements.lean` and `grh/src/Statements.lean`, where `src/Main.lean` proves `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`).

GRH enters both certificates only through the explicit AP prime-counting bound of Grenié–Molteni / Johnston–Starichkova (`arXiv:2208.01229v3`, Lemma 5.1). Both packages use the closed-interval `(H*)` correction replacing Bordignon–Johnston–Starichkova (`arXiv:2207.09452v6`, Theorem 6).

## Active Formalization Branch (`on-dev`)

Pull requests discharging the remaining classical analytic lemmas in `k3/BuchstabSwitching/External/` should target the **`on-dev`** branch (`leanprover/lean4:v4.36.0`, Mathlib `fc4f59e5`):

- **Already Discharged in Lean 4**: `BuchstabSeriesPremise` (`buchstabSeriesPremise_proved`), `RobinOmegaBound` (`robinOmegaBound_holds`, PR `#4`), `CertifiedConstants` (`canonicalConstants`), and `EulerProductVPremise` (`eulerProductVPremise_of_schoenfeld_and_mertens`).
- **Retained External Computational Premise (Out of Scope)**: `SmallEvenPremise` (`4 ≤ N < 4 * 10^18` distributed binary prime verification, Oliveira e Silva–Herzog–Pardi 2014) is intentionally kept as an external finite-table premise and is excluded from formalization PRs.
- **Open Contributor Targets (`3` Analytic Lemmas)**:
  1. **`JSLemma51Premise canonicalLi2`** ([`k3/BuchstabSwitching/External/CharacterSums/DirichletGRH.lean`](k3/BuchstabSwitching/External/CharacterSums/DirichletGRH.lean)) — Explicit GRH prime counting in arithmetic progressions (Grenié–Molteni 2019, Cor. 1; Johnston–Starichkova `arXiv:2208.01229v3`, Lemma 5.1).
  2. **`SchoenfeldPrimePremise canonicalLi2`** ([`k3/BuchstabSwitching/External/SchoenfeldRH/PrimeCountingRH.lean`](k3/BuchstabSwitching/External/SchoenfeldRH/PrimeCountingRH.lean)) — Schoenfeld (1976, Cor. 1) explicit RH prime-counting bound $|\pi(x) - \operatorname{li}(x)| \le \frac{\sqrt{x}\log x}{8\pi}$ for $x \ge 2657$.
  3. **`MertensPrimeSumPremise meisselMertensConst`** ([`k3/BuchstabSwitching/External/MertensSums/ReciprocalPrimeSums.lean`](k3/BuchstabSwitching/External/MertensSums/ReciprocalPrimeSums.lean)) — Explicit Mertens reciprocal-prime sum bounds (Johnston–Starichkova `arXiv:2208.01229v3`, Lemma 3.2; BJS `arXiv:2207.09452v6`, Lemmas 16–17).

See [`k3/CONTRIBUTING.md`](k3/CONTRIBUTING.md) and [`k3/BLUEPRINT.md`](k3/BLUEPRINT.md) for modular PR instructions and fast local verification workflows.

## Summary of Certified Results

| Package | Target ($\forall$ even $N \ge 4$) | Finite Range | Tail Range | Lean 4 Project |
| :--- | :--- | :--- | :--- | :--- |
| [`k4/`](k4/README.md) | $\Omega(\eta) \le 4$ | `[4·10^18, 10^500)`: `58` Brun block slabs (`min net > 1.6796e-3`) | `[10^500, ∞)`: linear sieve `ε = 1/80` (`net > 0.07522`) | [`k4/lean/AllEvenOnePlusFour/`](k4/lean/AllEvenOnePlusFour/README.md) (`Challenge.lean` reduction + `comparator`) |
| [`k3/`](k3/README.md) | $\Omega(m) \le 3$ | `[4·10^18, 10^600)`: `127` slabs (`min net >= 0.001763`, `min sieve_net >= 0.003969`, `min tol = 1.04x`) | `[10^600, ∞)`: closed `(H*)` `Q0_100` + Lean `C₂ ≤ 494` (`cap 495`, `net >= 0.046825`, `C₂ break-even <= 1853.2`, `tol = 608.7x`; `100:old` `0.051880`, `100:new` `0.055785`) | [`k3/`](k3/README.md) (`all_even_one_plus_three_of_classical`, binary `Dyadic` reflection on `127` slabs + `120` ray strips, `by decide` + `comparator`) |

## Reproduce

### `k4/` (`1 + 4`)
```bash
cd k4/certificate
python3 -m unittest discover -s all_even_1p4/tests -t .
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
python3 scripts/certify_omega_le_3.py   # regenerates scripts/data/certified_bounds.txt and scripts/data/certified_slabs.json
python3 scripts/generate_lean_data.py   # regenerates BuchstabSwitching/Certificates/Data.lean from certified_slabs.json
python3 -m scripts.sieve_cert.slab_witness_export  # regenerates 12 binary Dyadic witness shards SlabCertInstData*.lean
bash comparator/run_comparator.sh
```
