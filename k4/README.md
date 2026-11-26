# All-Even `1 + 4` Subpackage (`k4/`)

Explicit conditional proof for **every** even integer under GRH for Dirichlet $L$-functions:

> **(GRH)** Every even $N \ge 4$ is $p + \eta$ with $p$ prime and $\Omega(\eta) \le 4$.

The GRH premise `DirichletLNonvanishingRightOfHalf` is pinned to the Mathlib-only definition
in [`lsernau/grh-lean`](https://github.com/lsernau/grh-lean) (commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, `grh-compact/src/Statements.lean` and
`grh/src/Statements.lean`, proved in `src/Main.lean` as `LFunction_ne_zero_of_half_lt_re`).

## Method & Regimes

Sifted set $A = \{N - p : p \le N,\ p \nmid N\}$, density $g(p) = 1/(p-1)$ on $p \nmid N$, with
Kuhn–Richert weights $w(a) = 1 - \frac{1}{2}\#\{z \le q < y : q \mid a\} - \frac{1}{2}\#\{z \le q < y : q^2 \mid a\}$
satisfying $z y^4 \ge N$ and $y^5 > N$ (`w(a) > 0`, $(a, P(z)) = 1 \implies \Omega(a) \le 4$):

| Range | Argument | Margin |
| :--- | :--- | :--- |
| `4 <= N <= 4·10^18` | Numerical verification of Goldbach (Oliveira e Silva–Herzog–Pardi) | n/a |
| `4·10^18 <= N < 10^500` | `58` contiguous slabs certified with the Brun block sieve + divisor-omission monotonicity | `min net > 1.6796e-3` |
| `N >= 10^500` | Explicit closed-interval `(H*)` linear sieve (`Q₀`, `ε = 1/80`, `C_1 = 391.82`, `C_2 = 390.69`; shared inputs in `../shared/data/linear_sieve_inputs/`) | `net > 0.07522` (`> 0.03909` old recursion) |

## Contents

- [`notes/`](notes/proof-map.md): `proof-map.md` (architecture and parameter summary) and `frame-weighted-inequality.md` (combinatorial frame & prime-divisor worst case).
- [`certificate/`](certificate/all_even_1p4/README.md): stdlib-only Python packages `all_even_1p4/` (interval arithmetic, cited bounds, remainders, pytest suite) and `all_even_1p4_ext/` (Brun block slabs, linear-sieve tail, replay). Reads linear-sieve provenance from `../shared/data/linear_sieve_inputs/`.
- [`data/certificate/`](data/certificate/README.md): certified ladder (`ladder_4e18_500_all.json`, `LADDER_TABLE.md`), tail (`tail/tail_at_500.json`), cross-checks, and replay logs.
- [`lean/AllEvenOnePlusFour/`](lean/AllEvenOnePlusFour/README.md): Lean `v4.37.0-rc1` / Mathlib `31ce06ea` project containing `Challenge.lean`, kernel-checked weight lemma `w(a) > 0 ⟹ Ω(a) ≤ 4`, reduction to explicit regime hypotheses at `10^500`, and `comparator/` verification (`propext`, `Classical.choice`, `Quot.sound`).

## Reproduce

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
