# Shared Sieve Notes, Linear-Sieve Certifiers, and Provenance Data (`shared/`)

Shared mathematical derivations, linear-sieve certification code, and SHA-256-verified provenance
data used by both [`k4/`](../k4/README.md) (`1 + 4`) and [`k3/`](../k3/README.md) (`1 + 3`).

## Contents

| Path | Description |
| :--- | :--- |
| [`notes/linear-sieve/`](notes/linear-sieve/README.md) | Explicit $\beta = 2$ Jurkat–Richert linear sieve with arbitrary pre-sieve `Q₀` under the closed-interval `(H*)` hypothesis (`S1`–`S6`), including why fixed-`z` / half-open hypotheses fail (`BJS` Theorem 6 counterexample and `Table 1` discrepancy) |
| `notes/block-sieve/brun-block-sieve.md` | Brun combinatorial block lower/upper sieve (`Theorem A` parity truncation, explicit block remainder `E^±`, level bound, and prime-divisor omission monotonicity `Lemma C`) |
| `certificate/linear_sieve/` | Independent stdlib-only Python certifiers (`hstar_certify.py`, `cn_certify.py`, `tau_constants.py`, `core_checks.py`) generating/auditing closed `(H*)` bounds (`hstar.log`) and explicit `C₁(ε), C₂(ε)` tables (`cn_rows_all.json`) |
| `data/linear_sieve_inputs/` | Pinned SHA-256 provenance inputs (`logs/hstar.log`, `cn_rows_all.json`, and sweep logs) consumed by both `k4/certificate/all_even_1p4_ext/tail_x31.py` and `k3/scripts/sieve_cert/linear_sieve.py` |
| `data/linear_sieve_constants/` | Recorded outputs from `cn_certify.py`, `hstar_certify.py`, `tau_constants.py`, and `core_checks.py` |
