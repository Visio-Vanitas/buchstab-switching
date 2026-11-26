# X31 tail: least N_3 per eps = 1/k, and the Regime 2 ladder above 10^170

Status: **unchecked**. Nothing here has been reviewed. Computed 2026-11-25.

## What is certified, for which N

- **Tail (Regime 3, X26 structure with the X31 closed-interval hypothesis).** For each k in the table, the tail
  certificate `X31Tail.certify` returns a positive lower bound on the net for every even N >= 10^e, where e is the
  `log10 N_3` column. The same certificate with e - 1 fails (column "net at e-1"). The search used 60 slices to
  bisect and 200 slices for the final certificate.
- **Regime 2 (Bonferroni slabs, the package's `certify_slab`, unchanged).** `ladder.json` is a contiguous chain of
  slabs from 10^170 upward. Its last `x_hi` is where the ladder stops (see `LADDER.md`).
- **Gap.** Between the top of the ladder (about 10^238.7, slab 54) and the best N_3 (10^399, k = 80, sharper
  recursion) nothing is certified. The slab method is limited by the even Bonferroni order (m_even <= 6 is the
  largest that passes the level constraint), so it cannot simply be extended to 10^399.

## Inputs

- C1(1/k), C2(1/k): independent rerun of `cn_certify` (scripts/x31_linear_sieve) for both recursions,
  `x31_linear_sieve/run_cn.py`. Exact Fractions are in `cn_rows_all.json`; complete logs are in `logs/cn_*.log`. The table in
  `N3_TABLE.md` prints them rounded **up** at 1e-6 from the Fractions (`mk_n3_table.py`). The tail uses the
  Fractions themselves.
- Q0(k) and its log upper bound: `x31_linear_sieve/hstar_rows.py` (hstar_certify targets extended to k = 74..200), log in
  `logs/hstar.log`. All rows PASS.
- f, F at their true arguments: an outward Riemann grid of the delay-differential equations (`sieve_fF.py`), with
  f(8) >= 0.999738 and F(8) <= 1.000378. Squarefree density 0.65 (more conservative than 0.608).
- Only eps = 1/k with k >= 74 is used (checked in `tail_x31.py`).

## Files

- `N3_TABLE.md`: the N_3 table (sharper recursion is the main column) and the C1/C2 table.
- `n3/n3_{new,old}.json`: the final certificate for each k (all interval quantities), plus `.grid.json`, the full
  (M, B) grid at 60 slices. `n3/rows_{new,old}.json`: the inputs.
- `LADDER.md`, `ladder.json`, `logs/ladder.log`: the contiguous Regime 2 ladder. `logs/edge2.log`: a 1-decade parameter
  sweep at sample exponents 176..250 (`all_even_1p4_ext/edge_diag/`).
- `eps/`: certified eps* (closed intervals) for greedy Q at W = 10^7 (`eps_W1e7.json`), and the prime-bound table
  b = 79..227 (`table_b.json`). These are side results; the N_3 search uses the hstar Q0 sets, which are better.

## Reproduce

```
cd scripts            # all_even_1p4 and all_even_1p4_ext sit side by side here
python3 -I x31_linear_sieve/run_cn.py 74 76 80 85 90 95 100 110 120 140 160 180 200   # writes cn_rows_<ks>.json
python3 -I x31_linear_sieve/hstar_rows.py
python3 -I all_even_1p4_ext/n3_search.py ../data/x31_tail_n3/n3/rows_new.json n3_new.json   # about 25 min on 8 cores
python3 -I all_even_1p4_ext/n3_search.py ../data/x31_tail_n3/n3/rows_old.json n3_old.json
python3 -I all_even_1p4_ext/ladder.py 170 400 ladder.json             # about 14 min; stops near 10^238.7
python3 -I all_even_1p4_ext/mk_n3_table.py ../data/x31_tail_n3
```
