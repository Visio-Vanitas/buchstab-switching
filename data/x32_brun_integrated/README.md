# X32 block sieve integrated into the package; one ladder from 4e18 to 10^500; tail moved to 10^500

Status: **unchecked**. Computed 2026-11-25/26. This answers the gaps in review (X32) and review (X31 tail).

## Result

- **Regime 2, one method.** `scripts/all_even_1p4_ext/regime2_brun.py` (`certify_brun_slab`) certifies **58 contiguous
  slabs from 4·10^18 to 10^500**. The least net is 1.68·10^-3, at the slab from 10^390 to 10^400. Consecutive slabs
  share their exact integer endpoints, which was checked on the merged list `ladder_4e18_500_all.json`. Table:
  `LADDER_TABLE.md`. So the block sieve alone covers what Regime 2 (30 slabs, 4e18..10^170), the unreviewed old
  extension (10^170..10^238.7, data/x31_tail_n3/LADDER.md) and X32 (10^238..10^400) covered, and goes further.
  The overlap with the old ladder is explicit: the block slab [10^230, 10^240) contains the old top 10^238.7 (net 2.38·10^-3).
- **Tail moved to N_3 = 10^500.** At eps' = 1/80, both recursions, with a finer f/F mesh (H = 2000) and 2000 slices
  (`tail/tail_at_500.json`):
  - sharper recursion: M = 22, B = 3.01, alpha = 0.1024, **net >= 0.07522**; with C1 and C2 both multiplied by 1.05, net >= 0.07067.
  - old recursion: M = 24, B = 3.01, alpha = 0.1024, **net >= 0.03910**; with C1 and C2 multiplied by 1.05, net >= 0.03492.
  - For comparison, the earlier start 10^399 had net 0.000825 (sharper only). The same certificate at 10^399 with the finer mesh gives 0.00116 (H = 400) or 0.00258 (H = 1000 with 1000 slices).
  - The other k and e values are in `tail/tail_final.log` and `.json`. For example, at 10^480 for k = 80: 0.0638 (sharper) and 0.0281 (old).
- **Together:** if the inputs survive review, Regime 1 (N < 4·10^18), the block ladder [4·10^18, 10^500) and the tail N ≥ 10^500 cover every even N.

## Integration 

`certify_brun_slab` uses only the package's inputs, each through its own range check:
- the per-modulus remainder (*): `grh_remainder_coeff` (certified c_pi(X_lo) of [JS] Lemma 5.1 plus 1/(16 pi)) and
  `omega_upper` (Robin), identical to `regime2.certify_slab`. The placeholder C_PI = 10 is gone.
- sums over primes: exact over the primes <= P_CUT = 30000; above that, the package's `sum_inv_p_upper` and `sum_inv_p_lower`
  ([JS] (3.1)-(3.3), [BJS] Lemma 16; Meissel–Mertens constant M0 from `constants`); pi(x) from `prime_count_upper`
  (Schoenfeld under RH, x >= 2657). No Rosser–Schoenfeld input remains.
- ln, exp, sqrt: the package's `ln_iv`, `exp_iv`, `Iv.sqrt` (outward, rounding audit on). No raw Decimal ln/exp.
- z, y: `regime2.choose_z_y`. The q sums: `regime2.q_sums`. |A| > N/log N: `require_js_lemma_3_1`. The q^2 term: the same two branches as `certify_slab`.
- completeness against X26 §3 item 6. The docstring maps each term. It has the same three remainder families as `certify_slab`
  (lower sieve on A; the upper sieves on A_q, which cover the r(qd), r(q)·Σ1/phi(d) and r(q)·R+ terms; and the q^2 term).
  The counts are from X32 Lemma E.2, and R-/R+ are 1 -/+ E (Lemma B.3, D).
- level: (prod Q1 · M_chi-)^2 <= X_lo and (y · prod Q1 · M_chi+)^2 <= X_lo, as exact integers (y rather than y-1, as in certify_slab).
- parity: every lower cap is odd and every upper cap is even.
- one deliberate looseness: above P_CUT, -log(1-w) <= w + w^2 (w <= 1/2). This is cruder than the package's c_log form.

## Cross-check 

`crosscheck_200_205.txt` covers [10^200, 10^205), with M = 29 and a = 8. This is the old slab's parameters, analytic branch:
1. the package's `certify_slab` with orders (13, 6): main >= 2.8083e-4, net >= 2.8079e-4.
2. the block certificate with single blocks (13,)/(6,), which is the same sieve: main >= 2.7865e-4, which is 0.9922 of (1). The V lower
   bounds differ only by a factor 0.99970 (4.551975e-2 vs 4.553358e-2). Almost all of the difference comes from the
   bracket b (6.1215e-3 vs 6.1676e-3). The bound R+ <= 1 + E+ = 1.021487, against the package's R_even <= 1.021440,
   is multiplied by sum_q/2 ≈ 0.97. That lowers b by about 4.6e-5, which is 0.75% of b. With the 0.03% from V
   this gives the 0.78% .
3. the block certificate with caps (9,13,15)/(4,8): main >= 1.0848e-3, net >= 1.0847e-3.
4. a rigorous upper reference U = V_hi (1 - Σ_q,lo/2) <= 1.2342e-3, which bounds every true main term with R- <= 1 <= R+.
   All three certified main lower bounds are below U.

## Exploration 

- **Down:** the ladder starts at 4·10^18 with net 1.8·10^-3 (M = 10, a = 4, caps (3,)/(0,)).
  Below 4·10^18 [JS] Lemma 5.1 is out of range, so the remainder bound is unavailable, and that floor is not a sieve limit.
- **Up:** single 1-decade slabs certify at 10^450, 500, 600, 700, 800, 1000, 1500 and 2000 (`probes/`). The nets are 2.1e-3, 1.9e-3, 1.6e-3, 1.3e-3, 1.1e-3,
  7.6e-4, 4.4e-4 and 2.2e-4. They shrink slowly, and the grid edge M = 22 was binding at most points, so more is likely available. The block
  ladder could therefore also replace a large part of the tail, but the tail at 10^500 is already comfortable.

## review items (tail code)

- `tail_x31.py` reads Q0, k, C1, C2 from the committed files (`X31Tail.from_files`). It asserts that the hstar log has the
  analytic tail beyond the scan ("[tail] B = 10000000") and the full scan to 9999991, and that target 1/k PASSed.
- the Mertens coefficient guard is now applied at max(z0, 10^12) instead of a constant.
- the JSON report rounds outward to 10 digits and keeps the exponent (rq, q2 were truncated before).
- `try_certify` also catches HypothesisError and CertificationError.
- the `__main__` smoke test is labelled "not a certificate". `regime3.certify_tail`, `regime3.epsilon_bound` and
  `cited.bjs_table_row` are labelled SUPERSEDED in their docstrings, and their code is unchanged, so the package tests still pass (28 passed, 1 skipped).
- `n3_search.py` no longer claims that the net is increasing in e. It now says the bisection assumes it, and that e - 1 is checked directly.

## Files

- `ladder/ladder_<from>_<to>.{json,log}`: six segments with full logs. `ladder_4e18_500_all.json`: merged. `LADDER_TABLE.md`.
- `probes/`: the exploration up (`probe_up_*`) and down (`probe_down.*`, sample points 4e18..10^220).
- `tail/tail_at_500.{json,log}`: the tail certificates at 10^500. `tail/tail_final.{json,log}`: the scan over k ∈ {74,80,85,90},
  e ∈ {420..550}, both recursions. It stopped before k = 100, which is not needed.
- `crosscheck_200_205.txt`.
- Code: `scripts/all_even_1p4_ext/{regime2_brun,brun_ladder,brun_crosscheck,tail_final,tail_at_500,tail_x31}.py`.

## Reproduce

```
cd scripts
python3 -I all_even_1p4_ext/brun_ladder.py ladder x4000000000000000000 100 l1.json 10-24 2-7 small
python3 -I all_even_1p4_ext/brun_ladder.py ladder 100 170 l2.json 16-26 2-8 small
python3 -I all_even_1p4_ext/brun_ladder.py ladder 170 230 l3.json 20-28 2-8 small
python3 -I all_even_1p4_ext/brun_ladder.py ladder 230 300 l4.json 25-29 6-9
python3 -I all_even_1p4_ext/brun_ladder.py ladder 300 400 l5.json 25-29 6-9
python3 -I all_even_1p4_ext/brun_ladder.py ladder 400 500 l6.json 20-25 6-8 big
python3 -I all_even_1p4_ext/brun_crosscheck.py 200 205 29 8 13 6
python3 -I all_even_1p4_ext/tail_at_500.py
```
Each ladder segment takes 10 to 60 minutes on 8 cores. `tail_at_500.py` takes a few minutes on one core.
