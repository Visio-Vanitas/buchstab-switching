# Table A: all-even K = 4 certificate, per-slab parameters and margins

Source: `research/goldbach/scripts/certify_all_even_1p4.py` at hub main `4233ed11fd`, run unchanged with `python3 -I`.
Machine: Linux-6.18.44-fc-v880-x86_64-with-glibc2.39, Intel(R) Xeon(R) Processor @ 2.10GHz, 4 vCPU. Python 3.13.18. Wall time 162.3 s, peak RSS 16 MB, exit code 0.
SHA-256 of the script: `243601207739fd338ae05c8652184405b207818343cf9d6f1bcde49d79e15b87`. SHA-256 of stdout: `c6350fdb99e921a592f9004ca8db13f938ee337632568e7b4272a5488d632f1f`. This is byte-identical to `data/certify_all_even_1p4_output.txt` (yes).

The per-term columns come from `scripts/table_a_extract.py`. It imports the same script, runs `main()` unchanged, and reads the locals of `certify_slab_K4` and `regime3` on return through `sys.setprofile`. Nothing is recomputed. Lower bounds (main, net) are rounded down and upper bounds (errors) rounded up, to 6 significant digits. All quantities are normalised by N/log N. Full 90-digit intervals are in `table_a_raw.json`.

## Regime 2: slabs on [4e18, 10^170)

Notation:
- z = ceil(X_hi^(1/M)) and y with y^5 > X_hi, z·y^4 >= X_hi.
- Pre-sieve Q_1 = the first a odd primes, up to p_a, sieved with exact inclusion–exclusion.
- Bonferroni orders m_odd (lower) and m_even (upper) on P_2 = (p_a, z).
- Level: max d = Q_1·(largest m_odd primes of P_2), checked to be <= sqrt(X_lo); for the switching sum, y·max d_even <= sqrt(X_lo).
- Regime 2 uses Bonferroni truncation, not the [BJS] table, so table row, eps, C_1 and C_2 do not apply (n/a).
- Errors: E_A = lower-sieve remainder; E_Aq = switching remainder over z <= q < y; E_q2 = (1/2)·sum |A_{q^2}|, via the level bound (L) when y^4 <= X_lo and the elementary bound (e) otherwise.

| # | [X_lo, X_hi) | M | a | p_a | m_odd | m_even | z | y | level: max d_odd / sqrt(X_lo) | y·max d_even / sqrt(X_lo) | main >= | E_A <= | E_Aq <= | E_q2 <= | total err <= | net >= |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | [4e18, 1e20) | 14 | 5 | 13 | 3 | 0 | 27 | 4.3870e+04 | 5.58e-2 | 3.30e-1 | 0.0707219 | 4.21315e-5 | 0.0151319 | 0.00495070 (L) | 0.0201247 | 0.0505972 |
| 2 | [1e20, 1e22) | 10 | 4 | 11 | 3 | 0 | 159 | 8.9054e+04 | 4.08e-1 | 1.03e-2 | 0.0307869 | 0.00328533 | 0.00365959 | 0.000731523 (L) | 0.00767644 | 0.0231105 |
| 3 | [1e22, 1e24) | 12 | 5 | 13 | 3 | 0 | 101 | 3.1544e+05 | 1.08e-1 | 4.74e-2 | 0.0299431 | 0.000164582 | 0.00239882 | 0.00103404 (L) | 0.00359744 | 0.0263456 |
| 4 | [1e24, 1e26) | 12 | 6 | 17 | 3 | 0 | 147 | 9.0818e+05 | 6.37e-1 | 2.32e-1 | 0.0257024 | 0.000109657 | 0.00138386 | 0.000635432 (L) | 0.00212895 | 0.0235734 |
| 5 | [1e26, 1e28) | 14 | 3 | 7 | 5 | 2 | 101 | 3.1544e+06 | 4.34e-2 | 2.86e-1 | 0.0603005 | 1.33831e-5 | 0.0136372 | 0.000969064 (L) | 0.0146197 | 0.0456809 |
| 6 | [1e28, 1e30) | 14 | 3 | 7 | 5 | 2 | 139 | 9.2097e+06 | 2.95e-2 | 1.74e-1 | 0.0535273 | 8.05343e-6 | 0.00789367 | 0.000641081 (L) | 0.00854280 | 0.0449845 |
| 7 | [1e30, 1e33) | 14 | 3 | 7 | 5 | 2 | 228 | 4.5763e+07 | 4.40e-2 | 2.44e-1 | 0.0440409 | 8.64435e-6 | 0.00947594 | 0.0272727 (e) | 0.0367573 | 0.00728366 |
| 8 | [1e33, 1e36) | 14 | 3 | 7 | 5 | 2 | 373 | 2.2755e+08 | 1.88e-2 | 9.96e-2 | 0.0350140 | 2.86067e-6 | 0.00375545 | 0.0175345 (e) | 0.0212928 | 0.0137212 |
| 9 | [1e36, 1e40) | 14 | 3 | 7 | 5 | 2 | 720 | 1.9305e+09 | 1.78e-2 | 1.04e-1 | 0.0233033 | 2.05509e-6 | 0.00337963 | 0.00981327 (e) | 0.0131950 | 0.0101084 |
| 10 | [1e40, 1e45) | 16 | 4 | 11 | 5 | 2 | 650 | 3.5219e+10 | 1.21e-3 | 1.70e-1 | 0.0223189 | 3.13577e-8 | 0.00108575 | 0.0121567 (e) | 0.0132425 | 0.00907650 |
| 11 | [1e45, 1e50) | 16 | 5 | 13 | 5 | 2 | 1334 | 5.2325e+11 | 1.87e-3 | 4.36e-1 | 0.0183388 | 5.73566e-9 | 0.000394618 | 0.00694808 (e) | 0.00734270 | 0.0109961 |
| 12 | [1e50, 1e56) | 18 | 6 | 17 | 5 | 2 | 1292 | 1.6680e+13 | 8.91e-5 | 7.09e-1 | 0.0148863 | 3.64930e-11 | 7.90205e-5 | 0.00804480 (e) | 0.00812382 | 0.00676251 |
| 13 | [1e56, 1e62) | 20 | 7 | 19 | 5 | 2 | 1259 | 5.3088e+14 | 1.39e-6 | 3.98e-1 | 0.0115709 | 7.59732e-14 | 5.19168e-6 | 0.00916854 (e) | 0.00917373 | 0.00239726 |
| 14 | [1e62, 1e70) | 22 | 2 | 5 | 9 | 4 | 1520 | 5.0645e+16 | 5.30e-2 | 3.83e-1 | 0.0121814 | 7.12339e-12 | 0.000111172 | 0.00883273 (e) | 0.00894390 | 0.00323756 |
| 15 | [1e70, 1e78) | 22 | 3 | 7 | 9 | 4 | 3512 | 4.1078e+18 | 7.74e-2 | 6.42e-1 | 0.0116373 | 1.22348e-12 | 3.61082e-5 | 0.00554496 (e) | 0.00558107 | 0.00605631 |
| 16 | [1e78, 1e86) | 22 | 3 | 7 | 9 | 4 | 8112 | 3.3321e+20 | 1.55e-2 | 1.51e-1 | 0.00825736 | 1.18419e-13 | 6.24039e-6 | 0.00423363 (e) | 0.00423987 | 0.00401749 |
| 17 | [1e86, 1e94) | 22 | 4 | 11 | 9 | 4 | 18739 | 2.7028e+22 | 3.22e-2 | 3.84e-1 | 0.00759556 | 2.29972e-14 | 2.16879e-6 | 0.00382138 (e) | 0.00382355 | 0.00377201 |
| 18 | [1e94, 1e102) | 24 | 6 | 17 | 9 | 4 | 17783 | 2.7384e+24 | 4.41e-4 | 6.94e-1 | 0.00676364 | 7.06379e-18 | 7.87460e-8 | 0.00418159 (e) | 0.00418167 | 0.00258197 |
| 19 | [1e102, 1e110) | 22 | 5 | 13 | 9 | 4 | 100001 | 1.7783e+26 | 1.51e-2 | 2.68e-1 | 0.00211421 | 1.26103e-15 | 2.10932e-7 | 0.00126643 (e) | 0.00126664 | 0.000847585 |
| 20 | [1e110, 1e118) | 24 | 7 | 19 | 9 | 4 | 82541 | 1.8657e+28 | 8.63e-5 | 4.20e-1 | 0.00324720 | 1.25831e-19 | 4.80138e-9 | 0.00164590 (e) | 0.00164591 | 0.00160130 |
| 21 | [1e118, 1e126) | 24 | 7 | 19 | 9 | 4 | 177828 | 1.5399e+30 | 8.63e-6 | 7.47e-2 | 0.00128167 | 6.88572e-21 | 6.58854e-10 | 0.000815753 (e) | 0.000815754 | 0.000465923 |
| 22 | [1e126, 1e134) | 24 | 8 | 23 | 9 | 4 | 383119 | 1.2711e+32 | 1.99e-5 | 3.06e-1 | 0.000733793 | 7.91237e-22 | 1.84661e-10 | 0.000402679 (e) | 0.000402679 | 0.000331115 |
| 23 | [1e134, 1e138) | 28 | 4 | 11 | 11 | 6 | 84835 | 1.8529e+33 | 1.90e-10 | 7.98e-2 | 0.00223854 | 2.22200e-26 | 2.31200e-10 | 5.93232e-6 (L) | 5.93255e-6 | 0.00223261 |
| 24 | [1e138, 1e142) | 26 | 3 | 7 | 11 | 6 | 289427 | 1.3634e+34 | 1.26e-7 | 8.42e-1 | 0.00302880 | 2.09819e-23 | 6.42015e-9 | 1.73850e-6 (L) | 1.74492e-6 | 0.00302706 |
| 25 | [1e142, 1e146) | 26 | 3 | 7 | 11 | 6 | 412463 | 1.2478e+35 | 6.18e-8 | 6.46e-1 | 0.00266010 | 7.51583e-24 | 4.12574e-9 | 1.21970e-6 (L) | 1.22382e-6 | 0.00265888 |
| 26 | [1e146, 1e150) | 26 | 3 | 7 | 11 | 6 | 587802 | 1.1421e+36 | 3.04e-8 | 4.95e-1 | 0.00228135 | 2.72251e-24 | 2.66778e-9 | 8.55719e-7 (L) | 8.58387e-7 | 0.00228049 |
| 27 | [1e150, 1e154) | 28 | 5 | 13 | 11 | 6 | 316228 | 1.3335e+37 | 4.75e-11 | 2.01e-1 | 0.00190669 | 2.38232e-28 | 4.38643e-11 | 1.59036e-6 (L) | 1.59040e-6 | 0.00190510 |
| 28 | [1e154, 1e158) | 28 | 5 | 13 | 11 | 6 | 439398 | 1.2282e+38 | 1.77e-11 | 1.33e-1 | 0.00174543 | 6.62380e-29 | 2.47125e-11 | 1.14438e-6 (L) | 1.14441e-6 | 0.00174429 |
| 29 | [1e158, 1e164) | 28 | 5 | 13 | 11 | 6 | 719686 | 3.4333e+39 | 4.03e-11 | 7.17e-1 | 0.00149552 | 9.64225e-29 | 1.02947e-10 | 0.000262354 (e) | 0.000262354 | 0.00123316 |
| 30 | [1e164, 1e170) | 28 | 5 | 13 | 11 | 6 | 1178769 | 9.5972e+40 | 9.17e-12 | 3.87e-1 | 0.00123471 | 1.46859e-29 | 4.44793e-11 | 4.26431e-7 (L) | 4.26475e-7 | 0.00123428 |

All 30 slabs are contiguous with exact integer endpoints, and every net lower bound is positive. The minimum is slab 22, net >= 0.000331115. y is shown to 5 digits here and given exactly in the raw JSON.

## Regime 3: tail N >= 10^170 ([BJS] Theorem 6 with pre-sieve)

| parameter | value |
|---|---|
| X_LS | 10^170 |
| M (z = N^(1/M)) | 22 |
| beta (y = N^beta) | 0.238636 |
| pre-sieve Q | primes 3 <= p < u0 = 41, prod = 3710369067405 |
| B (H = sqrt(N)/log^(B+1) N) | 3.05 |
| alpha (level D = N^(1/2-alpha)) | 0.1358 (required >= 0.135705) |
| z0 = X_LS^(1/M) >= | 53366900 |
| eps (product condition) <= | 0.00852599 |
| [BJS] Table 1 row | eps^-1 = 100, eps' = 1/100 |
| C_1, C_2 | 276, 277 |
| s = M(1/2 - alpha) | 8.0124 |
| s_min = M(1/2 - alpha - beta) | 2.76239 |
| delta_V (V(z) Mertens product) <= | 0.00159168 |
| c_4G <= | 0.0871478 |
| f(s) - eps' C_2 e^2 h(s) >= | 0.975814 |
| (1/2) sum_q phi(s_q)/(q-1) <= | 0.973128 |
| main >= | 0.00268343 |
| E_R1 <= | 1.51930e-5 |
| E_R2 <= | 0.00109031 |
| E_rq <= | 5.44626e-7 |
| E_q2 <= | 8.80275e-5 |
| total err <= | 0.00119407 |
| net >= | 0.00148936 |
| slices for the switching sum | 200 |

Net is the coefficient c in pi_4(N) > c · M · U_N · N / log^2 N for all even N >= 10^170. Regime 1 (4 <= N <= 4·10^18) is the cited numerical verification, so it has no parameters here.

Scope: this table reproduces the certificate as written. It does not settle the open reading of the [BJS] product hypothesis on sub-intervals (note X30). Under that reading, the tail row above would need u0 = 103; that is the follow-up job.
