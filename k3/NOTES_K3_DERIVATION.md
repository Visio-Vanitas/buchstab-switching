# Explicit Conditional $K = 3$ ($\Omega(m) \le 3$) All-Even Switching Certificate (`k3/`)

This note documents the mathematical derivation, normalization conventions, finite-terminating Buchstab error bounds, two-variable Mertens closure, and parameter robustness of the `k3/` subproject, verifying:

> **Theorem (`BuchstabSwitching.all_even_one_plus_three_of_classical` & `even_eq_prime_add_omegaMult_le_three`).** *Assuming `DirichletLNonvanishingRightOfHalf` (GRH for Dirichlet $L$-functions, instantiated against Mathlib's `DirichletCharacter.LFunction` matching `https://github.com/lsernau/grh-lean@72fead102f663d5c7a407964a13dc0cf9d977207`, `grh-compact/src/Statements.lean`) together with the six classical literature premises in `BuchstabSwitching.External.ClassicalBasicLemmas`, every even integer $N \ge 4$ satisfies $N = p + m$ with $p$ prime, $0 < m$, and $\Omega(m) \le 3$.*

---

## 1. Combinatorial Core & One-Step Switching Inequality

For an even integer $N \ge 4$ and integer sieve cutoffs $2 \le z \le y$ satisfying
$$N \le y^4, \qquad N \le z y^3,$$
define:
- $\mathcal{A}_N := \{N - p : p < N \text{ prime},\ p \nmid N\}$, with cardinality $|\mathcal{A}_N| = \pi(N-1) - O(\omega(N))$;
- $\mathbb{P}_N := \{p \text{ prime} : p \nmid N\}$ (note $2 \mid N \implies 2 \notin \mathbb{P}_N$);
- $P_N(z) := \prod_{p \in \mathbb{P}_N,\ p < z} p$;
- $S(\mathcal{A}_N, z) := \#\{p < N \text{ prime},\ p \nmid N : (N - p, P_N(z)) = 1\}$;
- $S(\mathcal{A}_{N,q}, z) := \#\{p < N \text{ prime},\ p \nmid N,\ q \mid (N - p) : (N - p, P_N(z)) = 1\}$.

**Deterministic Pinch (`ShiftedPrimes.omegaMult_le_three_of_sieve_pinch` & `OneStepSwitching.switchingBalance_le_card_good`, kernel-verified in Lean 4):**
For every even $N$ with $2 \le z \le y$, $N \le y^4$, $N \le z y^3$, any prime $p \in \mathcal{A}_N$ with $(N - p, P_N(z)) = 1$ and $\Omega(N - p) \ge 4$ must have either some prime $q \in [z, y)$ with $q^2 \mid N - p$ or at least two distinct primes $q_1 \ne q_2 \in [z, y)$ dividing $N - p$. Therefore, weighting every divisor $q \in [z, y) \cap \mathbb{P}_N$ and every prime square $q^2$ ($z \le q < y$) by $\frac{1}{2}$ yields:
$$\#\{p < N \text{ prime} : \Omega(N - p) \le 3\} \ge \operatorname{switchingBalance}(N, z, y) := S(\mathcal{A}_N, z) - \frac{1}{2} \sum_{\substack{z \le q < y \\ q \in \mathbb{P}_N}} S(\mathcal{A}_{N,q}, z) - \frac{1}{2} \sum_{\substack{z \le q < y \\ q \in \mathbb{P}_N}} |\mathcal{A}_{N, q^2}|.$$

No quadratic $q_1 q_2 q_3$ remainder term is needed for $K = 3$: a single switching step suffices.

---

## 2. Normalizations & Meaning of `main`, `err`, `net`, `sieve_net`, `tol`

Every numerical line in `k3/scripts/data/certified_bounds.txt` decomposes a normalized lower bound on $\operatorname{switchingBalance}(N, z, y)$ into:
$$\frac{\operatorname{switchingBalance}(N, z, y)}{\text{scale}} \ge \underbrace{\mathrm{main}}_{\text{sieve main term}} - \underbrace{\mathrm{err}}_{\text{GRH remainder } + q^2 + \text{edge}} =: \mathrm{net} > 0,$$
where $\mathrm{tol} := \mathrm{main\_lo} / \mathrm{err\_hi}$ measures the uniform multiplicative factor by which the entire remainder budget (`err`) could inflate before `net` reaches zero.

The four contiguous regimes span all even integers $[4, +\infty)$:

| Regime | Range of $N$ | Method & Scale Normalization | Minimum Margin |
| :--- | :--- | :--- | :--- |
| **Regime 1** | $[4, 4 \cdot 10^{18})$ | Binary prime sum ($K=1 \le 3$; Oliveira e Silva–Herzog–Pardi, *Math. Comp.* **83**, 2014) | `exact` |
| **Regime 2a** | $[4 \cdot 10^{18}, 2 \cdot 10^{23})$ (21 slabs) | `scale = \|A_N\|`; `{P_sub, EvenBonf}` + exact prime sums `< 27000` (`48` slices) + Mertens/Schoenfeld (`4` slices) on $[z, y)$, Lean `Dyadic`-witness aligned | `net >= 0.001832` (`2a-03`), `sieve_net >= 0.008025`, `tol >= 1.04x` |
| **Regime 2b** | $[2 \cdot 10^{23}, 10^{84})$ (40 slabs) | `scale = \|A_N\|`; `Q_1(a) x OddBonf(m_odd)` + hybrid `{P_sub, multi-cutoff EvenBonf}` on `56` slices (`P_EXACT = 27000`), Lean `Dyadic`-witness aligned | `net >= 0.001763` (`2b-40`), `sieve_net >= 0.024224`, `tol >= 2.30x` |
| **Regime 2c** | $[10^{84}, 10^{600})$ (66 slabs) | `scale = \|A_N\| * V_N(z)`; `max(OddBonf, BrunBlock)` on $S(\mathcal{A}_N)$ + `min(EvenBonf, Adaptive Selberg)` on `48` slices (11-step hybrid `J_odd` + Lean `Dyadic`-witness aligned) | `net = sieve_net >= 0.003969` (`2c-07`), `tol >= 1.41x` |
| **Regime 3** | $[10^{600}, +\infty)$ (ray) | `scale = 16 * U_N * N / ln^2 N`; closed `(H*)` linear sieve (`Q0_100`, `k=100`, Lean `certifiedDecaySeq` `C_2 <= 494`, Python cap `495`) + Selberg `J_full` (`M=16`, `L=120` strips) | `net >= 0.046825`, `tot_err <= 0.000078`, `C_2 <= 1853.2`, `tol = 608.7x` (`100:old` `0.051880`, `100:new` `0.055785`) |

In sub-regimes `2a`/`2b`, `sieve_net := net / V_full(z) >= net / V_N(z)` expresses the exact fraction of the pure rough-density main term $|\mathcal{A}_N| V_{\mathrm{full}}(z)$ surviving as positive surplus (corresponding directly to `net` in `2c`).

### Error Term Decomposition (`err = rem_a + 0.5 * err_aq + err_q2 + err_one`)
1. `rem_a`: GRH arithmetic-progression remainder summed over sieve moduli $d \le \sqrt{X_{\mathrm{lo}}}$ in $S(\mathcal{A}_N, z)$ (weighted by `epd_norm_iv = c_pi(ln X_lo) * (ln^2 X_lo) / sqrt(X_lo) + ...`, using Grenié–Molteni *Ramanujan J.* **49** (2019), 535–548 / Johnston–Starichkova `arXiv:2208.01229v3` Lemma 5.1), using odd squarefree counting $\sum_{d \le X,\ 2 \nmid d} \mu^2(d) \le \frac{4}{\pi^2} X + \sqrt{X}$.
2. `0.5 * err_aq`: Weighted GRH remainder summed over $[z, y)$ slices (`2a`/`2b`/`2c`), incorporating either Bonferroni modulus counts (`2^{a_q}` times block/level DP counts) or Selberg `Λ²` collision multiplicity $\sum_{L \le \xi_q^2,\ 2 \nmid L} \mu^2(L) 3^{\omega(L)} \le \frac{1}{16} \xi_q^2 (2 \ln \xi_q + 6)^2$ together with $\sum_{d \le \xi_q} \frac{|\mu(d)|}{\varphi(d)} \le H_{\mathrm{tilde}} \cdot f_0(\xi_q^2)$.
3. `err_q2`: Contribution of prime squares $q^2 \mid N - p$ for $z \le q < y$: bounded cleanly across $q \in [z, y)$ by $\sum_{q \ge z} (N / q^2 + O(1))$, plus edge-loss accounting.
4. `err_one`: Edge shift loss for $N - p = 1$ or $p \mid N$.

---

## 3. Closed-Interval Two-Variable Pre-Sieve `(H*)` & Self-Contained Ray Reduction

In Regime 3 (`[10^{600}, +\infty)`), we apply an explicit linear sieve lower bound under a **closed-interval** two-variable Mertens hypothesis `(H*)` over the residual prime set $\mathcal{S}_0 := \{p \ge 3\text{ prime}\} \setminus Q_0$, where $Q_0 := Q_{0, 100}$ is an explicit finite set of $31$ odd primes in $[3, 227]$ ($\ln \prod_{p \in Q_0} p \le 117.6157$):
$$\prod_{\substack{a \le p \le b \\ p \in \mathcal{S}_0}} \frac{p - 1}{p - 2} \le (1 + \varepsilon_*) \frac{\ln b}{\ln a} \qquad (\forall\, a \le b \text{ in } \mathcal{S}_0).$$

1. **Causal Closed-Interval Verification (`certify_closed_hstar_q0`)**: Over $\mathcal{S}_0 \cap [3, 250{,}000]$, a single forward pass tracks the running minimum of the Mertens offset before each upper prime $b \ge a$ (handling singleton intervals $a = b$ explicitly), and joins at $250{,}000 > e^{12.4}$ with Johnston–Starichkova (`arXiv:2208.01229v3`, Lemma 3.2). This certifies $\varepsilon_* \le 0.0099009901 < \frac{1}{100}$.
2. **Certified Linear-Sieve Constants (Lean `certifiedDecaySeq`, `100:old` & `100:new`)**: Lean kernel-certifies parity-split `ValidDecaySeq certifiedDecaySeq` (`Even n -> 2 <= s`, `Odd n -> 1 <= s`) with `C2_bjs certifiedDecaySeq (1/100) <= 494`. Matching Python cap `c2_lean_cap = 495` yields `main_coeff >= 0.046903`, `tot_err <= 0.000078`, `net >= 0.046825`, GRH tol `608.7x`; `linear_sieve.py` also pins exact rational certificates `100:old` ($C_2 \le 348.365884$, `net >= 0.051880`, GRH tol `674.3x`) and `100:new` ($C_2 \le 235.091292$, `net >= 0.055785`, GRH tol `725.0x`) from `shared/data/linear_sieve_inputs/` (SHA-256 verified), all well below break-even $C_2 \le 1853.2$.
3. **Integer Cutoffs & Shifted-Prime Factor Monotonicity**: For $z = \lfloor N^{1/16} \rfloor \ge N^{1/16} - 1$ and $y = \lceil (N/z)^{1/3} \rceil \le N^{\beta}$ ($\beta > \frac{1}{4}$, $\frac{1}{16} + 3\beta \ge 1$), integer rounding shifts $\ln z$ by at most $\eta_{\mathrm{int}} = 1 / ((z_0 - 1)\ln z_0)$, which `regime_asymptotic.py` carries into both $\delta_V$, the lower bound $s_A \ge M(\frac{1}{2} - \alpha)$, and Selberg's `vj_monotone_lb_iv`. Omitting divisors $p \mid N$ strictly increases $V_N(z) / V_{\mathrm{full}}(z)$ and $J_N(z, \xi_q) / J_{\mathrm{full}}(z, \xi_q)$ (`sqrt_down`/`sqrt_up` outward rounding in `Iv.sqrt`).

---

## 4. Regime `2c` Brun Block Lower Sieve (`brun_block_sieve.py`)

For slabs in `[10^{84}, 10^{600})` where single-order odd Bonferroni hits the $O(1)$ remainder ceiling, `certify_slab_2c` compares pure `OddBonferroni` against the proved **Brun combinatorial block lower sieve** on pre-sieved odd moduli $Q_1(a) \times P_2$:
- **Partition & Parity Rule**: Descending block endpoints $z = z_0 > z_1 > \dots > z_r = p_a + 1$ partition $[p_a+1, z)$ into $T_i = [z_i, z)$, with odd caps $m_1 < m_2 < \dots < m_r$ (e.g. `(5, 9, 11)` or `(5, 9, 11, 13)`). By alternating-sign truncation on the largest prime at each block step, every odd cap satisfies Brun parity ($\chi^- \le \mathbf{1}$).
- **Explicit Remainder & Level**: With $S_hi(u, v) \ge \sum_{u \le p < v} \frac{1}{p-1}$ and $V_{\mathrm{lo}}(u, v) \le \prod_{u \le p < v} (1 - \frac{1}{p-1})$,
  $$E^- \le \sum_{i=1}^r \frac{S_{\mathrm{hi}}(T_i)^{m_i + 1}}{(m_i + 1)!\, V_{\mathrm{lo}}(T_i)}, \qquad M_{\chi^-} = \prod_{i=0}^{r-1} z_i^{m_i - m_{i-1}}$$
  so every modulus $d$ in support satisfies $d < \left(\prod_{p \in Q_1} p\right) M_{\chi^-} \le \sqrt{X_{\mathrm{lo}}}$, with exact DP divisor count $2^a \cdot \mathrm{adm\_count}(\mathrm{caps}, \mathrm{sizes})$ and monotonic preservation under removing primes $p \mid N$. On `[10^{84}, 10^{600})`, Brun block (`P_EXACT = 27000` + `MertensPrimeSumPremise`) + Selberg `J_full` (with 11-step hybrid `J_odd` + Lean-witness alignment) yields `net = sieve_net >= 0.003969` and GRH tolerance $\ge 1.41\times$ across all `66` slabs.

---

## 5. Robustness Summary & Arithmetic Discipline

- **Arithmetic Purity**: `interval.py` arms `decimal.getcontext().traps[Inexact] = True` and `traps[Rounded] = True` globally at `PREC = 90` digits. Every non-exact operation must enter `directed_context(ROUND_FLOOR | ROUND_CEILING)`. Square roots (`sqrt_down`, `sqrt_up`) use integer-scaled square comparisons (`_square_exact`) rather than `ROUND_HALF_EVEN`. Transcendental `ln`/`exp` run at `102` digits with a `2-ulp` outward Table-Maker safety pad before rounding back to `90` digits. AST audits forbid IEEE-754 `float` literals/conversions and `import math`.
- **Lean 4 Kernel & Comparator Replay**: Rational lower/upper bounds in `Data.lean` (`DENOM = 10^10`) are checked in Lean `v4.36.0` exclusively by kernel reduction (`by decide`, zero `sorry`, zero custom `axiom` declarations, `#print axioms` = `[propext, Classical.choice, Quot.sound]`), and independently exported and verified under `comparator` (`leanchecker-paranoid` and `nanoda_bin`).
- **Perturbation Margins**:
  - Finite slabs `[4*10^18, 10^600)` (127 slabs, Lean `Dyadic` binary-reflection witness-aligned with `10^-9` outward pad): $\min \mathrm{net} = 0.001763$ (`2b-40`), $\min \mathrm{sieve\_net} = 0.003969$ (`2c-07`), $\min \mathrm{tol} = 1.04\times$ (`2a-03`) (`2a`: $\min \mathrm{net} = 0.001832$, $\min \mathrm{sieve\_net} = 0.008025$, $\min \mathrm{tol} = 1.04\times$; `2b`: $\min \mathrm{net} = 0.001763$, $\min \mathrm{sieve\_net} = 0.024224$, $\min \mathrm{tol} = 2.30\times$; `2c`: $\min \mathrm{net} = \min \mathrm{sieve\_net} = 0.003969$, $\min \mathrm{tol} = 1.41\times$).
  - Asymptotic ray `[10^600, ∞)`: $\mathrm{net} \ge 0.046825 > 0$ (`certifiedDecaySeq` Lean $C_2 \le 494$, Python cap `495`, `main_coeff >= 0.046903`, `tot_err <= 0.000078`; `100:old` `net >= 0.051880` & `100:new` `net >= 0.055785` cross-checks), tolerance $608.7\times$ on total GRH+diagonal remainder, and break-even $C_2 \le 1853.2$.

---

## 6. Lean 4 Binary Proof-by-Reflection Architecture (`SlabCertInst*`)

To verify all `127` finite slabs (`6,448` `[z, y)` slices and up to `2,001`-bit integers near $10^{600}$) inside the Lean 4 kernel without `native_decide`, custom axioms, or decimal big-integer division bottlenecks, `BuchstabSwitching/Sieve/Regime2SlabBridge/SlabCertInst*.lean` (`41` modules, every file $\le 750$ lines) implements a **Binary Proof-by-Reflection** verifier mirrored bit-for-bit in `scripts/sieve_cert/{dyadic_mirror,slab_witness_export}.py`:

1. **Biased Binary `Dyadic` Intervals (`SlabCertInstDefs.lean`, `SlabCertInstSciProofs.lean`)**:
   - Each dyadic endpoint `(m, e) : Dyadic` represents exact real value $\operatorname{toReal}(m, e) := m \cdot 2^e / 2^{8192}$ (`dyadicBias = 8192`), with `@[irreducible] def twoPowBias` preventing the kernel from unfolding $2^{8192}$.
   - Outward-rounded arithmetic (`mulLb`, `mulUb`, `divDyadicLb`, `divDyadicUb`, `trimLb`, `trimUb` at precision $W = 80$ bits) executes exclusively via hardware-aligned bitshifts (`<<<`, `>>>`) and comparisons, eliminating decimal $10^k$ Euclidean divisions inside `decide`.
2. **Non-Deterministic Algebraic & Transcendental Witnesses (`SlabCertInstExpProofs.lean`, `SlabCertInstEpdLi.lean`, `SlabCertInstElemBounds.lean`)**:
   - Instead of computing logs, roots, or factorials inside the Lean kernel, Python (`slab_witness_export.py`) emits compact certificate witnesses (`2,433` lines across 12 shards `SlabCertInstData2a1..2c6`, max `326` lines/file), and Lean verifies cleared-denominator inequalities:
     - `LogWitness`: Binary reduction $N = 2^k r$ plus rational Padé / odd-power $\operatorname{artanh}$ `Q64` series enclosures for $\ln N$;
     - `expNegUb6` / `expNegLb8`: Alternating Taylor polynomial enclosures for $\exp(-x)$ on $[0, 1]$ (`SlabCertInstExpProofs.lean`);
     - `EpdWitness`, `AnalyticRangeWitness`, `MertensTailWitness`, `BrunStepWitness`: Cleared-denominator verification of $c_\pi(X_{\mathrm{lo}})$, $\mathrm{epdNorm}$, $\mathrm{li}(N)/|\mathcal{A}_N|$, Mertens prime-reciprocal tails, and Brun block factorials/products.
3. **Depth-6 Static Segment Tree `OddPrimeTree` (`SlabCertInstPrimeTree.lean`)**:
   - Covers all `2,960` odd primes $3 \le p < 27{,}000$ via a balanced depth-6 binary tree (`64` leaves, `47` primes/leaf), storing outward-rounded `[prodLb, prodUb]` for $\prod (1 - \frac{1}{p-1})$ and `[sumLb, sumUb]` for $\sum \frac{1}{p-1}$.
   - Answers arbitrary prime-range product/sum queries on $[u, v)$ in $O(\log N)$ ($\le 12$ node merges) rather than linear list scans.
4. **Literal-Folded `J_odd` Staircase & Memoized Slice Checkers (`SlabCertInstJOddSmall.lean`, `SlabCertInstSound2ab.lean`, `SlabCertInstSound2c*.lean`)**:
   - `jOddStepTableFast` pre-folds the 11-step dyadic upper staircase for $J_{\mathrm{odd}}(\xi)$ over the `415` odd squarefree integers $d \le 1024$ (`jOddStepUb_eq_chunks`), paired with the convolution bound $H_0(\frac{1}{2}\ln\xi + \alpha_0) + C_J \xi^{-1/4}$ for $\xi > 1024$.
   - `checkSlices2abMemo` caches sub-cutoff Euler-product ratios across the `3,280` `2a/2b` slices, while `SlabCertInstSound2c*` verifies `2,211` adaptive Selberg two-prime discrete grids (`TwoPrimeDiscreteGrid`) and `957` `EvenBonf` slices across the `66` `2c` slabs.
5. **Sharded Kernel Compilation & Resource Profile (`v4.36.0`, `8,211` total build jobs)**:
   - **17 binary soundness & tree modules**: `~145s` cumulative (`5s–25s` per file);
   - **12 witness data shards (`SlabCertInstData2a1..2c6`)**: `~180s` cumulative (`8s–43s` per file);
   - **3 Regime `2a/2b` leaf shards (`SlabCertInst2ab1..3`, `21 + 20 + 20 = 61` slabs)**: `44s`, `65s`, `108s`;
   - **6 Regime `2c` leaf shards (`SlabCertInst2c1..6`, `11` slabs/shard = `66` slabs)**: `214s`, `362s`, `494s`, `468s`, `433s`, `383s` (`< 500 MB` RAM per `lean` process);
   - **End-to-end cold build**: `~9–11m` wall-clock under parallel `lake build BuchstabSwitching` on a 32 GB machine (`~2.5 GB` peak RAM, critical path dominated by `SlabCertInst2c3` at `494s`), or `~45.5m` strictly sequential 1-worker build (`< 500 MB` RAM).
