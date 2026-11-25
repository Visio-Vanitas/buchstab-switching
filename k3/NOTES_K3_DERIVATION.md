# Explicit Conditional $K = 3$ ($\Omega(m) \le 3$) All-Even Switching Certificate (`k3/`)

This note documents the mathematical derivation, normalization conventions, finite-terminating Buchstab error bounds, two-variable Mertens closure, and parameter robustness of the `k3/` subproject, verifying:

> **Theorem (`BuchstabSwitching.even_eq_prime_add_omegaMult_le_three`).** *Assuming `DirichletLNonvanishingRightOfHalf` (GRH for Dirichlet $L$-functions, instantiated against Mathlib's `DirichletCharacter.LFunction`) together with the four isolated analytic/computational bridges in `BuchstabSwitching/External/`, every even integer $N \ge 4$ satisfies $N = p + m$ with $p$ prime and $\Omega(m) \le 3$.*

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
| **Regime 2a** | $[4 \cdot 10^{18}, 2 \cdot 10^{23})$ (21 slabs) | `scale = \|A_N\|`; exact `P_sub` IE + exact prime sums on 64 geometric slices of $[z, y)$ | `net >= 0.00402`, `sieve_net >= 0.0176`, `tol >= 1.1x` |
| **Regime 2b** | $[2 \cdot 10^{23}, 10^{84})$ (40 slabs) | `scale = \|A_N\|`; `Q_1(a) x OddBonf(m_odd)` + hybrid `{P_sub, multi-cutoff EvenBonf}` on 56 slices | `net >= 0.00183`, `sieve_net >= 0.0251`, `tol >= 1.7x` |
| **Regime 2c** | $[10^{84}, 10^{600})$ (66 slabs) | `scale = \|A_N\| * V_N(z)`; `max(OddBonf, Finite Buchstab)` on $S(\mathcal{A}_N)$ + `min(EvenBonf, Clamped Buchstab, Adaptive Selberg)` on 48 slices | `net = sieve_net >= 0.00774`, `tol >= 1.7x` |
| **Regime 3** | $[10^{600}, +\infty)$ (ray) | `scale = U_N * N / (M * ln^2 N)`; BJS linear sieve (`u_0=251`, `k=99`, `C_2=345`) + two-var `eps_sup` + pre-sieve-free monotone Selberg `J_full` (`M=16`) | `net >= 0.010936`, `C_2 <= 417.1`, `tol >= 142.9x` |

In sub-regimes `2a`/`2b`, `sieve_net := net / V_full(z) >= net / V_N(z)` expresses the exact fraction of the pure rough-density main term $|\mathcal{A}_N| V_{\mathrm{full}}(z)$ surviving as positive surplus (corresponding directly to `net` in `2c`).

### Error Term Decomposition (`err = rem_a + 0.5 * err_aq + err_q2 + err_one`)
1. `rem_a`: GRH arithmetic-progression remainder summed over sieve moduli $d \le \sqrt{X_{\mathrm{lo}}}$ in $S(\mathcal{A}_N, z)$ (weighted by `epd_norm_iv = c_pi(ln X_lo) * (ln^2 X_lo) / sqrt(X_lo) + ...`, using Grenié–Molteni *Ramanujan J.* **49** (2019), 535–548 / Johnston–Starichkova `arXiv:2208.01229v3` Lemma 5.1), using odd squarefree counting $\sum_{d \le X,\ 2 \nmid d} \mu^2(d) \le \frac{4}{\pi^2} X + \sqrt{X}$.
2. `0.5 * err_aq`: Weighted GRH remainder summed over $[z, y)$ slices (`2a`/`2b`/`2c`), incorporating either Bonferroni modulus counts, Buchstab odd-sieve remainder, or Selberg `Λ²` collision multiplicity $\sum_{L \le \xi_q^2,\ 2 \nmid L} \mu^2(L) 3^{\omega(L)} \le \frac{1}{16} \xi_q^2 (2 \ln \xi_q + 6)^2$ together with $\sum_{d \le \xi_q} \frac{|\mu(d)|}{\varphi(d)} \le H_{\mathrm{tilde}} \cdot f_0(\xi_q^2)$.
3. `err_q2`: Contribution of prime squares $q^2 \mid N - p$ for $z \le q < y$: under GRH when $q \le X_{\mathrm{lo}}^{1/4}$ and via trivial bound $\lfloor N / q^2 \rfloor \le N / q^2$ for $q > X_{\mathrm{lo}}^{1/4}$.
4. `err_one`: Edge shift loss for $N - p = 1$ or $p \mid N$.

---

## 3. Resolution of the Order-Respecting Two-Variable Mertens Condition (`eps_sup_two_var`)

A recurring subtlety in applying explicit Jurkat–Richert / Bordignon–Johnston–Starichkova (`arXiv:2207.09452`, Theorem 6) linear-sieve error tables concerns the hypothesis
$$\prod_{w \le p < z_1} \left(1 - \frac{1}{p-1}\right)^{-1} \le (1 + \varepsilon) \frac{\ln z_1}{\ln w} \qquad (\forall\, p_* \le w < z_1 < \infty).$$
Fixing $z_1 = z_0$ checks only one endpoint; conversely, bounding $\sup_{z_1} E_M(z_1) - \inf_{w} E_M(w)$ independently overestimates the excursion by illegally pairing a post-prime $z_1$ with $w > z_1$.

In `primes_and_mertens.py:eps_sup_two_var(pstar)`, we perform a **single forward pass over all primes $p \in [p_*, 25{,}000]$**, tracking the causal running minimum `min_lo_so_far` of $\sum_{p < w} \frac{1}{p} - \ln\ln w - M_0$ **before** evaluating $\sum_{p \le z_1} \frac{1}{p} - \ln\ln z_1 - M_0$ at $z_1 \ge w$, and joining at $25{,}000 > e^{10.1}$ with Johnston–Starichkova (`arXiv:2208.01229v3`, Lemma 3.2). Since $(p-1)^{-2}$ tails strictly decrease with $w \ge p_*$, this yields a valid **all-pairs two-variable** bound:
- $p_* = 131 \implies \varepsilon \le 0.015122$ ($1/\varepsilon \ge 66.129$);
- $p_* = 251 \implies \varepsilon \le 0.0100583$ ($1/\varepsilon \ge 99.42$, BJS Table 1 row $k = 99 \implies C_2 = 345$).

Furthermore, since omitting divisors $p \mid N$ strictly decreases both $(1 - 1/(p-1))^{-1}$ factors and Selberg $1/J_N$ denominators (and preserves $\mathrm{ratio}_{\mathrm{odd}}(\mathbb{P}_N) \ge \mathrm{ratio}_{\mathrm{odd}}(\mathbb{P}_{\mathrm{full}})$, $\mathrm{ratio}_{\mathrm{even}}(\mathbb{P}_N) \le \mathrm{ratio}_{\mathrm{even}}(\mathbb{P}_{\mathrm{full}})$, and $V_N(z_{\mathrm{sub}}) / V_N(z) \le V_{\mathrm{full}}(z_{\mathrm{sub}}) / V_{\mathrm{full}}(z)$ for $z_{\mathrm{sub}} \le z$), a single machine-checkable certificate per slab covers all even $N \in [X_{\mathrm{lo}}, X_{\mathrm{hi}})$ regardless of prime factorization.

---

## 4. Finite-Terminating Buchstab Recursion (`compute_n_term`) & Clamped Upper Level

In Rosser–Iwaniec's combinatorial identity ($n \ge 3$), $T_n(D, z)$ sums over prime tuples $p_n < \dots < p_1 < z$ ($\ge p_*$) satisfying $p_m < (D / (p_1 \cdots p_m))^{1/2}$ for $m < n$, $m \equiv n \pmod 2$. In particular $m = n - 2$ gives $p_1 \cdots p_{n-3} p_{n-2}^3 < D$. Letting $q_1 < q_2 < \dots$ enumerate all odd primes $\ge p_*$, we must have
$$q_3^3 \prod_{j=4}^{n} q_j \le p_{n-2}^3 \prod_{j=1}^{n-3} p_j < D.$$
Whenever $n \ge n_{\mathrm{term}}(p_*, D)$ (the least index where the left-hand product exceeds $D$), **$T_n(D, z) = 0$ identically**. For Regime `2c` ($D_1 \le z^{5.20}$, $D_q := \min(H_2/(Q(p_{2,*}) q_1),\ z^{4.90})$), $n_{\mathrm{term}} \le 83$, eliminating infinite Lyapunov contraction tails while integrating exact level-$n$ two-variable bounds `eps_large_u_two_var` (`u_{2k} = (D_1/z)^{3^{-k}}`, `u_{2k+1} = D_q^{3^{-(k+1)}}`) for small $n$.

---

## 5. Robustness Summary & Arithmetic Discipline

- **Arithmetic Purity**: `interval.py` arms `decimal.getcontext().traps[Inexact] = True` and `traps[Rounded] = True` globally at `PREC = 90` digits. Every non-exact operation must enter `directed_context(ROUND_FLOOR | ROUND_CEILING)`. Transcendental `ln`/`exp` run at `102` digits with a `2-ulp` outward Table-Maker safety pad before rounding back to `90` digits. AST audits forbid IEEE-754 `float` literals/conversions and `import math`.
- **Lean 4 Kernel Replay**: Rational lower/upper bounds in `Data.lean` (`DENOM = 10^10`) are checked in Lean 4.37.0-rc1 exclusively by kernel reduction (`by decide`, never `native_decide`), zero `sorry`, and zero custom `axiom` declarations.
- **Perturbation Margins**:
  - Finite slabs `[4*10^18, 10^600)` (127 slabs): $\min \mathrm{net} = 0.001833$, $\min \mathrm{sieve\_net} = 0.007749$, $\min \mathrm{tol} = 1.10\times$ (at `2a-01..05`; $\ge 1.7\times$ across all slabs $\ge 10^{22}$).
  - Asymptotic ray `[10^600, ∞)`: $\mathrm{net} \ge 0.010936 > 0$, tolerance $142.9\times$ on total GRH+diagonal remainder, and BJS constant break-even $C_2 \le 417.1$ (versus used $C_2 = 345$).
