# Reference Note: Explicit Linear Sieve (BJS, BS, Rosser–Iwaniec, and `k3/scripts/sieve_cert/linear_sieve.py`)

This reference note extracts exact definitions, theorem/lemma numbers, recurrences, proofs, and version comparisons from:
- **[BJS v6]** Bordignon, Johnston, Starichkova, *An explicit version of Chen's theorem and the linear sieve*, Int. J. Number Theory 21 (2025), no. 10, 2497–2572, DOI `10.1142/S1793042125501192`, `arXiv:2207.09452v6`.
- **[BJS v2]** `arXiv:2207.09452v2` (and checked against v1, v3, v4, v5).
- **[BS v1]** Bordignon, Starichkova, *An explicit version of Chen's theorem assuming the Generalized Riemann Hypothesis*, Ramanujan J. 64 (2024), no. 4, 1213–1242, DOI `10.1007/s11139-024-00866-x`, `arXiv:2211.08844v1`.
- **[HR1974]** Halberstam, Richert, *Sieve Methods*, 1974.
- **[Iw1980]** Iwaniec, *A new form of the error term in the linear sieve*, Acta Arith. 37 (1980), 307–320.
- Repository modules: `shared/certificate/linear_sieve/`, `k4/certificate/all_even_1p4_ext/`, and `k3/scripts/sieve_cert/` (with Lean 4 formalizations in `k3/BuchstabSwitching/Sieve/LinearSieveBJS/`).

*(Lemma/Theorem/Proposition numbers below follow the compiled TeX `\newtheorem` counters of the respective papers, verified directly from the TeX sources.)*

---

## 1. Rosser–Iwaniec $\lambda^\pm$ ($D^\pm$) Weights and $T_n(D, z)$ Recursion ([BJS v6] §2)

### 1.1 Exact BJS Formulation (Lemmas 11 & Proposition 13)

In [BJS v6] §2, the combinatorial sieve weights $\lambda^\pm(d)$ are introduced by citing Nathanson [Ch. 9, Theorem 9.3, Lemma 9.3, (9.10), (9.13), Lemma 9.8]. Let $\mathbb{P}$ be a set of primes, $g(d):\mathbb{N}\to\mathbb{C}$ a multiplicative function with $0 \le g(p) < 1$ for $p \in \mathbb{P}$, and for $2 \le z \le D$ ($D \in \mathbb{R}^+$):
$$P(z) := \prod_{\substack{p \in \mathbb{P} \\ p < z}} p, \qquad V(z) := \prod_{p \mid P(z)} (1 - g(p)), \qquad s := \frac{\log D}{\log z}.$$

For $n \ge 1$ and primes $p_1, \dots, p_n \in \mathbb{P}$, define the Rosser–Iwaniec cutoff ([BJS v6] §2.3, `eq: def-y_n` / `eq: def-T-n-D-z`):
$$y_n = y_n(D, p_1, \dots, p_n) := \left(\frac{D}{p_1 \cdots p_n}\right)^{1/2},$$
$$T_n(D, z) := \sum_{\substack{p_1, \dots, p_n \in \mathbb{P} \\ y_n \le p_n < \dots < p_1 < z \\ p_m < y_m \,\forall m < n,\; m \equiv n \pmod 2}} g(p_1 \cdots p_n) V(p_n).$$

In **Proposition 13** ([BJS v6], TeX label `theo:G`, citing [Nathanson, Lemma 9.3]), for the Rosser–Iwaniec upper- and lower-bound sieve weights $\lambda^\pm(d)$ constructed in [Nathanson, Theorem 9.3] (i.e., $\lambda^+(d) = \mu(d)\mathbf{1}_{D^+}(d)$ supported on squarefree $d = p_1 \cdots p_n \mid P(z)$ with $p_n < \dots < p_1 < z$ satisfying $p_m < y_m$ for all odd $m \le n$, and $\lambda^-(d) = \mu(d)\mathbf{1}_{D^-}(d)$ with $p_m < y_m$ for all even $m \le n$):
$$G(z, \lambda^\pm) := \sum_{d \mid P(z)} \lambda^\pm(d) g(d),$$
$$G(z, \lambda^+) = V(z) + \sum_{\substack{n=1 \\ n \equiv 1 \pmod 2}}^\infty T_n(D, z), \qquad G(z, \lambda^-) = V(z) - \sum_{\substack{n=1 \\ n \equiv 0 \pmod 2}}^\infty T_n(D, z).$$
Here $T_n(D, z)$ captures the exact "Buchstab boundary" terms where the parity-constrained Rosser–Iwaniec condition $p_m < y_m$ holds for all $m < n$ ($m \equiv n \pmod 2$) and fails at step $n$ ($p_n \ge y_n$).

### 1.2 Exact $T_n(D, z)$ Recurrence ([BJS v6] Lemma 11, TeX label `lemma:expf_n`)

Assume $0 \le g(p) < 1$ for $p \in \mathbb{P}$, and suppose (see §3 below on the fixed-$z$ vs all-levels issue) that
$$\frac{V(u)}{V(z)} := \prod_{\substack{p \in \mathbb{P} \\ u \le p < z}} (1 - g(p))^{-1} \le K \frac{\log z}{\log u}, \qquad 1 < K < 1 + \varepsilon.$$

1. **Base case $n = 1$** ([BJS v6] Lemma 11 proof, citing [Nathanson, Lemma 9.3 & (9.13)]):
   - If $s > 3$, $T_1(D, z) = 0$ (since $p_1 < z < D^{1/3}$ contradicts $y_1 = (D/p_1)^{1/2} \le p_1 \iff p_1 \ge D^{1/3}$).
   - If $1 \le s \le 3$, $T_1(D, z) = V(D^{1/3}) - V(z)$, so using the product bound at $u = D^{1/3}$:
     $$\frac{T_1(D, z)}{V(z)} \le \frac{3K}{s} - 1 = \left(\frac{3}{s} - 1\right) + \frac{3}{s}(K - 1) < f_1(s) + \frac{3\varepsilon}{s}.$$
     (With $3/s \le 3 \le 3 e^2 h(s)$ on $1 \le s \le 3$, this yields $\tau_1 = 3$.)

2. **Inductive step $n \ge 2$, case $s \ge 3$ (or $n \ge 2$ even and $s \ge 2$)** ([BJS v6] eq. `Tneq`, citing [Nathanson, Lemma 9.8 & Theorem 9.5]):
   Unfolding $T_n(D, z) = \sum_{p_1 < z} g(p_1) T_{n-1}(D/p_1, p_1)$, applying the induction hypothesis $T_{n-1}(D', z') < V(z')(f_{n-1}(s') + E_{n-1}(s'))$ at $D' = D/p_1$, $z' = p_1$, $s' = \frac{\log D}{\log p_1} - 1$, and integrating by parts via [Nathanson, Lemma 9.8]:
   $$\frac{T_n(D, z)}{V(z)} < (K - 1)\big(f_{n-1}(s-1) + E_{n-1}(s-1)\big) + \frac{K}{s}\int_s^\infty \big(f_{n-1}(t-1) + E_{n-1}(t-1)\big)\,\mathrm{d}t.$$
   (In [BJS v6], $E_{n-1}$ is taken to be $h_{n-1}(s) := \varepsilon \tau_{n-1} e^2 h(s)$.)

3. **Inductive step $n \ge 3$ odd and $1 \le s \le 3$** ([BJS v6] lines 834–843):
   Because $m = 1 \equiv n \pmod 2$ imposes $p_1 < y_1 = (D/p_1)^{1/2} \iff p_1 < D^{1/3} < z$, we have $T_n(D, z) = T_n(D, D^{1/3})$. Applying the $s = 3$ step at upper level $z' = D^{1/3}$ gives:
   $$T_n(D, z) < (K - 1)V(D^{1/3})\big(f_{n-1}(2) + E_{n-1}(2)\big) + \frac{K V(D^{1/3})}{3}\int_3^\infty \big(f_{n-1}(t-1) + E_{n-1}(t-1)\big)\,\mathrm{d}t.$$
   Using $V(D^{1/3}) \le \frac{3K}{s} V(z)$ gives:
   $$\frac{T_n(D, z)}{V(z)} < \frac{3K(K-1)}{s}\big(f_{n-1}(2) + E_{n-1}(2)\big) + \frac{K^2}{s}\int_3^\infty \big(f_{n-1}(t-1) + E_{n-1}(t-1)\big)\,\mathrm{d}t.$$
   *Note:* [BJS v6] Footnote 1 (p. 11 / TeX line 833) explicitly records that this fixes an error in Nathanson (and in [BJS v2] lines 790–793!), where it had been falsely claimed via [Nathanson, (9.15)] that $T_n(D,z) < V(z)(f_n(3) + h_n(3))$ for $1 \le s \le 3$, which would contradict the optimality of the linear sieve (cf. Iwaniec, *Opera de Cribro*, §12.3).

### 1.3 Combinatorial Termination (`T_n(D, z) = 0` for $n \ge n_{\mathrm{term}}$)

In `T_n(D, z)`, for $n \ge 3$, setting $m = n - 2$ ($m \equiv n \pmod 2$) gives $p_{n-2} < y_{n-2} = (D/(p_1\cdots p_{n-2}))^{1/2}$, i.e., $p_1 \cdots p_{n-3} p_{n-2}^3 < D$. Since $p_n < p_{n-1} < p_{n-2} < \dots < p_1$ all lie in $\mathbb{P} = \{q_1 < q_2 < q_3 < \dots\}$, we must have $p_{n-2} \ge q_3$ and $p_{n-j} \ge q_{j+1}$ for $j \ge 3$, so
$$q_3^3 \prod_{j=4}^n q_j < D.$$
Thus $T_n(D, z) = 0$ identically for all $n \ge n_{\mathrm{term}}$, where $n_{\mathrm{term}}$ is the smallest $n \ge 3$ with $q_3^3 \prod_{j=4}^n q_j > D$ (also $T_n(D, z) = 0$ whenever $s \ge n + 2$, since $(D/(p_1\cdots p_n))^{1/2} \le p_n < z$ and $p_i < z$ forces $D < z^{n+2}$).

---

## 2. $f_n(s)$, $E_n(s)$, $h(s)$, Contraction Constants, $\tau_n(\varepsilon)$, and $C_1(\varepsilon), C_2(\varepsilon)$

### 2.1 Definition of $f_n(s)$ ([BJS v6] §2.1)

For $s \ge 1$ ($n$ odd) and $s \ge 2$ ($n$ even):
- (`eq:f11`):
  $$s f_1(s) := \begin{cases} 3 - s, & 1 \le s \le 3, \\ 0, & s > 3. \end{cases}$$
- (`eq:f22`): for $n \ge 2$ even and $s \ge 2$, or $n \ge 3$ odd and $s \ge 3$:
  $$s f_n(s) := \int_s^\infty f_{n-1}(t-1)\,\mathrm{d}t.$$
- (`eq:odd`): for $n \ge 3$ odd and $1 \le s \le 3$:
  $$s f_n(s) := 3 f_n(3) = \int_3^\infty f_{n-1}(t-1)\,\mathrm{d}t.$$
- Closed form for $n = 2$ ([BJS v6] §2.2, `eq:f2`):
  $$s f_2(s) = \begin{cases} s - 3\log(s-1) + 3\log 3 - 4, & 2 \le s \le 4, \\ 0, & s \ge 4. \end{cases}$$
- Reduction for $n \ge 4$ even, $2 \le s \le 4$ ([BJS v6] §2.2, `eq:f4`):
  $$s f_n(s) = 3 f_{n-1}(3)\log\left(\frac{3}{s-1}\right) + \int_4^\infty f_{n-1}(t-1)\,\mathrm{d}t.$$
- Connection to $F(s), f(s)$ ([BJS v6] `bigFdeffn`, `lilFdeffn`; citing [Nathanson, Theorem 9.4]):
  $$F(s) = 1 + \sum_{\substack{n=1 \\ n \text{ odd}}}^\infty f_n(s) \quad (s \ge 1), \qquad f(s) = 1 - \sum_{\substack{n=2 \\ n \text{ even}}}^\infty f_n(s) \quad (s \ge 2).$$
  **Important [BJS v6] TeX typo:** Line 461 (`lilFdeffn`) in [BJS v6] prints `n \text{ odd}` instead of `n \text{ even}` in the sum for $f(s)$! The proof of Proposition 13 (`theo:G`, line 986) correctly uses the even $n$ sum $V(z) - \sum_{n\equiv 0 \pmod 2} T_n(D,z)$. (In [BJS v2] Theorem 13, both signs were wrong: it wrote $f(s) = 1 + \sum_{n \ge 2 \text{ even}} f_n(s)$ and $G(z,\lambda^-) = V(z)(f(s) + \epsilon e^2 h(s)\sum \tau_{2n})$.)

### 2.2 Bound $f_n(s) \le 2 e^2 c_n^{n-1} h(s)$ ([BJS v6] Lemmas 7–8)

[BJS v6] defines (`eq-def-h(s)`):
$$h(s) := \begin{cases} e^{-2}, & 1 \le s \le 2, \\ e^{-s}, & 2 \le s \le 3, \\ 3 s^{-1} e^{-s}, & s \ge 3. \end{cases}$$
With $c_1 = 1$, **Lemma 7** (`lemma:fsmall`, Table 2, proved in §2.2 via Riemann sums of step $1/1000$) gives valid constants $c_n$ for $2 \le n \le 500$ in
$$f_n(s) \le 2 e^2 (c_n)^{n-1} h(s) \qquad (\text{`eq:fh`}):$$
- $c_2 = 0.33$, $c_3 = 0.39$, $c_4 = 0.45$, $c_5 = 0.51$, $c_6 = 0.54$, $c_7 = 0.57$, $c_8 = 0.58$, $c_{9\text{--}10} = 0.61$, $c_{11\text{--}12} = 0.63$, $c_{13} = 0.64$, $c_{14} = 0.65$, $c_{15\text{--}18} = 0.66$, $c_{19\text{--}20} = 0.67$, $c_{21\text{--}26} = 0.68$, $c_{27\text{--}34} = 0.69$, $c_{35\text{--}46} = 0.70$, $c_{47\text{--}82} = 0.71$, $c_{83\text{--}345} = 0.72$, $c_{346\text{--}500} = 0.73$.

**Lemma 8** (`lemma:f_n`, citing [Nathanson, Lemma 9.7]) gives $c_n = 0.9607$ for all $n \ge 2$ (from $H(2)/(2h(2)) = \alpha = 0.96068\ldots$).

### 2.3 $h(s)$ Contraction Constants ([BJS v6] Lemmas 9–10)

- **Lemma 9** (`lem:hsm1`): With $\gamma_3 := \frac{4e}{3}$ and $\gamma_{s_0} := e^{s_0 - 2}$ for $2 \le s_0 \le 2.8$:
  $$h(s - 1) \le \begin{cases} \gamma_{s_0}\, h(s), & 2 \le s \le s_0 + 0.2, \\ \gamma_3\, h(s), & s \ge 3, \end{cases} \qquad \text{and} \qquad \frac{3}{s} h(2) \le 3 h(s) \quad (1 \le s \le 3).$$
- **Lemma 10** (`lemma:forg`): With $H(s) := \int_s^\infty h(t-1)\,\mathrm{d}t$ ($s \ge 2$) and $\alpha := \frac{e^2 H(2)}{2} = 0.96068\ldots$:
  $$H(s) \le \kappa_{s_0}\, s\, h(s) \quad (s \ge s_0), \qquad s_0 \in \{2, 2.2, 2.4, 2.6, 2.8, 3\},$$
  where:
  $$\kappa_2 = 0.9607,\quad \kappa_{2.2} = 0.9557,\quad \kappa_{2.4} = 0.9457,\quad \kappa_{2.6} = 0.9261,\quad \kappa_{2.8} = 0.8914,\quad \kappa_3 = 0.8349$$
  (and for $s \ge 4$, the proof shows $H(s) \le 0.81\, s\, h(s)$), and for $1 \le s \le 3$:
  $$H(3) \le \tilde{\kappa}\, s\, h(s), \qquad \tilde{\kappa} = 0.9214 \quad (\text{since } \max\{\tfrac{e(2\alpha-1)}{3},\, 2\alpha-1\} = 2\alpha - 1 \le 0.9214).$$

### 2.4 Lyapunov $\tau_n(\varepsilon)$ Recurrence, $\tau'_n$, and $C_1(\varepsilon), C_2(\varepsilon)$ ([BJS v6] Lemmas 11, 12, 14 & Theorem 6)

In **Lemma 11** (`lemma:expf_n`), setting $h_n(s) := \varepsilon \tau_n e^2 h(s)$ yields $T_n(D,z) < V(z)(f_n(s) + \varepsilon \tau_n e^2 h(s))$ with $\tau_1 = 3$ and for $n \ge 2$ (`eq:tau`):
$$\tau_n := \begin{cases} \tau_{n-1} \cdot \max\{\xi_2, \xi_{2.2}, \xi_{2.4}, \xi_{2.6}, \xi_{2.8}, \xi_3\}, & n \text{ even}, \\ \tau_{n-1} \cdot \max\{\xi_3, \tilde{\xi}\}, & n \text{ odd}, \end{cases}$$
where
$$\xi_{s_0} := \kappa_{s_0} + (\gamma_{s_0} + \kappa_{s_0})\varepsilon + 2\gamma_{s_0}\frac{(c_{n-1})^{n-2}}{\tau_{n-1}} + 2\frac{(c_n)^{n-1}}{\tau_{n-1}},$$
$$\tilde{\xi} := \tilde{\kappa} + (5 + 4\varepsilon)\varepsilon + 6(1+\varepsilon)\frac{(c_{n-1})^{n-2}}{\tau_{n-1}} + 2(2+\varepsilon)\frac{(c_n)^{n-1}}{\tau_{n-1}}.$$
*(Minor typo in [BJS v6] proof line 846: prints $(c_n)^{n-2}$ where the lemma statement correctly has $(c_{n-1})^{n-2}$.)*

In **Lemma 12** (`lem: taup`), for $0 < \varepsilon \le 1/74$, $\tau_n \le \tau'_n$ where $\tau'_1 = 3$ and (`eq:taup`):
$$\tau'_n := \tau'_{n-1}\left(\kappa_2 + (\gamma_2 + \kappa_2)\varepsilon + \frac{8e}{3}\frac{(c_{n-1})^{n-2}}{\tau'_{n-1}} + 2(2+\varepsilon)\frac{(c_n)^{n-1}}{\tau'_{n-1}}\right), \qquad (\gamma_2 = e^{0.2}).$$
The bound $\varepsilon \le 1/74$ is used specifically to ensure $\tilde{\kappa} + (5 + 4\varepsilon)\varepsilon \le \kappa_2 + (\gamma_2 + \kappa_2)\varepsilon$ (while $\max_{s_0}(\kappa_{s_0} + (\gamma_{s_0}+\kappa_{s_0})\varepsilon) \le \kappa_2 + (\gamma_2+\kappa_2)\varepsilon$ holds for $\varepsilon \le 1/54$, and $\kappa_2 + (\gamma_2+\kappa_2)\varepsilon < 1$ requires $\varepsilon < 1/55$).

In **Lemma 14** (`lemma:exprec`), for $\varepsilon \in (0, 1/74]$ and $k_e, k_o \ge 1$:
$$C_1(\varepsilon) := \sum_{n=1}^\infty \tau_{2n-1} \le \sum_{n=1}^{k_o} \tau_{2n-1} + \tau'_{2k_o}\sum_{n=1}^\infty J(2k_o + 1)^{2n-1},$$
$$C_2(\varepsilon) := \sum_{n=1}^\infty \tau_{2n} \le \sum_{n=1}^{k_e} \tau_{2n} + \tau'_{2k_e+1}\sum_{n=1}^\infty J(2k_e + 2)^{2n-1},$$
$$J(k) := \kappa_2 + (\gamma_2 + \kappa_2)\varepsilon + \frac{8e}{6}\left(\frac{\kappa_2}{\kappa_2 + (\gamma_2+\kappa_2)\varepsilon}\right)^{k-2} + \frac{2(2+\varepsilon)}{3}\frac{\kappa_2^{k-1}}{\big(\kappa_2 + (\gamma_2+\kappa_2)\varepsilon\big)^{k-2}}.$$
Table 1 of [BJS v6] is computed with $k_e = 250$, $k_o = 249$ (using higher-precision $c_n$ up to $n = 500$ and Lemma 8's $c_{501} = 0.9607$).

**Theorem 6** ([BJS v6], `theo:JR`): Suppose $0 < \varepsilon \le 1/74$ and $\prod_{p \in \mathbb{P}/\mathbb{Q},\, u \le p < z} (1 - g_n(p))^{-1} < (1 + \varepsilon)\frac{\log z}{\log u}$ for all $n$ and $1 < u < z$. Then:
$$S(A, \mathbb{P}, z) < \big(F(s) + \varepsilon C_1(\varepsilon) e^2 h(s)\big)X_A + R \quad (D \ge z),$$
$$S(A, \mathbb{P}, z) > \big(f(s) - \varepsilon C_2(\varepsilon) e^2 h(s)\big)X_A - R \quad (D \ge z^2),$$
where $X_A := \sum_{n=1}^\infty a(n)\prod_{p \mid P(z)}(1 - g_n(p))$ and $R := \sum_{d \mid P(z),\, d < QD} |r(d)|$.

**Table 1 of [BJS v6] (24 rows; decreasing in $\varepsilon^{-1}$):**

| $\varepsilon^{-1}$ | $C_1(\varepsilon)$ | $C_2(\varepsilon)$ | $\varepsilon^{-1}$ | $C_1(\varepsilon)$ | $C_2(\varepsilon)$ | $\varepsilon^{-1}$ | $C_1(\varepsilon)$ | $C_2(\varepsilon)$ | $\varepsilon^{-1}$ | $C_1(\varepsilon)$ | $C_2(\varepsilon)$ |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 74 | 631 | 630 | 95 | 302 | 302 | 200 | 153 | 154 | 800 | 115 | 116 |
| 76 | 559 | 559 | 100 | 276 | 277 | 300 | 133 | 134 | 900 | 114 | 115 |
| 78 | 504 | 504 | 120 | 218 | 219 | 400 | 125 | 126 | 1000 | 113 | 114 |
| 80 | 461 | 461 | 140 | 189 | 190 | 500 | 121 | 122 | 2000 | 109 | 110 |
| 85 | 386 | 386 | 160 | 172 | 173 | 600 | 118 | 119 | 10000 | 106 | 108 |
| 90 | 336 | 337 | 180 | 161 | 162 | 700 | 116 | 117 | 100000 | 106 | 107 |

### 2.5 Key Differences Between [BJS v2] (also reproduced in [BS v1]) and [BJS v6]

1. **Range of $\varepsilon$ and hypothesis inequality:**
   - [BJS v2] (Theorem 6) had $0 < \varepsilon < 1/63$ and non-strict $\le (1+\varepsilon)\frac{\log z}{\log u}$.
   - [BJS v6] (Theorem 6) restricts to $0 < \varepsilon \le 1/74$ and strict $< (1+\varepsilon)\frac{\log z}{\log u}$.
2. **Fix of $c_n$ and $H(s)$ gap on $2 \le s < 3$:**
   - [BJS v2] Theorem 8 claimed $c_n \le 0.9214$ for all $n$ via Theorem 10 ($H(s) \le 0.9214 s h(s)$ for $s \ge 3$ and $H(3) \le 0.9214 s h(s)$ for $1 \le s \le 3$), overlooking $2 \le s < 3$ where $H(s)/(sh(s))$ reaches $\alpha = 0.96068\ldots$ at $s=2$.
   - [BJS v6] Lemma 8 restores $c_n = 0.9607$ (Nathanson Lemma 9.7), splits $s_0 \in \{2, 2.2, 2.4, 2.6, 2.8, 3\}$ in Lemmas 9–10, and extends Table 2 ($c_n$) from $n \le 450$ to $n \le 500$ (with minor shifts for $n \ge 21$, e.g., $21\text{--}26: 0.68$ vs v2 $21\text{--}24$; $83\text{--}345: 0.72$ vs v2 $81\text{--}308$; $346\text{--}500: 0.73$ vs v2 $309\text{--}450$).
3. **Fix of $n \ge 3$ odd, $1 \le s \le 3$ bug in Lemma 11:**
   - [BJS v2] Lemma 12 (`lemma:expf_n`) falsely claimed $T_n(D,z) < V(z)(f_n(3)+h_n(3))$ for $n \ge 3$ odd, $1 \le s \le 3$ (and misprinted $s \ge 0$ for $n$ even).
   - [BJS v6] Lemma 11 replaces this with the $D^{1/3}$ recursion and the $\tilde{\xi}$ branch, which in turn necessitates Lemma 12's $\tau'_n$ and $\varepsilon \le 1/74$.
4. **Fix of Proposition 13 (`theo:G`) signs & tail bound:**
   - [BJS v2] Theorem 13 (`theo:G`) had wrong `+` signs in $f(s)$ and $G(z,\lambda^-)$, and bounded the $\tau_n$ tail in Lemma 14 via $\tau_{2k_1+1}/\tau_{2k_1}$ without proving ratio monotonicity.
   - [BJS v6] Proposition 13 fixes the signs/inequalities, and Lemma 14 proves the tail rigorously via $\tau'_n$ and $J(k)$ (though [BJS v6] introduces the parity typo `n odd` in `lilFdeffn` line 461).
5. **Table 1 ($C_1, C_2$) and Table 3 ($\tau_n$ at $\varepsilon = 1/200$):**
   - [BJS v2] Table 1 (48 rows, reproduced verbatim in [BS v1] Table 1) runs from $\varepsilon^{-1} = 63$ (`32881, 32875`) to $39500$ (`111, 113`), with `200 -> (162, 164)`, `300 -> (141, 142)`, `400 -> (132, 134)`, `500 -> (127, 129)`, `1000 -> (119, 120)`.
   - [BJS v6] Table 1 (24 rows) runs from $\varepsilon^{-1} = 74$ (`631, 630` vs v2 `729, 730`) to $100000$ (`106, 107`), with `200 -> (153, 154)`, `1000 -> (113, 114)`.
   - Table 3 ($\tau_n$ at $\varepsilon = 1/200$): v2 has $\tau_2 = 11, \tau_3 = 13, \tau_{4\text{--}6} = 14, \dots, \tau_{429\text{--}450} = 10^{-9}$; v6 has $\tau_2 = 8, \tau_{3\text{--}10} = 10, \dots, \tau_{449\text{--}500} = 10^{-7}$.

---

## 3. All-Levels Two-Variable Hypothesis vs Fixed-$z$ Issue in [BJS] Theorem 6

In [BJS v6] Theorem 6 (`eq:cond1`, lines 331–335) and Lemma 11 (`eq:prod11`, lines 741–750), the stated product hypothesis has its upper endpoint **fixed at $z$**:
$$\prod_{\substack{p \in \mathbb{P}/\mathbb{Q} \\ u \le p < z}} (1 - g_n(p))^{-1} < (1 + \varepsilon)\frac{\log z}{\log u} \qquad (\forall\, n \ge 1,\; 1 < u < z).$$

However, the **proof of Lemma 11 (`lemma:expf_n`)** requires the stronger **all-levels two-variable** condition:
$$\prod_{\substack{p \in \mathbb{P}/\mathbb{Q} \\ u \le p < w}} (1 - g_n(p))^{-1} < (1 + \varepsilon)\frac{\log w}{\log u} \qquad (\forall\, n \ge 1,\; 1 < u < w \le z).$$

Specifically, the fixed-$z$ condition fails to support the proof at two places in Lemma 11:
1. **Induction step (`Tneq`, line 790):** Expressing $T_n(D, z) = \sum_{p_1 < z} g(p_1) T_{n-1}(D/p_1, p_1)$ applies the induction hypothesis for $T_{n-1}$ at **upper endpoint $w = p_1 < z$**, requiring the product bound on $[u, p_1)$ for all $1 < u < p_1$.
2. **Case $n \ge 3$ odd, $1 \le s \le 3$ (lines 834–843):** Here $p_1 < y_1 \iff p_1 < D^{1/3} < z$, so $T_n(D, z) = T_n(D, D^{1/3})$ is expanded via [Nathanson, Lemma 9.8] at the **real upper endpoint $w = D^{1/3} < z$** (producing $(K-1)V(D^{1/3})\dots + \frac{K V(D^{1/3})}{3}\dots$), which requires the product bound on $[u, D^{1/3})$ for $1 < u < D^{1/3}$ as well as on $[u, p_1)$ inside $T_{n-1}$.

Because $\prod_{u \le p < w} = \frac{V(u)/V(z)}{V(w)/V(z)}$, an upper bound at fixed $z$ does not control $V(u)/V(w)$ for $w < z$. For example, with pre-sieve $\mathbb{Q} = \{3 \le p < 41\}$ and $g(p) = 1/(p-1)$ (as in `notes/all-even-1p4-under-grh.md` §4.2), the fixed-$z$ condition at $z \ge 5.33\cdot 10^7$ gives $\varepsilon \le 8.526\cdot 10^{-3}$ ($\varepsilon^{-1} \ge 117.29$), whereas on the sub-interval $[97, 113)$ the true two-variable ratio is
$$\frac{\prod_{97 \le p < 113} \frac{p-1}{p-2}}{\log 113 / \log 97} - 1 = \frac{\frac{96}{95}\cdot\frac{100}{99}\cdot\frac{102}{101}\cdot\frac{106}{105}\cdot\frac{108}{107}}{\log 113 / \log 97} - 1 \approx 0.016460 > \frac{1}{74},$$
violating both $\varepsilon \le 1/100$ and BJS's validity threshold $\varepsilon \le 1/74$. By contrast, `primes_and_mertens.py:eps_sup_two_var(pstar)` computes a strictly order-respecting all-pairs two-variable bound over $p_* \le w < z_1 < \infty$.

---

## 4. [BJS v6] Lemma 19 and Lemma 38

### 4.1 Lemma 19 (`lem: estimetes-f-F`, citing [Cai, Lemma 2], lines 1180–1188)

Let $f, F$ be as defined in (`def-f(s)-F(s)`): $F(s) = \frac{2e^\gamma}{s}$, $f(s) = 0$ for $0 < s \le 2$; $(sF(s))' = f(s-1)$, $(sf(s))' = F(s-1)$ for $s \ge 2$. Then:
$$F(s) = \frac{2e^\gamma}{s} \quad (0 < s \le 3), \qquad F(s) = \frac{2e^\gamma}{s}\left(1 + \int_2^{s-1}\frac{\log(t-1)}{t}\,\mathrm{d}t\right) \quad (3 \le s \le 4),$$
$$f(s) = 0 \quad (0 < s \le 2), \qquad f(s) = \frac{2e^\gamma \log(s-1)}{s} \quad (2 \le s \le 4).$$
*(Extension via $(sF(s))' = f(s-1)$: the same integral formula for $F(s)$ holds on $3 \le s \le 5$, since $s-1 \in [2, 4]$; similarly on $4 \le s \le 6$, $sf(s) = 2e^\gamma(\log(s-1) + \int_3^{s-1} \frac{1}{t}\int_3^t \frac{\log(w-2)}{w-1}\,\mathrm{d}w\,\mathrm{d}t)$.)*

### 4.2 Lemma 38 (`vjlem`, lines 1799–1869)

With $P^{(j)}(x) = \prod_{p < x,\, p \nmid N,\, p \notin \{q_1,\dots,q_j\}} p$ (`eq: def-mj-Aj-Pj(x)`), $V^{(j)}(x) = \prod_{p \mid P^{(j)}(x)} (1 - \frac{1}{p-1})$ (`eq: def-V(x)-Vj(x)`), $m_j = q_1 \cdots q_j \le \log^{10} N$ (and $m_0 = 1$, $V^{(0)}(x) = V(x)$), and
$$U_N^{(j)} := 2e^{-\gamma} \prod_{p>2}\left(1 - \frac{1}{(p-1)^2}\right)\prod_{\substack{p>2 \\ p \mid N m_j}}\frac{p-1}{p-2} \qquad (\text{`eq: def-UNj`}),$$
**Lemma 38** states that for $x \ge 285$ and $j = 0, \dots, \ell$:
$$V^{(j)}(x) = \frac{U_N^{(j)}}{\log x}\left[1 + 1.45\,\theta_1(x)\frac{\log N}{x - 1}\left(1 + \frac{10\log\log N}{\log N}\right)\right]\left(1 + \frac{1.002\,\theta_2(x)}{x - 3}\right)\left(1 + \frac{\theta_3(x)}{2\log^2 x}\right),$$
where $|\theta_i(x)| \le 1$ for $i = 1, 2, 3$. (For $j = 0$, the proof's $m_j \le \log^{10} N$ bound is not needed since $\omega(N) \le \frac{\log N}{\log 2}$, so the $10\log\log N/\log N$ term is absent when bounding $\omega(N)$ directly, though Lemma 38's formula remains valid with it.) In particular, for $x = z = N^{1/8} \ge e^{20}$ and $x = y = N^{1/3} \ge e^{20}$, [BJS v6] gives relative errors $32.02/\log^2 N$ and $4.51/\log^2 N$.

*(Contrast with [BS v1] Lemma 11 `vjlem`: under GRH for $x \ge 8$, [BS v1] uses Schoenfeld Cor. 3 to get factors $(1 + \frac{\theta(3\log x + 5)}{8\pi\sqrt{x}})(1 + \frac{2\theta}{x})(1 + \frac{8\theta\log N}{x})(1 + \frac{\theta}{x-1})$, **with a typo $2e^\gamma$ instead of $2e^{-\gamma}$ in $U_N$**. Both `k4/` and `k3/` avoid [BS v1] Lemma 11 in favor of unconditional [BJS v6] Lemma 38.)*

---

## 5. Implementation Alignment Across `shared/`, `k4/`, and `k3/`

1. **Closed-Interval `(H*)` & Certified $C_1(\varepsilon), C_2(\varepsilon)$ (`shared/certificate/linear_sieve/`, `shared/notes/linear-sieve/S1`–`S6`)**:
   - Because the inductive proof of Lemma 11 requires the two-variable product bound across all intermediate levels (see §3), both packages certify the **closed-interval `(H*)`** hypothesis directly rather than relying on the fixed-$z$ hypothesis of [BJS v6] Theorem 6:
     - `k4/` (`[10^500, ∞)`): `ε = 1/80` on `Q₀` (`odd primes ≤ 82 ∪ {103, 107, 191, 223}`), certified in `shared/data/linear_sieve_inputs/logs/hstar.log` with exact rational `80:new` / `80:old` rows in `cn_rows_all.json`.
     - `k3/` (`[10^600, ∞)`): `certify_closed_hstar_q0(Q0_100, 100)` over the 31-prime pre-sieve `Q0_100 ⊂ [3, 227]` ($\varepsilon_* \le 0.0099009901 < 1/100$), paired with Lean kernel-certified `C2_bjs certifiedDecaySeq (1/100) ≤ 494` (`Sieve/LinearSieveBJS/CertifiedC2.lean`, Python cap `495`) and SHA-256-pinned cross-check rows `100:old` ($C_2 \le 348.365884$) and `100:new` ($C_2 \le 235.091292$) in `cn_rows_all.json`.
2. **Quadrature & Pointwise Buchstab Envelopes (`k3/scripts/sieve_cert/linear_sieve.py`)**:
   - Quadrature bounds on $F(s)$ (`[3, 5]`, $2000$ panels) and $f(s)$ (`[4, 6]`, $200$ panels) use $\max_{[2,4]} |(\frac{\ln(t-1)}{t})''| = 1.0 < 1.3$ and $\max_{[3,5]} |(\frac{1}{t}\int_3^t \frac{\ln(w-2)}{w-1}\,\mathrm{d}w)''| = \frac{1}{6} < 0.3$.
   - Where finite-terminating Buchstab envelopes are evaluated (`_ensure_f_hat`, `_run_e_const_hi`, step $\Delta s = 0.005$ up to $n = 110$), left-endpoint ceiling Riemann sums implement [BJS v6] `eq:f11`, `eq:f22`, `eq:odd` and the inductive inequalities of Lemma 11 (`Tneq` and the $D^{1/3}$ odd branch on $1 \le s < 3$).
3. **Primary-Source Errata Recorded**:
   - [BJS v6] `lilFdeffn` (TeX line 461) prints `n odd` instead of `n even`, and proof line 846 prints $(c_n)^{n-2}$ instead of $(c_{n-1})^{n-2}$;
   - [BS v1] Lemma 1 misprints $x \ge 3$ for Schoenfeld's $x \ge 2657$ threshold, and Lemma 11 misprints $2e^\gamma$ instead of $2e^{-\gamma}$ in $U_N$.
