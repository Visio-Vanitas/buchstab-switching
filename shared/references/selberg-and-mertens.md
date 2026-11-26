# Reference Note: Explicit Mertens, GRH Prime Counting, Selberg $\Lambda^2$ Weights, and Counting Bounds

**Sources verified:**
- **Johnston–Starichkova**: D. R. Johnston and V. V. Starichkova, *Some explicit results on the sum of a prime and an almost prime*, Acta Math. Hungar. **177** (2025), no. 1, 163–192, DOI `10.1007/s10474-025-01572-w`, [`arXiv:2208.01229v3`](https://arxiv.org/abs/2208.01229) (`main.tex` / `references.bib` extracted from `2208.01229` e-print).
- **Rosser–Schoenfeld**: J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. **6** (1962), no. 1, 64–94, DOI `10.1215/ijm/1255631807`.
- **Schoenfeld**: L. Schoenfeld, *Sharper bounds for the Chebyshev functions $\theta(x)$ and $\psi(x)$. II*, Math. Comp. **30** (1976), no. 134, 337–360, DOI `10.1090/s0025-5718-1976-0457374-x`.
- **Robin**: G. Robin, *Estimation de la fonction de Tchebychef $\theta$ sur le $k$-ième nombre premier et grandes valeurs de la fonction $\omega(n)$ nombre de diviseurs premiers de $n$*, Acta Arith. **42** (1983), no. 4, 367–389.
- **Büthe**: J. Büthe, *An analytic method for bounding $\psi(x)$*, Math. Comp. **87** (2018), no. 312, 1991–2009, DOI `10.1090/mcom/3264`.
- **Grenié–Molteni**: L. Grenié and G. Molteni, *An explicit Chebotarev density theorem under GRH*, J. Number Theory **200** (2019), 441–485, DOI `10.1016/j.jnt.2018.12.005` (and *Ramanujan J.* **49** (2019), 535–548).
- **Broadbent–Kadiri–Lumley–Ng–Wilk**: S. Broadbent, H. Kadiri, A. Lumley, N. Ng, and K. Wilk, *Sharper bounds for the Chebyshev function $\theta(x)$*, Math. Comp. **90** (2021), no. 331, 2281–2315, DOI `10.1090/mcom/3643`.
- **Repository cross-checks**:
  - `k3/scripts/sieve_cert/constants.py`
  - `k3/scripts/sieve_cert/primes_and_mertens.py`
  - `k3/scripts/sieve_cert/selberg_weights.py`
  - `k3/scripts/sieve_cert/regime_slabs.py` and `k3/scripts/sieve_cert/regime_asymptotic.py`

---

## 1. Johnston–Starichkova (JS) Lemmas 3.1, 3.2, 5.1, 5.7, 5.8 & Auxiliary Bounds

### 1.1 Auxiliary Inputs Cited in JS
- **Rosser–Schoenfeld (1962, Theorem 2)**: $\pi(N) > \dfrac{N}{\log N - 1/2}$ (used for $N \ge 250$ in JS Lemma 3.1; valid for $x \ge 67$). Also **Theorem 15** (explicit $\varphi$ upper/lower bounds, used in JS Theorem 5.4).
- **Robin (1983, Théorème 11)**: For all $n \ge 3$,
  $$\omega(n) \le \frac{1.3841 \log n}{\log\log n}.$$
- **Büthe (2018, Theorem 2)**: For $x \le 10^{19}$,
  $$x - \theta(x) \le 1.95\sqrt{x}.$$
- **Schoenfeld (1976, Corollary 1)**: Assuming RH, for all $x \ge 2657$,
  $$|\pi(x) - \mathrm{li}(x)| \le \frac{\sqrt{x}\log x}{8\pi}.$$
- **Broadbent et al. (2021, Corollary 5.1)**: For all $x \ge 4 \cdot 10^{18}$,
  $$\psi(x) - \theta(x) \le (1 + 1.93378 \cdot 10^{-8})\sqrt{x} + 1.04320\, x^{1/3}$$
  (used in JS Lemma 5.2 to pass from Grenié–Molteni's $\psi(x;q,a)$ bound to $\theta(x;q,a)$).
- **BJV22 (`arXiv:2207.09452v4`)**:
  - **Lemma 16**: $\sum_{p \le x} \frac{1}{p} \le \log\log x + M_0 + \frac{2}{\sqrt{x}\log x}$ for $\exp(10) < x \le 10^{12}$ (used in JS Lemma 3.2).
  - **Lemma 17**: $\sum_{p < x} \frac{1}{p} \ge \log\log x + M_0 - \frac{2.964 \cdot 10^{-6}}{\log x}$ for $x \ge 2$, and the integral representation eq. (3.5) in JS for $10^{12} < x \le 10^{19}$.
  - **Lemma 23**: $\sum_{d \le x} \mu^2(d) \le 0.65\,x$ for $x \ge 45$ (used in JS Lemmas 5.7 and 5.8).

### 1.2 JS Lemma 3.1 (`\label{Alem}`, `main.tex` lines 252–268)
For $A = \{N - p : p \le N,\ p \nmid N\}$, **for all $N \ge 71$**:
$$|A| > \frac{N}{\log N}.$$
**Proof**: For $N \ge 250$, $|A| = \pi(N) - \omega(N)$. By Rosser–Schoenfeld (1962, Theorem 2) and Robin (1983, Théorème 11):
$$|A| \ge \frac{N}{\log N - \frac{1}{2}} - \frac{1.3841 \log N}{\log\log N} > \frac{N}{\log N}.$$
The range $71 \le N < 250$ is checked by direct computation.

### 1.3 JS Lemma 3.2 (`\label{mertenlem}`, `main.tex` lines 272–309)
Let $M_0 = 0.261497\ldots$ be the Meissel–Mertens constant (`M0_CONST` $\in [0.261496246734, 0.261497246735]$ in `constants.py`). Then:
$$\begin{aligned}
\sum_{p < x} \frac{1}{p} &\ge \log\log x + M_0 - \frac{2.964 \cdot 10^{-6}}{\log x}, \quad & x \ge 2, \quad &\text{(JS 3.2)} \\
\sum_{p < x} \frac{1}{p} &\le \log\log x + M_0 + 1.614 \cdot 10^{-3}, \quad & x > \exp(8.9), \quad &\text{(JS 3.3)} \\
\sum_{p < x} \frac{1}{p} &\le \log\log x + M_0 + \frac{6.836 \cdot 10^{-6}}{\log x}, \quad & x > 10^{12}. \quad &\text{(JS 3.4)}
\end{aligned}$$
**Proof sketch**:
- Lower bound (JS 3.2) is BJV22 Lemma 17.
- For (JS 3.3): direct computation on $[\exp(8.9), \exp(10)]$, and BJV22 Lemma 16 on $(\exp(10), 10^{12}]$ giving error $\le \frac{2}{\sqrt{x}\log x} \le 1.348 \cdot 10^{-3}$; for $x > 10^{12}$, (JS 3.4) is stronger.
- For (JS 3.4): on $10^{12} < x \le 10^{19}$, BJV22 Lemma 17 + Büthe (2018, Theorem 2) $y - \theta(y) \le 1.95\sqrt{y}$ gives
  $$\int_x^{10^{19}} \frac{(y - \theta(y))(1 + \log y)}{y^2 \log^2 y}\,dy \le \frac{1}{\log x}\left(\frac{1.95}{\sqrt{x}} - 0.975\,\mathrm{li}\!\left(\frac{1}{\sqrt{x}}\right)\log x - 2.759\cdot 10^{-11}\log x\right);$$
  combining with the remaining terms $\frac{6.9322\cdot 10^{-5}}{\log^2 x} + 8.6315\cdot 10^{-7}\!\left(\frac{\log x}{2\log^2(10^{19})} + \frac{\log x}{\log(10^{19})}\right)\frac{1}{\log x}$ yields (JS 3.4) on $(10^{12}, 10^{19}]$, and for $x > 10^{19}$ the integral vanishes leaving $\frac{6.9322\cdot 10^{-5}}{\log^2 x} + 8.6315\cdot 10^{-7}\!\left(\frac{1}{2\log^2 x} + \frac{1}{\log x}\right) \le \frac{6.836\cdot 10^{-6}}{\log x}$.

**Cross-check with `primes_and_mertens.py`**:
- `sum_inv_p_ub(z, log_z)` (lines 133–151): exact prime table `INV_P_PREFIX` for $z.\mathrm{hi} \le P_{\mathrm{PREFIX\_MAX}} = 250{,}000$; for $z.\mathrm{lo} > 10^{12}$, uses JS (3.4) error `6.836e-6 / log_z`; for $\ln z.\mathrm{lo} > 10$, uses BJV22 Lemma 16 error `2 / (z.sqrt() * log_z)`; for $\ln z.\mathrm{lo} > 8.9$, uses JS (3.3) error `1.614e-3`.
- `sum_inv_p_lb(z, log_z)` (lines 154–161): exact `INV_P_PREFIX` for $z.\mathrm{lo} \le 250{,}000$; otherwise JS (3.2) error `-2.964e-6 / log_z`.

### 1.4 JS Lemma 5.1 (`\label{epilem}`, `main.tex` lines 621–637)
Let $x \ge X_2 \ge 4 \cdot 10^{18}$, and let $q, a$ be integers with $3 \le q \le \sqrt{x}$ and $(a, q) = 1$. Assuming GRH:
$$\left|\pi(x; q, a) - \frac{\mathrm{li}(x)}{\varphi(q)}\right| \le c_\pi(X_2)\sqrt{x}\log x,$$
where
$$c_\pi(X_2) := \frac{3}{8\pi} + \frac{6 + 1/\pi}{4\log X_2} + \frac{6}{\log^2 X_2} + \frac{\mathrm{li}(2)}{\sqrt{X_2}\log X_2} \le 0.16.$$
**Proof**: Apply Grenié–Molteni (2019, *J. Number Theory* **200**, Corollary 1) to $K = \mathbb{Q}$ and $L = \mathbb{Q}[e^{2\pi i/q}]$, which gives
$$\left|\pi(x; q, a) - \frac{\mathrm{li}(x) - \mathrm{li}(2)}{\varphi(q)}\right| \le \left(\frac{3}{8\pi} + \frac{6 + 1/\pi}{4\log X_2} + \frac{6}{\log^2 X_2}\right)\sqrt{x}\log x,$$
and add $\frac{\mathrm{li}(2)}{\varphi(q)} \le \mathrm{li}(2)$ (using $\varphi(q) \ge 1$) via the triangle inequality.

**Cross-check with `primes_and_mertens.py`**:
- `c_pi_iv(log_x)` (lines 123–130) implements this exact 4-term formula in outward-rounded `Iv`:
  `3/(8*PI) + (6 + 1/PI)/(4*log_x) + 6/(log_x**2) + LI2/(sqrt_x*log_x)`, where `LI2` $\in [1.045163780117, 1.045163780118]$ is computed via the convergent Ramanujan–Soldner series in `constants.py:81–91`.

### 1.5 JS Lemma 5.7 (`\label{lem: bound E_pi}`, `main.tex` lines 792–824)
Assume GRH and suppose $B > 0$, $N \ge X_2 \ge 4\cdot 10^{18}$ is even, and $H := \frac{\sqrt{N}}{\log^{B+1} N} \ge 45$. Then:
$$\sum_{\substack{d \le H \\ (d, N) = 1}} \mu^2(d)\left|\pi(N; d, N) - \frac{\pi(N)}{\varphi(d)}\right| \le \frac{p_G(X_2) N}{\log^B N}, \qquad p_G(X_2) := 0.65\left(c_\pi(X_2) + \frac{1}{16\pi}\right) \le 0.117.$$
**Proof**: For $d = 1$ the summand vanishes, and $d \ne 2$ since $2 \mid N$. For $d \ge 3$ with $(d, N) = 1$, $\varphi(d) \ge 2$, so by the triangle inequality, JS Lemma 5.1, and Schoenfeld (1976, Corollary 1):
$$\left|\pi(N; d, N) - \frac{\pi(N)}{\varphi(d)}\right| \le \left|\pi(N; d, N) - \frac{\mathrm{li}(N)}{\varphi(d)}\right| + \frac{|\mathrm{li}(N) - \pi(N)|}{\varphi(d)} \le \left(c_\pi(X_2) + \frac{1}{16\pi}\right)\sqrt{N}\log N.$$
Summing over $d \le H$ with $\sum_{d \le H} \mu^2(d) \le 0.65 H$ (BJV22 Lemma 23, valid for $H \ge 45$) gives $0.65 H (c_\pi(X_2) + \frac{1}{16\pi})\sqrt{N}\log N = \frac{p_G(X_2) N}{\log^B N}$.

### 1.6 JS Lemma 5.8 (`\label{rgrhlem}`, `main.tex` lines 826–859)
Under the notation and hypotheses of JS Lemma 5.7, with $r(d) = |A_d| - |A|/\varphi(d)$:
$$\sum_{\substack{d < H \\ d \mid P(z)}} |r(d)| < \frac{c_{4,G}(X_2) N}{\log^B N}, \qquad c_{4,G}(X_2) := p_G(X_2) + \frac{0.9}{\sqrt{X_2}\log\log X_2} \le 0.117.$$
**Proof**: Since $|A| = \pi(N) - \omega(N)$ and $|A_d| = \pi(N; d, N) - \omega(N; d, N)$ (where $\omega(N; d, N)$ counts prime factors $p \mid N$ with $p \equiv N \pmod d$), we have $0 \le \omega(N; d, N) \le \omega(N)$ and $\varphi(d) \ge 1$, so
$$|r(d)| \le \left|\pi(N; d, N) - \frac{\pi(N)}{\varphi(d)}\right| + \omega(N).$$
Applying JS Lemma 5.7, Robin (1983, Théorème 11) $\omega(N) \le \frac{1.3841\log N}{\log\log N}$, and BJV22 Lemma 23 ($\sum_{d \le H} \mu^2(d) \le 0.65 H$) gives $0.65 \cdot 1.3841 = 0.899665 < 0.9$, yielding the bound. *(Note: `main.tex` line 856 has a minor typo $\sqrt{X}$ for $\sqrt{X_2}$.)*

**Cross-check with `primes_and_mertens.py`**:
- `epd_norm_iv(x_lo_iv, log_x_lo)` (lines 174–180) bounds $|r(d)| / (N / \log N)$ uniformly for $3 \le d \le \sqrt{N}$ and $N \ge x_{\mathrm{lo}}$ ($\log x_{\mathrm{lo}} > 4.5$):
  $$\frac{|r(d)|}{N/\log N} \le \left(c_\pi(\log x_{\mathrm{lo}}) + \frac{1}{16\pi}\right)\frac{\log^2 x_{\mathrm{lo}}}{\sqrt{x_{\mathrm{lo}}}} + \frac{1.3841\log x_{\mathrm{lo}}}{\log\log x_{\mathrm{lo}}}\cdot \frac{\log x_{\mathrm{lo}}}{x_{\mathrm{lo}}}.$$
  (Here both $\frac{\log^2 N}{\sqrt{N}}$ and $\frac{\log^2 N}{N\log\log N}$ are decreasing for $\log N > 4.5$, and by JS Lemma 3.1 $|A_N| > N/\log N$.)
- `li_ratio_ub(x_lo_iv, log_x_lo)` (lines 183–189) bounds $\mathrm{li}(N)/|A_N|$ for $N \ge x_{\mathrm{lo}} \ge 4 \cdot 10^{18}$ via $|A_N| \ge \mathrm{li}(N) - \frac{\sqrt{N}\log N}{8\pi} - \omega_{\mathrm{ub}}(N)$ and $\mathrm{li}(N) > \frac{N}{\log N}$:
  $$\frac{\mathrm{li}(N)}{|A_N|} \le \left(1 - \frac{\sqrt{x_{\mathrm{lo}}}\log^2 x_{\mathrm{lo}} / (8\pi) + \omega_{\mathrm{ub}}(x_{\mathrm{lo}})\log x_{\mathrm{lo}}}{x_{\mathrm{lo}}}\right)^{-1}.$$

---

## 2. Exact Derivation of $J_{\mathrm{odd}}(\xi)$, $\tilde{H}$, $C_{f_0}$, $\alpha_0$, and $H_{1/4}$

### 2.1 Definitions and Interval Values in `constants.py` and `selberg_weights.py`
In `constants.py` (lines 94–151) and `selberg_weights.py` (lines 18–66):
- **Twin-prime constant** $C_2 := \prod_{p > 2} \left(1 - \frac{1}{(p-1)^2}\right) \in [0.660161530508, 0.660161860589]$ (`C2_TWIN`).
  - `constants.py:94–100` computes the finite product over $3 \le p \le 10^6$ and multiplies by $[1 - \frac{1}{2 \cdot 10^6}, 1]$, since $\sum_{p > 10^6} \frac{1}{(p-1)^2} \le \sum_{m \ge 5\cdot 10^5 + 1} \frac{1}{(2m)^2} < \frac{1}{2\cdot 10^6}$.
- **$U_{\mathrm{const}}$ and $H_0$**:
  $$U_{\mathrm{const}} := 2 C_2 \in [1.320323061017, 1.320323721179], \qquad H_0 := \frac{2}{U_{\mathrm{const}}} = \frac{1}{C_2} = \prod_{p > 2} \frac{(p-1)^2}{p(p-2)} \in [1.514780025472, 1.514780782862].$$
  *(Note convention difference: JS defines $U_N = 2 e^{-\gamma} C_2 \prod_{p>2, p \mid N}\frac{p-1}{p-2}$, whereas `constants.py` omits $e^{-\gamma}$ from `U_CONST`, so $V_{\mathrm{full}}(z) \approx U_{\mathrm{const}} e^{-\gamma} / \ln z$.)*
- **$\alpha_0$**:
  $$\alpha_0 := \frac{\gamma + \ln 2}{2} \in [0.635181422730, 0.635181422731].$$
- **$C_{f_0}$**: `C_F0 = 0.78`.
- **$H_{1/4}$** (`H_SIGMA`):
  $$H_{1/4} := \prod_{p > 2} \left(1 + \frac{2 p^{1/4} + p^{1/2}}{p(p-2)}\right) \in [5.360998310866, 5.360998310867].$$
- **$C_J$** (`C_J_CONST`):
  $$C_J := (\alpha_0 + C_{f_0})\, H_{1/4} \in [7.586785216829, 7.586785216830].$$
- **$\tilde{H}$** (`H_TILDE`):
  $$\tilde{H} := \prod_{p > 2} \left(1 + \frac{1}{p(p-1)}\right) \in [1.295731517927, 1.295731517928].$$
- **$J_{\mathrm{odd}}(\xi)$** (`selberg_weights.py:19`):
  $$J_{\mathrm{odd}}(\xi) := \sum_{\substack{d \le \xi \\ 2 \nmid d}} \frac{\mu^2(d)}{\prod_{p \mid d}(p-2)}.$$

### 2.2 Odd Harmonic Function $f_0(x)$ and Verification of $C_{f_0} = 0.78$
Define for $x \ge 1$:
$$f_0(x) := \sum_{\substack{n \le x \\ 2 \nmid n}} \frac{1}{n} = \frac{1}{2}\ln x + \alpha_0 + R_0(x), \qquad \alpha_0 = \frac{\gamma + \ln 2}{2}.$$
**Claim**: $|R_0(x)| \le \dfrac{C_{f_0}}{x}$ for all real $x \ge 1$, with $C_{f_0} = 0.78$ (in fact $\sup_{x \ge 1} x|R_0(x)| = 3(\ln 3 / 2 + \alpha_0 - 1) \approx 0.553463 < 0.78$).

**Rigorous proof**:
For integers $m \ge 1$, $S_m := \sum_{k=1}^m \frac{1}{2k-1} = H_{2m} - \frac{1}{2} H_m$. Using the standard Euler–Maclaurin bound for harmonic numbers $H_N = \ln N + \gamma + \frac{1}{2N} - \theta_N \frac{1}{12N^2}$ with $0 < \theta_N < 1$ ($N \ge 1$), the $\frac{1}{4m}$ terms cancel identically:
$$S_m - \left(\frac{1}{2}\ln(2m) + \alpha_0\right) = \left(H_{2m} - \ln(2m) - \gamma\right) - \frac{1}{2}\left(H_m - \ln m - \gamma\right) \in \left(-\frac{1}{48 m^2},\ \frac{1}{24 m^2}\right).$$
For any real $x \ge 1$, let $m = \lfloor (x+1)/2 \rfloor \ge 1$, so $2m - 1 \le x < 2m + 1$ and $f_0(x) = S_m$:
- **Case $m = 1$ ($1 \le x < 3$)**: $f_0(x) = 1$, and $x(1 - \frac{1}{2}\ln x - \alpha_0)$ is decreasing on $[e^{1 - 2\alpha_0}, 3) \approx [0.763, 3)$, taking values from $1 - \alpha_0 \approx 0.3648$ at $x=1$ down to $3(1 - \frac{1}{2}\ln 3 - \alpha_0) \approx -0.5535$ as $x \to 3^-$. Hence $x|R_0(x)| < 0.56 < 0.78$.
- **Case $m \ge 2$**: Write $R_0(x) = \left(S_m - \frac{1}{2}\ln(2m) - \alpha_0\right) + \frac{1}{2}\ln\frac{2m}{x}$.
  - On $[2m-1, 2m]$: $0 \le \frac{1}{2}\ln\frac{2m}{x} \le \frac{1}{2}\ln\frac{2m}{2m-1} \le \frac{1}{2(2m-1)}$, so $x|R_0(x)| \le 2m\left(\frac{1}{24m^2} + \frac{1}{2(2m-1)}\right) = \frac{1}{12m} + \frac{m}{2m-1} \le \frac{1}{24} + \frac{2}{3} = \frac{17}{24} \approx 0.7083 < 0.78$.
  - On $[2m, 2m+1)$: $0 \ge \frac{1}{2}\ln\frac{2m}{x} > \frac{1}{2}\ln\frac{2m}{2m+1} \ge -\frac{1}{4m}$, so $x|R_0(x)| \le (2m+1)\left(\frac{1}{24m^2} + \frac{1}{4m}\right) \le \frac{5}{96} + \frac{5}{8} = \frac{65}{96} \approx 0.6771 < 0.78$.

*(Note: Furthermore, for all $x \ge 1$, $f_0(x) \le \frac{1}{2}\ln x + 1$, since $1 + \sum_{k=2}^m \frac{1}{2k-1} \le 1 + \frac{1}{2}\int_1^{2m-1}\frac{dt}{t} = 1 + \frac{1}{2}\ln(2m-1) \le 1 + \frac{1}{2}\ln x$.)*

### 2.3 Derivation of $J_{\mathrm{odd}}(\xi) = H_0 \left(\frac{1}{2}\ln\xi + \alpha_0\right) + O^*(C_J\, \xi^{-1/4})$
Let $g(d) := \mathbf{1}_{2 \nmid d} \frac{\mu^2(d)}{\prod_{p \mid d}(p-2)}$ and $f_{\mathrm{odd}}(n) := \mathbf{1}_{2 \nmid n} \frac{1}{n}$. Their Dirichlet series are
$$G(s) = \sum_{d=1}^{\infty} \frac{g(d)}{d^s} = \prod_{p > 2} \left(1 + \frac{1}{(p-2)p^s}\right), \qquad F_{\mathrm{odd}}(s) = \sum_{n=1}^{\infty} \frac{f_{\mathrm{odd}}(n)}{n^s} = \prod_{p > 2} \left(1 - \frac{1}{p^{s+1}}\right)^{-1}.$$
Define the convolution factor $h$ by $G(s) = F_{\mathrm{odd}}(s)\, H(s)$ (i.e., $g = f_{\mathrm{odd}} * h$):
$$H(s) = \prod_{p > 2} \left(1 - \frac{1}{p^{s+1}}\right)\left(1 + \frac{1}{(p-2)p^s}\right) = \prod_{p > 2} \left(1 + \frac{2}{p(p-2)p^s} - \frac{1}{p(p-2)p^{2s}}\right).$$
Thus $h$ is multiplicative, supported on odd cube-free integers, with prime-power values for $p > 2$:
$$h(1) = 1, \qquad h(p) = \frac{2}{p(p-2)}, \qquad h(p^2) = -\frac{1}{p(p-2)}, \qquad h(p^k) = 0 \;\;(k \ge 3).$$
At $s = 0$:
- $H(0) = \sum_{\substack{k \ge 1 \\ 2 \nmid k}} h(k) = \prod_{p > 2} \left(1 + \frac{1}{p(p-2)}\right) = \prod_{p > 2} \frac{(p-1)^2}{p(p-2)} = H_0$.
- Moreover, $\frac{H'(0)}{H(0)} = \sum_{p > 2} \frac{-\frac{2\ln p}{p(p-2)} + \frac{2\ln p}{p(p-2)}}{1 + \frac{1}{p(p-2)}} = 0$, so **identically**:
  $$\sum_{\substack{k=1 \\ 2 \nmid k}}^{\infty} h(k) \ln k = -H'(0) = 0.$$
  *(Equivalently, $h(p)\ln p + h(p^2)\ln(p^2) = 0$ on every Euler factor.)*

Writing $J_{\mathrm{odd}}(\xi) = \sum_{\substack{k \le \xi \\ 2 \nmid k}} h(k) f_0(\xi/k)$ and substituting $f_0(\xi/k) = \frac{1}{2}\ln\xi - \frac{1}{2}\ln k + \alpha_0 + R_0(\xi/k)$:
$$J_{\mathrm{odd}}(\xi) - H_0\left(\frac{1}{2}\ln\xi + \alpha_0\right) = \sum_{\substack{k \le \xi \\ 2 \nmid k}} h(k) R_0\!\left(\frac{\xi}{k}\right) - \sum_{\substack{k > \xi \\ 2 \nmid k}} h(k) \left(\frac{1}{2}\ln\frac{\xi}{k} + \alpha_0\right).$$
Now bound both sums via $H_{1/4} = \sum_{\substack{k \ge 1 \\ 2 \nmid k}} |h(k)| k^{1/4} = \prod_{p > 2} \left(1 + \frac{2p^{1/4} + p^{1/2}}{p(p-2)}\right)$:
1. **First sum ($1 \le k \le \xi$, so $\xi/k \ge 1$)**: By Section 2.2, $|R_0(\xi/k)| \le \frac{C_{f_0}}{\xi/k} \le C_{f_0}\left(\frac{k}{\xi}\right)^{1/4}$, so
   $$\left|\sum_{\substack{k \le \xi \\ 2 \nmid k}} h(k) R_0\!\left(\frac{\xi}{k}\right)\right| \le C_{f_0}\,\xi^{-1/4} \sum_{\substack{k \le \xi \\ 2 \nmid k}} |h(k)| k^{1/4} \le C_{f_0}\, H_{1/4}\, \xi^{-1/4}.$$
2. **Tail sum ($k > \xi$, let $u = k/\xi > 1$)**: Maximize $\varphi(u) := u^{-1/4}\left|\alpha_0 - \frac{1}{2}\ln u\right|$ over $u > 1$:
   - At $u = 1$: $\varphi(1) = \alpha_0$.
   - For $u > e^{2\alpha_0}$, $\frac{d}{du}\left[u^{-1/4}(\frac{1}{2}\ln u - \alpha_0)\right] = \frac{u^{-3/4}}{8}(4 - \ln u + 2\alpha_0)$, which vanishes at $\ln u = 4 + 2\alpha_0$, giving the unique interior stationary value
     $$\varphi(e^{4 + 2\alpha_0}) = \frac{2}{\exp(1 + \frac{1}{2}\alpha_0)} \approx 0.535613 < \alpha_0 \approx 0.635181.$$
     *(Verified explicitly by `crit_val` assertion in `constants.py:130–131`!)*
   - Hence $\left|\frac{1}{2}\ln\frac{\xi}{k} + \alpha_0\right| \le \alpha_0 \left(\frac{k}{\xi}\right)^{1/4}$ for all $k > \xi$, so
     $$\left|\sum_{\substack{k > \xi \\ 2 \nmid k}} h(k) \left(\frac{1}{2}\ln\frac{\xi}{k} + \alpha_0\right)\right| \le \alpha_0\, \xi^{-1/4} \sum_{\substack{k > \xi \\ 2 \nmid k}} |h(k)| k^{1/4} \le \alpha_0\, H_{1/4}\, \xi^{-1/4}.$$

Adding the two bounds yields:
$$\left|J_{\mathrm{odd}}(\xi) - H_0\left(\frac{1}{2}\ln\xi + \alpha_0\right)\right| \le (\alpha_0 + C_{f_0}) H_{1/4}\, \xi^{-1/4} = C_J\, \xi^{-1/4}.$$
*(Remark: in fact the split $\sum_{k \le \xi} + \sum_{k > \xi}$ even gives $\max(\alpha_0, C_{f_0}) H_{1/4} \xi^{-1/4}$, while `constants.py:132` uses the conservative sum $(\alpha_0 + C_{f_0}) H_{1/4}$.)*

**Tail bound for $H_{1/4}$ in `constants.py:114–128`**:
For $p > h_{\mathrm{cut}} = 100{,}000$,
$$\frac{2 p^{1/4} + p^{1/2}}{p(p-2)} = \frac{1}{p^{3/2}} \cdot \frac{1 + 2 p^{-1/4}}{1 - 2/p} \le \frac{c_{\mathrm{tail}}}{p^{3/2}}, \qquad c_{\mathrm{tail}} := \frac{1 + 2 h_{\mathrm{cut}}^{-1/4}}{1 - 2/h_{\mathrm{cut}}}.$$
Summing over odd primes $p \ge h_{\mathrm{cut}} + 1$ satisfies $\sum_{p > h_{\mathrm{cut}}} p^{-3/2} \le \frac{1}{2}\int_{h_{\mathrm{cut}}-1}^{\infty} t^{-3/2}\,dt = (h_{\mathrm{cut}} - 1)^{-1/2}$, and $\prod(1 + a_p) \le \exp(\sum a_p)$ yields `h_sigma = prod_h * exp(c_tail / sqrt(h_cut - 1))`.

### 2.4 Role of $\tilde{H}$ (`H_TILDE`) in $\sum_{d \le X,\ 2 \nmid d} \mu^2(d)/\varphi(d)$
Compare the Dirichlet series of $c(d) := \mathbf{1}_{2\nmid d}\frac{\mu^2(d)}{\varphi(d)}$ with $F_{\mathrm{odd}}(s)$:
$$\sum_{\substack{d=1 \\ 2\nmid d}}^{\infty} \frac{\mu^2(d)}{\varphi(d) d^s} = \prod_{p > 2} \left(1 + \frac{1}{(p-1)p^s}\right), \qquad F_{\mathrm{odd}}(s)\prod_{p > 2}\left(1 + \frac{1}{p(p-1)p^s}\right) = \prod_{p > 2}\left(1 + \frac{1}{p \cdot p^s} + \frac{1}{p^2 p^{2s}} + \dots\right)\left(1 + \frac{1}{p(p-1)p^s}\right).$$
Comparing coefficients of $p^{-ks}$ for each odd prime $p$: for $k=0$ both equal $1$; for $k=1$ both equal $\frac{1}{p} + \frac{1}{p(p-1)} = \frac{1}{p-1}$; for $k \ge 2$ the left side is $0$ while the right side is $\ge 0$. Thus pointwise $c(d) \le (f_{\mathrm{odd}} * b_+)(d)$, where $b_+(k) = \mathbf{1}_{2\nmid k}\frac{\mu^2(k)}{\prod_{p\mid k} p(p-1)} \ge 0$ and $\sum_{2\nmid k} b_+(k) = \tilde{H}$. Hence for all $X \ge 1$:
$$\sum_{\substack{d \le X \\ 2 \nmid d}} \frac{\mu^2(d)}{\varphi(d)} \le \sum_{\substack{k \le X \\ 2 \nmid k}} b_+(k)\, f_0\!\left(\frac{X}{k}\right) \le \tilde{H} \cdot \left(\frac{1}{2}\ln X + \alpha_0 + \frac{C_{f_0}}{X}\right).$$
*(Used in `regime_slabs.py:510–511` with $X = \xi_q^2$ and `regime_asymptotic.py:123–124` with $X = \sqrt{N}$ via $\sum_{g a \le \xi,\ g b \le \xi,\ 2 \nmid gab} \frac{\mu^2(gab)}{\varphi(g)\varphi(a)\varphi(b)} \le \big(\sum_{d \le \xi, 2 \nmid d} \frac{\mu^2(d)}{\varphi(d)}\big)^3 \le (\tilde{H} f_0)^3$.)*

**Tail bound for $\tilde{H}$ in `constants.py:123,133`**:
For $p > P_{\mathrm{cut}} = 10^6$, $\sum_{p > P_{\mathrm{cut}}} \frac{1}{p(p-1)} \le \frac{1}{2} \sum_{m \ge P_{\mathrm{cut}}/2} \frac{1}{2m(2m-1)} \le \frac{1}{2(P_{\mathrm{cut}} - 1)}$, so $\prod_{p > P_{\mathrm{cut}}} (1 + \frac{1}{p(p-1)}) \le \exp(\frac{1}{2(P_{\mathrm{cut}}-1)})$.

### 2.5 Pre-Sieve-Free Two-Prime Inclusion-Exclusion & Monotonicity (`selberg_weights.py`)
For $1 \le \xi < z^3$, an odd squarefree $d \le \xi$ has at most $2$ prime factors $\ge z$, yielding the exact inclusion-exclusion identity:
$$J_{\mathrm{full}}(z, \xi) = J_{\mathrm{odd}}(\xi) - \sum_{z \le p_1 \le \xi} \frac{1}{p_1 - 2} J_{\mathrm{odd}}\!\left(\frac{\xi}{p_1}\right) + \sum_{\substack{z \le p_1 < p_2 \\ p_1 p_2 \le \xi}} \frac{1}{(p_1 - 2)(p_2 - 2)} J_{\mathrm{odd}}\!\left(\frac{\xi}{p_1 p_2}\right),$$
implemented on geometric slices in `j_full_lb_z3` (`selberg_weights.py:69–120`) and in asymptotic scale-invariant form in `vj_monotone_lb_iv` (`selberg_weights.py:123–195`).
Moreover, for any even $N$, omitting any prime $p_0 \mid N$ ($3 \le p_0 < z$) from $P$ satisfies
$$V(P) J(P, \xi) = \frac{p_0-2}{p_0-1} V(P') \left(J(P', \xi) + \frac{1}{p_0-2} J(P', \xi/p_0)\right) \le V(P') J(P', \xi),$$
so $V_N(z) J_N(z, \xi) \ge V_{\mathrm{full}}(z) J_{\mathrm{full}}(z, \xi)$ uniformly for all even $N$.

---

## 3. Odd Squarefree Counting & Selberg Collision Sum

### 3.1 Odd Squarefree Counting: $\sum_{\substack{d \le X \\ 2 \nmid d}} \mu^2(d) \le \frac{4}{\pi^2} X + \sqrt{X}$ ($X \ge 1$)
**Proof**:
Using $\mu^2(d) = \sum_{k^2 \mid d} \mu(k)$, notice $2 \nmid d \iff 2 \nmid k$ and $2 \nmid (d/k^2)$. Let $R := \lfloor (\sqrt{X} + 1)/2 \rfloor \ge 1$ be the number of odd integers $k \le \sqrt{X}$ (so $2R - 1 \le \sqrt{X} < 2R + 1$). Writing the number of odd integers $\le Y$ as $\lfloor \frac{Y+1}{2} \rfloor = \frac{Y}{2} + \eta(Y)$ with $|\eta(Y)| \le \frac{1}{2}$:
$$\sum_{\substack{d \le X \\ 2 \nmid d}} \mu^2(d) = \sum_{\substack{k \le \sqrt{X} \\ 2 \nmid k}} \mu(k) \left\lfloor \frac{X/k^2 + 1}{2} \right\rfloor = \frac{X}{2}\sum_{\substack{k=1 \\ 2 \nmid k}}^{\infty} \frac{\mu(k)}{k^2} - \frac{X}{2}\sum_{\substack{k > \sqrt{X} \\ 2 \nmid k}} \frac{\mu(k)}{k^2} + \sum_{\substack{k \le \sqrt{X} \\ 2 \nmid k}} \mu(k)\,\eta\!\left(\frac{X}{k^2}\right).$$
1. Main term: $\sum_{\substack{k=1 \\ 2 \nmid k}}^{\infty} \frac{\mu(k)}{k^2} = \frac{1}{\zeta(2)(1 - 2^{-2})} = \frac{1}{(\pi^2/6)(3/4)} = \frac{8}{\pi^2}$, so $\frac{X}{2} \cdot \frac{8}{\pi^2} = \frac{4}{\pi^2} X$.
2. Tail sum: Every odd $k > \sqrt{X}$ has $k = 2r + 1$ with $r \ge R$. Since $\frac{1}{(2r+1)^2} < \frac{1}{4r(r+1)} = \frac{1}{2}(\frac{1}{2r} - \frac{1}{2r+2})$, telescoping gives
   $$\sum_{r=R}^{\infty} \frac{1}{(2r+1)^2} < \frac{1}{4R}.$$
3. Rounding sum: $\left|\sum_{\substack{k \le \sqrt{X} \\ 2 \nmid k}} \mu(k)\eta(X/k^2)\right| \le \frac{R}{2}$.

Hence the total error is at most $\frac{X}{8R} + \frac{R}{2}$.
- If $R = 1$ ($1 \le X < 9$): $\frac{X}{8} + \frac{1}{2} \le \sqrt{X}$ holds because $\sqrt{X} - \frac{X}{8} - \frac{1}{2}$ is concave in $\sqrt{X}$ and positive at $\sqrt{X} = 1$ ($0.375$) and $\sqrt{X} = 3$ ($1.375$).
- If $R \ge 2$: since $X < (2R+1)^2$ and $\sqrt{X} \ge 2R - 1$,
  $$\frac{X}{8R} + \frac{R}{2} < \frac{(2R+1)^2}{8R} + \frac{R}{2} = R + \frac{1}{2} + \frac{1}{8R} \le 2R - 1 \le \sqrt{X},$$
  since $R \ge \frac{3}{2} + \frac{1}{8R}$ holds for all $R \ge 2$. $\square$

### 3.2 Selberg Collision Sum: $\sum_{\substack{L \le X \\ 2 \nmid L}} \mu^2(L) 3^{\omega(L)} \le \frac{1}{16} X (\ln X + 6)^2$ ($X \ge 1$)
For squarefree $L$, $3^{\omega(L)} = \tau_3(L) = \sum_{a b c = L} 1$, so it suffices to prove the stronger bound for $\tau_k^{\mathrm{odd}}(X) := \sum_{\substack{n_1 \cdots n_k \le X \\ 2 \nmid n_1 \cdots n_k}} 1$ at $k = 3$ (verified numerically on $[1, 5000]$ to have ratio $\le 0.5978$ for $\tau_3^{\mathrm{odd}}$ and $\le 4/9$ for $\mu^2 \cdot 3^\omega$):

**Proof by elementary induction ($k = 1, 2, 3$)** for all $X \ge 1$:
1. **$k = 1$**: $\tau_1^{\mathrm{odd}}(X) = \left\lfloor \frac{X+1}{2} \right\rfloor \le \frac{X+1}{2}$.
2. **$k = 2$**: Using $f_0(X) = \sum_{\substack{a \le X \\ 2 \nmid a}} \frac{1}{a} \le \frac{1}{2}\ln X + 1$ (Section 2.2),
   $$\tau_2^{\mathrm{odd}}(X) = \sum_{\substack{a \le X \\ 2 \nmid a}} \tau_1^{\mathrm{odd}}\!\left(\frac{X}{a}\right) \le \frac{X}{2} f_0(X) + \frac{1}{2}\tau_1^{\mathrm{odd}}(X) \le \frac{X}{4}\ln X + \frac{3}{4}X + \frac{1}{4} \le \frac{1}{4} X (\ln X + 4),$$
   since $\frac{3}{4}X + \frac{1}{4} \le X$ for all $X \ge 1$.
3. **$k = 3$**: Applying the $k = 2$ bound at $u = X/a \ge 1$:
   $$\tau_3^{\mathrm{odd}}(X) = \sum_{\substack{a \le X \\ 2 \nmid a}} \tau_2^{\mathrm{odd}}\!\left(\frac{X}{a}\right) \le \frac{X}{4}\sum_{\substack{a \le X \\ 2 \nmid a}} \frac{\ln(X/a) + 4}{a}.$$
   Since $t \mapsto \frac{\ln(X/t)}{t}$ is positive and strictly decreasing on $[1, X]$, separating $a = 1$ and bounding odd $a \ge 3$ by $\frac{1}{2}\int_{a-2}^a$ gives
   $$\sum_{\substack{a \le X \\ 2 \nmid a}} \frac{\ln(X/a)}{a} \le \ln X + \frac{1}{2}\int_1^X \frac{\ln(X/t)}{t}\,dt = \ln X + \frac{1}{4}(\ln X)^2.$$
   Adding $4 f_0(X) \le 2\ln X + 4$ yields
   $$\sum_{\substack{a \le X \\ 2 \nmid a}} \frac{\ln(X/a) + 4}{a} \le \frac{1}{4}(\ln X)^2 + 3\ln X + 4 = \frac{1}{4}\!\left((\ln X)^2 + 12\ln X + 16\right) \le \frac{1}{4}(\ln X + 6)^2.$$
   Multiplying by $\frac{X}{4}$ gives $\sum_{\substack{L \le X \\ 2 \nmid L}} \mu^2(L) 3^{\omega(L)} \le \tau_3^{\mathrm{odd}}(X) \le \frac{1}{16} X (\ln X + 6)^2$. $\square$

*(Cross-check: used in `regime_slabs.py:508–509` with $X = \xi_q^2$, so $\ln X + 6 = 2\ln\xi_q + 6$, and in `regime_asymptotic.py:116–120` with $\ln X \le \frac{1}{2}\ln N$.)*

---

## 4. Two-Variable Mertens Closure: `eps_sup_two_var` & `eps_large_u_two_var`

In explicit linear-sieve remainder theorems (BJS `arXiv:2207.09452v4`, Theorem 6 / Table 1; cf. JS Lemma 3.3), one requires an **all-pairs** bound $\varepsilon > 0$ such that for all $p_* \le w < z_1 < \infty$:
$$\prod_{w \le p < z_1} \left(1 - \frac{1}{p-1}\right)^{-1} \le (1 + \varepsilon) \frac{\ln z_1}{\ln w}.$$

### 4.1 `eps_sup_two_var(pstar)` (`primes_and_mertens.py:105–120, 192–223`)
Requires $p_* \ge 29$ (`pstar in PREFIX_TWIN`, precomputed up to $1000$).
1. **Twin-prime factor**:
   $$\prod_{w \le p < z_1} \frac{(p-1)^2}{p(p-2)} \le \prod_{p \ge p_*} \frac{(p-1)^2}{p(p-2)} = \frac{1/C_2}{\prod_{3 \le p < p_*} \frac{(p-1)^2}{p(p-2)}} = \frac{\mathrm{TWIN\_RECIP}}{\mathrm{PREFIX\_TWIN}[p_*]}.$$
2. **Quadratic log-tail bound**: For $x = 1/p \le 1/p_* =: x_*$, the function $\frac{-\ln(1-x)-x}{x^2} = \sum_{k=0}^\infty \frac{x^k}{k+2}$ is strictly increasing on $(0, 1)$, so
   $$\sum_{w \le p < z_1} \left(-\ln\!\left(1 - \frac{1}{p}\right) - \frac{1}{p}\right) \le c_{p_*} \sum_{p \ge p_*} \frac{1}{p^2}, \qquad c_{p_*} := \frac{-\ln(1 - x_*) - x_*}{x_*^2}.$$
3. **Order-respecting causal Mertens excursion** on $\Delta(w, z_1) := E_M(z_1^-) - E_M(w^-)$, where $E_M(x^-) := \sum_{p < x} \frac{1}{p} - \ln\ln x - M_0$:
   - Only pairs with at least one prime $p \in [w, z_1)$ can give $\Delta(w, z_1) > 0$.
   - On each interval $(p_k, p_{k+1}]$, $E_M(z_1^-)$ is strictly decreasing in $z_1$ and bounded above by $E_M(p_k^+) = \sum_{q \le p_k} \frac{1}{q} - \ln\ln p_k - M_0$ (`after_hi` in `_MERTENS_RECS`).
   - On $[p_j, p_{j+1})$, $E_M(w^-)$ is bounded below by $E_M(p_{j+1}^-) = \sum_{q < p_{j+1}} \frac{1}{q} - \ln\ln p_{j+1} - M_0$ (`before_lo` in `_MERTENS_RECS`).
   - A **single forward pass** over primes $p \in [p_*, 25{,}000]$ updates `min_lo_so_far = min(min_lo_so_far, before_lo(p))` **before** evaluating `after_hi(p) - min_lo_so_far`, so every `after_hi(p)` is paired strictly with `before_lo(q)` for $p_* \le q \le p$ (never illegally pairing a post-prime $z_1$ with $w > z_1$).
   - For $z_1 > 25{,}000 > e^{10.1}$: by BJV22 Lemma 16 on $(e^{10.1}, 10^{12}]$ and JS Lemma 3.2 (3.4) on $(10^{12}, \infty)$,
     $$E_M(z_1^-) \le \max\!\left(\frac{2}{e^{5.05}\cdot 10.1},\ \frac{6.836\cdot 10^{-6}}{\ln(10^{12})}\right) = \frac{2}{e^{5.05}\cdot 10.1} = \text{\_MERTENS\_TAIL\_UP\_101}.$$
     The lower excursion across all $w \ge p_*$ (including $(p_{\max}, 25{,}000]$ and $w > 25{,}000$) is bounded below via JS Lemma 3.2 (3.2) by `min(min_lo_so_far, -2.964e-6 / ln(pstar))`, giving `tail_diff`.
4. Combining all factors:
   $$\varepsilon_{\mathrm{sup}}(p_*) = \frac{\mathrm{TWIN\_RECIP}}{\mathrm{PREFIX\_TWIN}[p_*]} \exp\!\left(\max_{\text{causal}}\Delta + c_{p_*}\sum_{p \ge p_*}\frac{1}{p^2}\right) - 1.$$
   **Certified interval values**:
   - $p_* = 29$: $\varepsilon_{\mathrm{sup}}(29) \in [0.062079770466, 0.062080301506]$
   - $p_* = 131$: $\varepsilon_{\mathrm{sup}}(131) \in [0.015121246229, 0.015121753790]$
   - $p_* = 251$: $\varepsilon_{\mathrm{sup}}(251) \in [0.010057852648, 0.010058357677]$ ($1/\varepsilon > 99$); for the `k3` asymptotic ray $[10^{600}, \infty)$, `primes_and_mertens.py:certify_closed_hstar_q0(Q0_100, 100)` instead certifies closed-interval $\varepsilon_* \le 0.0099009901 < 1/100$ over the 31-prime pre-sieve `Q0_100` in $[3, 227]$, paired with Lean-certified `C_2 ≤ 494` (Python cap `495`).

### 4.2 `eps_large_u_two_var(ln_u)` (`primes_and_mertens.py:225–237`)
Used in finite-terminating Buchstab error sums (`linear_sieve.py:305, 345`) for local cutoffs $u \le w < z_1 < \infty$ when $\ln u > 10.1$ (returning conservative $0.5$ if $\ln u.\mathrm{lo} \le 10.1$).
1. **Combined twin-prime and quadratic tail**: For $p \ge u > e^{10.1} \approx 24343$,
   $$\ln\frac{p-1}{p-2} - \frac{1}{p} = \frac{1}{p(p-1)} + \sum_{k=2}^\infty \frac{1}{k(p-1)^k} < \frac{2}{p(p-1)},$$
   and $\sum_{p \ge u} \frac{2}{p(p-1)} \le \sum_{n = \lceil u \rceil}^\infty \frac{2}{n(n-1)} = \frac{2}{\lceil u \rceil - 1} \le \frac{2}{u - 1} < \frac{2.0002}{u}$ (`tail_err = 2.0002 / exp(ln_u)`).
2. **Two-variable Mertens excursion for $u \le w < z_1$**:
   - Lower bound on $E_M(w^-)$: by JS Lemma 3.2 (3.2), $E_M(w^-) \ge -\frac{2.964 \cdot 10^{-6}}{\ln w} \ge -\frac{2.964 \cdot 10^{-6}}{\ln u}$.
   - Upper bound on $E_M(z_1^-)$:
     - If $u > 10^{12}$ (`ln_u.lo > LN_1E12.hi`), then $z_1 > 10^{12}$, so JS Lemma 3.2 (3.4) gives $E_M(z_1^-) \le \frac{6.836 \cdot 10^{-6}}{\ln u}$.
     - If $e^{10.1} < u \le 10^{12}$, then $z_1 \in (u, 10^{12}]$ gives $\le \frac{2}{\sqrt{u}\ln u}$ (BJV22 Lemma 16) while $z_1 > 10^{12}$ gives $\le \frac{6.836\cdot 10^{-6}}{\ln(10^{12})}$, so taking the maximum covers all $z_1 > w \ge u$.
3. Thus $\prod_{w \le p < z_1}\left(1 - \frac{1}{p-1}\right)^{-1} \le \exp(\mathrm{tail\_err} + \mathrm{mert})\frac{\ln z_1}{\ln w}$, yielding `exp(tail_err + mert) - 1`.
