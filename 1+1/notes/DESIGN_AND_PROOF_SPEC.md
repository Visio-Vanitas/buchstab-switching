# Design and Proof Specification: All-Range Explicit `1+1` Exceptional Set and Short-Interval Goldbach under GRH

**Target Theorems (under GRH + $E(4\cdot 10^{18}) = 0$)**:
- **Theorem 1A (All-Range Explicit `1+1` Exceptional Set)**: For all $X \ge 4$,
  $$E(X) := \#\{n \le X : 2 \mid n,\ n \ge 4,\ n \neq p_1 + p_2\} \le 12731 \sqrt{X} (\log X)^3 \qquad (c = 3,\ C = 12731).$$
- **Theorem 1B (All-Range Explicit Short-Interval `1+1`)**: For every $X \ge 4$, the interval $[X, X + H]$ with $H \ge 6281 (\log X)^2$ contains an even integer $N = p_1 + p_2$ ($c' = 2$, $C_1 = 6281$). *(For $X \ge 4\cdot 10^{18}$, Theorem 1B requires only RH for $\zeta(s)$.)*

All numerical constants below are certified without IEEE-754 floats by [`certify_exceptional_short.py`](./certify_exceptional_short.py) using directed outward-rounded `decimal.Decimal` (`prec = 80`, `FloatOperation` trap armed) and exact `fractions.Fraction` arithmetic.

---

## 1. Kernel Selection: Why Laplace/Abel Smoothing Beats Sharp Cutoff, Fejér, and Compact Polynomial Weights

To bound $\sum_{N} |R(N) - M(N)|^2$ on $[Y/2, Y]$ or $\sum_{N \in [X, X+H]} W(N) R(N)$, the exponential sum kernel must satisfy two simultaneous requirements:
1. **Exact convolution/Parseval compatibility in $N = n_1 + n_2$**: If prime weights $w(n_1)$ and $w(n_2)$ depend on $n_1, n_2$, their product $w(n_1) w(n_2)$ must factor cleanly (or admit a clean lower/upper comparison) as a function of $N = n_1 + n_2$ so that $\int_0^1 S(\alpha)^2 e(-N\alpha)\,d\alpha$ isolates $R(N)$.
2. **Rapid critical-line zero-sum convergence without minor-arc $\sup$-norm loss**:

| Kernel | $S(\alpha)$ Weight | $w(n_1)w(n_2)$ Factorization | Critical-Line Kernel | Minor-Arc $\sup\|S\|$ under GRH | Verdict |
|---|---|---|---|---|---|
| **Sharp cutoff** $n \le Y$ | $\Lambda(n)\mathbf{1}_{n \le Y}$ | Exact ($n_1, n_2 \le Y$) | $\frac{Y^s}{s}$ (divergent without truncation) | Vaughan + GRH gives $Y^{4/5}(\log Y)^4 \implies E(X) \ll X^{3/5}$ | Fails $X^{1/2}$ |
| **Linear / Quadratic** $(1-n/Y)$, $\frac{n}{Y}(1-\frac{n}{Y})$ | Compact on $[1, Y]$ | Does **not** factor purely in $N = n_1 + n_2$ | $\frac{Y^s}{s(s+1)}$ or $\frac{Y^s}{(s+1)(s+2)}$ | Requires 2D Mellin coupling or Dirichlet convolution | Clean for single $N$, awkward for $L^2$ Parseval |
| **Fejér / Cesàro** | $\Lambda(n)(1 - n/Y)_+$ | Convolution $\neq f(N)$ | $\frac{Y^s}{s(s+1)}$ | Similar to Laplace, loses factor in $N = n_1+n_2$ weight | Suboptimal vs Laplace |
| **Laplace / Abel** $e^{-n/Y}$ | $\Lambda(n) e^{-n/Y}$ | **Exact:** $e^{-n_1/Y} e^{-n_2/Y} = e^{-N/Y}$ | $\Gamma(s) z^{-s}$ ($z = \frac{1}{Y} - 2\pi i \beta$) | **Uniform $O(Y^{3/4} \log Y)$** via Euler reflection $|\Gamma(\frac{1}{2}+i\gamma)| = \sqrt{\pi/\cosh(\pi\gamma)}$ | **Optimal** |

**Key algebraic identity of Laplace smoothing**: For every integer $N \ge 1$ and $S(\alpha) := \sum_{n \ge 2} \Lambda(n) e^{-n/Y} e(n\alpha)$,
$$R_{\mathrm{Lap}}(N) := \int_{-1/2}^{1/2} S(\alpha)^2 e(-N\alpha)\,d\alpha = e^{-N/Y} \sum_{n_1 + n_2 = N} \Lambda(n_1)\Lambda(n_2) = e^{-N/Y} R_\Lambda(N).$$
Because $e^{-n/Y}$ is multiplicative under addition, $S(\alpha)^2$ recovers the **exact** unweighted Goldbach count $R_\Lambda(N)$ multiplied by $e^{-N/Y}$ (which is bounded below by $e^{-1}$ on $N \le Y$), while $\Gamma(s) z^{-s}$ decays exponentially in $|\operatorname{Im}(s)|$ along $\operatorname{Re}(s) = \frac{1}{2}$ at rate $\exp(-|\gamma| / (|z|Y))$!

---

## 2. Shared Analytic Engine: Explicit Formula, Poisson Zero Density, and Parseval

### 2.1 Elementary Arithmetic & Analytic Constants
Let $Y \ge 4\cdot 10^{18}$ ($L := \log Y \ge 42.83$). All constants are certified in `AnalyticConstants`:
1. **Twin-prime constant lower bound** (matching [`UpperErrors.lean`](./LEAN4_INTERFACE.md)):
   $$\Pi_2 := \prod_{p > 2} \left(1 - \frac{1}{(p-1)^2}\right) \ge 0.6592836 \implies \mathfrak{S}(N) \ge 2\Pi_2 \ge 1.3185672 \quad (\text{even } N \ge 4).$$
2. **Chebyshev & prime-power bounds** (Rosser–Schoenfeld 1962, Thms. 12–13, valid for all $t > 0$):
   $$\psi(t) \le \alpha_\psi t \quad (\alpha_\psi = 1.03883), \qquad \psi(t) - \vartheta(t) \le \alpha_{\mathrm{pp}} \sqrt{t} \quad (\alpha_{\mathrm{pp}} = 1.4262).$$
3. **Parseval prime-square bound**: Writing $\log n = \int_1^n \frac{du}{u}$ and applying Abel summation to $\sum_{n \ge u} \Lambda(n) e^{-2n/Y} \le \alpha_\psi (u + \frac{Y}{2}) e^{-2u/Y}$:
   $$\int_0^1 |S(\alpha)|^2\,d\alpha = \sum_{n \ge 2} \Lambda(n)^2 e^{-2n/Y} \le \frac{\alpha_\psi}{2} Y \left(\log Y + C_{\mathrm{pars}}\right), \qquad C_{\mathrm{pars}} := 1 - \log 2 + e^{-1} \le 0.67474.$$
4. **Totient sum bounds**:
   - $\frac{q}{\varphi(q)} = \sum_{d \mid q} \frac{\mu^2(d)}{\varphi(d)} \implies \sum_{q \le Q_0} \frac{q}{\varphi(q)} \le C_{q/\varphi} Q_0$ and $\sum_{q \le Q_0} \frac{1}{\varphi(q)} \le C_{q/\varphi}(\log Q_0 + 1)$, where $C_{q/\varphi} := \prod_p \left(1 + \frac{1}{p(p-1)}\right) \le 1.94913$.
   - $\varphi(q) \ge \sqrt{q/2}$ for all $q \ge 1$ (since $p-1 \ge \sqrt{p}$ for all odd primes $p \ge 3$, and $\varphi(2^k) = 2^{k-1} \ge 2^{(k-1)/2}$).
   - $\frac{\mu^2(r)}{\varphi(r)^2} = \frac{\mu^2(r)}{r^2} \sum_{k \mid r} \prod_{p \mid k} \frac{2p-1}{(p-1)^2} \implies \sum_{r > R} \frac{\mu^2(r)}{\varphi(r)^2} \le \frac{2 K_2}{R}$ for all $R > 0$, where $K_2 := \prod_p \left(1 + \frac{2p-1}{p(p-1)^2}\right) \le 4.46901$.
   - Since $541^8 < 271 \cdot 270^8$, $\frac{2p-1}{p-1} \le p^{1/8}$ for all $p \ge 271$, giving $\prod_{p \mid N} \frac{2p-1}{p-1} \le K_{1/8} N^{1/8}$ with $K_{1/8} \le 15655.23$.

### 2.2 Character Expansion & Gauss Sum Cauchy–Schwarz
For $\alpha = \frac{a}{q} + \beta$ with $\gcd(a, q) = 1$, set $z := \frac{1}{Y} - 2\pi i \beta$ ($\operatorname{Re}(z) > 0$) and $A := |z| Y = \sqrt{1 + (2\pi \beta Y)^2} \ge 1$. Expanding $e(an/q)$ in Dirichlet characters $\bmod\, q$ for $(n, q) = 1$, and replacing each $\chi \bmod q$ by its inducing primitive character $\chi^* \bmod q^*$ ($q^* \mid q$):
$$S\left(\frac{a}{q} + \beta\right) = \frac{1}{\varphi(q)} \sum_{\chi \bmod q} \tau(\bar\chi) S(\chi^*, z) + E_{\gcd}(a, q, z), \qquad S(\chi^*, z) := \sum_{n \ge 1} \Lambda(n) \chi^*(n) e^{-nz}.$$
Here:
- **Gauss-sum average**: Since $\sum_{\chi \bmod q} |\tau(\bar\chi)|^2 = \varphi(q)^2$, Cauchy–Schwarz gives $\frac{1}{\varphi(q)} \sum_{\chi \bmod q} |\tau(\bar\chi)| \le \sqrt{\varphi(q)} \le \sqrt{q}$, while for $\chi_0$ we have $\tau(\bar\chi_0) = \mu(q)$.
- **Prime-power / imprimitivity correction**: Each $p \mid q$ contributes at most $\sum_{k \ge 1} (\log p) e^{-p^k/Y} \le \log(Y \log Y) + 1$, so for $q \le 2 Y^{1/2}$:
  $$|E_{\gcd}(a, q, z)| \le 2\omega(q)(\log(Y\log Y) + 1) \le 2\left(\frac{\log(2 Y^{1/2})}{\log 2} + 1\right)(\log Y + \log\log Y + 1).$$

### 2.3 Mellin-Laplace Explicit Formula & Poisson Zero-Sum Envelope
By Mellin inversion $e^{-nz} = \frac{1}{2\pi i} \int_{(2)} \Gamma(s)(nz)^{-s}\,ds$, for every primitive $\chi^* \bmod q^*$:
$$S(\chi^*, z) = \delta_{q^*=1}\frac{1}{z} - \sum_{\rho_{\chi^*}} \Gamma(\rho) z^{-\rho} + R_{\mathrm{vert}}(\chi^*, z),$$
where shifting to $\operatorname{Re}(s) = \sigma_{\mathrm{v}}$ gives:
- **For Theorem 1A ($\sigma_{\mathrm{v}} = \frac{1}{4}$, all $q^* \ge 1$)**: No poles in $(\frac{1}{4}, \frac{1}{2})$. Using $|\Gamma(\frac{1}{4}+it)| \le \sqrt{2}\, \Gamma(\frac{1}{4}) e^{-\frac{\pi}{2}|t|} \le 4\sqrt{2}\, e^{-\frac{\pi}{2}|t|}$ (from $B(\frac{1}{4}+it, \frac{1}{4})$ and Young's inequality $t^{1/4} \le \frac{3}{4} + \frac{t}{4}$) and subtracting $\frac{L'(7/4+it, \chi^*)}{L(7/4+it, \chi^*)}$ yields:
  $$\left|\frac{L'(\frac{1}{4}+it, \chi^*)}{L(\frac{1}{4}+it, \chi^*)}\right| \le A_{\mathrm{vert}}(1/4) + 15\left(\log q^* + \log(4 + |t|) + C(q^*)\right), \qquad A_{\mathrm{vert}}(1/4) \le 12.239.$$
  Integrating against $|z^{-1/4-it}| \le |z|^{-1/4} e^{|t|(\pi/2 - 1/A)}$ bounds $|R_{\mathrm{vert}}(\chi^*, z)|$ by $O(|z|^{3/4} Y \log(q^* A))$.
- **For Theorem 1B ($\sigma_{\mathrm{v}} = -\frac{1}{2}$, $q^* = 1$ only)**: For $\zeta(s)$, $\zeta(0) = -\frac{1}{2} \neq 0$, so $s = 0$ is a **simple** pole with residue $-\frac{\zeta'(0)}{\zeta(0)} = -\log(2\pi)$ (no double pole). Using the functional equation of $\zeta(s)$ and $|\Gamma(-\frac{1}{2}+it)| = \frac{|\Gamma(1/2+it)|}{\sqrt{1/4+t^2}} \le \frac{\sqrt{2\pi} e^{-\frac{\pi}{2}|t|}}{\sqrt{1/4+t^2}}$ gives the **pointwise** bound for $|\alpha| \le \frac{1}{4}$:
  $$|R_{\mathrm{vert}}(1, z)| \le \log(2\pi) + \sqrt{\frac{2}{\pi}} |z|^{1/2} \Bigl(2(\log 5 + C_{-1/2}) + (\log(A+4) + C_{-1/2})\log A + \log(A+5) + C_{-1/2} + 1\Bigr) = O((\log X)^2).$$

**Critical-line zero sum via Poisson trace**: Under GRH, $\rho = \frac{1}{2} + i\gamma$. By Euler's reflection formula, $|\Gamma(\frac{1}{2} + i\gamma)| = \sqrt{\frac{\pi}{\cosh(\pi\gamma)}} \le \sqrt{2\pi} e^{-\frac{\pi}{2}|\gamma|}$. With $\theta = -\arg z = \arctan(2\pi \beta Y) \in (-\frac{\pi}{2}, \frac{\pi}{2})$ and $\frac{\pi}{2} - |\theta| \ge \sin(\frac{\pi}{2} - |\theta|) = \frac{1}{A}$:
- On the matching-sign half ($\operatorname{sgn}(\gamma) = -\operatorname{sgn}(\theta)$): $|\Gamma(\rho) z^{-\rho}| \le \sqrt{2\pi} |z|^{-1/2} e^{-|\gamma|/A}$.
- On the opposite-sign half ($\operatorname{sgn}(\gamma) = \operatorname{sgn}(\theta)$): $|\Gamma(\rho) z^{-\rho}| \le \sqrt{2\pi} |z|^{-1/2} e^{-\frac{\pi}{2}|\gamma|}$.

From [`DirichletPoissonZeroMass.long_poisson`](./LEAN4_INTERFACE.md) ($a = \frac{5}{4}$, $C(q^*) = 0.2$ for $q^* > 1$; and $C_\zeta \le 3.0300$ for $q^* = 1$ via $-\frac{\zeta'(7/4)}{\zeta(7/4)} \le 0.9555$ and Binet's digamma bound), integrating $\tau \in [-h, T+h]$ gives for all $T \ge 0$, $h \ge \frac{5}{4}$:
$$N^\pm_{\chi^*}(T) \le \frac{T + 2h}{4\arctan(4h/5)}\left(\log q^* + \log(T + h + 4) + C(q^*)\right).$$
Stieltjes integration by parts $\sum_{\gamma \ge 0} e^{-\gamma/A} = \int_0^\infty \frac{1}{A} e^{-T/A} N^+(T)\,dT$ with $T = A u$, $Au + h + 4 \le (A+h+4)(u+1)$, and $\int_0^\infty u e^{-u}\log(u+1)\,du = 1$, $\int_0^\infty e^{-u}\log(u+1)\,du \le 1$ yields:
$$\sum_{\gamma_{\text{same}}} |\Gamma(\rho) z^{-\rho}| \le \sqrt{2\pi} |z|^{-1/2} \frac{A + 2h}{4\arctan(4h/5)}\left(\log q^* + \log(A + h + 4) + C(q^*) + 1\right).$$
Choosing $h = \frac{5}{4}$ for $A \in [1, 100]$ and $h = 25$ for $A > 100$, and noting $q A \le (2+\pi)\sqrt{Y}$ on $\mathfrak{m}$ (and $\le (0.5+\pi)\sqrt{Y}$ on $\mathfrak{M}$) gives $\sup_{\mathfrak{m}} |S(\alpha)| \le K_{\mathfrak{m}} Y^{3/4} \log Y$ explicitly.

---

## 3. Proof Blueprint for Theorem 1A ($E(X) \le 12731 \sqrt{X} (\log X)^3$)

Fix $Y \ge 4\cdot 10^{18}$. Set $Q_0 := \lfloor \frac{1}{2} Y^{1/2} \rfloor$, $Q_D := 2 Y^{1/2}$, and Major Arcs
$$\mathfrak{M} := \bigsqcup_{q \le Q_0} \bigsqcup_{\substack{1 \le a \le q \\ (a,q)=1}} \left\{\alpha \in \mathbb{R}/\mathbb{Z} : \left|\alpha - \frac{a}{q}\right| \le \frac{1}{2 q Y^{1/2}}\right\}, \qquad \mathfrak{m} := (\mathbb{R}/\mathbb{Z}) \setminus \mathfrak{M}.$$
1. **Disjointness & Dirichlet minor arcs**: For distinct $a/q, a'/q'$ with $q, q' \le Q_0$, $\frac{1}{2qY^{1/2}} + \frac{1}{2q'Y^{1/2}} \le \frac{Q_0}{qq'Y^{1/2}} \le \frac{1}{2qq'} < \frac{1}{qq'}$. By Dirichlet's approximation theorem with $Q_D = 2 Y^{1/2}$, every $\alpha \in \mathfrak{m}$ admits $q \in (\frac{1}{2}Y^{1/2}, 2 Y^{1/2}]$ and $(a, q)=1$ with $|\alpha - a/q| \le \frac{1}{2qY^{1/2}}$.
2. **Major-arc approximant**: Define $M(\frac{a}{q}+\beta) := \frac{\mu(q)}{\varphi(q)} \frac{1}{1/Y - 2\pi i \beta}$ on $\mathfrak{M}(q, a)$ and $M(\alpha) := 0$ on $\mathfrak{m}$. Its squared Fourier coefficient $M^*_{\mathrm{Lap}}(N) := \int_{-1/2}^{1/2} M(\alpha)^2 e(-N\alpha)\,d\alpha$ satisfies for all even $N \in (Y/2, Y]$:
   $$M^*_{\mathrm{Lap}}(N) \ge e^{-N/Y} N \mathfrak{S}(N) - \frac{2 K_2 K_{1/8}}{e \cdot 0.4999\, Y^{3/8}} Y - \frac{K_2 K_{1/8} (\frac{1}{2}\log Y + 1)}{\pi^2 Y^{3/8}} Y \ge \left(e^{-1} \Pi_2 - \varepsilon_{\mathrm{tail}}\right) Y.$$
3. **Exceptional count on $(Y/2, Y]$**: If $N \in (Y/2, Y]$ is even and $N \neq p_1 + p_2$, then $R_\Lambda(N) \le 2(\log Y)\alpha_{\mathrm{pp}}\sqrt{Y}$, so $|R_{\mathrm{Lap}}(N) - M^*_{\mathrm{Lap}}(N)| \ge \gamma_0 Y$ with $\gamma_0 > 0.242$ for all $Y \ge 4\cdot 10^{18}$. By Parseval:
   $$\gamma_0^2 Y^2 \left(E(Y) - E(Y/2)\right) \le \int_{\mathfrak{m}} |S(\alpha)|^4\,d\alpha + 2\int_{\mathfrak{M}} |S(\alpha) - M(\alpha)|^4\,d\alpha + 8\int_{\mathfrak{M}} |M(\alpha)|^2 |S(\alpha) - M(\alpha)|^2\,d\alpha.$$
   - **Minor integral**: $\int_{\mathfrak{m}} |S|^4 \le (\sup_{\mathfrak{m}} |S|)^2 \int_0^1 |S|^2 \le K_{\mathfrak{m}}^2 C_{\mathrm{pars}}^{\mathrm{mult}} Y^{5/2} (\log Y)^3$.
   - **Major Part 1**: $2\int_{\mathfrak{M}} |S-M|^4 \le 2 K_{\mathfrak{M}}^2 \left(2\int_0^1 |S|^2 + 2\int_{\mathfrak{M}} |M|^2\right) \le C_{\mathrm{M1}} Y^{5/2}(\log Y)^3$.
   - **Major Part 2**: Keeping $|z|^{1/2} Y$ explicit in $|S-M|$ cancels $1/|z|^2$ down to $1/|z|$. Splitting $A \le 100$ ($h=\frac{5}{4}$, $\int \frac{d\beta}{|z|} \le \frac{\log 201}{\pi}$) and $A > 100$ ($h = 25$, $\int \frac{d\beta}{|z|} \le \frac{1}{\pi}(\frac{1}{2}\log Y + \log(2\pi+2))$) and summing $\sum_{q \le Q_0} \frac{q}{\varphi(q)} \le \frac{1}{2} C_{q/\varphi} Y^{1/2}$ gives $\le C_{\mathrm{M2}} Y^{5/2}(\log Y)^3$.
4. **Dyadic closure & small-$X$ base**: Certifying cells across $[4\cdot 10^{18}, 10^{10000}]$ plus the monotonic tail $[10^{10000}, \infty)$ gives $E(Y) - E(Y/2) \le 3728.72 \sqrt{Y} (\log Y)^3$. Summing dyadically from $X$ down to $4\cdot 10^{18}$ (using $E(4\cdot 10^{18}) = 0$) multiplies by $\sum_{k=0}^\infty 2^{-k/2} = 2 + \sqrt{2} < 3.4143$, yielding $C = \lceil 3728.7126 \cdot (2+\sqrt{2}) \rceil = 12731$ for all $X \ge 4$.

---

## 4. Proof Blueprint for Theorem 1B ($[X, X + 6281 (\log X)^2]$)

Fix $X \ge 4\cdot 10^{18}$ (for $4 \le X < 4\cdot 10^{18}$, $C_1 (\log 4)^2 > 2$ ensures $[X, X + H]$ contains an even integer $\le 4\cdot 10^{18}$, which is $p_1 + p_2$ by $E(4\cdot 10^{18}) = 0$). Set $H := C_1 (\log X)^2$, $M_0 := \lfloor H/2 \rfloor$, $N_0 := \lceil X \rceil$, and define the Fejér triangle weight
$$W(n) := \frac{1}{M_0} (\mathbf{1}_{[0, M_0)} * \mathbf{1}_{[0, M_0)})(n - N_0), \qquad |\hat{W}(\alpha)| = \frac{1}{M_0} \left(\frac{\sin(\pi M_0 \alpha)}{\sin(\pi\alpha)}\right)^2 \le \min\left(M_0,\ \frac{1}{4 M_0 \|\alpha\|^2}\right).$$
By Parseval, $\sum_n W(n) e^{-n/X} R_\Lambda(n) = \int_{-1/2}^{1/2} S(\alpha)^2 \hat{W}(-\alpha)\,d\alpha$.
1. **Outer region $1/4 \le |\alpha| \le 1/2$**: $|\hat{W}(\alpha)| \le \frac{2}{M_0}$, so the integral is bounded by $\frac{2}{M_0} \int_0^1 |S|^2 \le \frac{\alpha_\psi}{M_0} X (\log X + C_{\mathrm{pars}})$.
2. **Main term on $|\alpha| \le 1/4$**: Writing $S(\alpha) = M_1(\alpha) + E(\alpha)$ with $M_1(\alpha) = \frac{1}{1/X - 2\pi i \alpha}$, we have $\int_{-1/4}^{1/4} M_1(\alpha)^2 \hat{W}(-\alpha)\,d\alpha \ge M_0 X e^{-1 - H/X} - 0.21 M_0$.
3. **Direct Mellin-Fejér $L^2$ bound for $\int_{-B}^{B} |E(\alpha)|^2\,d\alpha$ ($B \in [\frac{1}{2\pi X}, \frac{1}{4}]$)**:
   Using the $\operatorname{Re}(s) = -\frac{1}{2}$ explicit formula for $\zeta(s)$ (where $|R_{\mathrm{vert}}(-1/2)| = O((\log X)^2)$):
   - On $|\alpha| \le \frac{1}{2\pi X}$: $\int \le O(1)$.
   - On each dyadic shell $[B_j, 2 B_j]$ ($u = \log(2\pi\alpha X) \in [u_0, u_0 + \log 2]$, $A_0 = 2\pi B_j X$): write $g_\gamma(u) = g_\gamma(u_0) + \int_{u_0}^u g'_\gamma(w)\,dw$, apply Minkowski in $L^2([u_0, u_0 + \log 2])$, and dominate $\mathbf{1}_{[u_0, u_0+\log 2]}(u)$ by $\frac{1}{0.989} \Phi(u - u_c)$ where $\Phi(x) = (\frac{\sin(x/2)}{x/2})^2$ has compactly supported Fourier transform $\hat{\Phi}(\xi) = 2\pi \max(1 - |\xi|, 0)$.
   - Off-diagonal zeros $|\gamma' - \gamma| \le 1$ collapse via $1 - |t| \le \frac{25/16}{25/16 + t^2}$ to `long_poisson` at $\tau = \gamma$, while Stieltjes integration by parts and $\log(u+1) \le \sqrt{u}$ bound the $\gamma$-sum cleanly. Across all $X \ge 4\cdot 10^{18}$, this certifies
     $$\int_{-B}^{B} |E(\alpha)|^2\,d\alpha \le C_{\mathrm{Sel}} B X (\log X)^2, \qquad C_{\mathrm{Sel}} \le 78.0389.$$
4. **Error integration & closure**: Splitting $[-1/4, 1/4]$ into $|\alpha| \le 1/M_0$ and dyadic shells $[B_j, 2B_j]$ ($B_j = 2^j/M_0$) yields $\int_{-1/4}^{1/4} |E(\alpha)|^2 |\hat{W}(\alpha)|\,d\alpha \le 2 C_{\mathrm{Sel}} X (\log X)^2$, and Cauchy–Schwarz against $\int_{-1/4}^{1/4} |M_1|^2 |\hat{W}| \le \frac{1}{2} M_0 X$ bounds the cross term by $2\sqrt{C_{\mathrm{Sel}} M_0}\, X \log X$. Subtracting odd-$n$ ($\le 2 e^{-1}(H+1)(\log(X+H))^2$) and prime-power ($\le 2 e^{-1}(H+1)\alpha_{\mathrm{pp}}\sqrt{X+H}\log(X+H)$) contributions certifies positivity for **$C_1 = 6281$**.
