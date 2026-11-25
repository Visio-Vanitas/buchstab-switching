# X26. Every even N ≥ 4 is p + η with Ω(η) ≤ 4, under GRH

## Packet header

- **Claim ID:** `X26` | **Author:** `local-carbon` (with `d255528d`) | **Date:** `2026-11-25`
- **Status:** `unchecked (repaired after R17)`. **Level:** `conjecture`.
- **Standing premise:** GRH for Dirichlet L-functions (and RH) is used as an established theorem (`docs/COLLABORATION.md`, Rule 0.5).
- **Script:** `research/goldbach/scripts/certify_all_even_1p4.py` (run: `python3 research/goldbach/scripts/certify_all_even_1p4.py`, exit 0).
- **Output:** `research/goldbach/data/certify_all_even_1p4_output.txt` (regenerated from a run of the repaired script).
- **Review answered:** `notes/R17-review-X26-all-even-1p4-under-grh.md` and `notes/R17-x26-reports/` (see the section "Answers to R17" at the end).

**What changed after R17, in one paragraph.** The theorem statement is unchanged, and it still covers every even N ≥ 4. Its Regime 3 now rests on the explicit linear sieve exactly as stated in arXiv:2207.09452**v6** (Theorem 6 and Table 1 of v6, quoted in §0.1). The old script used a different table, the one printed in arXiv:2211.08844v1, which quotes an earlier version of the same theorem. With the v6 table, applied at ε' = 1/100 (the largest row below our 1/ε = 117.29), the net Regime-3 coefficient drops from 0.031666 to **0.001489**. It is positive, but thin. Benchmark 0 now passes with the table exactly as Regime 3 uses it. The weighted inequality now uses the set A = {N − p : p ∤ N}, so no ω(N) correction is lost. The interval arithmetic now rounds outward everywhere, and the run checks this mechanically.

---

## Theorem

**Theorem 1.** *Assume GRH for Dirichlet L-functions. Then every even integer N ≥ 4 can be written as N = p + η with p prime and Ω(η) ≤ 4, where Ω counts prime factors with multiplicity.*

The proof has three regimes:

- **Regime 1, 4 ≤ N ≤ 4·10^18.** The Goldbach verification gives N = p₁ + p₂, so Ω(η) = 1. Quoted in §0.6.
- **Regime 2, 4·10^18 ≤ N < 10^170.** Thirty slabs, each with a Bonferroni sieve (§2–§3). The smallest net margin is 0.000331, in slab 22.
- **Regime 3, N ≥ 10^170.** The linear sieve of [BJS] Theorem 6 with a pre-sieve (§4). It gives π₄(N) > 0.001489 · 22 U_N N/log²N.

Here π₄(N) := #{p ≤ N prime : Ω(N − p) ≤ 4}, and U_N is defined in §0.5.

**Exact question for a verifier.** Are the following correct, and does the script check exactly these statements?

1. The quoted statements in §0.
2. The use of the hypothesis of [BJS] Theorem 6 in §4.2, which ranges over all 1 < u < z for every z ≥ z₀.
3. Lemmas 1–2 in §2.
4. The error decomposition in §4.4.

---

## 0. Sources, quoted

All quotations below were read in this session from the arXiv sources, TeX and PDF. Lemma numbers follow the PDF of the stated version. Where the TeX label differs from the printed number, the label is given too. In the quotations, displayed TeX is reflowed inline: summation limits written with `\substack` are put on one line, and `\cite` keys are abbreviated. The words and symbols are unchanged.

### 0.1 [BJS] Bordignon–Johnston–Starichkova, arXiv:2207.09452v6, Theorem 6 ("The linear-sieve, explicit version", TeX label `theo:JR`)

> Let $A=\{a(n)\}_{n=1}^{\infty}$ be an arithmetic function such that $a(n)\ge 0$ for all $n$ and $|A|=\sum_{n=1}^{\infty} a(n)< \infty$. Let $\mathbb{P}$ be a set of prime numbers and for $z\ge 2$, let $P(z):=\prod_{p \in \mathbb{P},\, p<z}p$. Let $S(A,\mathbb{P}, z):=\sum_{n\ge1,\ (n, P(z))=1}a(n)$. For every $n\ge 1$, let $g_n(d)$ be a multiplicative function such that $0\le g_n(p)< 1$ for all $p \in \mathbb{P}$. Define $|A_d|$ and $r(d)$ by
> $$|A_d|:=\sum_{n\ge1,\ d|n} a(n)= \sum_{n=1}^{\infty} a(n)g_n(d)+r(d).$$
> Let $\mathbb{Q}\subseteq \mathbb{P}$, and $Q$ be the product of its primes. Suppose that, for some $\varepsilon$ satisfying $0<\varepsilon\le 1/74$, the inequality
> $$\prod_{\substack{p\in \mathbb{P}/\mathbb{Q}\\ u \le p < z}}(1-g_n(p))^{-1}<(1+\varepsilon) \frac{\log z}{\log u},$$
> holds for all $n$ and $1<u<z$. Then, for any $D\ge z$ we have the upper bound
> $$S(A,\mathbb{P},z)<(F(s)+\varepsilon C_{1}(\varepsilon) e^2h(s))X_A+R,$$
> and for any $D\ge z^2$ we have the lower bound
> $$S(A,\mathbb{P},z)>(f(s)-\varepsilon C_{2}(\varepsilon) e^2h(s))X_A-R,$$
> where $s:=\frac{\log D}{\log z}$,
> $$h(s):= \begin{cases} e^{-2} & 1\le s \le 2, \\ e^{-s} & 2\le s \le 3, \\ 3s^{-1}e^{-s} & s\ge 3, \end{cases}$$
> $F(s)$ and $f(s)$ are the two functions defined by the following delay differential equations (see [Cai]): $F(s) = \frac{2 e^{\gamma}}{s}$, $f(s) = 0$ for $0 < s \le 2$; $(sF(s))' = f(s - 1)$, $(sf(s))' = F(s-1)$ for $s \ge 2$; $C_1(\varepsilon)$ and $C_2(\varepsilon)$ come from Table 1,
> $$X_A:=\sum_{n=1}^{\infty} a(n) \prod_{p\mid P(z)}(1-g_n(p))=|A|\prod_{p\mid P(z)}(1-g_n(p)),$$
> and the remainder term is $R:=\sum_{d|P(z),\ d<QD}|r(d)|$. If there is a multiplicative function $g(d)$ such that $g_n(d)=g(d)$ for all $n$, then $X_A=V(z)|A|$, where $V(z):=\prod_{p|P(z)}(1-g(p))$.

Two details of the source text matter here. The product is written "$\mathbb{P}/\mathbb{Q}$" in the source; it means $\mathbb{P}\setminus\mathbb{Q}$. And the hypothesis ranges over **all $1<u<z$ with the upper endpoint fixed at $z$**. It does not range over arbitrary subintervals $[w_1,w_2)$.

**Table 1 of v6, "Values for $C_1(\varepsilon)$ and $C_2(\varepsilon)$".** The columns are $\varepsilon^{-1}$, $C_1(\varepsilon)$, $C_2(\varepsilon)$:

| ε⁻¹ | C₁ | C₂ | ε⁻¹ | C₁ | C₂ | ε⁻¹ | C₁ | C₂ | ε⁻¹ | C₁ | C₂ |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 74 | 631 | 630 | 95 | 302 | 302 | 200 | 153 | 154 | 800 | 115 | 116 |
| 76 | 559 | 559 | 100 | 276 | 277 | 300 | 133 | 134 | 900 | 114 | 115 |
| 78 | 504 | 504 | 120 | 218 | 219 | 400 | 125 | 126 | 1000 | 113 | 114 |
| 80 | 461 | 461 | 140 | 189 | 190 | 500 | 121 | 122 | 2000 | 109 | 110 |
| 85 | 386 | 386 | 160 | 172 | 173 | 600 | 118 | 119 | 10000 | 106 | 108 |
| 90 | 336 | 337 | 180 | 161 | 162 | 700 | 116 | 117 | 100000 | 106 | 107 |

The text after the table says: "To read Table 1 it is useful to remember that $C_1(\varepsilon)$ and $C_2(\varepsilon)$ are decreasing in $\varepsilon^{-1}$."

[BJS] Lemma 14 defines the constants as $C_1(\varepsilon):=\sum_{n\ge1}\tau_{2n-1}$ and $C_2(\varepsilon):=\sum_{n\ge1}\tau_{2n}$, for ε ∈ (0, 1/74]. So C₁ goes with the upper bound and C₂ with the lower bound.

**How the script reads the table.** If the hypothesis holds with some ε, it also holds with every ε' ∈ [ε, 1/74], because the right side only grows. We therefore apply the theorem **at ε' = 1/k**, where k is the largest table row with k ≤ 1/ε, and we use the tabulated C_i(1/k). No interpolation is used, and no monotonicity in ε is needed. In the code this is `lookup_BJS` and `eps_used`.

**[BJS] Lemma 19 (= [Cai, Lemma 2]).** For the explicit values of f and F:

> $F(s)=\frac{2e^{\gamma}}{s}$, $0 < s \le 3$; $F(s)=\frac{2e^{\gamma}}{s} \left( 1 + \int_2^{s-1} \frac{\log(t-1)}{t} \mathrm{d}t \right)$, $3 \le s \le 4$; $f(s)= 0$, $0 < s \le 2$; $f(s)=\frac{2e^{\gamma} \log(s-1)}{s}$, $2 \le s \le 4$.

[JS] §2 adds: "$F(s)$ monotonically decreases towards 1 and $f(s)$ monotonically increases towards 1". The same formula for F holds on [3, 5]. For s ∈ [3, 5] we have s − 1 ∈ [2, 4], so the quoted delay equation and the formula for f give $sF(s) = 3F(3) + \int_3^s f(t-1)\,dt = 2e^\gamma(1+\int_2^{s-1}\log(t-1)/t\,dt)$.

**[BJS] Lemma 23.** "For all $x\ge 45$, we have $\sum_{n\le x}\mu^2(n)\le 0.65x$." This is used only in Benchmark 0.

**[BJS] Lemma 38** (j = 0 case; $P(x)=\prod_{p<x,\ p\nmid N}p$ and $V(x)=\prod_{p|P(x)}(1-\frac1{p-1})$, as in [BJS] (111)):

> For $x\ge 285$ and $j=0,\ldots,\ell$, we have $V^{(j)}(x) = \frac{U_N^{(j)}}{\log x} \left[ 1 + 1.45\,\theta_1(x) \frac{\log N}{x-1} \left( 1 + \frac{10 \log \log N}{\log N} \right) \right]\cdot\left( 1 + \frac{1.002\,\theta_2(x)}{x-3} \right) \left( 1 + \frac{\theta_3(x)}{2 \log^2 x} \right)$, where $|\theta_i|\le 1$, $i = 1, 2, 3$.

### 0.2 [JS] Johnston–Starichkova, arXiv:2208.01229v3 (numbering of the v3 PDF)

**Lemma 5.1** (TeX label `epilem`):

> Let $x\geq X_2\geq 4\cdot 10^{18}$, and $q$ and $a$ be integers such that $3\leq q\leq \sqrt{x}$ and $(a,q)=1$. Then, assuming GRH, $\left|\pi(x;q,a)-\frac{\li(x)}{\varphi(q)}\right|\leq c_{\pi}(X_2)\sqrt{x}\log x$, where $c_{\pi}(X_2)=\frac{3}{8\pi}+\frac{6 + 1/\pi}{4\log X_2}+\frac{6}{\log^2 X_2} + \frac{\li(2)}{\sqrt{X_2} \log X_2} \leq 0.16.$

The proof in [JS] is: "We apply [17, Corollary 1] for $K = \mathbb{Q}$ and $L = \mathbb{Q}[e^{2\pi i/q}]$ and the bounds on $x$ and $q$ to get $|\pi(x;q,a)-\frac{\li(x)-\li(2)}{\varphi(q)}|\leq ( \frac{3}{8\pi}+\frac{6 + 1/\pi}{4\log X_2}+\frac{6}{\log^2 X_2} ) \sqrt{x}\log x$. We conclude by using the triangle inequality and $\varphi(q) \geq 1$." So:

- The main term in Lemma 5.1 is li(x), not li(x) − li(2). The li(2) is absorbed into the last term of c_π.
- li is $\int_0^x dt/\log t$ ([JS] §3).
- Here [17] is Grenié–Molteni (JNT 2019).

I checked that this is consistent with Grenié–Molteni, arXiv:1709.07609v3, Corollary 1.2, read here. That corollary reads: "Assume GRH holds. Then $\forall x\geq 2$, $\Big|\frac{|G|}{|C|}\pi(C;x)-\int_2^x \frac{du}{\log u}\Big| \leq \sqrt{x}\Big[\Big(\frac{1}{2\pi} + \frac{3}{\log x}\Big)\log\Delta_L + \Big(\frac{\log x}{8\pi} + \frac{1}{4\pi} + \frac{6}{\log x}\Big)n_L\Big]$". Take L = Q(ζ_q), K = Q and C = {a}, so |G| = n_L = φ(q). With log Δ_L ≤ φ(q) log q ≤ ½ φ(q) log x, dividing by φ(q) gives $\sqrt x\log x\,[\frac{1}{4\pi}+\frac{1}{8\pi} + (\frac32+\frac1{4\pi})\frac1{\log x} + \frac{6}{\log^2x}]$. This is exactly the [JS] bracket, since $\frac32+\frac1{4\pi}=\frac{6+1/\pi}{4}$. The [JS] constant in X₂ ≤ x follows because the bracket decreases in x. The discriminant bound log Δ_L ≤ φ(q) log q is standard and was not read from a source here.

**Lemma 3.1.** "For all $N\geq 71$, $|A|>\frac{N}{\log N}$." Here $A=\{N-p : p\leq N,\ p\nmid N\}$, defined in [JS] §2.1.

**Lemma 3.2.** We have
> $\sum_{p<x}\frac{1}{p}\geq\log\log x+M_0-\frac{2.964\cdot 10^{-6}}{\log x}$, $x\geq 2$ (3.1);
> $\sum_{p<x}\frac{1}{p}\leq\log\log x+M_0+1.614\cdot 10^{-3}$, $x>\exp(8.9)$ (3.2);
> $\sum_{p<x}\frac{1}{p}\leq\log\log x+M_0+\frac{6.836\cdot 10^{-6}}{\log x}$, $x>10^{12}$ (3.3),
> where $M_0=0.261497\ldots$ is the Meissel–Mertens constant.

**[BJS] Lemma 16.** "For all $2\le x\le 10^{12}$, we have $\log\log x+M<\sum_{p\le x}\frac{1}{p}<\log\log x+M+\frac{2}{\sqrt{x}\log x}$." Here M is the same constant as M₀. These are unconditional and computational: Lemma 16 is a direct computation up to 10^12, and (3.3) uses Büthe and Broadbent et al. They are not RH bounds, so being sharper than Schoenfeld's RH bound is no contradiction.

The script uses each bound **only in its stated range** (`mertens_ub_err`). Lemma 16 is used for x ≤ 10^12, (3.3) for x > 10^12, and (3.2) as a cap. The lower bound (3.1) holds for all x ≥ 2, so its use at x = 41 and x = 30000 is inside its range.

**Lemmas 5.7 and 5.8 and Theorem 5.9** are used only in Benchmark 0. Lemma 5.7 reads: "$\sum_{d\le H,(d,N)=1}\mu^2(d)|\pi(N;d,N)-\frac{\pi(N)}{\varphi(d)}|\leq \frac{p_G(X_2)N}{\log^B N}$, $p_G(X_2)=0.65(c_{\pi}(X_2)+\frac{1}{16\pi})$". Its proof bounds $\frac{1}{\varphi(d)}|\li(N)-\pi(N)|$ by $\frac{1}{8\pi\varphi(d)}\sqrt N\log N\le\frac{1}{16\pi}\sqrt N\log N$, using Schoenfeld and d ≥ 3. Lemma 5.8 gives "$c_{4,G}(X_2)=p_G(X_2)+\frac{0.9}{\sqrt{X_2}\log\log X_2}$". Its proof uses "$|r(d)|\leq |\pi(N;d,N)-\frac{\pi(N)}{\varphi(d)}|+\omega(N)$", from $|A|=\pi(N)-\omega(N)$ and $|A_d|=\pi(N;d,N)-\omega(N;d,N)$.

### 0.3 [BS] Bordignon–Starichkova, arXiv:2211.08844v1

- **Lemma 1** ([Schoenfeld 1976, Cor. 1]): "If the Riemann hypothesis (RH) holds, then $|\pi(x) - \li(x)| \leq \frac{\sqrt{x} \log x}{8 \pi}$, for $3 \leq x$." We use it only for x ≥ 4·10^18 and for x = y > 30000. Schoenfeld's paper itself was not read (see Gaps).
- **Lemma 4** ([Robin]): "$\omega(N)< \frac{1.3841\log N}{\log \log N}$ for $N \geq 3$."
- **Lemma 5** ([Büthe]): "For $x \geq 10^9$, $\sum_{n\le x} \mu^2(n) \le 0.608 x$, $\sum_{n\le x}\frac{\mu^2(n)}{\varphi(n)}\le\log x + 1.333 +\frac{58}{\sqrt{x}}\le 1.1\log x$."

The packet used to cite "2211.08844 Lemma 9" for V(z). In v1, Lemma 9 is the bilinear-form lemma. The V(x) lemma of [BS] is Lemma 11, and it prints U_N with $2e^{\gamma}$ instead of $2e^{-\gamma}$. We no longer use it: Regime 3 now uses [BJS] Lemma 38 (§0.1), which is unconditional and has $2e^{-\gamma}$.

### 0.4 Elementary facts proved here

- $\mathrm{li}(x) < x/(\log x-2)$ for x ≥ e⁵. With L = log x, the difference $x/(L-2)-\mathrm{li}(x)$ has derivative $(L-4)/(L(L-2)^2) > 0$ for L > 4, and it is positive at e⁵. The script asserts li(e⁵) < e⁵/3.
- $\log(t-1)/t$ is increasing on [2, 4]. Its derivative has the sign of $t/(t-1)-\log(t-1)$, which is decreasing in t and equals 1.333 − 1.0986 > 0 at t = 4.
- $-\log(1-x)\le x + x^2/(2(1-x))$ for 0 < x < 1.

### 0.5 U_N

$U_N:=2 e^{-\gamma}\prod_{p>2}( 1-\frac{1}{(p-1)^2})\prod_{p>2,\ p|N}\frac{p-1}{p-2}$. This is [BJS] (2), quoted in [BJS] Theorem 3 and [JS] §2.1. Hence $U_N \ge U_c := 2e^{-\gamma}C_2$, where C₂ is the twin-prime constant. The script encloses U_c ∈ [0.741285, 0.741311].

### 0.6 Regime 1

[BJS] §1 says: "This conjecture was verified for all even $N\le 4\cdot 10^{18}$ by Oliveira e Silva [TOS]." [JS] §1 says: "Goldbach's conjecture is known to hold for $2<N\leq 4\cdot 10^{18}$ as the result of a large computation by Oliveira e Silva, Herzog and Pardi." The primary paper was not read.

---

## 1. Setup and the weighted inequality

Let N ≥ 4·10^18 be even. Define

- A := {N − p : p ≤ N prime, p ∤ N}, as in [JS] and [BJS]. Distinct p give distinct elements.
- 𝐏 := {p : p ∤ N}. Since N is even, 2 ∉ 𝐏.
- P(w) := ∏_{p∈𝐏, p<w} p.
- A_d := {a ∈ A : d | a}.
- r(d) := |A_d| − |A|/φ(d).

**Every a = N − p ∈ A is coprime to N**, because gcd(N − p, N) = gcd(p, N) = 1. So a is odd, and no prime ℓ | N divides a. Hence, for a ∈ A, the condition (a, P(z)) = 1 means that *a has no prime factor below z at all*.

Take real numbers z < y with z·y⁴ ≥ N and y⁵ > N. Regime 2 takes integers z, y with z^M ≥ X_hi, y⁵ > X_hi and z·y⁴ ≥ X_hi. Regime 3 takes z = N^{1/22} and y = N^{21/88}, so z y⁴ = N. Put the weight

$$w(a) := 1 - \tfrac12\#\{q \in [z,y) \text{ prime} : q\mid a\} - \tfrac12\#\{q\in[z,y) \text{ prime}: q^2\mid a\}$$

on each a ∈ A with (a, P(z)) = 1. Then w(a) > 0 implies Ω(a) ≤ 4:

- If no q ∈ [z, y) divides a, every prime factor of a is ≥ y and a < N < y⁵, so Ω(a) ≤ 4.
- If exactly one q divides a, and q² ∤ a, then a/q < N/z ≤ y⁴ has all its prime factors ≥ y, so Ω(a/q) ≤ 3.
- Otherwise w(a) ≤ 0.

Since w(a) ≤ 1 always, this gives

$$\pi_4(N) \ \ge\ \#\{a\in A:\Omega(a)\le4\}\ \ge\ S(A,P(z)) - \tfrac12\sum_{\substack{z\le q<y\\ q\in\mathbf P}} S(A_q,P(z)) - \tfrac12\sum_{\substack{z\le q<y\\ q\in\mathbf P}}|A_{q^2}|. \tag{1.1}$$

Here q runs over 𝐏 because A_q = ∅ when q | N. η = 1 needs no exclusion, since Ω(1) = 0 ≤ 4.

The elements N − p with p | N are simply not in A. There are at most ω(N) of them (N − 2 is one). In the old write-up, with the larger set {N − p : p ≤ N}, those elements had to be subtracted: (1.1) with that set needs −ω(N), not −1. Here they enter only through |A| = π(N) − ω(N) and |A_d| = π(N; d, N) − ω(N; d, N). That gives the explicit ω(N) term in the remainder bound (∗) below, which the script carries per modulus: `err_per_d_norm` in Regime 2 and the 1.3841/(√N log log N) part of c₄G in Regime 3.

**Remainder per modulus.** Let 3 ≤ d ≤ √N with (d, N) = 1. By [JS] Lemma 5.1 with X₂ = X_lo (or X_LS), by [BS] Lemma 1 with φ(d) ≥ 2, and by the decomposition of [JS] Lemma 5.8,

$$|r(d)| \le |\pi(N;d,N)-\tfrac{\li N}{\varphi(d)}| + \tfrac{|\pi(N)-\li N|}{\varphi(d)} + \omega(N) \le \big(c_\pi(X_2)+\tfrac{1}{16\pi}\big)\sqrt N\log N + \tfrac{1.3841\log N}{\log\log N}. \tag{$*$}$$

The modulus d may be a square, d = q². For d = 1, r(1) = 0. Every modulus the script uses satisfies 3 ≤ d ≤ √X_lo ≤ √N and (d, N) = 1, and the script asserts this with exact integer comparisons. The extra 1/(16π) in the script is exactly the middle term of (∗).

**|A_{q²}|.** A_{q²} consists of distinct integers in [1, N − 1] divisible by q², so |A_{q²}| ≤ ⌊(N−1)/q²⌋ ≤ N/q². No +1 is needed because the counted integers are distinct and lie in [1, N−1].

**Main term.** |A| > N/log N by [JS] Lemma 3.1. Every main term below has the form |A| × (a bracket that the script proves positive), so the lower bound for |A| may be used.

---

## 2. Lemmas for Regime 2: worst case over the primes dividing N

Fix a slab, a set Q₁ of the first a odd primes, and P₂ = {odd p : p_a < p < z}. For a given N, the primes actually sieved are Q₁' = Q₁ ∖ {p | N} and P₂' = P₂ ∖ {p | N}. Put w_p = 1/(p − 1), V₂(T) = ∏_{p∈T}(1 − w_p), $g_m(T)=\sum_{j=0}^m(-1)^je_j(w_p:p\in T)$ and R_m(T) = g_m(T)/V₂(T).

**Lemma 1 (sieve weights).** For d | ∏Q₁'·∏P₂', let λ_d = μ(d)·1[ω_{P₂'}(d) ≤ m]. Then $\sum_{d|n}\lambda_d = \mathbf 1[(n,Q_1')=1]\sum_{j=0}^m(-1)^j\binom{\omega_{P_2'}(n)}{j}$. This is ≤ 1[(n, P(z)) = 1] for m odd and ≥ 1[(n, P(z)) = 1] for m even.

*Proof.* For k ≥ 1, $\sum_{j\le m}(-1)^j\binom kj=(-1)^m\binom{k-1}m$. ∎

Hence, for a ∈ A and any prime q ∈ [z, y) ∩ 𝐏:

$$S(A,P(z)) \ge |A|\,V(Q_1')\,g_{m_{odd}}(P_2') + \textstyle\sum\lambda^-_d r(d), \qquad S(A_q,P(z)) \le \tfrac{|A|}{q-1}V(Q_1')\,g_{m_{even}}(P_2') + E_q,$$

where E_q is bounded in §3. The identity $\sum_{d}\lambda_d/\varphi(d) = V(Q_1')g_m(P_2')$ holds because d is squarefree with odd prime factors. Write $V_N := V(Q_1')V_2(P_2') = \prod_{2<p<z,\,p\nmid N}(1-\tfrac1{p-1})$. Then $V(Q_1')g_m(P_2') = V_N R_m(P_2')$.

**Lemma 2 (removing primes that divide N).**

(a) For T' = T ∖ {p}: $g_m(T) = (1-w_p)g_m(T') + (-1)^m w_p e_m(T')$. Hence $R_m(T')-R_m(T) = -(-1)^m\frac{w_p e_m(T')}{(1-w_p)V_2(T')}$. So R_odd can only increase, and R_even can only decrease, when primes are removed.

(b) Let $b := R_{odd}(P_2) - \tfrac12 R_{even}(P_2)\sum_{z\le q<y}\frac1{q-1}$, where the sum runs over all primes in [z, y). If b > 0, then for every even N in the slab the main term of (1.1) satisfies

$$V_N\Big[R_{odd}(P_2') - \tfrac12R_{even}(P_2')\sum_{q\in[z,y)\cap\mathbf P}\tfrac1{q-1}\Big] \ \ge\ V_N\, b\ \ge\ V_{\rm full}\, b,$$

with $V_{\rm full} := \prod_{2<p<z}(1-\frac1{p-1}) \le V_N$.

*Proof.* (a) follows from $e_j(T)=e_j(T')+w_pe_{j-1}(T')$, which gives $g_m(T)=g_m(T')-w_pg_{m-1}(T')$, together with $g_{m-1}=g_m-(-1)^me_m$. For (b), the bracket for N is ≥ b by (a), and adding the q | N terms only subtracts more. Then V_N ≥ V_full is used, and that step needs b > 0. ∎

The script bounds b from below:

- **Exact branch** (z ≤ 30000): exact symmetric functions on P₂.
- **Analytic branch** (z > 30000): $R_{odd} \ge 1 - e_{m+1}/V_2$ and $R_{even}\le 1+e_{m+1}/V_2$, with $e_{m+1}\le S_1^{m+1}/(m+1)!$ and $V_2 \ge \exp(-S_1 - c\sum(p-1)^{-2})$, where S₁ = Σ_{P₂} 1/(p−1) is bounded by §0.2.

It asserts b > 0 (`bracket.lo > 0`) and uses a lower bound V_lb ≤ V_full. This replaces the old Lemma 2. The old version had a wrong normalisation |A_q| V_N R/V₂ and claimed monotonicity "unconditionally", while the correct statement needs b > 0.

---

## 3. Regime 2 (4·10^18 ≤ N < 10^170): what the script does

The slab table `SLABS` has 30 half-open intervals [X_lo, X_hi). Contiguity from 4·10^18 to 10^170 is asserted. Each slab has parameters (M, a, m_odd, m_even). For each slab, `certify_slab_K4` does the following:

1. **Choose z and y.** It takes integers z, y with z^M ≥ X_hi, y⁵ > X_hi, z y⁴ ≥ X_hi and y > z, all asserted exactly.
2. **Lower sieve on S(A, P(z)).** Lemma 1 with exact inclusion–exclusion on Q₁ and odd-order Bonferroni of order m_odd on P₂.
3. **Upper sieve on each S(A_q, P(z)), z ≤ q < y.** Lemma 1 with even order m_even on P₂. When m_even = 0 (slabs 1–4), A_q is sieved by Q₁ alone: S(A_q, P(z)) ≤ #{a ∈ A_q : (a, Q₁') = 1}, computed by exact inclusion–exclusion over d | Q₁'. There is no other sieve: no Selberg Λ², no "trivial sieve", no P_sub inclusion–exclusion and no log-spaced slices.
4. **Sums over q.** For y ≤ 30000 they are exact sums over primes. Otherwise the part up to 30000 is exact, and above it the script uses Σ_{P<q<y} 1/q ≤ (upper bound at y) − (lower bound at P), from §0.2 in its stated ranges, and Σ_{q≥P} 1/(q(q−1)) ≤ 1/P. The count π(y) is bounded by [BS] Lemma 1 plus §0.4.
5. **Main term.** $|A|\,V_{lb}\,b$ with |A| > N/log N.
6. **Errors**, normalized by N/log N. Each is evaluated at the end of the slab where it is largest:
   - Lower sieve: (number of d with λ_d ≠ 0) × (∗). The count is ≤ 2^a Σ_{j≤m}C(|P₂|, j), or ≤ 2^a Σ π(z)^j/j! in the analytic branch.
   - Upper sieve for A_q, for each q: $E_q \le \#\{d\}\cdot\max|r(qd)| + |r(q)|\sum_d 1/\varphi(d) + |r(q)|\,R_{even}$. The first two terms are the remainder for $r_q(d)=r(qd)-r(q)/\varphi(d)$ when A_q is approximated by |A_q|/φ(d). The third comes from $|A_q| = |A|/(q-1)+r(q)$ in the main term, with $V_N R_{even}(P_2')\le R_{even}(P_2)$. This is `err_Aq_norm`.
   - q² term. If y⁴ ≤ X_lo (only then is q² ≤ √N guaranteed), the script uses ½ Σ_q (|A|/(q(q−1)) + (∗)). Here |A| ≤ π(N) ≤ li(N) + √N log N/(8π) and li(N) < N/(log N − 2). This branch is used only in slab 1. Otherwise it uses ½ Σ_q N/q².
   - Monotonicity. The terms of (∗) divided by N/log N, namely (c_π + 1/16π) log²N/√N and 1.3841 log²N/(N log log N), decrease in N, so they are evaluated at X_lo. c_π(X_lo) is valid for all N ≥ X_lo. The elementary q² term grows like log N, so it is evaluated at X_hi. The integer z, y and the moduli bounds are fixed per slab.

The output per slab is main ≥, err ≤ and net ≥, and every net is asserted positive. The minimum is 0.000331, at slab 22 [10^126, 10^134). That margin comes from the elementary q² term, not from the GRH constant. The numbers did not change from the R17 version, because the changes only touch terms of size ≤ 10^−15 in Regime 2.

---

## 4. Regime 3 (N ≥ 10^170)

### 4.1 Parameters

The parameters are:

- M = 22, z = N^{1/22}, y = N^β with β = 21/88 > 1/5 (so z y⁴ = N).
- u₀ = 41 and B = 3.05.
- Q = ∏_{3≤p<41, p∤N} p ≤ ∏_{3≤p≤37} p = 3 710 369 067 405.
- α = 0.1358, the 4-decimal ceiling of (log ∏_{3≤p≤37} p + (B+1) log log X_LS)/log X_LS.
- D = N^{1/2−α} and H = √N/log^{B+1}N.

Asserted, each for N = X_LS and increasing in N:

- N^α/log^{B+1}N ≥ ∏_{3≤p≤37}p. Its log-derivative is α − (B+1)/log N > 0. Hence QD ≤ H.
- H ≥ 10^9, so [BS] Lemma 5 applies.
- y ≤ H, which needs ½ − β > (B+1)/log N.
- log N > 2M = 44.

Also asserted: s := log D/log z = 22(½ − α) = 8.0124 ≥ 2, so D ≥ z². And s_min := 22(½ − α − β) = 2.7624 ≥ 1, so D/q ≥ z for all q < y. Finally z₀ = X_LS^{1/22} ≥ 5.3367·10^7 > 285 and log z₀ > 8.9.

### 4.2 The ε-hypothesis of [BJS] Theorem 6

Apply Theorem 6 with 𝐏 = {p ∤ N}, ℚ = {3 ≤ p < 41, p ∤ N} ⊆ 𝐏, g_n(p) = g(p) = 1/(p − 1), and z = N^{1/22} ≥ z₀. The hypothesis must hold for **every** 1 < u < z and for every such z. It does not need to hold for arbitrary [w₁, w₂). The R17 test w₁ = 41, w₂ = 42 therefore does not apply. What has to be checked instead is all u, with the upper endpoint z.

- **u ≤ 41.** The product runs over p ∈ 𝐏 ∖ ℚ ∩ [u, z), which is contained in [41, z). So it is at most the product over all primes in [41, z), and log z/log u ≥ log z/log 41. So it suffices to treat 41 ≤ u < z.
- **41 ≤ u < z.** Write $(1-\frac1{p-1})^{-1} = \frac{(p-1)^2}{p(p-2)}(1-\frac1p)^{-1}$ and drop the condition p ∤ N, which only enlarges the product. Then:
  - $\prod_{u\le p<z}\frac{(p-1)^2}{p(p-2)} < \prod_{p\ge41}\frac{(p-1)^2}{p(p-2)} = C_2^{-1}/\prod_{2<p<41}\frac{(p-1)^2}{p(p-2)}$ =: twin_tail.
  - $\prod_{u\le p<z}(1-\frac1p)^{-1}\le \exp\big(\sum_{u\le p<z}\frac1p + c\sum_{p\ge41}p^{-2}\big)$ with c = 1/(2(1 − 1/41)).
  - $\sum_{u\le p<z}\frac1p \le \log\frac{\log z}{\log u} + E_{\max} + \frac{2.964\cdot10^{-6}}{\log 41}$. Here E_max bounds $\sum_{p<z}1/p - \log\log z - M_0$ for **all** z ≥ z₀. By [BJS] Lemma 16 for z ≤ 10^12 this is ≤ 2/(√z₀ log z₀), and by [JS] (3.3) for z > 10^12 it is ≤ 6.836·10⁻⁶/log 10^12. The lower bound is [JS] (3.1) at u ≥ 41.

So the hypothesis holds with $1+\varepsilon = \text{twin\_tail}\cdot\exp(E_{\max}+2.964\cdot10^{-6}/\log41 + c\sum_{p\ge41}p^{-2})$, uniformly in u and in N ≥ X_LS. The script gets **ε ≤ 8.525989·10⁻³, 1/ε ≥ 117.29**. The largest row with k ≤ 117.29 is **k = 100**. The theorem is applied with **ε' = 1/100, C₁ = 276, C₂ = 277**; ε < ε' is asserted, which gives the strict inequality.

### 4.3 Main term

By [BJS] Lemma 38 at x = z ≥ 285, (1 − δ_V) M U_N/log N ≤ V(z) ≤ (1 + δ_V) M U_N/log N. Here δ_V is built from the three factors, evaluated at N = X_LS, where all three are decreasing in N: δ_V ≤ 1.591674·10⁻³.

- **Lower bound.** S(A, P(z)) > (f(s) − ε'C₂e²h(s)) V(z)|A| − R, with f(s) ≥ f(4) because f is increasing. Bracket: **≥ 0.975815**.
- **Upper bound for each q ∈ [z, y) ∩ 𝐏.** Apply Theorem 6 to A_q with D_q = D/q, s_q = log D_q/log z ≥ s_min, X = V(z)|A_q| and $r_q(d)=|A_{qd}|-|A_q|/\varphi(d) = r(qd)-r(q)/\varphi(d)$. This gives S(A_q, P(z)) < φ(s_q) V(z)|A_q| + R_q with φ = F + ε'C₁e²h. This is the BJS upper bound; there is no Selberg Λ² bound. Then |A_q| ≤ |A|/(q − 1) + |r(q)|.
- **The q-sum.** [1/22, β] is split into 200 equal slices [u_k, u_{k+1}]. For q ∈ [N^{u_k}, N^{u_{k+1}}), s_q ≥ 22(½ − α − u_{k+1}). F and h are decreasing, and F is evaluated by the formula on [3, 5] (§0.1), with an upper Riemann sum and F(s) ≤ F(5) for s > 5. The sum is Σ_slice 1/(q−1) ≤ (z₀/(z₀−1)) [log(u_{k+1}/u_k) + (C_up + 2.964·10⁻⁶)/(u_k log N)], with C_up = max(2/√z₀, 6.836·10⁻⁶). This holds because, for x ≥ z₀, $\sum_{p<x}1/p-\log\log x-M_0 \le C_{up}/\log x$: for x ≤ 10^12 by Lemma 16, since 2/(√x log x) ≤ (2/√z₀)/log x, and for x > 10^12 by (3.3). Result: ½ Σ_q φ(s_q)/(q − 1) **≤ 0.973127**.
- **main_coeff** = (1 − δ_V)(0.975815 − 0.973127) **≥ 0.002683**, in units of M U_N N/log²N.

### 4.4 Errors, in units of M U_N N/log²N, using U_N ≥ U_c

Let Σ* denote a sum over squarefree n ≤ H with (n, N) = 1. By (∗), [BS] Lemma 5 (Σμ² ≤ 0.608H, H ≥ 10^9) and [BS] Lemma 4, Σ*|r(n)| ≤ c₄G N/log^B N, with c₄G = 0.608 (c_π(X_LS) + 1/(16π) + 1.3841/(√N log log N)) ≤ 0.087148.

- **R1** = R + ½ Σ_q Σ_{d|P(z), d<QD/q} |r(qd)|. The products n = qd are distinct, because q ≥ z is the largest prime factor of n, and n < QD ≤ H. So R1 ≤ 1.5 c₄G N/log^B N. Normalized: 1.5 c₄G/(M U_c log^{B−2}N) **≤ 0.000015**.
- **R2** = ½ Σ_q |r(q)| Σ_{d<QD} μ²(d)/φ(d) ≤ ½ · c₄G N/log^B N · 1.1 log H ≤ 0.275 c₄G N/log^{B−1}N. This uses q < y ≤ H and [BS] Lemma 5. Normalized: **≤ 0.001090**.
- **rq** = ½ V(z) φ(s_min) Σ_q |r(q)| ≤ ½(1 + δ_V)(M U_N/log N) φ(s_min) c₄G N/log^B N. Normalized: **≤ 0.000001**. U_N cancels here.
- **q²** = ½ Σ_{q≥z} N/q² ≤ N/(2(z − 1)). Normalized: log²N/(2 M U_c (N^{1/22} − 1)) **≤ 8.80·10⁻⁵**. It is decreasing for log N > 44.
- **Monotonicity in N.**
  - c_π(X_LS) is valid for all N ≥ X_LS.
  - 1.3841/(√N log log N) is decreasing.
  - The powers log^{B−2}, log^{B−3} and log^{B−1} increase, since B > 3.
  - δ_V, z/(z−1) and the slice Mertens terms decrease.
  - ε, s and s_min do not depend on N.

  So evaluating everything at N = X_LS bounds all N ≥ X_LS.

**Net:** 0.002683 − 0.001194 ≥ **0.001489 > 0**. Hence π₄(N) > 0.001489 · 22 U_N N/log²N for all even N ≥ 10^170.

---

## 5. Script facts

- **No float, no math module.** An AST check of the file finds no float literal, no float() call and no import other than decimal and fractions.
- **Arithmetic.** Intervals of Decimal at 90 digits, with every rounding operation in a localcontext set to ROUND_FLOOR or ROUND_CEILING. Negation uses copy_negate, which is exact; plain unary minus rounds in the default context and was a second instance of R17 finding 5.
- **π enclosure.** The arctan series uses exact integer denominators.
- **Integer conditions.** All integer conditions, such as moduli ≤ √X_lo and y⁴ ≤ X_lo, are exact int comparisons.
- **Mechanical audit.** At import, the default Decimal context traps `Inexact` and `Rounded`, so any rounding outside a directed context aborts the run. The two heuristic contexts are marked HEURISTIC and switch off the traps: one picks a scaling exponent and one picks k in exp. Their results are re-verified in interval arithmetic.
- **Assertions.** Every inequality used above is asserted. No assert is disabled.
- **Benchmark 0.** It reproduces the K values in the proof of [JS] Theorem 1.4 and the coefficient of [JS] Theorem 5.9 at their parameters. With their ε = 1.312·10⁻² × 559 it gives 1.4890. With the Regime-3 lookup (row 76, ε' = 1/76, C₂ = 559) it gives 1.4456. Both are asserted > 1.4; [JS] report 1.48.

---

## 6. Literature, as read

- **[JS] v3.** Theorem 1.3: every even N ≥ 4 is p + η with η having at most 395 prime factors (unconditional). Theorem 1.4: under GRH, at most 31. Inside the proof of Theorem 1.4: 17 for N ≥ exp(exp(5.077)) under GRH, and 25 for N < exp(104). The old header said "Theorem 1.3: K = 25 (N ≥ 4), K = 17 for large N, unconditional". That was wrong.
- **[JS] Remark after Theorem 4.2.** "The restriction $M\geq 5$ is so that the condition $\frac{N^{1/2-\alpha}}{\log^{2\alpha_1}N}\geq z^2$ can be satisfied. This also means that our approach works for at best $K=4$ prime factors." Theorem 1 here uses switching (the A_q terms) on top of that approach to reach K = 4 for all N ≥ 4 under GRH.
- **[BJS] v6.** Theorem 3: π₂(N) > 2·10⁻⁴ U_N N/log²N for N > exp(exp(32.7)). Corollary 4: Chen with squarefree η for N > exp(exp(32.7)). Theorem 5: every even N ≥ 4 is p + (product of at most e^{29.3} primes).
- **[BS] v1.** Corollary 1: under GRH, Chen for N > exp(exp(15.85)).
- **Removed.** The old comparisons "Rényi 1 + K, K = 4 / Yamada 2015 for N ≥ exp(exp(36))" and "Deshouillers 1976, 1 + 3 under GRH" were removed. [BJS] describes Yamada's unpublished attempt at Chen's theorem as containing mistakes, and no source for a 1 + 3 or 1 + 4 statement was read.

---

## 7. Known gaps (for the verifier)

1. **Regime-3 margin is thin.** The net is 0.001489 against a subtracted q-sum of 0.973. Its ε'C₁e²h part is ≈ 0.12. The proof depends on [BJS] v6 Table 1 row 100 being right (C₁ = 276, C₂ = 277) and on the table being read as stated (§0.1). An earlier version of the table, reproduced in [BS] v1 with ε < 1/63, has other values (row 76: 635/636; row 114: 247/249). Those older values were what the R17 script used. That version of [BJS] itself was not read.
2. **Proof of [BJS] Theorem 6 not re-checked.** Only its statement, Table 1 and the definitions of C_i (Lemma 14) were read.
3. **Not read in primary form.** Schoenfeld 1976 (used as quoted in [BS] Lemma 1, for x ≥ 3), Robin, Büthe, Oliveira e Silva–Herzog–Pardi, and Cai's Lemma 2. Each is used as quoted by [BS], [JS] or [BJS].
4. **The cyclotomic discriminant bound** log Δ ≤ φ(q) log q, used only in the consistency check of [JS] Lemma 5.1 against Grenié–Molteni, was not read from a source. [JS] Lemma 5.1 itself is used as quoted.
5. **Regime 2's analytic Bonferroni bounds** (e_{m+1} ≤ S₁^{m+1}/(m+1)!, the truncation sign) are proved in §2 and checked by R17 v2. They are not from a source.

---

## Answers to R17

| # | Finding | What was changed, and where |
|---|---|---|
| 1 | BJS sieve not quoted | Theorem 6 of arXiv:2207.09452v6 is quoted verbatim in §0.1: both bounds, ε and its range, the quantifier "for all n and 1<u<z", h(s), R, X_A and the Table-1 semantics. The table in the script (`BJS_TABLE`) is the v6 table. The old table was the one printed in arXiv:2211.08844v1 (an earlier BJS version, ε < 1/63). The theorem is applied at ε' = 1/k, with C₁ in the upper bound and C₂ in the lower bound (§0.1, §4.2–4.3, `lookup_BJS`). |
| 2 | ε hypothesis | The source has a fixed upper endpoint z and all 1 < u < z, so the w₁ = 41, w₂ = 42 test does not apply. The hypothesis is now proved for all u and all z ≥ z₀ (§4.2): ε ≤ 8.53·10⁻³, row 100, ε' = 1/100. Regime 3 still holds at 10^170, with net 0.001489 (was 0.031666). |
| 3 | Benchmark 0 | Cause: two different versions of the BJS table. [JS] v3 uses 559 = C at ε⁻¹ = 76 in v6. The script's 636 came from the older table in [BS] v1. The benchmark now uses the same lookup as Regime 3 and asserts positivity in both forms: 1.4890 and 1.4456 (§5, `verify_benchmark_0`). |
| 4 | ω(N) elements | A := {N − p : p ∤ N}, as in [JS] and [BJS], so every element is coprime to N and (1.1) needs no correction. The ω(N) appears explicitly in (∗) via \|A\| = π(N) − ω(N), and the −1 is removed (§1; `r_coeff_iv`, `err_per_d_norm`, c₄G). |
| 5 | GRH bound for π(x;q,a) | One source quoted: [JS] v3 **Lemma 5.1** (TeX label `epilem`). Range x ≥ X₂ ≥ 4·10^18, 3 ≤ q ≤ √x, (a,q) = 1, main term li(x) with li(2) absorbed. It was checked against Grenié–Molteni v3 Cor. 1.2 (§0.2). The 1/(16π) and ω(N) terms are derived in (∗). The script asserts X₂ ≥ 4·10^18 and moduli in [3, √X_lo]. |
| 6 | Interval arithmetic | `_atan_inv_iv` now uses exact int denominators. Moduli checks are exact int comparisons. A further defect was found and fixed: unary minus on Decimal rounds in the default context; it is now replaced by copy_negate. The default context now traps Inexact and Rounded for the whole run (§5). |
| 7 | Note ≠ code | §3–§4 now describe exactly what the code does. Regime 3 uses the BJS upper bound F + ε'C₁e²h with pre-sieve; slabs 1–4 sieve A_q exactly by Q₁. Selberg Λ², "trivial sieve", `PRIMES_BIG`, P_sub and log-spaced slices are gone. |
| 8 | Smaller items | Mertens bounds: quoted with their ranges ([JS] Lemma 3.2, [BJS] Lemma 16) and each used only inside its range (`mertens_ub_err`). "JS Lemma 3.2" is correct for v3. V(z): the old citation "2211.08844 Lemma 9" was wrong (Lemma 9 is a bilinear form). [BJS] Lemma 38 is now used, and U_N is defined (§0.5). \|A_{q²}\|: proved ≤ N/q² (distinct integers in [1, N−1]; §1), so +1 is not needed. Lemma 2: rewritten with the correct normalisation and the positivity condition (§2). Regime 3: the R1/R2/rq/q² decomposition and the monotonicity of each piece are written out (§4.4). Literature: corrected (§6). Benchmark numbering: "Theorem 5.6" is Theorem 5.9 in v3, and the GRH result is Theorem 1.4. The 1.25506 branch of `pi_ub_iv` was unsourced and unreachable, and is removed. |
