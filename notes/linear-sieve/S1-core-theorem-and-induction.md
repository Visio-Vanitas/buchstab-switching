> Errata applied after review: the constancy statement in (S2); the threshold 1/78.6 in S.6 item 2. Still to fix: Step 9 should cite (h2) of Step 7, not Step 8; three printed digits in the script's expected-output comments.

# Core section: the explicit β = 2 linear sieve under the all-levels product hypothesis

**Summary of findings.**
- The bound on $T_n$ and both $G$-bounds are proved under a hypothesis on **all real intervals** $[u,w)$ with $1<u<w\le z$. For prime data this is equivalent to a **closed prime-interval** condition. All recursion and summation-by-parts steps are written out in full.
- One displayed lemma of [BJS] is false as stated even under the strong hypothesis: Lemma `lem:hsm1` needs $\gamma_{s_0}=e^{s_0-1.8}$, not $e^{s_0-2}$.
- The tabulated $\tau_n$ (Table `tab:tau`) cannot be the $\tau_n$ defined by [BJS] (`eq:tau`): that definition forces $\tau_2>9.7$, while the table says 8.
- Consequently Table `tab:fF` (the $C_i$ that the frame note uses) is **not established** by the argument in the TeX. A script that decides whether it is even consistent is supplied.

---

## Statement

### S.0 Setting and notation

- **(S1)** $\mathbb P$ is a set of primes and $g:\mathbb P\to[0,1)$. For squarefree $d$ whose prime factors all lie in $\mathbb P$, put $g(d)=\prod_{p\mid d}g(p)$, with $g(1)=1$.
- **(S2)** For real $w>0$, $V(w):=\prod_{p\in\mathbb P,\,p<w}(1-g(p))$; the empty product is 1. Properties:
  - $V$ is positive, nonincreasing, and constant on every interval $[a,b]$ with $\mathbb P\cap[a,b)=\emptyset$.
  - For $p\in\mathbb P$ put $V(p^+):=V(p)(1-g(p))=\prod_{q\in\mathbb P,\,q\le p}(1-g(q))$.
  - $V(p^+)=V(w)$ for every $w\in(p,p']$, where $p'$ is the next element of $\mathbb P$ (or for all $w>p$ if there is none).
- **(S3)** For real $1<u<w$: $\;V(u)/V(w)=\prod_{p\in\mathbb P,\;u\le p<w}(1-g(p))^{-1}$.
- **(S4)** $z\ge2$ is real, $P(z):=\prod_{p\in\mathbb P,\,p<z}p$, $D>0$ is real and $s:=\log D/\log z$.
- **(S5)** $T_n(D,z)$ is [BJS] (`eq: def-T-n-D-z`). With $y_m=(D/p_1\cdots p_m)^{1/2}$ we have $p_m<y_m\iff p_1\cdots p_{m-1}p_m^3<D$ (all quantities are positive). Hence
$$T_n(D,z)=\sum_{(p_1,\dots,p_n)}g(p_1\cdots p_n)V(p_n),$$
where the sum is over $p_i\in\mathbb P$ satisfying:
  - (a) $z>p_1>\dots>p_n$;
  - (b) $p_1\cdots p_{n-1}p_n^3\ge D$;
  - (c) $p_1\cdots p_{m-1}p_m^3<D$ for every $m<n$ with $m\equiv n\pmod 2$.

### S.1 The hypothesis: which form, and how the forms relate

**Definition 1.** Let $z\ge2$ and $K\ge1$.

- **H(z,K)** (real endpoints, half-open): $V(u)/V(w)\le K\log w/\log u$ for **all real** $u,w$ with $1<u<w\le z$.
- **C(z,K)** (closed prime intervals): for all $p\le q$ in $\mathbb P$ with $q<z$,
$$\Pi[p,q]:=\prod_{r\in\mathbb P,\ p\le r\le q}(1-g(r))^{-1}\le K\,\frac{\log q}{\log p}.$$
  The case $p=q$ reads $(1-g(p))^{-1}\le K$.
- $K_*(z):=\max\bigl(1,\ \max_{p\le q<z;\ p,q\in\mathbb P}\Pi[p,q]\log p/\log q\bigr)$. This is a finite maximum.

**Lemma 0.**
- (a) H(z,K) ⟺ C(z,K).
- (b) (Heredity) H(z,K) ⟹ H(z′,K) for every $2\le z'\le z$.
- (c) For $K\ge1$: H(z,K) ⟺ $K\ge K_*(z)$. Hence "H(z,K) for some $K\in[1,1+\varepsilon)$" ⟺ $K_*(z)<1+\varepsilon$.
- (d) The [BJS] hypothesis (`eq:prod11`) is H(z,K) restricted to $w=z$. It is **not** hereditary. Example: $\mathbb P=\{41,43\}$, $g(p)=1/(p-1)$ with $z$ large satisfies it with $K$ close to 1 for $z$ large, while the level $w=43^+$ requires $K\ge \Pi[41,43]\log41/\log43=1.0374$.

**Decision.**
- The theorems below are stated under H(z,K), equivalently C(z,K).
- The proof uses H at the following levels:
  - the current top of every induction stage, which is $z$ or a prime $p_k<z$;
  - the **real** levels $w=D_k^{1/3}$, $D_k:=D/(p_1\cdots p_k)$;
  - the pairs $(u,w)=(D_k^{1/3},\text{top})$.

  Steps 10 and 14 make this list precise.
- Quantified over all real $D$, the real levels $D_k^{1/3}$ sweep every $w$ just above a prime. That is why the closed form, not the half-open form at prime levels, is the condition that matters.
- The half-open-at-prime-levels form is strictly weaker. Example: $\mathbb P=\{41\}$, $z=42$, $g(41)=1/40$. It needs only $K\ge(40/39)\log41/\log42=1.0190$, while C needs $K\ge40/39=1.0256$. I do **not** prove the theorems under that weaker form.

### S.2 Functions and constants (all as in [BJS], with one correction)

**The functions $h$ and $H$.**
- $h(s)=e^{-2}$ on $[1,2]$, $e^{-s}$ on $[2,3]$, and $3e^{-s}/s$ on $[3,\infty)$.
- $H(s)=\int_s^\infty h(t-1)\,dt$ for $s\ge2$.

**The functions $f_n$** ([BJS] `eq:f11`, `eq:f22`, `eq:odd`).
- $sf_1(s)=3-s$ on $[1,3]$, and $f_1=0$ on $(3,\infty)$.
- For $n\ge2$ even and $s\ge2$, and for $n\ge3$ odd and $s\ge3$: $sf_n(s)=\int_s^\infty f_{n-1}(t-1)dt$.
- For $n\ge3$ odd and $1\le s\le3$: $sf_n(s)=\int_3^\infty f_{n-1}(t-1)dt$.

**The constants.**
- $\kappa_2=0.9607$, $\kappa_{2.2}=0.9557$, $\kappa_{2.4}=0.9457$, $\kappa_{2.6}=0.9261$, $\kappa_{2.8}=0.8914$, $\kappa_3=0.8349$, and $\tilde\kappa=0.9214$.
- $\Sigma:=\{2,2.2,2.4,2.6,2.8,3\}$.
- **$\gamma_{s_0}:=e^{s_0-1.8}$ for $s_0\in\{2,\dots,2.8\}$ (corrected; [BJS] prints $e^{s_0-2}$)**, and $\gamma_3:=4e/3$.

**Admissible sequence $(c_n)$.** Positive numbers with
$$\textbf{(Fn)}\qquad f_n(s)\le 2e^2c_n^{\,n-1}h(s)\quad(s\ge1\text{ if $n$ odd},\ s\ge2\text{ if $n$ even}).$$
- $c_1=1$ and $c_n=0.9607$ for $n\ge2$ is admissible; this is proved in Step 8.
- The [BJS] Table `tab:cn1` values are an unverified computational input.

**The numbers $\tau_n$.** Put $\tau_1=3$. For $n\ge2$, with $\xi_{s_0},\tilde\xi$ exactly as printed after (`eq:tau`) but using the corrected $\gamma_{s_0}$:
$$\xi_{s_0}=\kappa_{s_0}+(\gamma_{s_0}+\kappa_{s_0})\varepsilon+2\gamma_{s_0}\frac{c_{n-1}^{\,n-2}}{\tau_{n-1}}+2\frac{c_n^{\,n-1}}{\tau_{n-1}},\qquad
\tilde\xi=\tilde\kappa+(5+4\varepsilon)\varepsilon+6(1+\varepsilon)\frac{c_{n-1}^{\,n-2}}{\tau_{n-1}}+2(2+\varepsilon)\frac{c_n^{\,n-1}}{\tau_{n-1}}.$$
Then:
- $\tau_n=\tau_{n-1}\max_{s_0\in\Sigma}\xi_{s_0}$ for $n$ even;
- $\tau_n=\tau_{n-1}\max(\xi_3,\tilde\xi)$ for $n$ odd;
- $h_n(s):=\varepsilon\tau_ne^2h(s)$;
- $C_1:=\sum_{n\text{ odd}}\tau_n$ and $C_2:=\sum_{n\text{ even}}\tau_n$, each in $(0,\infty]$.

### S.3 Theorem A (the $T_n$ bound)

Let $\varepsilon>0$, let $1\le K<1+\varepsilon$, and let $(c_n)$ be admissible. Then the following holds for every:
- $n\ge1$;
- real $z\ge2$;
- real $D$ with $s\ge1$ ($n$ odd) or $s\ge2$ ($n$ even);
- $(\mathbb P,g)$ satisfying H(z,K).

Conclusion:
$$T_n(D,z)<V(z)\bigl(f_n(s)+h_n(s)\bigr)=V(z)\bigl(f_n(s)+\varepsilon\tau_ne^2h(s)\bigr).$$

The $\tau_n$ depend only on $\varepsilon$ and $(c_n)$. The task statement wrote "$\varepsilon\tau_ne^2h_n(s)$"; the correct form is the one displayed here.

### S.4 Rosser weights and Theorem B

**Definition of the weights.** Fix $D>1$. For a squarefree $d\mid P(z)$, write $d=p_1\cdots p_r$ with $p_1>\dots>p_r$.
- $d\in\mathcal D^+$ iff $p_1\cdots p_{m-1}p_m^3<D$ for every **odd** $m\le r$.
- $d\in\mathcal D^-$ iff the same holds for every **even** $m\le r$.
- Note $1\in\mathcal D^\pm$.
- $\lambda^\pm(d):=\mu(d)\mathbf 1_{\mathcal D^\pm}(d)$, and $G(z,\lambda^\pm):=\sum_{d\mid P(z)}\lambda^\pm(d)g(d)$.

This is the standard Rosser–Iwaniec construction with $\beta=2$. I have not checked that it is literally Nathanson's Thm 9.3 (the book is not in the packet). Nothing below depends on that.

**Theorem B.** For all real $D>1$ and $z\ge2$:
- (i) $G(z,\lambda^+)=V(z)+\sum_{n\text{ odd}}T_n(D,z)$ and $G(z,\lambda^-)=V(z)-\sum_{n\text{ even}}T_n(D,z)$. Both sums are finite.
- (ii) For every integer $m\ge1$:
$$\sum_{d\mid (m,P(z))}\lambda^-(d)\le\mathbf 1_{(m,P(z))=1}\le\sum_{d\mid(m,P(z))}\lambda^+(d).$$
- (iii) $|\lambda^\pm|\le1$. If $\lambda^+(d)\ne0$ then $d<D$. If $z\le D$ and $\lambda^-(d)\ne0$ then $d<D$.

### S.5 Theorem C (corrected Prop. `theo:G`) and the external input

Put $\tilde F(s):=1+\sum_{n\text{ odd}}f_n(s)$ for $s\ge1$, and $\tilde f(s):=1-\sum_{n\text{ even}}f_n(s)$ for $s\ge2$. Both series converge (Step 8).

**Theorem C.** Assume the hypotheses of Theorem A (in particular H(z,K)).
- (i) If $s\ge1$ and $C_1<\infty$: $\;G(z,\lambda^+)<V(z)\bigl(\tilde F(s)+\varepsilon e^2h(s)C_1\bigr)$.
- (ii) If $s\ge2$ and $C_2<\infty$: $\;G(z,\lambda^-)>V(z)\bigl(\tilde f(s)-\varepsilon e^2h(s)C_2\bigr)$.
- (iii) If $0<\varepsilon\le1/74$ and $\sup_{n\ge2}c_n<1$ (for example $c_n=0.9607$), then $C_1,C_2<\infty$.

**EXTERNAL INPUT E1** (Nathanson Thm 9.4, cited by [BJS] as (`bigFdeffn`), (`lilFdeffn`); the book was not read). $\tilde F=F$ on $[1,\infty)$ and $\tilde f=f$ on $[2,\infty)$, where $F,f$ are the functions of [BJS] (`def-f(s)-F(s)`). [BJS] (`lilFdeffn`) prints "$n$ odd"; it must read "$n$ even". Step 17 proves that E1 is equivalent to two numerical facts: $3\tilde F(3)=2e^\gamma$ and $\tilde f(2)=0$.

**Corollary D** (Theorem C + E1). Under H(z,K):
- for $s\ge1$: $G(z,\lambda^+)<V(z)(F(s)+\varepsilon C_1e^2h(s))$;
- for $s\ge2$: $G(z,\lambda^-)>V(z)(f(s)-\varepsilon C_2e^2h(s))$.

Here $C_i$ are the sums of the corrected $\tau_n$. **The numerical values of Table `tab:fF` are not established by this proof** (see S.6, item 6).

### S.6 Where [BJS] must be corrected (proved in Steps 7, 13, 14, 18)

1. **Hypothesis.** (`eq:prod11`)/(`eq:cond1`) must be H(z,K) (all $1<u<w\le z$), not $w=z$ only.
2. **Lemma `lem:hsm1` is false as stated.** For $2\le s\le s_0+0.2\le3$ one has $h(s-1)/h(s)=e^{s-2}$. Its maximum on $[s_0,s_0+0.2]$ is $e^{s_0-1.8}>e^{s_0-2}$, attained at $s=s_0+0.2$. The correct constant is $\gamma_{s_0}=e^{s_0-1.8}$. With this value:
   - the [BJS] Remark ($\gamma_2=e^{0.2}$) is consistent;
   - the thresholds "$\varepsilon\le1/54$" and "$\varepsilon\le1/74$" in Lemma `lem: taup` are consistent. With the printed $\gamma_2=1$ the second threshold would be $\approx1/78.6$.
3. **Case $n$ odd, $s<3$.** The display has $(c_n)^{n-2}$; it must be $(c_{n-1})^{n-2}$. The definition of $\tilde\xi$ is correct and its $\varepsilon$-coefficient $(5+4\varepsilon)$ is a valid upper bound.
4. **Proof of Lemma `lemma:forg`** writes "$\tfrac13e^{-s}H(s)$"; it must be $\tfrac13e^{s}H(s)$. The constants $\kappa_{s_0}$ and $\tilde\kappa$ are correct (certified by the script, Part 1).
5. **Table `tab:tau` is inconsistent with (`eq:tau`).** For $n=2$ the maximum includes $\xi_3$. So for every $\varepsilon>0$ and every $c_2\ge0$:
$$\tau_2\ge\tau_1\xi_3\ge3\kappa_3+2\gamma_3=2.5047+7.2487>9.75,$$
   whereas the table lists $\tau_2=8$. With the [BJS] $c_n$ and $\varepsilon=1/200$, $\tau_2=10.4803\ldots$ and $\tau_3=12.519\ldots$; the table lists 8 and 10.
6. **Consequence of item 5.** Table `tab:fF` ($C_1(1/100)=276$, the value the frame note uses) is not implied by the printed argument.
   - A hand iteration of the printed recursion gives $\sum_{n\text{ odd}}\tau_n\approx3.4\cdot10^2$ at $\varepsilon=1/100$ and $\approx1.9\cdot10^2$ at $\varepsilon=1/200$. Table 1 lists 276 and 153.
   - This is uncertified; the script (Part 2) gives rigorous lower bounds that decide it.

---

## Proof

**Step 1 (Lemma 0).**

*(a), H ⟹ C.* Let $p\le q<z$ be in $\mathbb P$. Let $w_0:=\min(z,q')$, where $q'$ is the next element of $\mathbb P$ after $q$ ($q'=\infty$ if none). Then $w_0>q$.
- For $w\in(q,w_0]$ we have $\mathbb P\cap[p,w)=\mathbb P\cap[p,q]$, because $\mathbb P\cap(q,w)=\emptyset$ and $w$ itself is excluded.
- So by (S3) and H with $(u,w)=(p,w)$, where $1<p<w\le z$: $\Pi[p,q]\le K\log w/\log p$ for every $w\in(q,w_0]$.
- Letting $w\downarrow q$ gives $\Pi[p,q]\le K\log q/\log p$.

*(a), C ⟹ H.* Let $1<u<w\le z$ and $S:=\mathbb P\cap[u,w)$.
- If $S=\emptyset$: $V(u)/V(w)=1<\log w/\log u\le K\log w/\log u$.
- Otherwise let $p=\min S\ge u$ and $q=\max S<w\le z$. Then $V(u)/V(w)=\Pi[p,q]\le K\log q/\log p\le K\log w/\log u$, because $0<\log u\le\log p$ and $\log q<\log w$.

*(b)* The quantifier set of H(z′,K) is contained in that of H(z,K).

*(c)* By (a), for $K\ge1$, H(z,K) holds iff $K\ge\Pi[p,q]\log p/\log q$ for all pairs. The set of pairs is finite because $P(z)$ is a finite product.

*(d)* The example is computed directly: $\Pi[41,43]=\frac{40}{39}\cdot\frac{42}{41}=1.050657$ and $\log41/\log43=0.98734$. ∎

**Step 2 (telescoping).** Let $1<a<W$ and let $q_1<\dots<q_m$ be the elements of $\mathbb P\cap[a,W)$. Then:
- $g(q_i)V(q_i)=V(q_i)-V(q_i^+)$, with $V(q_i^+)=V(q_{i+1})$ for $i<m$ and $V(q_m^+)=V(W)$, by (S2).
- Hence $\sum_{p\in\mathbb P\cap[a,W)}g(p)V(p)=V(a)-V(W)$, using $V(q_1)=V(a)$.
- Also $\sum_{e\mid P(w)}\mu(e)g(e)=\prod_{p\in\mathbb P,p<w}(1-g(p))=V(w)$ (expand the finite product).

**Step 3 ($T_1$).**
- For $n=1$, conditions (c) are void and (b) reads $p_1^3\ge D$.
- So $T_1(D,z)=\sum_{p\in\mathbb P,\ D^{1/3}\le p<z}g(p)V(p)$.
- By Step 2 this equals $V(D^{1/3})-V(z)$ if $D^{1/3}<z$ (and $D^{1/3}>1$), and $0$ if $D^{1/3}\ge z$.

**Step 4 (recursion, exact side conditions).** For $n\ge2$, real $z\ge2$ and $D>0$:
$$T_n(D,z)=\sum_{\substack{p\in\mathbb P,\ p<z\\ p^3<D\text{ if $n$ odd}}}g(p)\,T_{n-1}(D/p,\,p).$$
*Proof.* In (S5) put $p=p_1$, $D'=D/p_1$ and $q_j=p_{j+1}$ for $j=1,\dots,n-1$. Then:
- (a) becomes $z>p_1$ together with $p_1>q_1>\dots>q_{n-1}$.
- (b) becomes $q_1\cdots q_{n-2}q_{n-1}^3\ge D'$.
- For $m\ge2$, condition (c) becomes $q_1\cdots q_{m'-1}q_{m'}^3<D'$ with $m'=m-1$. As $m$ runs over $\{2,\dots,n-1\}$ with $m\equiv n$, $m'$ runs over $\{1,\dots,n-2\}$ with $m'\equiv n-1$.
- The only condition left on $p_1$ is (c) at $m=1$. It is present iff $1\equiv n\pmod2$, i.e. $n$ odd, and reads $p_1^3<D$.
- Multiplicativity gives $g(p_1\cdots p_n)=g(p_1)g(q_1\cdots q_{n-1})$ and $V(p_n)=V(q_{n-1})$.

So the inner sum is exactly $T_{n-1}(D',p_1)$. ∎

**Step 5 (Lemma A, partial summation).** Let $W>2$ and $K\ge1$. Let $\varphi:[2,W]\to[0,\infty)$ be nondecreasing. Assume
$$V(q)/V(W)\le K\log W/\log q\quad\text{for every } q\in\mathbb P,\ q<W.$$
Then
$$\Sigma:=\sum_{q\in\mathbb P,\,q<W}g(q)V(q)\varphi(q)\le V(W)\Bigl[(K-1)\varphi(W)+K\int_2^W\varphi(t)\frac{\log W\,dt}{t\log^2t}\Bigr].$$

*Proof.* If there are no such $q$, then $\Sigma=0\le$ RHS. Otherwise let $q_1<\dots<q_m$ be these primes, put $V_{m+1}:=V(W)$, $\varphi_i=\varphi(q_i)$ and $c_i:=\log W/\log q_i$.

1. By Step 2, $\Sigma=\sum_{i=1}^m(V(q_i)-V(q_{i+1}))\varphi_i$, where $V(q_{m+1})$ means $V(W)$.
2. Abel summation:
$$\Sigma=V(q_1)\varphi_1+\sum_{i=2}^mV(q_i)(\varphi_i-\varphi_{i-1})-V(W)\varphi_m.$$
   Check: $\sum_iV(q_i)\varphi_i-\sum_{j=2}^{m+1}V(q_j)\varphi_{j-1}$ gives exactly these terms.
3. The coefficients $\varphi_1$ and $\varphi_i-\varphi_{i-1}$ are $\ge0$, so each $V(q_i)$ may be replaced by its upper bound $KV(W)c_i$. The only negative term is $-V(W)\varphi_m$. It contains $V$ at the level $W$ itself and is kept exactly.
4. Abel again: $c_1\varphi_1+\sum_{i\ge2}c_i(\varphi_i-\varphi_{i-1})=c_m\varphi_m+\sum_{i<m}(c_i-c_{i+1})\varphi_i$.
5. Since $\frac{d}{dt}\frac1{\log t}=-\frac1{t\log^2t}$:
   - $c_i-c_{i+1}=\int_{q_i}^{q_{i+1}}\frac{\log W\,dt}{t\log^2t}\ge0$;
   - $c_m=1+\int_{q_m}^W\frac{\log W\,dt}{t\log^2t}$.

   Monotonicity gives $\varphi_i\le\varphi(t)$ on $[q_i,q_{i+1}]$ and $\varphi_m\le\varphi(t)$ on $[q_m,W]$. So the bracket in step 4 is at most $\varphi_m+\int_{q_1}^W\varphi(t)\frac{\log W\,dt}{t\log^2t}$.
6. Therefore $\Sigma\le V(W)[(K-1)\varphi_m+K\int_{q_1}^W\cdots]$. Since $K-1\ge0$ and $\varphi_m\le\varphi(W)$, and $\int_{q_1}^W\le\int_2^W$ (the integrand is $\ge0$), the claim follows. ∎

**Step 6 (Corollary A′).** Let $D>1$ and $W>2$, put $\sigma:=\log D/\log W$, and let $\Psi:[\sigma_0,\infty)\to[0,\infty)$ be nonincreasing with $\sigma-1\ge\sigma_0$. Put $\varphi(t):=\Psi(\log D/\log t-1)$ for $t\in[2,W]$. Then:
- The argument $\log D/\log t-1$ decreases in $t$ (since $\log D>0$) and is $\ge\sigma-1\ge\sigma_0$. So $\varphi$ is well defined, nondecreasing and $\ge0$.
- Substitute $x=\log D/\log t$. Then $\frac{1}{\log t}=\frac{x}{\log D}$, so $\frac{\log W\,dt}{t\log^2t}=-\frac{\log W}{\log D}dx=-\frac{dx}{\sigma}$. As $t$ runs over $2\to W$, $x$ runs over $\log D/\log2\to\sigma$.
- Hence, if Lemma A's hypothesis holds,
$$\Sigma\le V(W)\Bigl[(K-1)\Psi(\sigma-1)+\frac K\sigma\int_\sigma^{\infty}\Psi(x-1)\,dx\Bigr].\tag{6.1}$$
- Note $\varphi(W)=\Psi(\sigma-1)$, and enlarging the upper limit to $\infty$ is allowed because the integrand is $\ge0$.

**Step 7 (facts about $h$ and $H$).**
- **(h0)** $h>0$, $h$ is continuous ($e^{-2}$ at 2; $e^{-3}=3e^{-3}/3$ at 3) and nonincreasing.
- **(h1) Corrected `lem:hsm1`.**
  - For $2\le s\le3$: $s-1\in[1,2]$, so $h(s-1)/h(s)=e^{-2}/e^{-s}=e^{s-2}$. Hence $h(s-1)\le e^{s_0-1.8}h(s)$ on $[s_0,s_0+0.2]$ when $s_0\le2.8$, with equality at $s=s_0+0.2$. The printed $e^{s_0-2}$ is false there.
  - For $3\le s\le4$: $h(s-1)/h(s)=e^{1-s}/(3e^{-s}/s)=es/3\le4e/3$.
  - For $s\ge4$: $h(s-1)/h(s)=es/(s-1)\le4e/3$.
- **(h2)** For $1\le s\le3$: $\frac3sh(2)\le3h(s)$, i.e. $e^{-2}/s\le h(s)$.
  - On $[1,2]$: $1/s\le1$.
  - On $[2,3]$: this is $e^{s-2}\le s$. The function $e^{s-2}-s$ is convex and $\le0$ at both $s=2$ and $s=3$ ($1-2$ and $e-3$), so it is $\le0$ throughout.
- **(h3) Closed forms.** With $E_1(x)=\int_x^\infty e^{-t}t^{-1}dt$:
  - For $2\le s\le3$: $H(s)=(3-s)e^{-2}+(e^{-2}-e^{-3})+3E_1(3)=C-se^{-2}$, where $C:=4e^{-2}-e^{-3}+3E_1(3)$.
  - For $3\le s\le4$: $H(s)=e^{1-s}-e^{-3}+3E_1(3)$.
  - For $s\ge4$: $H(s)=3E_1(s-1)$.
- **(h4) The bound $H(s)\le\kappa_{s_0}sh(s)$ for $s\ge s_0$.**
  - On $[2,3]$ put $\phi(s)=e^sH(s)/s=H(s)/(sh(s))$. Then $\phi'(s)=\frac{e^s}{s^2}q(s)$ with $q(s)=(s-1)C-s^2e^{-2}$.
  - The discriminant of $q$ is $C(C-4e^{-2})=C(3E_1(3)-e^{-3})<0$, using $C>0$ and P1a of the script. The leading coefficient is negative, so $q<0$ and $\phi$ is decreasing.
  - On $[3,4]$: $H/(sh)=\frac13e^sH=\frac{e-e^{s-3}}3+e^sE_1(3)$, whose derivative is $e^{s-3}(-\frac13+e^3E_1(3))<0$ by P1b. Its value at 3 equals $\phi(3)$.
  - On $s\ge4$: integrate by parts three times to get $E_1(x)=e^{-x}(\frac1x-\frac1{x^2}+\frac2{x^3})-6\int_x^\infty e^{-t}t^{-4}dt$. Hence $E_1(x)\le e^{-x}(\frac1x-\frac1{x^2}+\frac2{x^3})$, and the bracket is decreasing (its derivative is $-(x^2-2x+6)/x^4$). This gives $\frac13e^sH(s)\le e\cdot\frac8{27}$ (P1e).
  - Hence $H(s)\le\phi(s_0)sh(s)$ on $[s_0,3]$, and $H(s)\le\max(\phi(3),8e/27)\,sh(s)$ on $[3,\infty)$.
  - Script P1c certifies $\phi(s_0)\le\kappa_{s_0}$, and $\kappa_3\le\kappa_{s_0}$. This proves the claim.
- **(h5)** $H(3)=H(2)-\int_1^2h=H(2)-e^{-2}=(2\alpha-1)e^{-2}$, where $\alpha=\phi(2)$. For $s\in[1,2]$, $sh(s)\ge e^{-2}$. For $s\in[2,3]$, $sh(s)\ge3e^{-3}$ and $(2\alpha-1)e/3<2\alpha-1$. So $H(3)\le(2\alpha-1)sh(s)\le\tilde\kappa\,sh(s)$ on $[1,3]$ (P1d).

**Step 8 (facts about $f_n$).** By induction on $n$:
- $f_n\ge0$, $f_n$ is bounded, nonincreasing and continuous on its domain, and $f_n=0$ on $[n+2,\infty)$.
- For $f_1$ this is immediate.
- Even $n$, or odd $n$ on $[3,\infty)$: $f_n=\frac1s\cdot$(a nonincreasing nonnegative integral).
- Odd $n$ on $[1,3]$: $f_n=3f_n(3)/s$, which matches at $s=3$.

*Admissibility of $c_n=0.9607$* (proves [BJS] Lemma `lemma:f_n` from Step 7):
- $n=1$: $f_1\le2e^2h$, i.e. $(3-s)/s\le2$ on $[1,2]$ and $(3-s)/s\le2e^{2-s}$ on $[2,3]$. Both hold, since the left side is $\le\frac12$ on $[2,3]$ and the right side is $\ge2/e$.
- If $f_{n-1}\le2e^2\kappa_2^{n-2}h$ on its domain, then:
  - for $n$ even and $s\ge2$, or $n$ odd and $s\ge3$: $f_n(s)\le\frac1s2e^2\kappa_2^{n-2}H(s)\le2e^2\kappa_2^{n-1}h(s)$ by (h4);
  - for $n$ odd and $s\in[1,3]$: $f_n(s)\le\frac1s2e^2\kappa_2^{n-2}H(s')|_{s'=3}\le2e^2\kappa_2^{n-2}\tilde\kappa h(s)$ by (h5), and $\tilde\kappa<\kappa_2$.
- Hence $\sum_nf_n$ converges uniformly on compacta, and $\int_\sigma^\infty f_{n}(x-1)dx<\infty$.

**Step 9 (Theorem A, $n=1$).** Assume H(z,K) and $s\ge1$, so $D\ge z\ge2$ and $D^{1/3}>1$.
- If $s\ge3$: $T_1=0<V(z)h_1(s)$.
- If $1\le s<3$: $1<D^{1/3}<z$. By Step 3 and H with $(u,w)=(D^{1/3},z)$:
$$\frac{T_1}{V(z)}=\frac{V(D^{1/3})}{V(z)}-1\le\frac{3K}s-1=f_1(s)+\frac{3(K-1)}s<f_1(s)+\frac{3\varepsilon}{s}\le f_1(s)+3\varepsilon e^2h(s).$$
  The strict step uses $K-1<\varepsilon$. The last step uses $1/s\le e^2h(s)$ on $[1,3]$ (Step 8, $n=1$). This is $f_1+h_1$ since $\tau_1=3$.

**Step 10 (Theorem A, $n\ge2$: reduction, and where the sub-levels enter).** Assume Theorem A for $n-1$, for all tops, all admissible $D$, and all data satisfying H at that top. Let $z,D,s$ and $(\mathbb P,g)$ with H(z,K) be given.

*Choice of $W$.* Put $W:=z$ if $n$ is even or $s\ge3$, and $W:=D^{1/3}$ if $n$ is odd and $s<3$. Then the $p$-range in Step 4 is exactly $\mathbb P\cap[2,W)$:
- $n$ even: no extra condition.
- $n$ odd, $s\ge3$: $p<z\le D^{1/3}$ forces $p^3<D$.
- $n$ odd, $s<3$: $D^{1/3}<z$, so $\{p<z,\ p^3<D\}=\{p<D^{1/3}\}$.

If this range is empty (in particular if $W\le2$), then $T_n=0<V(z)(f_n+h_n)$, because $h_n>0$ and $V(z)>0$.

*Domain checks.* Put $\sigma:=\log D/\log W$, so $\sigma=s$ or $\sigma=3$. For $p<W$, $s'(p):=\log(D/p)/\log p=\log D/\log p-1>\sigma-1$. This gives:
- $n$ even: $s'>s-1\ge1$, the odd domain;
- $n$ odd, $s\ge3$: $s'>2$, the even domain;
- $n$ odd, $s<3$: $s'>2$.

*Application of the induction hypothesis.*
- **Sub-level use U1.** The IH at $(D/p,p)$ needs H(p,K). This follows from H(z,K) by Lemma 0(b), since $p<z$. With $\Psi:=f_{n-1}+h_{n-1}$ (nonincreasing, $\ge0$, integrable at $\infty$ by Steps 7–8) and $g(p)\ge0$:
$$T_n(D,z)\le\sum_{p\in\mathbb P,\,p<W}g(p)V(p)\Psi(s'(p)),\qquad \Psi(s'(p))=\varphi(p)\ \text{as in Step 6}.$$
- **Lemma A's hypothesis at level $W$**: $V(q)/V(W)\le K\log W/\log q$ for $q\in\mathbb P$, $q<W$. This is H(z,K) with $1<q<W\le z$.
  - For $W=z$ it is the top level.
  - **Sub-level use U2:** for $W=D^{1/3}$ it is the real level $D^{1/3}<z$.

By (6.1) we get:
- **(R1)** if $W=z$: $\dfrac{T_n}{V(z)}\le(K-1)\Psi(s-1)+\dfrac Ks\displaystyle\int_s^\infty\Psi(x-1)dx$. This is [BJS] (`Tneq`), justified.
- **(R2)** if $W=D^{1/3}$: $T_n\le V(D^{1/3})\bigl[(K-1)\Psi(2)+\frac K3\int_3^\infty\Psi(x-1)dx\bigr]$. Moreover $V(D^{1/3})\le\frac{3K}sV(z)$ by H(z,K) with $(u,w)=(D^{1/3},z)$, where $1<D^{1/3}<z$.

Write $\eta:=K-1\in[0,\varepsilon)$. Recall $h_{n-1}=\varepsilon\tau_{n-1}e^2h$, so $2e^2\varepsilon c^{k}h=2\frac{c^k}{\tau_{n-1}}h_{n-1}$.

**Step 11 (Case I: $n\ge2$, $s\ge3$; uses R1).** Here $s-1\ge2$ lies in the domain of $f_{n-1}$ for either parity.

1. $\eta f_{n-1}(s-1)\le\varepsilon2e^2c_{n-1}^{n-2}h(s-1)\le2\gamma_3\frac{c_{n-1}^{n-2}}{\tau_{n-1}}h_{n-1}(s)$, by (Fn) and (h1).
2. $\eta h_{n-1}(s-1)\le\eta\gamma_3h_{n-1}(s)<\varepsilon\gamma_3h_{n-1}(s)$. This is strict because $\gamma_3h_{n-1}(s)>0$.
3. $\frac Ks\int_s^\infty f_{n-1}(t-1)dt=Kf_n(s)$ (definition, valid for $n$ even with $s\ge2$ and $n$ odd with $s\ge3$). Then $Kf_n(s)\le f_n(s)+\varepsilon2e^2c_n^{n-1}h(s)=f_n(s)+2\frac{c_n^{n-1}}{\tau_{n-1}}h_{n-1}(s)$.
4. $\frac Ks\int_s^\infty h_{n-1}(t-1)dt=\frac Ks\varepsilon\tau_{n-1}e^2H(s)\le K\kappa_3h_{n-1}(s)\le(1+\varepsilon)\kappa_3h_{n-1}(s)$, by (h4).

Summing: $T_n/V(z)<f_n(s)+\xi_3h_{n-1}(s)$, and $\xi_3h_{n-1}=\varepsilon\tau_{n-1}\xi_3e^2h\le h_n$, because $\xi_3$ is among the maxima in both parities. These are [BJS] (`eq:Tn3`)–(`eq:Tn2`), all justified as written.

**Step 12 (Case II: $n$ even, $s\in[s_0,s_0+0.2]$, $s_0\in\{2,\dots,2.8\}$; uses R1).** Here $s-1\in[1,2]$ lies in the domain of $f_{n-1}$ ($n-1$ odd). This is the same as Step 11 with three changes:
- $\gamma_3$ is replaced by $\gamma_{s_0}=e^{s_0-1.8}$, using the corrected (h1). The printed $e^{s_0-2}$ would make item 1 false.
- $\kappa_3$ is replaced by $\kappa_{s_0}$, using (h4).
- The definition of $f_n$ for $n$ even and $s\ge2$ is used.

Result: $T_n/V(z)<f_n(s)+\xi_{s_0}h_{n-1}(s)\le f_n+h_n$. The intervals $[s_0,s_0+0.2]$ cover $[2,3]$.

**Step 13 (Case III: $n\ge3$ odd, $1\le s<3$; uses R2).** Combining R2 with $V(D^{1/3})\le\frac{3K}sV(z)$ gives
$$\frac{T_n}{V(z)}\le\frac{3K}s\eta\bigl(f_{n-1}(2)+h_{n-1}(2)\bigr)+\frac{K^2}s\int_3^\infty\bigl(f_{n-1}+h_{n-1}\bigr)(t-1)dt,$$
which is the [BJS] display, now justified. The four terms are bounded as follows; note $K\eta<(1+\varepsilon)\varepsilon$ strictly, whether or not $K=1$.

- (a) $\frac{3K}s\eta f_{n-1}(2)\le K\eta\,2e^2c_{n-1}^{n-2}\cdot\frac3sh(2)\le K\eta\,6e^2c_{n-1}^{n-2}h(s)\le6(1+\varepsilon)\frac{c_{n-1}^{n-2}}{\tau_{n-1}}h_{n-1}(s)$, by (Fn) at $s=2$ and (h2). [BJS] prints $c_n^{n-2}$ here; the correct factor is $c_{n-1}^{n-2}$, as in $\tilde\xi$.
- (b) $\frac{3K}s\eta h_{n-1}(2)\le3K\eta\,h_{n-1}(s)<3\varepsilon(1+\varepsilon)h_{n-1}(s)$, by (h2).
- (c) $\frac{K^2}s\int_3^\infty f_{n-1}(t-1)dt=K^2f_n(s)$, by the definition for odd $n$ on $[1,3]$. Then $(K^2-1)f_n(s)\le\varepsilon(2+\varepsilon)2e^2c_n^{n-1}h(s)=2(2+\varepsilon)\frac{c_n^{n-1}}{\tau_{n-1}}h_{n-1}(s)$.
- (d) $\frac{K^2}s\varepsilon\tau_{n-1}e^2H(3)\le K^2\tilde\kappa h_{n-1}(s)\le(1+\varepsilon)^2\tilde\kappa h_{n-1}(s)$, by (h5).

Combining (b) and (d): $3\varepsilon(1+\varepsilon)+(1+\varepsilon)^2\tilde\kappa=\tilde\kappa+\varepsilon(3+2\tilde\kappa)+\varepsilon^2(3+\tilde\kappa)\le\tilde\kappa+(5+4\varepsilon)\varepsilon$, since $\tilde\kappa\le1$. So
$$T_n/V(z)<f_n(s)+\tilde\xi h_{n-1}(s)\le f_n+h_n.$$
The case $s=3$ is covered by Step 11 (there $W=D^{1/3}=z$).

**Step 14 (conclusion of Theorem A; the levels actually used).** Steps 9–13 cover every case: $n=1$; $n$ even with $s\ge3$ (Step 11) and $s\in[2,3]$ (Step 12); $n$ odd with $s\ge3$ (Step 11) and $s\in[1,3)$ (Step 13). By induction, Theorem A holds.

Unfolding the induction along $(p_1,\dots,p_k)$ with $D_k=D/(p_1\cdots p_k)$, H is used:
- at the top $Z\in\{z,p_1,p_2,\dots\}$ of every stage, with $u$ prime (Lemma A, Cases I and II);
- at the real level $W=D_k^{1/3}<Z$, with $u$ prime, whenever the remaining order $n-k\ge3$ is odd and $s_k<3$ (Case III, U2);
- at $(u,w)=(D_k^{1/3},Z)$, in Case III and in the base case $n-k=1$.

The fixed-$z$ hypothesis provides only the uses with $Z=z$ and $w=z$.

**Step 15 (Theorem B).** Let $M^+=$ odd integers and $M^-=$ even integers.

*Failure prefixes.* For $n\in M^\pm$ let $\mathcal B_n^\pm$ be the set of $b=p_1\cdots p_n$ with $p_i\in\mathbb P$, $z>p_1>\dots>p_n$, such that the $\mathcal D^\pm$-condition fails at $m=n$ ($p_1\cdots p_{n-1}p_n^3\ge D$) and holds at every $m<n$ with $m\in M^\pm$. By (S5),
$$\sum_{b\in\mathcal B_n^\pm}g(b)V(p_n(b))=T_n(D,z),$$
where $p_n(b)$ is the smallest prime of $b$.

*Bijection.* $\{d\mid P(z):d\notin\mathcal D^\pm\}\leftrightarrow\{(b,e):b\in\mathcal B_n^\pm\text{ for some }n\in M^\pm,\ e\mid P(p_n(b))\}$, via $d\mapsto(b,e)$ and $(b,e)\mapsto be$.
- Forward: let $n$ be the least $m\in M^\pm$ at which $d$ fails. Put $b=$ the product of the $n$ largest primes of $d$ and $e=d/b$. Every prime of $e$ is in $\mathbb P$ and $<p_n$.
- Backward: $be$ is squarefree and divides $P(z)$. Its $n$ largest primes are those of $b$, so its first failure is at $n$.

*(i)* By Step 2 and multiplicativity,
$$\sum_{d\mid P(z)}\lambda^\pm(d)g(d)=V(z)-\sum_{n\in M^\pm}\sum_{b\in\mathcal B_n^\pm}\mu(b)g(b)\sum_{e\mid P(p_n)}\mu(e)g(e)=V(z)-\sum_{n\in M^\pm}(-1)^nT_n(D,z).$$
This gives $V+\sum_{\rm odd}T_n$ and $V-\sum_{\rm even}T_n$. The sums are finite because $T_n=0$ for $n>\pi(z)$.

*(ii)* Put $m^*=(m,P(z))$. The same decomposition, with $g$ replaced by $d\mapsto\mathbf1_{d\mid m^*}$, gives
$$\sum_{d\mid m^*}\lambda^\pm(d)=\mathbf1_{m^*=1}-\sum_{n\in M^\pm}(-1)^n\#\{b\in\mathcal B^\pm_n:b\mid m^*,\ (m^*,P(p_n(b)))=1\}.$$
Here $\sum_{e\mid(m^*,P(p_n))}\mu(e)=\mathbf1_{(m^*,P(p_n))=1}\ge0$. The correction is $\ge0$ for $+$ (odd $n$) and $\le0$ for $-$ (even $n$).

*(iii)* Let $d=p_1\cdots p_r\in\mathcal D^+$ with $r\ge1$.
- $r$ odd: $d<p_1\cdots p_r^3<D$.
- $r$ even: $d<p_1\cdots p_{r-2}p_{r-1}^3<D$, using the condition at $m=r-1$.

For $\mathcal D^-$:
- $r$ even, or $r\ge3$ odd: the same argument.
- $r=1$: $d=p_1<z\le D$.

Also $1<D$. ∎

**Step 16 (Theorem C).**
- (i) For $s\ge1$, Theorem A applies to every odd $n$. With Theorem B(i), and strict inequality already at $n=1$:
$$G^+=V+\sum_{\rm odd}T_n<V\Bigl(1+\sum_{\rm odd}f_n+\varepsilon e^2h\sum_{\rm odd}\tau_n\Bigr)=V(\tilde F+\varepsilon e^2hC_1).$$
  The series converge by Step 8, assuming $C_1<\infty$.
- (ii) For $s\ge2$ every even $n$ is admissible, and $G^->V(\tilde f-\varepsilon e^2hC_2)$ in the same way.
- (iii) Finiteness. For $0<\varepsilon\le1/74$ every branch coefficient is bounded as follows, using $e^{0.2}=1.22140$, …, $4e/3=3.62438$ (all coefficients increase in $\varepsilon$):
  - $\kappa_{s_0}+(\gamma_{s_0}+\kappa_{s_0})\varepsilon\le0.99019$ (attained at $s_0=2$);
  - $\tilde\kappa+(5+4\varepsilon)\varepsilon\le0.98970$.

  Let $\bar c:=\sup_{n\ge2}c_n<1$. The terms with $c_1$ occur only as $c_1^0=1$. Hence
$$\tau_n\le\rho\tau_{n-1}+B\bar c^{\,n-2},\qquad \rho=0.9902,\quad B=10.2\ \ \bigl(\ge\max(2\gamma_3+2,\ 6(1+\varepsilon)+2(2+\varepsilon))\bigr).$$
  With $r=\max(\rho,\bar c)<1$ and $u_n=\tau_n/r^{n-1}$ we get $u_n\le u_{n-1}+B/r$, so $\tau_n\le r^{n-1}(3+(n-1)B/r)$, which is summable. ∎

**Step 17 (E1 reduces to two constants).** Term-by-term (Tonelli, nonnegative integrands):
- (a) For $1\le s\le3$: $s\tilde F(s)=s+(3-s)+\sum_{n\ge3\text{ odd}}3f_n(3)=3\tilde F(3)$.
- (b) For $s\ge3$: $s\tilde F(s)-3\tilde F(3)=(s-3)-\int_3^s\sum_{m\text{ even}}f_m(t-1)dt=\int_3^s\tilde f(t-1)dt$.
- (c) For $s\ge2$: $s\tilde f(s)-2\tilde f(2)=(s-2)+\int_2^s\sum_{m\text{ odd}}f_m(t-1)dt=\int_2^s\tilde F(t-1)dt$.

By the method of steps on $[k,k+1]$, $k=2,3,\dots$, the pair $(\tilde F,\tilde f)$ is determined by $A=3\tilde F(3)$ and $B=\tilde f(2)$. [BJS]'s $(F,f)$ solve the same integral equations with $A=2e^\gamma$ and $B=0$ (since $F=2e^\gamma/s$ and $f=0$ on $(0,2]$, with $f$ continuous at 2). So E1 ⟺ $3\tilde F(3)=2e^\gamma$ and $\tilde f(2)=0$. Both are left as external input.

**Step 18 (audit of [BJS] displays under H).** Justified as written:
- $n=1$;
- (`Tneq`);
- (`eq:Tn3`), (`eq:Tn4`), (`eq:Tn1`), (`eq:Tn2`) with $\gamma_3$;
- $\xi_3$;
- the odd $s<3$ display and its four bounds (up to the $c_n\to c_{n-1}$ typo);
- $\tilde\xi$;
- $\kappa_{s_0}$ and $\tilde\kappa$;
- (`eq:h12`).

Wrong even under H:
- `lem:hsm1`'s $\gamma_{s_0}$. The corrected value enlarges $\xi_{s_0}$ for $s_0\le2.8$, hence $\tau_n$ for even $n$ and everything downstream.
- Table `tab:tau`, as a table of the defined $\tau_n$ (S.6, item 5).

**Effect.** Theorem C holds with $C_i=\sum\tau_n$ as defined here. The numbers 276/277 (row 100) must not be used until recomputed.

---

## What is not proved here

1. **E1.** That $3\tilde F(3)=2e^\gamma$ and $\tilde f(2)=0$ (Nathanson Thm 9.4). Until this is supplied, Theorem C is proved with $\tilde F,\tilde f$, not with Cai's $F,f$.
2. **The numerical values of $C_1,C_2$.** Lemma `lemma:exprec` and its tail bound were not re-derived. The script gives only rigorous **lower** bounds for partial sums. Table `tab:fF` is not supported by the printed recursion, and the frame note's $C_1=276$ is unsupported.
3. **[BJS] Table `tab:cn1`.** The values $c_n$ for $2\le n\le500$ are an unverified computation. Everything holds with $c_n=0.9607$ (proved), at the cost of larger $\tau_n$.
4. **The passage from $G$ to $S(A,\mathbb P,z)$ with pre-sieve $\mathbb Q$.** This is Theorem `theo:JR` itself (this note §8, another section). Theorem B(ii),(iii) supply the needed ingredients, applied with $\mathbb P\setminus\mathbb Q$ in H.
5. **The version with $g_n$ depending on $n$.**
6. **Weaker hypotheses.** Whether the results hold under the half-open prime-level form, or under [BJS]'s fixed-$z$ form for the $S$-statement. Under fixed $z$ the Lemma itself is false (referee counterexample, $n=3$, $s=1.5$).
7. **Identity of the weights with Nathanson's Thm 9.3.** Not checked; not needed.
8. **The script has not been run.**

## Checks a referee should make

1. Lemma 0(a): the limit $w\downarrow q$ needs $\mathbb P\cap(q,w)=\emptyset$, which is ensured by $w\le\min(z,q')$.
2. Step 4: the index shift $m\mapsto m-1$ preserves "$\equiv n$" ⟺ "$\equiv n-1$". The condition $p^3<D$ appears iff $n$ is odd.
3. Step 5: both Abel summations and the sign of $-V(W)\varphi_m$. Its $V$ is at level $W$, which is why U2 is unavoidable when $W=D^{1/3}$.
4. Step 10: the domain checks $s'>\sigma-1$ and the equality of the $p$-range with $\mathbb P\cap[2,W)$.
5. Step 7 (h1): $h(1.2)/h(2.2)=e^{0.2}>1=\gamma_2^{\rm printed}$.
6. Step 13: $(1+\varepsilon)^2\tilde\kappa+3\varepsilon(1+\varepsilon)\le\tilde\kappa+(5+4\varepsilon)\varepsilon$.
7. Step 15: the bijection, including squarefreeness, divisibility by $P(z)$ and first-failure index, and the sign $(-1)^n$.
8. S.6 item 5 by hand: $\tau_2\ge3\cdot0.8349+8e/3>9.75$.
9. **For the frame note.** Under C, every sifted prime $p<z$ needs $(1-g(p))^{-1}\le K<1+\varepsilon$, i.e. $p>2+1/\varepsilon$ for $g=1/(p-1)$. With $\mathbb Q=$ primes in $[3,41)$, $p=41$ gives $K\ge40/39$, so the theorem does not apply for any $\varepsilon\le1/74$. The quantity to certify is $\sup_zK_*(z)$ over $(\mathbb P\setminus\mathbb Q,g)$.
10. Run the script below and compare with the expected output.

### Script

```python
#!/usr/bin/env python3
"""
bjs_core_check.py -- certified checks for the corrected beta = 2 linear-sieve constants.
Standard library only. Every real quantity is an interval (lo, hi) of Fractions with
lo <= true value <= hi; after each step both ends are rounded OUTWARD to a multiple of
10**-40. No floats.

EXTERNAL INPUT (only one): Euler's constant gamma in [0.57721566490, 0.57721566491].

PART 1 asserts:
  P1a  3*E1(3) < e^{-3}           (monotonicity of e^s H(s)/s on [2,3], Step 7 (h4))
  P1b  e^3*E1(3) < 1/3            (monotonicity of e^s H(s)/3 on [3,4])
  P1c  kappa(s0) := e^{s0}(C - s0 e^{-2})/s0 <= tabulated kappa_{s0},  C = 4e^-2 - e^-3 + 3E1(3)
  P1d  2*kappa(2) - 1 <= 0.9214   (tilde kappa)
  P1e  8e/27 <= 0.8349            (s >= 4 branch)
PART 2: enclosures of tau_n (n <= 500) DEFINED by (eq:tau) of BJS, multiplied out:
  tau_n = max_b [tau_{n-1}*rho_b + beta_b*c_{n-1}^{n-2} + beta'_b*c_n^{n-1}],
  with gamma_{s0} = e^{s0-1.8} ("corrected") or e^{s0-2} ("literal"), gamma_3 = 4e/3,
  c_n from BJS Table tab:cn1. Since all tau_n > 0, the printed partial sums over n <= 500
  are rigorous LOWER bounds for C_1 = sum_{odd} tau_n and C_2 = sum_{even} tau_n.
"""
from fractions import Fraction as Fr

SCALE = 10 ** 40


def rd_down(x):
    x = Fr(x)
    return Fr((x.numerator * SCALE) // x.denominator, SCALE)


def rd_up(x):
    x = Fr(x)
    return Fr(-((-x.numerator * SCALE) // x.denominator), SCALE)


def iv(lo, hi):
    lo, hi = Fr(lo), Fr(hi)
    assert lo <= hi, (lo, hi)
    return (rd_down(lo), rd_up(hi))


def show(x, d=6, up=False):
    """Decimal display of x: floor (up=False) or ceiling (up=True) at d digits."""
    x = Fr(x)
    n = x.numerator * 10 ** d
    q = -((-n) // x.denominator) if up else n // x.denominator
    sign = "-" if q < 0 else ""
    q = abs(q)
    return "%s%d.%0*d" % (sign, q // 10 ** d, d, q % 10 ** d)


def add(a, b):
    return iv(a[0] + b[0], a[1] + b[1])


def sub(a, b):
    return iv(a[0] - b[1], a[1] - b[0])


def mul_pos(a, b):
    assert a[0] >= 0 and b[0] >= 0
    return iv(a[0] * b[0], a[1] * b[1])


def scal(c, a):
    c = Fr(c)
    assert c >= 0
    return iv(c * a[0], c * a[1])


def inv_pos(a):
    assert a[0] > 0
    return iv(1 / a[1], 1 / a[0])


def exp_iv(x, N=80):
    """e^x, rational 0<=x<=4: lo = sum_{k<=N} x^k/k!; tail <= x^{N+1}/(N+1)!/(1-x/(N+2))."""
    x = Fr(x)
    assert 0 <= x <= 4
    term, s = Fr(1), Fr(1)
    for k in range(1, N + 1):
        term = term * x / k
        s += term
    nxt = term * x / (N + 1)
    return iv(s, s + nxt / (1 - x / (N + 2)))


def ln3_iv(J=80):
    """ln3 = 2*sum_{j>=0} 2^-(2j+1)/(2j+1); tail after J terms <= 2*2^-(2J+1)/(2J+1)*4/3."""
    s = Fr(0)
    for j in range(J):
        s += Fr(1, (2 * j + 1) * 2 ** (2 * j + 1))
    s *= 2
    tail = Fr(2, (2 * J + 1) * 2 ** (2 * J + 1)) * Fr(4, 3)
    return iv(s, s + tail)


EULER_GAMMA = (Fr("0.57721566490"), Fr("0.57721566491"))  # EXTERNAL INPUT


def E1_3_iv(K=150):
    """E1(3) = -gamma - ln3 + sum_{k>=1} (-1)^{k+1} 3^k/(k k!); terms decrease
    (ratio 3k/(k+1)^2 <= 3/4), so |sum - partial_K| <= next term."""
    term, s = Fr(1), Fr(0)
    for k in range(1, K + 1):
        term = term * 3 / k
        s += (term / k) if k % 2 == 1 else -(term / k)
    t_next = term * 3 / (K + 1) / (K + 1)
    ln3 = ln3_iv()
    return iv(s - t_next - EULER_GAMMA[1] - ln3[1],
              s + t_next - EULER_GAMMA[0] - ln3[0])


S0 = ["2", "2.2", "2.4", "2.6", "2.8", "3"]
KAPPA = {"2": Fr("0.9607"), "2.2": Fr("0.9557"), "2.4": Fr("0.9457"),
         "2.6": Fr("0.9261"), "2.8": Fr("0.8914"), "3": Fr("0.8349")}
KAPPA_T = Fr("0.9214")


def part1():
    print("PART 1: constants of BJS Lemma lemma:forg")
    e1, e2, e3 = exp_iv(1), exp_iv(2), exp_iv(3)
    em2, em3 = inv_pos(e2), inv_pos(e3)
    E = E1_3_iv()
    print("  E1(3) in [%s, %s]" % (show(E[0], 12), show(E[1], 12, True)))
    t = sub(em3, scal(3, E))
    assert t[0] > 0, "P1a failed"
    print("  P1a: e^-3 - 3 E1(3) >= %s > 0" % show(t[0], 8))
    t = mul_pos(e3, E)
    assert t[1] < Fr(1, 3), "P1b failed"
    print("  P1b: e^3 E1(3) <= %s < 1/3" % show(t[1], 8, True))
    C = add(sub(scal(4, em2), em3), scal(3, E))
    kap = {}
    for key in S0:
        s0 = Fr(key)
        inner = sub(C, scal(s0, em2))
        assert inner[0] > 0
        k = scal(1 / s0, mul_pos(exp_iv(s0), inner))
        kap[key] = k
        ok = k[1] <= KAPPA[key]
        print("  kappa(%s) in [%s, %s]  tabulated %s  %s" % (
            key, show(k[0], 7), show(k[1], 7, True), KAPPA[key], "OK" if ok else "FAIL"))
        assert ok, "P1c failed at " + key
    kt = sub(scal(2, kap["2"]), (Fr(1), Fr(1)))
    print("  2*alpha-1 in [%s, %s]  tabulated %s" % (show(kt[0], 7), show(kt[1], 7, True), KAPPA_T))
    assert kt[1] <= KAPPA_T, "P1d failed"
    t = scal(Fr(8, 27), e1)
    assert t[1] <= KAPPA["3"], "P1e failed"
    print("  P1e: 8e/27 <= %s <= 0.8349" % show(t[1], 7, True))


C_TABLE = [(1, 1, "1"), (2, 2, "0.33"), (3, 3, "0.39"), (4, 4, "0.45"), (5, 5, "0.51"),
           (6, 6, "0.54"), (7, 7, "0.57"), (8, 8, "0.58"), (9, 10, "0.61"), (11, 12, "0.63"),
           (13, 13, "0.64"), (14, 14, "0.65"), (15, 18, "0.66"), (19, 20, "0.67"),
           (21, 26, "0.68"), (27, 34, "0.69"), (35, 46, "0.70"), (47, 82, "0.71"),
           (83, 345, "0.72"), (346, 500, "0.73")]


def c_bjs(n):
    for a, b, v in C_TABLE:
        if a <= n <= b:
            return Fr(v)
    raise ValueError(n)


def gammas(corrected):
    g = {"3": scal(Fr(4, 3), exp_iv(1))}
    for key in S0[:-1]:
        g[key] = exp_iv(Fr(key) - (Fr("1.8") if corrected else Fr(2)))
    return g


def tau_run(eps, corrected, nmax=500):
    eps = Fr(eps)
    G = gammas(corrected)
    tau = {1: (Fr(3), Fr(3))}
    for n in range(2, nmax + 1):
        a = c_bjs(n - 1) ** (n - 2)
        A = iv(a, a)
        b = c_bjs(n) ** (n - 1)
        B = iv(b, b)
        t = tau[n - 1]
        cands = []
        for key in (S0 if n % 2 == 0 else ["3"]):
            k, g = KAPPA[key], G[key]
            lo = t[0] * (k + (g[0] + k) * eps) + 2 * g[0] * A[0] + 2 * B[0]
            hi = t[1] * (k + (g[1] + k) * eps) + 2 * g[1] * A[1] + 2 * B[1]
            cands.append((lo, hi))
        if n % 2 == 1:
            r = KAPPA_T + (5 + 4 * eps) * eps
            lo = t[0] * r + 6 * (1 + eps) * A[0] + 2 * (2 + eps) * B[0]
            hi = t[1] * r + 6 * (1 + eps) * A[1] + 2 * (2 + eps) * B[1]
            cands.append((lo, hi))
        tau[n] = iv(max(c[0] for c in cands), max(c[1] for c in cands))
    return tau


TAB_TAU = {1: 3, 2: 8, 3: 10, 4: 10, 5: 10, 6: 10, 7: 10, 8: 10, 9: 10, 10: 10,
           11: 9, 12: 9, 13: 9, 14: 8, 15: 8, 16: 8}
TABLE1 = {200: (153, 154), 100: (276, 277), 74: (631, 630)}


def part2():
    print("PART 2: tau_n as defined by (eq:tau)")
    tau = tau_run(Fr(1, 200), True, 16)
    print("  eps=1/200, corrected gamma:   n   enclosure of tau_n   BJS tab:tau")
    for n in range(1, 17):
        print("   %3d  [%s, %s]   %s" % (n, show(tau[n][0], 4), show(tau[n][1], 4, True), TAB_TAU[n]))
    assert tau[2][0] > 8
    print("  tau_2 > 8: Table tab:tau does not bound tau_2 as defined by (eq:tau).")
    for inv_eps in (200, 100, 74):
        for corrected in (True, False):
            tau = tau_run(Fr(1, inv_eps), corrected)
            s1 = sum(tau[n][0] for n in range(1, 501, 2))
            s2 = sum(tau[n][0] for n in range(2, 501, 2))
            c1, c2 = TABLE1[inv_eps]
            print("  eps=1/%d %s: sum_odd<=499 >= %s (Table1 C1=%d); sum_even<=500 >= %s "
                  "(Table1 C2=%d); tau_500 <= %s" % (
                      inv_eps, "corrected" if corrected else "literal  ",
                      show(s1, 2), c1, show(s2, 2), c2, show(tau[500][1], 6, True)))
            if s1 > c1:
                print("     -> C1 as defined in lemma:exprec EXCEEDS the Table 1 entry")
            if s2 > c2:
                print("     -> C2 as defined in lemma:exprec EXCEEDS the Table 1 entry")


if __name__ == "__main__":
    part1()
    part2()
```

**Expected output and sanity checks.**

Part 1:
- $E_1(3)\in[0.013048381094,\,0.013048381095]$ (classical value $0.0130483810942$).
- $\kappa(2)\approx0.960683$, $\kappa(2.2)\approx0.955673$, $\kappa(2.4)\approx0.945672$, $\kappa(2.6)\approx0.926025$, $\kappa(2.8)\approx0.891304$, $\kappa(3)\approx0.834845$; all are "OK", with margins of $1.7\cdot10^{-5}$ to $10^{-4}$.
- $2\alpha-1\approx0.921367$.
- $8e/27\approx0.805411$.

Part 2:
- $\tau_2\in[10.4803,10.4804]$ for both $\gamma$ conventions, since $n=2$ is governed by $\xi_3$.
- $\tau_3\approx12.519$ and $\tau_4\approx12.754$ (corrected convention). The table lists 8, 10, 10.
- A hand iteration (not certified) predicts odd partial sums of about $1.9\cdot10^2$ at $\varepsilon=1/200$ and about $3.4\cdot10^2$ at $\varepsilon=1/100$. Both would trigger the "EXCEEDS" lines for $C_1$.
- If the script prints sums below 153 and 276, my hand estimate is wrong. In that case S.6 item 6 should be withdrawn, while item 5 ($\tau_2$) stands regardless.
- The run should take a few seconds to well under a minute: about $6\times500$ steps with 40-digit rationals.