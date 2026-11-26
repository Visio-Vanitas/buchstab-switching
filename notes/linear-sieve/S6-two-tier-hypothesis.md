# Two-tier hypothesis: a level-dependent constant in the explicit β = 2 linear sieve

**Summary of findings.**

- **Which variable the constant depends on.** The level-dependent constant must depend on the **lower endpoint $u$**, not on $w$. For $g(p)=1/(p-1)$, a cluster of small primes at $u$ keeps the ratio $\Pi[u,w]\log u/\log w$ near $K_0$ for *every* $w>u$. The Mertens tail only adds $O(1/\log u)$.
- **Theorem 1 (proved, clean).** Each $T_n$ is bounded with the *small* constant $\varepsilon_1$ whenever $n$ is "shallow": $\sigma_0:=\log D/\log W_0\ge 3^{(n+1)/2}$ ($n$ odd), or $(s-1)\log z/\log W_0\ge 3^{n/2}$ ($n$ even). In those cases the tuples reaching below $W_0$ contribute exactly $0$. For deep $n$ the core bound with $\varepsilon_0$ applies. So $K_0$ enters only through $\tau_n(\varepsilon_0)$ with $n\gtrsim 2\log_3\sigma_0$.
- **Quantitative weakness of Theorem 1.** It is weak. The deep tail $\sum_{n\ge N}\tau_n(\varepsilon_0)$ is finite only if $\varepsilon_0\lesssim1/55$. Its decay in $\sigma_0$ is only polynomial, with a tiny exponent. It does **not** rescue the frame note ($\varepsilon_0\approx0.0374$).
- **Part (a), proved.** The exact two-tier recursion (Theorem 4). It rests on a two-tier partial-summation lemma (Proposition 3). Its new term is $(K_0-K_1)\cdot\frac1\sigma\bigl[\sigma_0\Theta(\sigma_0)+\int_{\sigma_0}^\infty\Theta\bigr]$, which carries the "$h(s\log z/\log W_0)$-type" factor at each single stage.
- **Part (b), not proved.** A conjectured closed form (Conjecture 5). I give an argument that the hoped-for form $(K_0-K_1)\,C\,h(s\log z/\log W_0)$ is probably **false**: the decay degrades through the induction. A polynomial-in-$\sigma_0$ form is conjectured instead.

---

## Statement

### 0. Setting

Notation is as in the core section ((S1)–(S5), $h,H,f_n,\tau_n(\varepsilon),c_n$). In particular:

- $\tau_n(\varepsilon)$ denotes the core's $\tau_n$ computed with parameter $\varepsilon$ and a fixed admissible sequence $(c_n)$.
- $h^{(\varepsilon)}_n(s):=\varepsilon\tau_n(\varepsilon)e^2h(s)$.

Fix a real $W_0\ge2$ and constants $1\le K_1\le K_0$. Define:
$$t:=\frac{\log z}{\log W_0},\qquad \sigma_0:=\frac{\log D}{\log W_0}=st .$$

**Definition (two-tier hypothesis $\mathrm{H}_2(z;W_0,K_0,K_1)$).**

- **(H0)** $V(u)/V(w)\le K_0\log w/\log u$ for all real $1<u<w\le z$. This is the core H(z,K_0).
- **(H1)** $V(u)/V(w)\le K_1\log w/\log u$ for all real $W_0\le u<w\le z$. This is vacuous if $z\le W_0$.

Equivalently: $V(u)/V(w)\le K(u)\log w/\log u$, with $K(u)=K_0$ for $u<W_0$ and $K(u)=K_1$ for $u\ge W_0$.

**Remark 0 (why $u$, not $w$; mixed pairs).**

- (i) *Multiplicativity.* (H1) together with H(W_0,K_0) implies (H0) with $K_0K_1$ in place of $K_0$. So (H0) may be replaced by H(W_0,K_0) at the cost $K_0\to K_0K_1$.
- (ii) *Application.* In the application section's notation, the natural choices are $K_0=1+\varepsilon^*(S)$ and $K_1=1+\varepsilon^*(S\cap[W_0,\infty))$. The latter is computable by the same certified scan restricted to $a\ge W_0$.
- (iii) *A $w$-dependent constant cannot be small.* Pairs $(a,b)$ with $a$ in a small cluster and $b\to\infty$ have $F_S(a,b)\ge F_S(a,a')-O(1/\log a)$. This uses Theorem D of the application section. Hence no constant depending only on $w$ can be small for large $w$.

### 1. Theorem 1 (shallow/deep split), proved

**Hypotheses.**
- $z\ge2$, $W_0\ge2$, $1\le K_1\le K_0$.
- $\varepsilon_1>0$ with $K_1<1+\varepsilon_1$, and $\varepsilon_0>0$ with $K_0<1+\varepsilon_0$.
- $(c_n)$ admissible.
- $n\ge1$, and $D$ with $s\ge1$ ($n$ odd) or $s\ge2$ ($n$ even).

**Definition of "shallow".** Call $n$ *shallow for $(D,z)$* if
$$n\text{ odd and }\sigma_0\ge3^{(n+1)/2},\qquad\text{or}\qquad n\text{ even and }(s-1)t\ge3^{n/2}.$$
Call $n$ *deep* otherwise.

**Conclusions.**
- (i) If (H1) holds and $n$ is shallow, then $T_n(D,z)<V(z)\bigl(f_n(s)+\varepsilon_1\tau_n(\varepsilon_1)e^2h(s)\bigr)$.
- (ii) If (H0) holds, then $T_n(D,z)<V(z)\bigl(f_n(s)+\varepsilon_0\tau_n(\varepsilon_0)e^2h(s)\bigr)$. This is the core Theorem A.

**Equivalent index thresholds.** Odd $n$ is deep iff $n\ge N_1:=\max(1,2\lfloor\log_3\sigma_0\rfloor+1)$. Even $n$ is deep iff $n\ge N_2:=\max(2,2\lfloor\log_3((s-1)t)\rfloor+2)$. For $\sigma_0<1$, respectively $(s-1)t<1$, every $n$ of that parity is deep.

### 2. Corollary 2 (G-bounds)

Assume $\mathrm H_2$. Define the branch-rate and constants:
$$\rho(\varepsilon):=\max\Bigl(\max_{s_0\in\Sigma}\bigl[\kappa_{s_0}+(\gamma_{s_0}+\kappa_{s_0})\varepsilon\bigr],\ \tilde\kappa+(5+4\varepsilon)\varepsilon\Bigr),\qquad B(\varepsilon):=\max\bigl(\tfrac{8e}{3}+2,\ 10+8\varepsilon\bigr),$$
with the corrected $\gamma_{s_0}$. Let $\bar c:=\sup_{n\ge2}c_n<1$ and $r_0:=\max(\rho(\varepsilon_0),\bar c)$.

If $r_0<1$ and $C_i(\varepsilon_1)<\infty$, then:

- for $s\ge1$: $G(z,\lambda^+)<V(z)\Bigl(\tilde F(s)+e^2h(s)\bigl[\varepsilon_1C_1(\varepsilon_1)+\varepsilon_0\mathcal T(N_1)\bigr]\Bigr)$;
- for $s\ge2$: $G(z,\lambda^-)>V(z)\Bigl(\tilde f(s)-e^2h(s)\bigl[\varepsilon_1C_2(\varepsilon_1)+\varepsilon_0\mathcal T(N_2)\bigr]\Bigr)$;

where
$$\mathcal T(N):=r_0^{N-1}\Bigl[\frac{3}{1-r_0}+\frac{B(\varepsilon_0)}{r_0}\Bigl(\frac{N-1}{1-r_0}+\frac{r_0}{(1-r_0)^2}\Bigr)\Bigr]\ \ge\ \sum_{n\ge N}\tau_n(\varepsilon_0).$$

**Remark (weakness).** Since $r_0\ge\kappa_2=0.9607$, the factor $r_0^{N-1}$ with $N\approx2\log_3\sigma_0$ is $\approx\sigma_0^{-2\log(1/r_0)/\log3}$. That exponent is $\le0.073$. Moreover $\rho(\varepsilon_0)<1$ forces $\varepsilon_0\lesssim1/55.6$, while the frame note has $\varepsilon_0\approx0.0374$.

*Illustration, not certified.* Take $z\approx5.3\cdot10^7$, $s\approx8$, $W_0=300$. Then only $n\le4$ are shallow.

### 3. Proposition 3 (two-tier partial summation), proved

**Hypotheses.**
- $2\le W_0<W$ and $1\le K_1\le K_0$.
- $\varphi:[2,W]\to[0,\infty)$ nondecreasing.
- $V(q)/V(W)\le K_0\log W/\log q$ for $q\in\mathbb P$, $q<W_0$.
- $V(q)/V(W)\le K_1\log W/\log q$ for $q\in\mathbb P$, $W_0\le q<W$.

With $\omega(t):=\log W/(t\log^2t)$:
$$\sum_{q\in\mathbb P,\,q<W}g(q)V(q)\varphi(q)\le V(W)\Bigl[(K_1-1)\varphi(W)+K_1\!\int_2^W\!\varphi\omega\,dt+(K_0-K_1)\Bigl(\tfrac{\log W}{\log W_0}\varphi(W_0)+\!\int_2^{W_0}\!\varphi\omega\,dt\Bigr)\Bigr].$$

### 4. Theorem 4 (the two-tier recursion: part (a)), proved

Write $\mathrm{dom}_k=[1,\infty)$ for $k$ odd and $[2,\infty)$ for $k$ even. Let $n\ge2$.

**Induction hypothesis.** $\Phi_{n-1}:\mathrm{dom}_{n-1}\times(0,\infty)\to[0,\infty)$ is nonincreasing in each variable, and
$$T_{n-1}(D',Z')\le V(Z')\,\Phi_{n-1}(s',\sigma_0')$$
for all $Z'\ge2$ and all $D'$ with $s'=\log D'/\log Z'\in\mathrm{dom}_{n-1}$. Here $\sigma_0'=\log D'/\log W_0$.

**Level ratio and auxiliary functions.** Put $\sigma:=s$ if $n$ is even or $s\ge3$, and $\sigma:=3$ if $n$ is odd and $s<3$. Define
$$\Theta(x):=\Phi_{n-1}\bigl(x-1,\ \sigma_0(1-1/x)\bigr)\quad(x\ge\sigma),$$
$$J_K:=(K-1)\Theta(\sigma)+\frac K\sigma\int_\sigma^\infty\Theta(x)\,dx,$$
$$X:=\frac1\sigma\Bigl[\sigma_0\Theta(\sigma_0)+\int_{\sigma_0}^\infty\Theta(x)\,dx\Bigr].$$
Note that $\Theta(\sigma_0)=\Phi_{n-1}(\sigma_0-1,\sigma_0-1)$.

**Definition of $R_n$.** Let $K_*:=K_1$ if $\sigma_0\ge3$ and $K_*:=K_0$ otherwise.

- *Case $\sigma=s$:*
  - $R_n:=J_{K_1}+(K_0-K_1)X$ if $\sigma_0>s$;
  - $R_n:=J_{K_0}$ if $\sigma_0\le s$.
- *Case $\sigma=3$:*
  - $R_n:=\frac{3K_1}{s}\bigl[J_{K_1}+(K_0-K_1)X\bigr]$ if $\sigma_0>3$;
  - $R_n:=\frac{3K_0}{s}J_{K_0}$ if $\sigma_0\le3$.

**Conclusion.** Under $\mathrm H_2(z;W_0,K_0,K_1)$:
$$T_n(D,z)\le V(z)R_n(s,\sigma_0).$$
For $n=1$: $T_1(D,z)\le V(z)R_1$ with $R_1:=0$ for $s\ge3$ and $R_1:=3K_*/s-1$ for $1\le s<3$.

**Consequently**, define recursively
$$\Phi_n:=\min\Bigl(\sup_{s'\ge s,\ \sigma_0'\ge\sigma_0}R_n(s',\sigma_0'),\ f_n+h_n^{(\varepsilon_0)}\Bigr).$$
Then $T_n(D,z)\le V(z)\Phi_n(s,\sigma_0)$ for all $n$, $z$ and admissible $D$. This is the strongest proved form here. It is a computable two-variable recursion, not a closed form.

**Sanity check.** If $K_0=K_1=K$, then $X$ drops out and $R_n$ is exactly the core's (R1)/(R2).

### 5. Conjecture 5 (part (b)), NOT proved

There exist explicit $A,a>0$, depending on $\varepsilon_0$ and $\varepsilon_1$ only, such that
$$\Phi_n(s,\sigma_0)\le f_n(s)+\varepsilon_1\tau_n(\varepsilon_1)e^2h(s)+(K_0-K_1)\,e^2h(s)\,\mu_n(t),$$
with:
- $\mu_n(t)=0$ for $n$ shallow (as in Theorem 1);
- $\sum_n\mu_n(t)\le A\,t^{-a}$.

I conjecture that **no** bound of the form $(K_0-K_1)\,C\,h(st)$ holds uniformly in $n$. The heuristic is given in Proof Step 9.

---

## Proof

**Step 1 (split).**
- Let $T_n^{\ge}$ (resp. $T_n^{<}$) be the part of the sum (S5) with $p_n\ge W_0$ (resp. $p_n<W_0$). Then $T_n=T_n^{\ge}+T_n^{<}$.
- Let $\mathbb P':=\mathbb P\cap[W_0,\infty)$ and $V'(w):=\prod_{p\in\mathbb P',p<w}(1-g(p))$.
- For $w\ge W_0$ we have $V(w)=V(W_0)V'(w)$, since the primes $<W_0$ contribute exactly $V(W_0)$.
- A tuple has $p_n\ge W_0$ iff all $p_i\in\mathbb P'$. Conditions (a)–(c) of (S5) involve only the primes. Hence $T_n^{\ge}(D,z)=V(W_0)\,T'_n(D,z)$, where $T'_n$ is (S5) for $(\mathbb P',g)$.

**Step 2 ($(\mathbb P',g)$ satisfies H(z,K_1) under (H1)).** Let $1<u<w\le z$. Then $V'(u)/V'(w)=\prod_{p\in\mathbb P,\ \max(u,W_0)\le p<w}(1-g(p))^{-1}$. There are three cases:

- If $w\le W_0$: the product is empty, so the ratio is $1<\log w/\log u\le K_1\log w/\log u$, using $K_1\ge1$.
- If $u\ge W_0$: this is (H1).
- If $u<W_0<w$: the ratio equals $V(W_0)/V(w)\le K_1\log w/\log W_0<K_1\log w/\log u$, by (H1) at $(W_0,w)$.

**Step 3 (Theorem 1(i): the $T^{\ge}$ part).**
- If $z\le W_0$, then $T_n^{\ge}=0$, because $p_n<z\le W_0$.
- Otherwise, by Step 2, core Theorem A applies to $(\mathbb P',g)$ with $K=K_1\in[1,1+\varepsilon_1)$. It gives $T'_n<V'(z)(f_n+h_n^{(\varepsilon_1)})$.
- Multiplying by $V(W_0)$: $T_n^{\ge}<V(z)(f_n+h_n^{(\varepsilon_1)})$.
- It remains to show that $T_n^{<}=0$ for shallow $n$ (Step 4). Since $h>0$, this also covers $z\le W_0$.

**Step 4 (shallow ⇒ $T_n^<=0$).** Take a tuple in $T_n^<$ and put $D_m:=D/(p_1\cdots p_m)$, with $D_0=D$.

1. *Rewriting the conditions.* Condition (c) at $m$ is $p_1\cdots p_{m-1}p_m^3<D$, i.e. $p_m^2<D_m$, equivalently $p_m^3<D_{m-1}$. Condition (b) is $p_n^2\ge D_n$, i.e. $D_{n-1}\le p_n^3<W_0^3$.
2. *Pair lemma.* Let $m\le n-2$ be a constrained index ($m\equiv n$). Then:
   - $D_m=D_{m-1}/p_m>D_{m-1}^{2/3}$, since $p_m<D_{m-1}^{1/3}$;
   - $D_{m+1}=D_m/p_{m+1}>D_m/p_m>D_m^{1/2}$, since $p_m<D_m^{1/2}$.

   Hence $\log D_{m+1}>\frac13\log D_{m-1}$. All these quantities exceed 1, because $D_{m-1}>p_m^3\ge8$.
3. *Iteration.* Apply the pair lemma at $m=n-2,n-4,\dots$:
   - $n$ odd: $(n-1)/2$ applications, down to $m=1$, give $\log D_{n-1}>3^{-(n-1)/2}\log D$.
   - $n$ even: $(n-2)/2$ applications, down to $m=2$, give $\log D_{n-1}>3^{-(n-2)/2}\log D_1$. Moreover $D_1>D/z\ge z>1$, because $s\ge2$.

   The cases $n=1,2$ are the empty iteration.
4. *Comparison.* With $\log D_{n-1}<3\log W_0$:
   - $n$ odd: $\sigma_0<3^{(n+1)/2}$;
   - $n$ even: $(s-1)t<3^{n/2}$.

   So for shallow $n$ the sum $T_n^<$ is empty.
5. *Thresholds.*
   - Odd $n$ is deep iff $(n+1)/2>\log_3\sigma_0$, i.e. $n\ge2\lfloor\log_3\sigma_0\rfloor+1$.
   - Even $n$ is deep iff $n\ge2\lfloor\log_3((s-1)t)\rfloor+2$.
   - Part (ii) of Theorem 1 is the core Theorem A under (H0). ∎

**Step 5 (Corollary 2).**
1. *Splitting the sums.* By core Theorem B(i), $G^+=V+\sum_{\rm odd}T_n$. Apply Theorem 1(i) to the shallow odd $n$ and 1(ii) to the deep ones. Then use $\sum_{\rm shallow}\tau_n(\varepsilon_1)\le C_1(\varepsilon_1)$, since all $\tau_n\ge0$. The case of $G^-$ is identical.
2. *Tail recursion.* As in core Step 16(iii), each branch coefficient is $\le\rho(\varepsilon_0)\tau_{n-1}+(\ldots)\bar c^{\,n-2}$, with $(\ldots)$ bounded as follows:
   - $2\gamma_{s_0}c_{n-1}^{n-2}+2c_n^{n-1}\le(2\gamma_3+2)\bar c^{\,n-2}$, using $\gamma_{s_0}\le\gamma_3$ and $c\le1$; for $n=2$, $c_1^0=1$.
   - $6(1+\varepsilon)c_{n-1}^{n-2}+2(2+\varepsilon)c_n^{n-1}\le(10+8\varepsilon)\bar c^{\,n-2}$.

   Hence $\tau_n\le\rho\tau_{n-1}+B\bar c^{\,n-2}$.
3. *Geometric bound.* With $u_n=\tau_n/r_0^{n-1}$ we get $u_n\le u_{n-1}+B/r_0$ and $u_1=3$. So $\tau_n\le r_0^{n-1}(3+(n-1)B/r_0)$.
4. *Tail sum.* Using $\sum_{k\ge M}kr^k=r^M\bigl(\frac M{1-r}+\frac r{(1-r)^2}\bigr)$ with $M=N-1$ gives $\mathcal T(N)$. Restricting to one parity only decreases the sum. ∎

**Step 6 (Proposition 3).** Let $q_1<\dots<q_m$ be the primes of $\mathbb P$ below $W$. If there are none, the claim is trivial. Put $\varphi_i:=\varphi(q_i)$, $c_i:=\log W/\log q_i$, $\Delta_1:=\varphi_1$ and $\Delta_i:=\varphi_i-\varphi_{i-1}\ge0$.

1. *Abel summation.* As in core Step 5, $\Sigma=\sum_iV(q_i)\Delta_i-V(W)\varphi_m$.
2. *Applying the hypothesis.* Each $V(q_i)$ has a coefficient $\Delta_i\ge0$, so we may insert $V(q_i)\le V(W)K(q_i)c_i$. Write $K(q_i)=K_1+(K_0-K_1)\mathbf 1_{q_i<W_0}$, and let $j:=\#\{i:q_i<W_0\}$. This gives
$$\Sigma\le V(W)\Bigl[K_1\sum_{i\le m}c_i\Delta_i-\varphi_m+(K_0-K_1)\sum_{i\le j}c_i\Delta_i\Bigr].$$
3. *The $K_1$ part.* By core Step 5, items 4–6: $\sum_{i\le m}c_i\Delta_i\le\varphi_m+\int_{q_1}^W\varphi\omega$. Hence the $K_1$ part is $\le(K_1-1)\varphi(W)+K_1\int_2^W\varphi\omega$.
4. *The extra part, $j\ge1$.*
   - Abel again: $\sum_{i\le j}c_i\Delta_i=c_j\varphi_j+\sum_{i<j}(c_i-c_{i+1})\varphi_i$.
   - The middle terms satisfy $(c_i-c_{i+1})\varphi_i=\varphi_i\int_{q_i}^{q_{i+1}}\omega\le\int_{q_i}^{q_{i+1}}\varphi\omega$.
   - For the first term, $c_j=\frac{\log W}{\log W_0}+\int_{q_j}^{W_0}\omega$, and $\varphi_j\le\varphi(t)$ for $t\ge q_j$. So $c_j\varphi_j\le\frac{\log W}{\log W_0}\varphi(W_0)+\int_{q_j}^{W_0}\varphi\omega$.
   - Summing, and enlarging $\int_{q_1}^{W_0}$ to $\int_2^{W_0}$ (the integrand is $\ge0$), gives the claim. Here $K_0-K_1\ge0$ is used. ∎

**Step 7 (Theorem 4).** Fix $n\ge2$, $Z=z$, $D$, and $W$ chosen as in core Step 10 ($W=z$ or $D^{1/3}$, so that $\sigma=\log D/\log W$).

1. *Recursion and pointwise bound.* By core Step 4, $T_n=\sum_{p<W}g(p)T_{n-1}(D/p,p)$. The domain checks are those of core Step 10. By the induction hypothesis at $(D/p,p)$:
$$T_{n-1}(D/p,p)\le V(p)\varphi(p),\qquad \varphi(p)=\Phi_{n-1}\bigl(s'(p),\sigma_0(p)\bigr),$$
   with $s'(p)=\log D/\log p-1$ and $\sigma_0(p)=\log(D/p)/\log W_0$.
2. *Monotonicity.* Both arguments decrease in $p$, and $\Phi_{n-1}$ is nonincreasing in each. So $\varphi$ is nondecreasing.
3. *Substitution.* Put $x=\log D/\log t$, as in core Step 6. Then:
   - $\omega\,dt=dx/\sigma$;
   - $\varphi(t)=\Theta(x)$, because $\log t/\log W_0=\sigma_0/x$;
   - $\log W/\log W_0=\sigma_0/\sigma$;
   - the point $t=W_0$ corresponds to $x=\sigma_0$.
4. *Case $W>W_0$ (i.e. $\sigma_0>\sigma$).* The hypotheses of Proposition 3 hold: (H0) gives them for $q<W_0$ and (H1) for $W_0\le q<W$, since $W\le z$. Proposition 3 gives $T_n\le V(W)[J_{K_1}+(K_0-K_1)X]$.
5. *Case $W\le W_0$.* Core Lemma A with $K_0$, via (H0), gives $T_n\le V(W)J_{K_0}$.
6. *Passing to $V(z)$.*
   - If $W=z$ there is nothing to do.
   - If $W=D^{1/3}<z$, then $V(D^{1/3})\le K_*\frac3sV(z)$. This is (H1) at $(D^{1/3},z)$ when $D^{1/3}\ge W_0\iff\sigma_0\ge3$, and (H0) otherwise.
7. *Case $n=1$.* This is core Step 9 with $K_*$ in place of $K$.
8. *Conclusion.* Finally, $R_n\le\sup_{s'\ge s,\sigma_0'\ge\sigma_0}R_n$. Also, the core Theorem A bound is valid under (H0). The minimum of two valid bounds is valid, and the minimum of two nonincreasing functions is nonincreasing. So $\Phi_n$ satisfies the hypotheses needed at the next stage, and induction on $n$ completes the proof. ∎

**Step 8 (where each use of the hypothesis sits).** This refines core Step 14.

- **U-top** (Lemma A at the top $Z$): uses $K_1$ for $q\ge W_0$, $K_0$ for $q<W_0$, and only enters through $X$.
- **U2** (Lemma A at the real level $D_k^{1/3}$): uses $K_0$ only if $D_k^{1/3}\le W_0$, i.e. $\sigma_0^{(k)}\le3$. Otherwise the split is the same as for U-top.
- **U3** ($V(D_k^{1/3})/V(Z)$): uses $K_0$ iff $\sigma_0^{(k)}<3$.

So $K_0$ appears only at stages whose remaining $\sigma_0^{(k)}=\log D_k/\log W_0$ is small (U2, U3), or through $X$. Here $X$ is controlled by $\Theta(\sigma_0)$, i.e. by $\Phi_{n-1}$ at $(\sigma_0-1,\sigma_0-1)$.

**Step 9 (heuristic for Conjecture 5: not a proof).**

1. *One stage gives the hoped-for decay.* At a single stage, take $\Theta\approx Ce^2h(x-1)$. Then $X/h(s)\approx C'\,t\,h(st-1)/h(s)$, which is the $h(s\log z/\log W_0)$-type decay.
2. *The decay degrades with depth.* The $K_1$-integral $\int_\sigma^\infty\Theta$ samples $\Phi_{n-1}$ with second argument $\sigma_0(1-1/x)$. Near $x=\sigma=2$ this is as small as $\sigma_0/2$, with weight $\asymp1/\sigma$. Iterating, the effective $\sigma_0$ shrinks by a bounded factor per stage. This matches Step 4: chains reach $W_0$ after about $2\log_3\sigma_0$ stages.
3. *Expected size of the deep contribution.* The contribution reaching depth $k$ carries roughly the geometric decay of $f_k$ (rate $\approx c_k$). This gives a total of order $\sigma_0^{-a}$ with $a\approx2\log(1/c)/\log3$, not $e^{-\sigma_0}$.
4. *Example.* For $n=5$ and $\sigma_0=20<27$, the set of tuples in $T_5^<$ is nonempty. Its weight is a fixed small fraction of $V(z)$, not $e^{-20}$.

**Obstacle to closing (b).** One needs a two-variable majorant $G(s,\sigma_0)$ that is stable under Theorem 4's recursion. In particular, it must absorb the factor $\sigma_0/\sigma$ in $X$ and the halving of $\sigma_0$. I did not find one within budget.

---

## What is not proved here

1. **Conjecture 5.** Neither the closed form nor any explicit decay rate of $\Phi_n-f_n-h_n^{(\varepsilon_1)}$ in $t$ beyond Theorem 1 is proved. The claim that $h(st)$-decay fails is a heuristic only.
2. **Numerical evaluation of Theorem 4's $\Phi_n$.** It is a computable recursion on $(s,\sigma_0)$, but I give no certified evaluation and no code.
3. **Usefulness for the frame note.** Corollary 2 needs $\rho(\varepsilon_0)<1$, i.e. $\varepsilon_0\lesssim1/55.6$. With $\varepsilon_0\approx0.0374$ the deep tail bound is infinite, so Theorem 1 gives nothing summable there. Theorem 4 has no such restriction in principle, because $\Phi_n$ is capped by the per-$n$ core bound. But summability over $n$ of its $\Phi_n$ is not established.
4. **Inherited caveats.** These are as in the core section: E1 ($\tilde F=F$, $\tilde f=f$), the values $C_i(\varepsilon)$, Table `tab:cn1`, and the interface to $S(A,\mathbb P,z)$ with pre-sieve.
5. **No script is supplied.**

## Checks a referee should make

1. **Step 4.** The pair lemma's two inequalities, and the counts $(n-1)/2$ and $(n-2)/2$ of constrained indices. Check by hand that $n=1,2,3$ give the thresholds $3$, $3$ and $9$.
2. **Step 2.** The mixed case $u<W_0<w$, which uses (H1) at the pair $(W_0,w)$. Also $K_1\ge1$ in the empty case.
3. **Step 1.** The identity $T_n^{\ge}=V(W_0)T_n'$. Note that the conditions (a)–(c) do not involve $V$.
4. **Step 6.** The bound on the term $c_j\varphi_j$, which uses that $\varphi$ is nondecreasing up to $W_0$. Also check the sign $K_0-K_1\ge0$.
5. **Step 7.** The substitution $\log t/\log W_0=\sigma_0/x$, which gives $\sigma_0(t)=\sigma_0(1-1/x)$. Also check that $\Phi_n$, as defined by sup and min, is nonincreasing in both variables.
6. **Reduction to the core.** With $K_0=K_1$, Theorem 4 must reduce verbatim to core (R1)/(R2) and Step 9.
7. **Corollary 2.** $B(\varepsilon)$ dominates both branch remainders. Check also the tail formula for $\sum_{k\ge M}kr^k$.