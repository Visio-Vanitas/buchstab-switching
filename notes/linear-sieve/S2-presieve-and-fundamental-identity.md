# Section 5. From the weights bound to the sieve theorem (pre‑sieved form, arbitrary ℚ)

**Scope.** This section contains only the combinatorial and algebraic passage:

- the β = 2 Rosser weights, their elementary properties, and the exact identity $G=V\pm\sum T_n$;
- the precise form of the product hypothesis and its elementary properties;
- the reduction of the sieve theorem for $S(\mathcal A,\mathbb P,z)$ with an arbitrary pre‑sieve ℚ to a bound for $G(\lambda^\pm)$ on $\mathbb P\setminus\mathbb Q$.

The analytic bound for $G(\lambda^\pm)$ (the "weights bound") is **not** proved here. It is stated once, as EXTERNAL INPUT (W), with its exact hypotheses. Everything else is proved from scratch.

---

## Statement

### 0. Conventions

- $z\ge 2$ and $D>0$ are real numbers, and $s:=\log D/\log z$.
- $\mathbb P$ is a set of primes. Put $\mathbb P_z:=\{p\in\mathbb P:\ p<z\}$, which is finite, and $P(z):=\prod_{p\in\mathbb P_z}p$. "$d\mid P(z)$" means $d$ is squarefree with all prime factors in $\mathbb P_z$.
- For a finite set of primes $\mathcal P$, $\mathcal S(\mathcal P)$ is the set of squarefree products of elements of $\mathcal P$, including $1$.
- Every $d\in\mathcal S(\mathcal P)$ with $\omega(d)=r\ge1$ has a unique **decreasing factorisation** $d=p_1p_2\cdots p_r$ with $p_1>\dots>p_r$.
  - Its $j$‑th **prefix** is $d_{(j)}:=p_1\cdots p_j$, with $d_{(0)}:=1$.
  - Its least prime factor is $p^-(d):=p_r$, and $p^-(1):=+\infty$.
- A set $\mathcal D\subseteq\mathcal S(\mathcal P)$ is **prefix‑closed** if $d\in\mathcal D$ implies $d_{(j)}\in\mathcal D$ for all $j$.
- A real function $g$ on $\mathcal S(\mathcal P)$ is **multiplicative** if $g(1)=1$ and $g(de)=g(d)g(e)$ whenever $(d,e)=1$. Equivalently, $g(d)=\prod_{p\mid d}g(p)$.
- For real $w$ (or $w=\infty$):
$$V_{\mathcal P,g}(w):=\prod_{q\in\mathcal P,\ q<w}(1-g(q)).$$

### Definition 1 (β = 2 Rosser–Jurkat–Richert weights of level D on a finite prime set)

Let $\mathcal P'$ be a finite set of primes and $D>0$.

- $\mathcal D^+=\mathcal D^+(\mathcal P',D)$ is the set of $d=p_1\cdots p_r\in\mathcal S(\mathcal P')$ (decreasing factorisation) such that
$$p_1\cdots p_{m-1}\,p_m^3<D\qquad\text{for every **odd** } m \text{ with } 1\le m\le r.$$
- $\mathcal D^-$ is defined in the same way with "**even** $m$".
- In particular $1\in\mathcal D^\pm$, since there are no conditions.
- Put
$$\lambda^\pm_d:=\mu(d)\,\mathbf 1_{\mathcal D^\pm}(d)\quad(d\in\mathcal S(\mathcal P')),\qquad G(\lambda^\pm;g):=\sum_{d\in\mathcal S(\mathcal P')}\lambda^\pm_d\,g(d).$$
- When $\mathcal P'\subset[2,z)$ this is the quantity [BJS] writes $G(z,\lambda^\pm)$.

### Definition of $T_n$

This is [BJS] `eq: def-T-n-D-z`, with prime set $\mathcal P'$. For $n\ge1$, put $y_m:=(D/(p_1\cdots p_m))^{1/2}$ and
$$T_n^{\mathcal P'}(D,z):=\sum_{\substack{p_1>\dots>p_n,\ p_i\in\mathcal P'\\ y_n\le p_n,\ p_1<z\\ p_m<y_m\ \forall m<n,\ m\equiv n\ (2)}} g(p_1\cdots p_n)\,V_{\mathcal P',g}(p_n).$$

### Lemma 1 (elementary properties of the weights)

Let $\mathcal P'$ be finite and $D>0$.

- (a) $\lambda^\pm_1=1$.
- (b) $\lambda^\pm_d\in\{-1,0,1\}$.
- (c) If $D>1$, then every $d$ with $\lambda^+_d\ne0$ satisfies $d<D$. No other condition is needed. A prime $p$ lies in $\operatorname{supp}\lambda^+$ iff $p^3<D$.
- (d) $\operatorname{supp}\lambda^-\subseteq[1,D)$ **if and only if** $D>1$ and every $p\in\mathcal P'$ satisfies $p<D$.
  - Every $p\in\mathcal P'$ lies in $\operatorname{supp}\lambda^-$.
  - The condition holds whenever $\mathcal P'\subset[2,z)$ and $D\ge z$, i.e. $s\ge1$.
  - $D\ge z^2$ is **not** needed for the support; it is needed only for the analytic bound (W−).
- (e) $\mathcal D^+$ and $\mathcal D^-$ are prefix‑closed.

### Lemma 2 (exact boundary decomposition)

Let $\mathcal P'$ be finite and $\mathcal D\subseteq\mathcal S(\mathcal P')$ prefix‑closed with $1\in\mathcal D$. Define the boundary
$$\partial\mathcal D:=\{(a,p):\ a\in\mathcal D,\ p\in\mathcal P',\ p<p^-(a),\ ap\notin\mathcal D\}.$$
Then for every multiplicative real $g$ on $\mathcal S(\mathcal P')$,
$$\sum_{d\in\mathcal D}\mu(d)g(d)\;=\;V_{\mathcal P',g}(\infty)\;+\;\sum_{(a,p)\in\partial\mathcal D}\mu(a)\,g(a)\,g(p)\,V_{\mathcal P',g}(p).$$

### Corollary 3 (sieve inequalities)

For every finite $\mathcal P'$, every $D>0$ and every $n\in\mathcal S(\mathcal P')$,
$$\sum_{d\mid n}\lambda^-_d\;\le\;[n=1]\;\le\;\sum_{d\mid n}\lambda^+_d .$$
More precisely, $\sum_{d\mid n}\lambda^\pm_d=[n=1]\pm N^\pm(n)$, where $N^\pm(n)$ is a nonnegative integer.

For an arbitrary positive integer $m$ apply this to $n=(m,\prod_{p\in\mathcal P'}p)$:
$$\sum_{d\mid (m,\prod\mathcal P')}\lambda^-_d\le[(m,\textstyle\prod\mathcal P')=1]\le\sum_{d\mid(m,\prod\mathcal P')}\lambda^+_d .$$

### Corollary 4 (fundamental identity)

Let $\mathcal P'\subset[2,z)$ be finite, $D>0$, and $g$ multiplicative and real on $\mathcal S(\mathcal P')$. No sign or size condition on $g$ is needed. Then
$$G(\lambda^+;g)=V_{\mathcal P',g}(z)+\sum_{n\ \mathrm{odd}}T_n^{\mathcal P'}(D,z),\qquad G(\lambda^-;g)=V_{\mathcal P',g}(z)-\sum_{n\ \mathrm{even}\ \ge2}T_n^{\mathcal P'}(D,z).$$
Both sums are finite, because $T_n=0$ for $n>|\mathcal P'|$.

### Definition 2 (the all‑levels product hypothesis)

Let $\mathcal P'\subset[2,z)$ be finite, $0\le g(p)<1$ on $\mathcal P'$, and $\varepsilon>0$.

**(H\*)** For all primes $p\le p'$ in $\mathcal P'$ (equality allowed):
$$\prod_{q\in\mathcal P',\ p\le q\le p'}(1-g(q))^{-1}\ \le\ (1+\varepsilon)\,\frac{\log p'}{\log p}.$$

**(H\_real)** For all real $u,w$ with $1<u<w\le z$:
$$\prod_{q\in\mathcal P',\ u\le q< w}(1-g(q))^{-1}\ \le\ (1+\varepsilon)\,\frac{\log w}{\log u}.$$

### Lemma 5 (properties of (H\*))

Let $\mathcal P'\subset[2,z)$ be finite and $0\le g<1$ on $\mathcal P'$.

- (a) **Equivalence.** (H\*) ⟺ (H\_real) ⟺ (H\_real) with "$<$" in place of "$\le$".
- (b) **Monotonicity.** If (H\*) holds for $(\mathcal P',g,\varepsilon)$, then it holds:
  - for $(\mathcal P'',g,\varepsilon)$ for every $\mathcal P''\subseteq\mathcal P'$;
  - for $(\mathcal P',g,\varepsilon')$ for every $\varepsilon'\ge\varepsilon$.
- (c) **Self‑similarity.** If (H\*) holds for $(\mathcal P',z)$, then (H\_real) holds for $(\mathcal P'\cap[2,w),w)$ for every real $2\le w\le z$. These are exactly the sub‑levels at which the Jurkat–Richert induction is run: tops $p_k$ and real tops $D_k^{1/3}$.
- (d) **Comparison with [BJS].** (H\*) implies the hypothesis `eq:cond1` / `eq:prod11` of [BJS] (fixed top $z$, strict inequality). The converse is false in general (referee reports on this note).
- (e) **Necessary single‑prime condition.** (H\*) implies $g(p)\le\varepsilon/(1+\varepsilon)$ for every $p\in\mathcal P'$.

### EXTERNAL INPUT (W) — the weights bound (companion section; not proved here)

> **(W)** Let $z\ge2$, let $\mathcal P'\subset[2,z)$ be finite, and let $g$ be multiplicative on $\mathcal S(\mathcal P')$ with $0\le g(p)<1$. Let $0<\varepsilon\le 1/74$ and assume (H\*) for $(\mathcal P',g,\varepsilon)$. Let $D>0$, $s=\log D/\log z$, and let $\lambda^\pm$ be the weights of Definition 1 on $\mathcal P'$. Then:
>
> - **(W+)** if $s\ge1$: $\ G(\lambda^+;g)\le V_{\mathcal P',g}(z)\,\bigl(F(s)+\varepsilon C_1(\varepsilon)e^2h(s)\bigr)$;
> - **(W−)** if $s\ge2$: $\ G(\lambda^-;g)\ge V_{\mathcal P',g}(z)\,\bigl(f(s)-\varepsilon C_2(\varepsilon)e^2h(s)\bigr)$.
>
> Here $F,f$ are as in [BJS] `def-f(s)-F(s)`, $h$ is as in [BJS] `eq-def-h(s)`, and $C_1(\varepsilon),C_2(\varepsilon)$ are whatever constants the companion section proves (W) with.

Notes on (W):

- In [BJS] this is Prop. `theo:G`, with $C_1=\sum\tau_{2n-1}$, $C_2=\sum\tau_{2n}$ and Table `tab:fF`. There it is stated under the fixed‑$z$ hypothesis, under which its proof is invalid. The referees report that Lemma `lemma:expf_n` is false as stated (n = 3, s = 1.5).
- By Corollary 4, (W±) is equivalent to the corresponding bound on $\sum_{n\ \mathrm{odd/even}}T_n^{\mathcal P'}(D,z)$, which is what the companion section bounds.

### Theorem 6 (explicit linear sieve with an arbitrary pre‑sieve)

**Hypotheses.**

1. $a:\mathbb N\to[0,\infty)$ with $|\mathcal A|:=\sum_m a(m)<\infty$. For $d\ge1$ put $|\mathcal A_d|:=\sum_{d\mid m}a(m)$, and $S(\mathcal A,\mathbb P,z):=\sum_{(m,P(z))=1}a(m)$.
2. $\mathbb P$ is a set of primes and $z\ge2$ is real.
3. $\mathbb Q\subseteq\mathbb P_z$ is an **arbitrary** subset, not necessarily an initial segment. Put $Q:=\prod_{p\in\mathbb Q}p$ (with $Q=1$ if $\mathbb Q=\emptyset$) and $\mathcal P':=\mathbb P_z\setminus\mathbb Q$.
4. $g$ is a real multiplicative function on the squarefree divisors of $P(z)$ with $0\le g(p)<1$ for $p\in\mathbb P_z$. Put $V(z):=\prod_{p\in\mathbb P_z}(1-g(p))$.
5. $X\ge0$ is real. For $d\mid P(z)$, $r(d)$ is **defined** by $|\mathcal A_d|=g(d)X+r(d)$. This is a definition, not an assumption; note that $r(1)=|\mathcal A|-X$.
6. $0<\varepsilon\le1/74$, and (H\*) holds for $(\mathcal P',g,\varepsilon)$, i.e. **only over $\mathbb P\setminus\mathbb Q$, at all levels**.
7. (W) holds for $(\mathcal P',g,\varepsilon,z)$. This is automatic once the companion section is proved.

**Conclusion.** Let $D>0$ and $s=\log D/\log z$, and put
$$R:=\sum_{d\mid P(z),\ d<QD}|r(d)| .$$

- **(Upper)** If $s\ge1$ (i.e. $D\ge z$):
$$S(\mathcal A,\mathbb P,z)\ \le\ X\,V(z)\bigl(F(s)+\varepsilon C_1(\varepsilon)e^2h(s)\bigr)+R .$$
- **(Lower)** If $s\ge2$ (i.e. $D\ge z^2$):
$$S(\mathcal A,\mathbb P,z)\ \ge\ X\,V(z)\bigl(f(s)-\varepsilon C_2(\varepsilon)e^2h(s)\bigr)-R .$$

**Refinements and complements.**

- $R$ may be replaced by
$$R^\pm:=\sum_{e\mid Q}\ \sum_{d\in\operatorname{supp}\lambda^\pm}|r(ed)|\ \le R,$$
in which every term has coefficient exactly 1.
- If $X>0$ and (W±) holds with strict inequality, then the corresponding conclusion holds with strict inequality.
- If ℚ is an arbitrary subset of $\mathbb P$ with $\mathbb Q\cap[2,z)$ finite, the theorem holds with $\mathbb Q$ replaced by $\mathbb Q\cap[2,z)$. Its conclusion then implies the conclusion with $R$ formed with $Q=\prod_{\mathbb Q\cap[2,z)}p$, which is at most the product over all of ℚ when that is finite.

### Theorem 6′ (variant with element‑dependent $g_m$, as in [BJS])

Keep hypotheses 1–3 of Theorem 6, and replace 4–7 by the following.

- For each $m\in\mathbb N$, $g_m$ is real multiplicative on the divisors of $P(z)$ with $0\le g_m(p)<1$.
- (H\*) and (W) hold for every $(\mathcal P',g_m,\varepsilon,z)$ with the same $\varepsilon$.
- $r(d):=|\mathcal A_d|-\sum_m a(m)g_m(d)$.
- $X_{\mathcal A}:=\sum_m a(m)\prod_{p\in\mathbb P_z}(1-g_m(p))$.

Then the conclusions of Theorem 6 hold with $XV(z)$ replaced by $X_{\mathcal A}$.

### Corollary 7 (template for $g=1/\varphi$; relevant to the frame note)

Setting:

- $N$ is even, $\mathbb P=\{p:\ p\nmid N\}$ (so $2\notin\mathbb P$), and $g(d)=1/\varphi(d)$ on odd squarefree $d$, so $g(p)=1/(p-1)<1$.
- $\mathbb Q_0$ is any finite set of odd primes, $\mathbb Q:=\mathbb Q_0\cap\mathbb P_z$, and $\mathcal U:=\{\text{odd primes}\}\setminus\mathbb Q_0$.

Statements:

- (i) If, for all primes $p\le p'$ in $\mathcal U$,
$$\prod_{q\in\mathcal U,\ p\le q\le p'}\frac{q-1}{q-2}\le(1+\varepsilon)\frac{\log p'}{\log p}, \tag{H\*$_\infty$}$$
then (H\*) holds for $\mathcal P'=\mathbb P_z\setminus\mathbb Q$ for **every** even $N$ and every $z\ge2$.
- (ii) Conversely, suppose some odd prime $p<2+1/\varepsilon$ is not in $\mathbb Q_0$. Then for every $z>p$ and every even $N$ with $p\nmid N$ (e.g. $N=2^k$), (H\*) fails for $\mathcal P'$.
  - Hence any statement uniform in $N$ requires $\mathbb Q_0\supseteq\{3\le p<2+1/\varepsilon\}$.
  - At $\varepsilon=1/100$ this means every odd prime $\le101$ (note $103\ge102$).
  - At any $\varepsilon\le1/74$ it means every odd prime $\le73$.
  - the frame note's current $\mathbb Q_0=\{3\le p<41\}$ violates this. For example $41\in\mathcal U$ and $1/39>1/74$.

---

## Proof

**Step 1 (Lemma 1(a), (b), (e)).**

- (a) $1$ has $r=0$, so there are no conditions; $1\in\mathcal D^\pm$ and $\mu(1)=1$.
- (b) $\lambda^\pm_d$ is either $\mu(d)\in\{\pm1\}$ ($d$ squarefree) or $0$.
- (e) The decreasing factorisation of a prefix $d_{(j)}$ is $(p_1,\dots,p_j)$. Its defining conditions are those of $d$ at indices $m\le j$, and each involves only $p_1,\dots,p_m$. So they are a subset of the conditions for $d$. ∎

**Step 2 (Lemma 1(c)).** Let $d=p_1\cdots p_r\in\mathcal D^+$.

- If $r=0$: $d=1<D$ because $D>1$.
- If $r$ is odd: the condition at $m=r$ gives $p_1\cdots p_{r-1}p_r^3<D$, so $d=p_1\cdots p_{r-1}p_r^3/p_r^2<D/p_r^2<D$.
- If $r\ge2$ is even: $m=r-1$ is odd, so $p_1\cdots p_{r-2}p_{r-1}^3<D$. Since $p_r<p_{r-1}$,
$$d=p_1\cdots p_{r-2}\,p_{r-1}\,p_r<p_1\cdots p_{r-2}p_{r-1}^2=\frac{p_1\cdots p_{r-2}p_{r-1}^3}{p_{r-1}}<\frac{D}{p_{r-1}}<D.$$
- For $r=1$ the only condition is $p_1^3<D$. ∎

**Step 3 (Lemma 1(d)).**

- "⟹": $1\in\operatorname{supp}\lambda^-$, so $D>1$ is needed. For $p\in\mathcal P'$, the tuple $(p)$ has no even index, so $p\in\mathcal D^-$ and $\lambda^-_p=-1\ne0$; hence $p<D$ is needed.
- "⟸": let $d=p_1\cdots p_r\in\mathcal D^-$.
  - $r=0$: $d=1<D$.
  - $r=1$: $d=p_1<D$ by assumption.
  - $r\ge2$ even: $m=r$ gives $d<D/p_r^2<D$.
  - $r\ge3$ odd: $m=r-1\ge2$ is even, and the computation of Step 2 gives $d<D/p_{r-1}<D$.
- If $\mathcal P'\subset[2,z)$ and $D\ge z$, then every $p\in\mathcal P'$ satisfies $p<z\le D$, and $D\ge z\ge2>1$. ∎

**Step 4 (Lemma 2).**

1. Since $g$ is multiplicative and $\mathcal P'$ is finite, expanding the product gives
$$\sum_{d\in\mathcal S(\mathcal P')}\mu(d)g(d)=\prod_{q\in\mathcal P'}(1-g(q))=V(\infty).$$
   Hence $\sum_{d\in\mathcal D}\mu g=V(\infty)-\sum_{d\in\mathcal S\setminus\mathcal D}\mu g$.

2. Let $\mathcal T$ be the set of triples $(a,p,b)$ with $(a,p)\in\partial\mathcal D$ and $b\in\mathcal S(\{q\in\mathcal P':q<p\})$. Define $\Phi(a,p,b)=apb$.

3. *$\Phi$ maps into $\mathcal S\setminus\mathcal D$.*
   - The primes of $b$ are $<p<p^-(a)$, so $apb$ is squarefree.
   - Its decreasing factorisation is (factorisation of $a$, $p$, factorisation of $b$), so $ap=(apb)_{(\omega(a)+1)}$.
   - If $apb\in\mathcal D$, prefix‑closedness would give $ap\in\mathcal D$, which is a contradiction.

4. *$\Phi$ is injective.* Let $d=apb$. All prefixes of $a$ lie in $\mathcal D$ (prefix‑closed, $a\in\mathcal D$), and $d_{(\omega(a)+1)}=ap\notin\mathcal D$. So $\omega(a)+1=j(d):=\min\{j:\ d_{(j)}\notin\mathcal D\}$. Thus $j(d)$, and hence $a=d_{(j-1)}$, $p=p_j$ and $b=d/d_{(j)}$, are determined by $d$.

5. *$\Phi$ is surjective.* Let $d\notin\mathcal D$. Then $j:=j(d)$ exists and $j\ge1$, since $d_{(0)}=1\in\mathcal D$. Put $a=d_{(j-1)}\in\mathcal D$ (minimality of $j$), $p=p_j<p^-(a)$, and $b=d/d_{(j)}$, whose primes are $<p$. Then $ap=d_{(j)}\notin\mathcal D$, so $(a,p,b)\in\mathcal T$.

6. For $(a,p,b)\in\mathcal T$, multiplicativity gives $\mu(apb)g(apb)=-\mu(a)g(a)g(p)\,\mu(b)g(b)$. Summing over $b$ for fixed $(a,p)$:
$$\sum_b\mu(b)g(b)=\prod_{q\in\mathcal P',q<p}(1-g(q))=V(p).$$
   Hence $\sum_{d\notin\mathcal D}\mu g=-\sum_{\partial\mathcal D}\mu(a)g(a)g(p)V(p)$, which proves the claim. ∎

**Step 5 (boundaries of $\mathcal D^\pm$).**

Let $a=p_1\cdots p_{m-1}\in\mathcal D^+$, $p\in\mathcal P'$ with $p<p^-(a)$, and $m:=\omega(a)+1$. The factorisation of $ap$ is $(p_1,\dots,p_{m-1},p)$. Its conditions at indices $<m$ are exactly those of $a$ and hold. The only possibly new condition is at index $m$, and it exists iff $m$ is odd. Hence
$$\partial\mathcal D^+=\{(a,p):\ a\in\mathcal D^+,\ p<p^-(a),\ \omega(a)+1\ \text{odd},\ a\,p^3\ge D\},\qquad \mu(a)=(-1)^{m-1}=+1 .$$
In the same way,
$$\partial\mathcal D^-=\{(a,p):\ a\in\mathcal D^-,\ p<p^-(a),\ \omega(a)+1\ \text{even},\ a\,p^3\ge D\},\qquad \mu(a)=-1 .$$
Both $\mathcal D^\pm$ are prefix‑closed and contain 1 (Lemma 1(a), (e)), so Lemma 2 applies.

**Step 6 (Corollary 3).**

1. Fix $n\in\mathcal S(\mathcal P')$ and let $g_n(d):=[d\mid n]$ on $\mathcal S(\mathcal P')$. It is multiplicative: $g_n(1)=1$, and for coprime squarefree $d,e$ we have $de\mid n\iff d\mid n$ and $e\mid n$.
2. Here:
   - $G(\lambda^\pm;g_n)=\sum_{d\mid n}\lambda^\pm_d$;
   - $V(\infty)=\prod_{q\in\mathcal P'}(1-[q\mid n])=[n=1]$;
   - each boundary term is $g_n(a)g_n(p)V(p)=[ap\mid n]\cdot[\text{no prime factor of }n\text{ is }<p]\in\{0,1\}$.
3. By Lemma 2 and Step 5:
   - $\sum_{d\mid n}\lambda^+_d=[n=1]+N^+(n)$, where $N^+(n)=\#\{(a,p)\in\partial\mathcal D^+:\ ap\mid n,\ p=p^-(n)\}\ge0$;
   - $\sum_{d\mid n}\lambda^-_d=[n=1]-N^-(n)$ with $N^-(n)\ge0$.
4. For general $m$, $(m,\prod\mathcal P')\in\mathcal S(\mathcal P')$, and $\{d\in\mathcal S(\mathcal P'): d\mid m\}=\{d: d\mid(m,\prod\mathcal P')\}$. ∎

**Step 7 (Corollary 4).**

1. Apply Lemma 2 with $g$ and $\mathcal D^\pm$. Since $\mathcal P'\subset[2,z)$, $V(\infty)=V_{\mathcal P',g}(z)$. Since $(a,p)=1$, $g(a)g(p)=g(ap)$.

2. Group the boundary terms by $n:=\omega(ap)=m$. For the upper weights, the terms with a given odd $n$ are indexed by tuples $p_1>\dots>p_n$ in $\mathcal P'$ with
$$p_1\cdots p_{j-1}p_j^3<D\ \ (j<n,\ j\ \text{odd})\qquad\text{and}\qquad p_1\cdots p_{n-1}p_n^3\ge D,$$
   each with weight $g(p_1\cdots p_n)V(p_n)$.

3. Compare with $T_n$. All quantities are positive, and $t\mapsto t^2$ is increasing on $[0,\infty)$.
   - $p_m<y_m\iff p_m^2<D/(p_1\cdots p_m)\iff p_1\cdots p_{m-1}p_m^3<D$.
   - $y_n\le p_n\iff D/(p_1\cdots p_n)\le p_n^2\iff D\le p_1\cdots p_{n-1}p_n^3$.
   - "$m<n$, $m\equiv n\pmod 2$" means "odd $m<n$" for odd $n$, and "even $m<n$" for even $n$.
   - $p_1<z$ is automatic.

   So the $n$‑th group is exactly $T_n^{\mathcal P'}(D,z)$, with coefficient $\mu(a)=+1$ for upper and $-1$ for lower. Odd $n$ arise only for $\lambda^+$ and even $n\ge2$ only for $\lambda^-$ (Step 5). ∎

This is [BJS]'s use of "[Nathanson, Lemma 9.3]" in the proof of Prop. `theo:G`. Here it is proved for the weights of Definition 1. Whether Definition 1 coincides verbatim with Nathanson's Theorem 9.3 was not checked (Nathanson not read). It does not need to, because every property used below is proved above.

**Step 8 (Lemma 5).**

*(a), (H\*) ⟹ (H\_real) with "<".* Let $1<u<w\le z$ and $S:=\mathcal P'\cap[u,w)$.
- If $S=\emptyset$, the product is $1<(1+\varepsilon)\log w/\log u$.
- Otherwise let $p=\min S$ and $p'=\max S$. Then $S=\mathcal P'\cap[p,p']$, so the product equals the (H\*) product for $(p,p')$, which is $\le(1+\varepsilon)\log p'/\log p$.
- Since $p\ge u>1$ and $p'<w$, we have $\log p'/\log p<\log w/\log u$.

*(a), (H\_real) ⟹ (H\*).* Let $p\le p'$ in $\mathcal P'$.
- Let $p'^+$ be the next element of $\mathcal P'$ above $p'$ (or $+\infty$), and take $w_k\downarrow p'$ with $p'<w_k\le\min(p'^+,z)$. This is possible because $p'<z$.
- Then $\mathcal P'\cap[p,w_k)=\mathcal P'\cap[p,p']$, and (H\_real) with $u=p$ gives $\prod\le(1+\varepsilon)\log w_k/\log p\to(1+\varepsilon)\log p'/\log p$.
- The "<" version implies the "≤" version trivially, which closes the cycle.

*(b).* For $\mathcal P''\subseteq\mathcal P'$ and $p\le p'$ in $\mathcal P''$: every factor $(1-g(q))^{-1}\ge1$, so the product over $\mathcal P''\cap[p,p']$ is at most the product over $\mathcal P'\cap[p,p']$, which is $\le(1+\varepsilon)\log p'/\log p$. Increasing $\varepsilon$ only increases the right side.

*(c).* (H\*) for $\mathcal P'$ implies (H\*) for $\mathcal P'\cap[2,w)$ by (b). Apply (a) with top $w$, noting $\mathcal P'\cap[2,w)\subset[2,w)$.

*(d).* (a) with $w=z$ gives the [BJS] hypothesis in strict form.

*(e).* Take $p=p'$: $(1-g(p))^{-1}\le1+\varepsilon$, i.e. $g(p)\le\varepsilon/(1+\varepsilon)$. ∎

**Step 9 (Theorem 6, set‑up).**

- $\mathbb Q$ and $\mathcal P'$ partition $\mathbb P_z$, so $P(z)=Q\cdot P'$ with $P':=\prod_{p\in\mathcal P'}p$ and $(Q,P')=1$. Hence $(m,P(z))=1\iff(m,Q)=1$ and $(m,P')=1$.
- Write $V_{\mathbb Q}:=\prod_{p\in\mathbb Q}(1-g(p))$, which is $>0$ because $g<1$, and $V'(z):=V_{\mathcal P',g}(z)$. Then $V_{\mathbb Q}V'(z)=V(z)$.
- Let $\lambda^\pm$ be the weights of Definition 1 on $\mathcal P'$ at level $D$, and $G^\pm:=G(\lambda^\pm;g|_{\mathcal S(\mathcal P')})$.

**Step 10 (pointwise inequality).** For every $m$, Corollary 3 gives $[(m,P')=1]\le\sum_{d\mid P',\,d\mid m}\lambda^+_d$. Multiply by $[(m,Q)=1]\ge0$ and by $a(m)\ge0$:
$$a(m)[(m,P(z))=1]\ \le\ a(m)\,[(m,Q)=1]\sum_{d\mid P',\,d\mid m}\lambda^+_d .$$
Only the indicator $[(m,Q)=1]$ is multiplied, and it is nonnegative. Its Möbius expansion is substituted only afterwards, as an identity.

**Step 11 (expansion).**

1. Substitute $[(m,Q)=1]=\sum_{e\mid Q,\,e\mid m}\mu(e)$ and sum over $m$.
2. The double sum over $(e,d)$ is finite, with coefficients bounded by $2^{|\mathbb P_z|}$, and $\sum a(m)<\infty$. So the order of summation may be exchanged.
3. Since $(e,d)=1$, "$e\mid m$ and $d\mid m$" is equivalent to "$ed\mid m$". Therefore
$$S(\mathcal A,\mathbb P,z)\ \le\ \Sigma^+:=\sum_{e\mid Q}\sum_{d\mid P'}\mu(e)\lambda^+_d\,|\mathcal A_{ed}| .$$
4. Each $ed\mid P(z)$, so $|\mathcal A_{ed}|=g(ed)X+r(ed)=g(e)g(d)X+r(ed)$ by multiplicativity. Hence, exactly,
$$\Sigma^+=X\Bigl(\sum_{e\mid Q}\mu(e)g(e)\Bigr)\Bigl(\sum_{d\mid P'}\lambda^+_dg(d)\Bigr)+\mathcal R^+=X\,V_{\mathbb Q}\,G^+ +\mathcal R^+,\qquad \mathcal R^+:=\sum_{e\mid Q}\sum_{d\mid P'}\mu(e)\lambda^+_d\,r(ed).$$

**Step 12 (remainder: where QD comes from, and no coefficient).**

1. *Injectivity.* The map $(e,d)\mapsto ed$ on $\{e\mid Q\}\times\{d\mid P'\}$ is injective, because $(Q,P')=1$ gives $e=(ed,Q)$ and $d=(ed,P')$.
2. *Size of each coefficient.* Each coefficient satisfies $|\mu(e)\lambda^+_d|\le1$, and it is nonzero only for $d\in\operatorname{supp}\lambda^+$.
3. *The bound $QD$.* For such $d$, $d<D$ by Lemma 1(c), since $D\ge z\ge2>1$. Also $e\le Q$. Hence $ed\le Qd<QD$. Every divisor $e$ of $Q$ occurs, because sieving by ℚ is exact Möbius inversion, with no truncation. This is the sole origin of the factor $Q$: the remainder moduli are (any divisor of $Q$) × (a modulus $<D$).
4. Therefore
$$|\mathcal R^+|\le\sum_{e\mid Q}\sum_{d\in\operatorname{supp}\lambda^+}|r(ed)|=R^+\le\sum_{d\mid P(z),\,d<QD}|r(d)|=R .$$
5. **No coefficient is needed in front of $|r(d)|$.** Each modulus occurs at most once (injectivity), with coefficient of absolute value at most 1.

**Step 13 (upper bound).**

1. Lemma 5(b)/(H\*) holds for $\mathcal P'$, and $s\ge1$. So (W+) gives $G^+\le V'(z)(F(s)+\varepsilon C_1e^2h(s))$.
2. Multiply by $XV_{\mathbb Q}\ge0$ (using $X\ge0$ and $V_{\mathbb Q}>0$). With $V_{\mathbb Q}V'(z)=V(z)$:
$$S\le XV(z)(F(s)+\varepsilon C_1e^2h(s))+R .$$
3. If $X>0$ and (W+) is strict, the multiplication preserves strictness. ∎

**Step 14 (lower bound).**

1. Corollary 3 gives $[(m,P')=1]\ge\sum_{d\mid(m,P')}\lambda^-_d$. Steps 10–11 with reversed inequality give $S\ge XV_{\mathbb Q}G^-+\mathcal R^-$.
2. In Step 12, $d<D$ now uses Lemma 1(d): every prime of $\mathcal P'$ is $<z\le z^2\le D$. Hence $|\mathcal R^-|\le R^-\le R$.
3. (W−) ($s\ge2$) multiplied by $XV_{\mathbb Q}\ge0$ gives the claim. ∎

**Step 15 (ℚ not contained in $\mathbb P_z$).** For general ℚ ⊆ ℙ, put $\mathbb Q_z:=\mathbb Q\cap[2,z)$.

- $S$ and $V(z)$ do not involve ℚ.
- $\{p\in\mathbb P\setminus\mathbb Q:\ p<z\}=\mathbb P_z\setminus\mathbb Q_z$, so the product hypothesis is the same.
- $Q_z\le Q$ implies $R(Q_z)\le R(Q)$.

So the theorem applied with $\mathbb Q_z$ implies the statement with $Q$. ∎

**Step 16 (Theorem 6′).** Steps 10–12 are unchanged. In Step 11, $|\mathcal A_{ed}|=\sum_m a(m)g_m(e)g_m(d)+r(ed)$, so
$$\Sigma^\pm=\sum_m a(m)\,V_{\mathbb Q,m}\,G_m^\pm+\mathcal R^\pm .$$
The sum converges absolutely, since $0\le g_m(\cdot)\le1$ on squarefree divisors of $P(z)$. Apply (W±) to each $G_m^\pm$ and multiply by $a(m)V_{\mathbb Q,m}\ge0$. The factor $F(s)+\dots$ (resp. $f(s)-\dots$) does not depend on $m$. Summing over $m$ gives $X_{\mathcal A}(\cdots)$, because $\sum_m a(m)V_{\mathbb Q,m}V'_m(z)=X_{\mathcal A}$. ∎

**Step 17 (Corollary 7).**

*(i).* Let $p\in\mathcal P'=\mathbb P_z\setminus\mathbb Q$. Then $p\nmid N$, so $p$ is odd. If $p\in\mathbb Q_0$, then $p\in\mathbb Q_0\cap\mathbb P_z=\mathbb Q$, a contradiction. So $p\in\mathcal U$, and hence $\mathcal P'\subseteq\mathcal U$. For any $p\le p'$ in $\mathcal U$ with $\{q\in\mathcal U:p\le q\le p'\}$ finite, (H\*$_\infty$) restricted to the finite set $\mathcal U\cap[2,z)$ is (H\*) for that set. Lemma 5(b) then transfers it to $\mathcal P'$.

*(ii).* Suppose the odd prime $p\notin\mathbb Q_0$, $p\nmid N$ and $z>p$. Then $p\in\mathcal P'$, and $(1-g(p))^{-1}=1+1/(p-2)>1+\varepsilon$ because $p<2+1/\varepsilon$. This contradicts Lemma 5(e). The numerical instances follow from $2+100=102$ and $2+74=76$. ∎

---

## What is not proved here

1. **Input (W), i.e. the analytic weights bound, and the values $C_1(\varepsilon)$, $C_2(\varepsilon)$.**
   - Not proved here. Under the fixed‑$z$ hypothesis of [BJS] it is not available: the referee reports show [BJS] Lemma `lemma:expf_n` is false as stated.
   - Under (H\*) it is the companion section's job. By Lemma 5(c), (H\*) supplies (H\_real) at every top $w\le z$ (primes $p_k$ and real $D_k^{1/3}$) for the restricted prime sets $\mathcal P'\cap[2,w)$. The companion must check that its proof needs nothing beyond this. In particular, [BJS]'s "$K$ with $1<K<1+\varepsilon$" quantifier must be reconciled with the closed "$\le$" form; the "<" form is available by Lemma 5(a).
   - Table `tab:fF` (via τ_n, Lemma `lem: taup`, `lemma:exprec`, and the referee‑flagged inconsistency in `lem:hsm1`) is not verified.
   - The identities $F=1+\sum_{n\ \mathrm{odd}}f_n$ and $f=1-\sum_{n\ \mathrm{even}}f_n$ ([BJS] cites Nathanson Thm 9.4) are not verified.
   - The facts $F\ge1\ge f$ (needed by (W) when $\mathcal P'=\emptyset$) are taken from [JS] §2 as quoted.
2. **Whether Theorem 6 holds under the fixed‑$z$ hypothesis alone.** Open; no sieve LP was solved.
3. **That Definition 1 coincides with Nathanson's Theorem 9.3 weights.** Not checked; not needed, since all properties are proved above.
4. **Numerical verification of (H\*$_\infty$) for any $\mathbb Q_0$ and $\varepsilon$, including a certified tail beyond a finite range.** Not done. Only the necessary condition 7(ii) is proved. The referee value $\log\prod_{3\le p\le101}p=87.650$ is quoted, not recomputed.
5. **the frame note application.** Bounds on $r(d)$, the repaired Regime 3, and the choice of $\mathbb Q_0$ are not addressed.
6. **The script below.** I have not run it.

## Checks a referee should make

1. **Lemma 1(c), even $r$.** The strict step $p_r<p_{r-1}$ is what gives $d<D$ from the condition at $m=r-1$.
2. **Lemma 1(d).** The exact condition is $\max\mathcal P'<D$, not $D\ge z^2$. This corrects this note §8.
3. **Lemma 2.** Prefix‑closedness is used in both directions: well‑definedness (Step 4.3) and injectivity (Step 4.4).
4. **Step 5 signs.** The boundary length $m$ is odd for $\lambda^+$, so $\mu(a)=+1$; it is even for $\lambda^-$, so $\mu(a)=-1$.
5. **Step 7, matching with [BJS] `eq: def-T-n-D-z`.** Check strict versus non‑strict: $p_m<y_m$ corresponds to "$<D$", and $y_n\le p_n$ corresponds to "$D\le$".
6. **Step 10.** Only the indicator $[(m,Q)=1]\ge0$ multiplies the inequality.
7. **Step 12.** Injectivity uses $(Q,P')=1$, which holds because ℚ ∩ 𝒫′ = ∅ by construction. Also check $ed\le Qd<QD$, and coefficient $\le1$. Note that $d=1$ contributes $r(e)$ for every $e\mid Q$, and $r(1)=|\mathcal A|-X$.
8. **Step 13.** $X\ge0$ and $V_{\mathbb Q}>0$ are used. (W) is applied to $\mathcal P'$, not to $\mathbb P_z$.
9. **Lemma 5(a).** The direction (H\_real) ⟹ (H\*) needs $p'<z$, so that some $w\in(p',z]$ exists.
10. **the frame note fit.** For $\mathcal A_q$, take $a_q(m)=a(m)[q\mid m]$, $X=|\mathcal A_q|$, $g=1/\varphi$, and $r_q(d)=|\mathcal A_{qd}|-|\mathcal A_q|/\varphi(d)$. Then $2\notin\mathbb P$, so $g<1$. Also $s_q\ge2.7624\ge1$ (upper) and $s=8.0124\ge2$ (lower).
11. **Run the script.** As a mutation test, swap `upper` parity in `in_support`; the W3/W4 checks must then fail.

## Code

```python
#!/usr/bin/env python3
"""
rosser_presieve_check.py -- exact brute-force checks of the algebraic statements of
Section 5 (Lemma 1, Corollaries 3-4, Theorem 6 Steps 10-12) on random small instances.
Arithmetic: Python ints and fractions.Fraction only; no floats anywhere.
Random: random.Random(20261125), integer methods only.

Checked (exact equalities / exact inequalities):
 W1 lambda^{+-}(1)=1, lambda^{+-}(d) in {-1,0,1}.
 W2 supp lambda^+ in [1,D) (D>1); supp lambda^- in [1,D) when max P' < D;
    every p in P' is in supp lambda^-.
 W3 for every n | P':  sum_{d|n} lambda^- <= [n=1] <= sum_{d|n} lambda^+.
 W4 G(lambda^+)=V(z)+sum_{n odd}T_n, G(lambda^-)=V(z)-sum_{n even}T_n, with T_n
    computed from the BJS definition: p_m<y_m tested as p_m^2*(p_1..p_m) < D,
    y_n<=p_n tested as D <= p_n^2*(p_1..p_n).
 P1 sum_m a(m)[(m,Q)=1] sum_{d|(m,P')} lambda(d) = X*V_Q*G + sum mu(e)lambda(d) r(ed),
    r(k) := |A_k| - g(k) X  (k | P(z)).
 P2 (e,d)->ed injective, ed | P(z), ed < Q*D on the support; |remainder| <= R.
 P3 S <= X V_Q G^+ + R ; S >= X V_Q G^- - R (when max P' < D).
Expected output: two lines ending in 'OK' and the line 'ALL CHECKS PASSED'.
"""
from fractions import Fraction
from itertools import combinations
from math import gcd
import random


class CheckFailed(Exception):
    pass


def check(cond, msg):
    if not cond:
        raise CheckFailed(msg)


def primes_upto(n):
    if n < 2:
        return []
    s = bytearray([1]) * (n + 1)
    s[0] = 0
    s[1] = 0
    i = 2
    while i * i <= n:
        if s[i]:
            for j in range(i * i, n + 1, i):
                s[j] = 0
        i += 1
    return [k for k in range(n + 1) if s[k]]


def iprod(t):
    r = 1
    for x in t:
        r *= x
    return r


def gprod(t, g):
    r = Fraction(1)
    for p in t:
        r *= g[p]
    return r


def in_support(tup, D, upper):
    """tup decreasing. Condition at index m: p_1...p_{m-1}*p_m^3 < D,
    imposed at odd m (upper=True) or even m (upper=False)."""
    pre = 1
    for m, p in enumerate(tup, start=1):
        if (m % 2 == 1) == upper:
            if not (pre * p ** 3 < D):
                return False
        pre *= p
    return True


def lam(tup, D, upper):
    if in_support(tup, D, upper):
        return -1 if len(tup) % 2 else 1
    return 0


def subsets(desc):
    """All sub-tuples of a decreasing tuple/list, as decreasing tuples."""
    out = []
    for k in range(len(desc) + 1):
        out.extend(combinations(desc, k))
    return out


def Vprod(g, primes, w):
    """prod_{q in primes, q < w}(1-g[q]); w=None: no upper limit."""
    r = Fraction(1)
    for q in primes:
        if w is None or q < w:
            r *= (1 - g[q])
    return r


def T_bjs(n, D, Pdesc, g):
    """T_n(D,z) from the BJS definition, prime set Pdesc (all < z)."""
    total = Fraction(0)
    for tup in combinations(Pdesc, n):
        pre = 1
        ok = True
        for m, p in enumerate(tup, start=1):
            pre *= p                       # pre = p_1...p_m
            if m < n and (n - m) % 2 == 0:
                if not (p * p * pre < D):  # p_m < y_m
                    ok = False
                    break
        if not ok:
            continue
        if not (D <= tup[-1] ** 2 * pre):  # y_n <= p_n ; pre = p_1...p_n
            continue
        total += gprod(tup, g) * Vprod(g, Pdesc, tup[-1])
    return total


def test_weights(rng, trials):
    base = primes_upto(60)
    ndiv = 0
    for _ in range(trials):
        k = rng.randint(0, 9)
        Pp = sorted(rng.sample(base, k), reverse=True)
        z = (Pp[0] + 1 if Pp else 2) + rng.randint(0, 5)
        D = Fraction(rng.randint(2, z ** 5), rng.randint(1, 4))
        if D <= 1:
            D = Fraction(2)
        g = {p: Fraction(rng.randint(0, 9), 10) for p in Pp}
        divs = subsets(Pp)
        lamv = {True: {d: lam(d, D, True) for d in divs},
                False: {d: lam(d, D, False) for d in divs}}
        for upper in (True, False):
            check(lamv[upper][()] == 1, "lambda(1) != 1")
            for d in divs:
                l = lamv[upper][d]
                check(l in (-1, 0, 1), "|lambda| > 1")
                if l != 0:
                    if upper:
                        check(iprod(d) < D, "upper support not < D")
                    elif (not Pp) or Pp[0] < D:
                        check(iprod(d) < D, "lower support not < D")
        for p in Pp:
            check(lamv[False][(p,)] == -1, "prime not in supp lambda^-")
        for n in divs:
            sp = sum(lamv[True][d] for d in subsets(n))
            sm = sum(lamv[False][d] for d in subsets(n))
            one = 1 if len(n) == 0 else 0
            check(sm <= one <= sp, "sieve inequality fails at n=%r" % (n,))
            ndiv += 1
        Vz = Vprod(g, Pp, None)
        Gp = sum(lamv[True][d] * gprod(d, g) for d in divs)
        Gm = sum(lamv[False][d] * gprod(d, g) for d in divs)
        Todd = sum(T_bjs(n, D, Pp, g) for n in range(1, len(Pp) + 1, 2))
        Teven = sum(T_bjs(n, D, Pp, g) for n in range(2, len(Pp) + 1, 2))
        check(Gp == Vz + Todd, "G+ != V + sum odd T_n  (P'=%r, D=%s)" % (Pp, D))
        check(Gm == Vz - Teven, "G- != V - sum even T_n (P'=%r, D=%s)" % (Pp, D))
    print("W1-W4: %d instances, %d divisor checks: OK" % (trials, ndiv))


def test_presieve(rng, trials, M=2000):
    for _ in range(trials):
        z = rng.randint(8, 32)
        Pz = [p for p in primes_upto(z - 1) if rng.randint(0, 3) > 0]
        Qset = [p for p in Pz if rng.randint(0, 2) == 0]       # arbitrary subset
        Pp = sorted((p for p in Pz if p not in Qset), reverse=True)
        Q, PZ, PP = iprod(Qset), iprod(Pz), iprod(Pp)
        D = Fraction(rng.randint(2, z ** 4), rng.randint(1, 3))
        if D <= 1:
            D = Fraction(2)
        g = {p: Fraction(rng.randint(0, p - 1), p) for p in Pz}
        a = [0] + [rng.randint(0, 3) for _ in range(M)]
        X = Fraction(rng.randint(0, 4 * M), rng.randint(1, 6))
        rcache = {}

        def r(ktuple):
            key = iprod(ktuple)
            if key not in rcache:
                Ak = sum(a[m] for m in range(key, M + 1, key))
                rcache[key] = Ak - gprod(ktuple, g) * X
            return rcache[key]

        S = sum(a[m] for m in range(1, M + 1) if gcd(m, PZ) == 1)
        VQ, VPp, Vz = Vprod(g, Qset, None), Vprod(g, Pp, None), Vprod(g, Pz, None)
        check(VQ * VPp == Vz, "V factorisation")
        divsP = subsets(Pp)
        divsQ = subsets(sorted(Qset, reverse=True))
        low_ok = (not Pp) or Pp[0] < D
        R = Fraction(0)
        for k in subsets(sorted(Pz, reverse=True)):
            if iprod(k) < Q * D:
                R += abs(r(k))
        for upper in (True, False):
            lamv = {d: lam(d, D, upper) for d in divsP}
            sumlam = {iprod(n): sum(lamv[d] for d in subsets(n)) for n in divsP}
            LHS = sum(a[m] * sumlam[gcd(m, PP)]
                      for m in range(1, M + 1) if gcd(m, Q) == 1)
            G = sum(lamv[d] * gprod(d, g) for d in divsP)
            rem = Fraction(0)
            seen = set()
            for e in divsQ:
                mu_e = -1 if len(e) % 2 else 1
                for d in divsP:
                    if lamv[d] == 0:
                        continue
                    k = iprod(e) * iprod(d)
                    check(k not in seen, "(e,d)->ed not injective")
                    seen.add(k)
                    check(PZ % k == 0, "ed does not divide P(z)")
                    if upper or low_ok:
                        check(k < Q * D, "ed >= QD")
                    rem += mu_e * lamv[d] * r(e + d)
            check(LHS == X * VQ * G + rem, "pre-sieve identity fails")
            if upper:
                check(S <= LHS, "upper pointwise inequality")
                check(abs(rem) <= R, "upper remainder > R")
                check(S <= X * VQ * G + R, "upper bound")
            else:
                check(S >= LHS, "lower pointwise inequality")
                if low_ok:
                    check(abs(rem) <= R, "lower remainder > R")
                    check(S >= X * VQ * G - R, "lower bound")
    print("P1-P3: %d instances: OK" % trials)


if __name__ == "__main__":
    rng = random.Random(20261125)
    test_weights(rng, 200)
    test_presieve(rng, 120)
    print("ALL CHECKS PASSED")
```

**Expected output.**

```
W1-W4: 200 instances, <some integer> divisor checks: OK
P1-P3: 120 instances: OK
ALL CHECKS PASSED
```

Any `CheckFailed` would refute a claim above. The divisor‑check count is deterministic for the fixed seed but was not computed by hand.

**Sanity checks.**

- With $\mathcal P'=\emptyset$, W4 reduces to $G^\pm=1=V$.
- $T_1$ from `T_bjs` equals $\sum_{p^3\ge D}g(p)V(p)$, which is this note's (3.3).
- this note reports an independent check of $G=V\pm\sum T_n$ on 272 instances.
- Mutation tests:
  - Swapping the parity test in `in_support` must break W3/W4.
  - Removing the `gcd(m, Q) == 1` filter must break P1.