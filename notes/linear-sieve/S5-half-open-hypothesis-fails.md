# Section: the odd‑$n$, $1\le s<3$ branch under half‑open prime‑interval hypotheses

**Summary.**

1. **Under the half‑open hypothesis alone, Theorem A is false.** An explicit three‑prime profile satisfies the half‑open hypothesis with $K=1$, yet violates the claimed bound for $T_3$ at $s=1$ (Proposition N).
2. The failure sits exactly in the $W=D^{1/3}$ step: the last sifting prime below $D^{1/3}$ may be followed by a gap.
3. **Adding a gap parameter $\rho_*$ repairs the branch.** Theorem A holds with the *same* $\tau_n$, $\xi_{s_0}$ and $\tilde\xi$ (no new recursion) under $H'(z,K)$ together with $K-1+\rho_*(z)<\varepsilon$.
4. This is only a second‑order improvement over the closed form. For the the frame note profile (sifting primes from 41 on) it does not help.

## Statement

**Setting.** As in the core section (S0–S5), with the corrected $\gamma_{s_0}=e^{s_0-1.8}$ and the corrected $\tau_n$ of S.2.

**Definition H′(z,K) (half‑open, prime endpoints).** For every $q\in\mathbb P$ with $q<z$, and every $w\in(\mathbb P\cap(q,z))\cup\{z\}$:
$$\frac{V(q)}{V(w)}=\prod_{p\in\mathbb P,\ q\le p<w}(1-g(p))^{-1}\le K\frac{\log w}{\log q}.$$
- Every such pair $(q,w)$ is a run of consecutive sifting primes $q_i,\dots,q_{j-1}$ with $w=q_j$ or $w=z$. So this is exactly the hypothesis in the task.
- H′ is hereditary: H′(z,K) implies H′(p,K) for every $p\in\mathbb P$ with $p<z$, because the pairs for $p$ form a subset of the pairs for $z$.
- C(z,K) implies H′(z,K). This is Lemma 0(a) of the core, specialised to prime $u$.

**Definition (gap parameter).**
- If $\mathbb P\cap[2,z)=\emptyset$, put $\rho_*(z)=0$.
- Otherwise, for $q\in\mathbb P$ with $q<z$, let $q^+$ be the next element of $\mathbb P$ below $z$, or $q^+=z$ if there is none. Put
$$\rho_*(z):=\max_{q\in\mathbb P,\ q<z}\Bigl(1-\frac{\log q}{\log q^+}\Bigr)\in[0,1).$$
- For real $x$ put $W'_Z(x):=\min(\mathbb P\cap[x,Z))$, or $W'_Z(x):=Z$ if this set is empty.

**Theorem A_H.** Let $\varepsilon>0$, $K\ge1$, let $(c_n)$ be admissible (Fn), and let $\tau_n$ be exactly as in core S.2. Assume
- H′(z,K), and
- $K-1+\rho_*(z)<\varepsilon$.

Then for every $n\ge1$ and every real $D$ with $s=\log D/\log z\ge1$ ($n$ odd) or $s\ge2$ ($n$ even):
$$T_n(D,z)<V(z)\bigl(f_n(s)+\varepsilon\tau_ne^2h(s)\bigr).$$

Since Theorem B is purely combinatorial and Theorem C uses only Theorem A, **Theorem C and Corollary D hold verbatim** with "H(z,K), $K<1+\varepsilon$" replaced by "H′(z,K), $K-1+\rho_*(z)<\varepsilon$".

**Proposition N (half‑open alone is insufficient).** Take
- $\mathbb P=\{53,829,10007\}$;
- $D=10007\cdot829\cdot53^3$ and $z=D$ (so $s=1$);
- $g(53)=1-\frac{\log53}{\log829}$, $g(829)=1-\frac{\log829}{\log10007}$, $g(10007)=1-\frac{\log10007}{\log z}$.

Then:
- H′(z,1) holds, with equality in every instance.
- $T_3(D,z)/V(z)\in[0.5192,0.5193]$.
- $f_3(1)\le0.48263$.
- With $c_n=0.9607$ and $\varepsilon=10^{-3}$: $\varepsilon\tau_3\le0.0203$.

Hence $T_3(D,z)>V(z)\bigl(f_3(1)+\varepsilon\tau_3e^2h(1)\bigr)$, although $1\le K=1<1+\varepsilon$. For this profile $\rho_*(z)=\tfrac23$, while closed‑form C needs $K\ge(1-g(10007))^{-1}\approx3.02$.

**Corollary R (comparison).**
- $K_C\le K_H/(1-\rho_*)$ and $K_H\le K_C$, where $K_C,K_H$ are the least admissible constants in C and H′.
- Hence the core theorem applies whenever $K_H/(1-\rho_*)<1+\varepsilon$.
- Theorem A_H needs only $K_H+\rho_*<1+\varepsilon$. The gain is $(K_H-1+\rho_*)\rho_*/(1-\rho_*)$, which is second order.

## Proof

**Step 1 (exact identities at the real level).** Let $Z\in\mathbb P\cup\{z\}$ be a current top and $x$ real with $1<x<Z$, and put $W'=W'_Z(x)$.
- $\mathbb P\cap[x,W')=\emptyset$, so $\{p\in\mathbb P:p<x\}=\{p\in\mathbb P:p<W'\}$. Hence $V(x)=V(W')$.
- If $W'<Z$, then H′ with the pair $(W',Z)$ gives $V(x)/V(Z)=V(W')/V(Z)\le K\log Z/\log W'$.
- If $W'=Z$, the ratio is $1\le K$.
- Writing $s=\log D/\log Z$ and $s'=\log D/\log W'$, in both cases $V(x)/V(Z)\le Ks'/s$.

**Step 2 (the route suggested in the task, and why it is circular).** Let $n$ be odd, $s<3$, $x=D^{1/3}$, and suppose $W'\in\mathbb P$ with $W'<Z$.
- The $p$‑range of Step 4 of the core for $T_n(D,Z)$ is $\{p<x\}=\{p<W'\}$.
- For $T_n(D,W')$ we have $s'\le3$. The range is $\{p<W',\ p^3<D\}=\{p<x\}$; this also holds when $s'=3$.
- The inner sums $T_{n-1}(D/p,p)$ coincide. So **$T_n(D,Z)=T_n(D,W')$ exactly.**

However:
- If $s'<3$, bounding $T_n(D,W')$ is the same branch for the same $n$, at a top below which $[x,W')$ contains no sifting prime. The reduction makes no progress.
- If one closed it by a double induction on $(n,\#\mathbb P\cap[2,\text{top}))$, the conversion back costs a factor $\frac{s'}{s}\frac{h(s')}{h(s)}$ on the $h$‑part. For $s<s'\le2$ this equals $s'/s$, which is up to 2 and is not $1+O(\varepsilon)$.

So this route only reduces to the gap case $W'=\text{top}$, which must be handled directly. The odd‑$n$ rule makes the $f_n$‑part lossless: $K\frac{s'}{s}\cdot\frac{3f_n(3)}{s'}=Kf_n(s)$. The loss lies entirely in the error terms.

**Step 3 (Lemma A at the real level with an inflated constant).** Continue with $n$ odd, $1\le s<3$, top $Z$, $x=D^{1/3}<Z$.
- If $x\le2$ or $\mathbb P\cap[2,x)=\emptyset$, then $T_n=0$ and the claim is trivial.
- Otherwise, for $q\in\mathbb P$ with $q<x$, apply H′ to the pair $(q,W')$, where $W'\in\mathbb P\cup\{Z\}$ and $q<W'$:
$$\frac{V(q)}{V(x)}=\frac{V(q)}{V(W')}\le K\frac{\log W'}{\log q}=\frac{3K}{s'}\cdot\frac{\log x}{\log q}.$$
- Here $K':=3K/s'\ge1$ because $s'\le3$. Core Lemma A (Step 5) does not require $W$ to be prime. Applying it with $W=x$ and constant $K'$, and then Corollary A′ with $\sigma=3$, gives
$$T_n(D,Z)\le V(x)\Bigl[(K'-1)\Psi(2)+\frac{K'}3\int_3^\infty\Psi(t-1)\,dt\Bigr],\qquad \Psi=f_{n-1}+h_{n-1}.$$
- This uses: U1 via heredity of H′; the domain check $s'(p)>2$ as in core Step 10; and $\Psi$ nonincreasing and $\ge0$.

**Step 4 (Case III bound).** Multiply Step 3 by $V(x)/V(Z)\le Ks'/s$ from Step 1:
$$\frac{T_n}{V(Z)}\le\frac1s\Bigl[(3K^2-Ks')\Psi(2)+K^2\int_3^\infty\Psi(t-1)dt\Bigr].$$
Write $3K^2-Ks'=3K(\eta+\rho')$, with $\eta=K-1$ and $\rho'=1-s'/3=1-\log x/\log W'\ge0$.

*Claim: $\rho'\le\rho_*(z)$.*
- Let $q$ be the largest sifting prime $<x$; it exists by Step 3.
- If $W'<Z$, then $W'=q^+$ by definition.
- If $W'=Z$, then no sifting prime lies in $[x,Z)$, and $Z\in\mathbb P\cup\{z\}$, so $q^+=Z$.
- In both cases $\rho'=1-\log x/\log q^+<1-\log q/\log q^+\le\rho_*(z)$.

So $\eta+\rho'\le\eta+\rho_*<\varepsilon$ and $K<1+\varepsilon$, whence $K(\eta+\rho')<(1+\varepsilon)\varepsilon$. The four terms of core Step 13 become:

- (a) $\frac{3K}s(\eta+\rho')f_{n-1}(2)\le6(1+\varepsilon)\frac{c_{n-1}^{n-2}}{\tau_{n-1}}h_{n-1}(s)$, by (Fn) at 2 and (h2).
- (b) $\frac{3K}s(\eta+\rho')h_{n-1}(2)<3\varepsilon(1+\varepsilon)h_{n-1}(s)$, by (h2). This is strict because $h_{n-1}>0$.
- (c) $\frac{K^2}{s}\int_3^\infty f_{n-1}(t-1)dt=K^2f_n(s)\le f_n(s)+2(2+\varepsilon)\frac{c_n^{n-1}}{\tau_{n-1}}h_{n-1}(s)$.
- (d) $\frac{K^2}s\varepsilon\tau_{n-1}e^2H(3)\le(1+\varepsilon)^2\tilde\kappa h_{n-1}(s)$, by (h5).

These are the core bounds with $\eta$ replaced by $\eta+\rho'$. Therefore $T_n/V(Z)<f_n(s)+\tilde\xi h_{n-1}(s)\le f_n(s)+h_n(s)$, with **$\tilde\xi$ unchanged**.

**Step 5 (remaining cases use only half‑open levels).**
- *Base case $n=1$ at top $Z$, $1\le s<3$.* $T_1=V(x)-V(Z)$, and $V(x)/V(Z)\le Ks'/s\le3K/s$ by Step 1. Core Step 9 then goes through with $K<1+\varepsilon$.
- *Cases I and II (core Steps 11–12).* These apply Lemma A at $W=Z$ with pairs $(q,Z)$, $q\in\mathbb P$, $Z\in\mathbb P\cup\{z\}$. They are instances of H′.
- *Heredity of the gap parameter.* For $p\in\mathbb P$ with $p<z$, every pair $(q,q^+)$ used in $\rho_*(p)$ is a consecutive pair for $z$, since $p\in\mathbb P$. Hence $\rho_*(p)\le\rho_*(z)$.
- *Induction.* As in core Steps 10 and 14, with $s=3$ handled by Case I. This proves Theorem A_H. ∎

**Step 6 (Proposition N).** Write $a_1=\log53$, $a_2=\log829$, $a_3=\log10007$, $L=\log z=a_3+a_2+3a_1$.

*H′(z,1) holds with equality.* $(1-g(r_i))^{-1}=a_{i+1}/a_i$ with $a_4:=L$, so the product telescopes:
$$\frac{V(r_i)}{V(w)}=\frac{\log w}{\log r_i}\qquad\text{for every } w\in\{r_{i+1},\dots,z\}.$$

*The only triple counted by $T_3$.* $T_3$ counts $p_1>p_2>p_3$ in $\mathbb P$ with $p_1<z$, $p_1^3<D$ and $p_1p_2p_3^3\ge D$. The only candidate is $(10007,829,53)$:
- $p_1p_2p_3^3=D$, so the second condition holds with equality.
- $10007^3<D$ is equivalent to $10007^2=100140049<829\cdot53^3=123419033$, which is true.

*Value of $T_3$.*
$$\frac{T_3}{V(z)}=g(10007)\,g(829)\,g(53)\,\frac{L}{a_1}=0.669169\cdot0.270418\cdot0.409200\cdot7.012616=0.51926.$$

*Bound on $f_3(1)$.* $f_3(1)=\int_2^4f_2(u)\,du$, where $uf_2(u)=u-3\log(u-1)+3\log3-4$ on $[2,4]$ and $f_2$ is nonincreasing (core Step 8). The upper Riemann sum with step $1/2$ gives
$$f_3(1)\le\tfrac12(0.647918+0.231777+0.072132+0.013418)=0.482623.$$

*Bound on $\varepsilon\tau_3$.* With $c_n=0.9607$ and $\varepsilon=10^{-3}$:
- $\tau_2=3\xi_3=3\bigl(0.8349+4.459\varepsilon+\tfrac{8e}{9}+\tfrac{2(0.9607)}3\bigr)\le11.69$.
- $\tau_3\le\max\bigl(\tau_2(0.8394)+2\gamma_3c_2+2c_3^2,\ \tau_2(0.92640)+6.006\,c_2+4.002\,c_3^2\bigr)\le20.30$.
- Since $e^2h(1)=1$, the claimed right side is $\le0.4826+0.0203<0.5192$.

*Where the proof breaks.* At top $z$ we have $x=D^{1/3}$, and $W'=z$ because $10007<x$. So $\rho'=2/3$, and the extra term $\frac{3K}{s}\rho'\Psi(2)=2\Psi(2)$ of Step 4 is of order 1. The term $g(10007)V(10007)$ carries the whole "gap mass" $V(10007)-V(z)=2.02\,V(z)$ at argument $s'(10007)\approx2$. ∎

**Step 7 (Corollary R).**
- *$K_C\le K_H/(1-\rho_*)$.* For $p\le q<z$ in $\mathbb P$, $\Pi[p,q]=V(p)/V(q^+)\le K_H\frac{\log q^+}{\log p}\le\frac{K_H}{1-\rho_*}\frac{\log q}{\log p}$.
- *$K_H\le K_C$.* This is core Lemma 0(a).
- *The gain.* $\frac{K_H}{1-\rho_*}-1-(K_H-1+\rho_*)=\frac{(K_H-1+\rho_*)\rho_*}{1-\rho_*}$. ∎

## What is not proved here

1. A version under H′ **without** a gap condition. Proposition N shows that none exists with $\varepsilon$‑small error. Any valid version must carry a term of size $\rho'\Psi(2)/s$.
2. Numerical values of $C_1,C_2$; this remains as in core S.6. E1 also remains external.
3. Any statement about $\rho_*$ for primes not dividing $N$. It depends on $N$: $N$ may be divisible by every prime in a block $[x,x^{1+\delta}]$ whenever the product of that block is $\le N$.

## Checks a referee should make

1. *Step 2.* The range identity $\{p<W',p^3<D\}=\{p<D^{1/3}\}$, including the case $s'=3$.
2. *Step 3.* $K'=3K/s'\ge1$, and Lemma A does not use primality of $W$.
3. *Step 4.* The algebra $3K^2-Ks'=3K(K-1)+K(3-s')$, and $\rho'<\rho_*$ in both sub‑cases ($W'<Z$ and $W'=Z$).
4. *Step 6.* Primality of 53, 829 and 10007; the integer inequality $10007^2<829\cdot53^3$; and that $T_3$ has a single term.
5. **Application with $g(p)=1/(p-1)$ on $\mathbb P=\{p\nmid N\}\setminus\mathbb Q$.** What must be certified numerically:
   - **(N1)** $K_H(z)=\max_{q<w}\frac{V(q)}{V(w)}\frac{\log q}{\log w}$ over $q\in\mathbb P$, $w\in\mathbb P\cup\{z\}$, $q<w\le z$. An $N$‑independent upper bound uses all primes in $[q,w)$, but needs Mertens bounds at **both** endpoints for all $q<w\le z$; [BJS]'s Lemma covers only $w=z>e^{4000}$.
   - **(N2)** $\rho_*(z)=\max\log(q^+/q)/\log q^+$ over consecutive elements of $\mathbb P$. This is $N$‑dependent.
   - **(N3)** $K_H-1+\rho_*<\varepsilon\le1/74$, and recomputed $C_i(\varepsilon)$.
   - For the frame note ($\mathbb Q=$ primes in $[3,41)$): $K_H\ge1.01265$ from the pair $(41,43)$, and $\rho_*\ge0.03026$ from $47\to53$. So $K_H+\rho_*\ge1.0429>1+1/74$, and Theorem A_H does not apply, just as the core theorem does not ($K_C\ge40/39$).
6. Run the script below.

```python
#!/usr/bin/env python3
"""halfopen_check.py -- certifies Proposition N and the the frame note numbers. Stdlib only.
Logs: ln x = k ln2 + 2 atanh(t), t=(y-1)/(y+1) in [0,1/3), y=x/2^k in [1,2);
partial sum of 2*sum t^(2j+1)/(2j+1), j<J, with tail <= 2 t^(2J+1)/((2J+1)(1-t^2)).
exp upper: Taylor sum to N plus tail <= next/(1-x/(N+2)), 0<=x<=2.
All enclosures are rounded outward to multiples of 1e-30. No floats."""
from fractions import Fraction as Fr

S = 10 ** 30


def dn(x):
    x = Fr(x)
    return Fr((x.numerator * S) // x.denominator, S)


def up(x):
    x = Fr(x)
    return Fr(-((-x.numerator * S) // x.denominator), S)


def two_atanh(t, J=70):
    t = Fr(t)
    assert 0 <= t <= Fr(1, 3)
    s, p = Fr(0), t
    for j in range(J):
        s += p / (2 * j + 1)
        p *= t * t              # p = t^(2J+1) after the loop
    tail = 2 * p / ((2 * J + 1) * (1 - t * t))
    return (dn(2 * s), up(2 * s + tail))


LN2 = two_atanh(Fr(1, 3))


def ln_iv(x):
    x = Fr(x)
    assert x >= 1
    k = 0
    while x >= 2:
        x /= 2
        k += 1
    a = two_atanh((x - 1) / (x + 1))
    return (dn(k * LN2[0] + a[0]), up(k * LN2[1] + a[1]))


def exp_up(x, N=40):
    x = Fr(x)
    assert 0 <= x <= 2
    term, s = Fr(1), Fr(1)
    for k in range(1, N + 1):
        term = term * x / k
        s += term
    nxt = term * x / (N + 1)
    return up(s + nxt / (1 - x / (N + 2)))


def sh(x, d=6, upw=False):
    n = Fr(x) * 10 ** d
    q = -((-n.numerator) // n.denominator) if upw else n.numerator // n.denominator
    return "%d.%0*d" % (q // 10 ** d, d, q % 10 ** d)


# ---- Proposition N ----
r1, r2, r3 = 53, 829, 10007
assert r3 ** 2 < r2 * r1 ** 3          # r3^3 < D;  D = r3*r2*r1^3 (condition (b) holds with equality)
a1, a2, a3 = ln_iv(r1), ln_iv(r2), ln_iv(r3)
L = (a3[0] + a2[0] + 3 * a1[0], a3[1] + a2[1] + 3 * a1[1])
g3 = 1 - a3[1] / L[0]
g2 = 1 - a2[1] / a3[0]
g1 = 1 - a1[1] / a2[0]
assert min(g1, g2, g3) > 0
T3lo = dn(g3 * g2 * g1 * L[0] / a1[1])  # lower bound for T_3/V(z); H'(z,1) holds by telescoping
print("T3/V(z) >=", sh(T3lo))

ln3 = ln_iv(3)


def f2_up(u):
    u = Fr(u)
    return up((u - 3 * ln_iv(u - 1)[0] + 3 * ln3[1] - 4) / u)


f3up = up(Fr(1, 2) * sum(f2_up(u) for u in (2, Fr(5, 2), 3, Fr(7, 2))))
print("f_3(1) <=", sh(f3up, upw=True))

eps = Fr(1, 1000)
c = Fr("0.9607")
eup = up(Fr(271828183, 10 ** 8))        # e < 2.71828183
KAP = {"2": Fr("0.9607"), "2.2": Fr("0.9557"), "2.4": Fr("0.9457"),
       "2.6": Fr("0.9261"), "2.8": Fr("0.8914")}
G = {k: exp_up(Fr(k) - Fr("1.8")) for k in KAP}
k3, g3c, kt = Fr("0.8349"), Fr(4, 3) * eup, Fr("0.9214")
xi2 = [KAP[k] + (G[k] + KAP[k]) * eps + 2 * G[k] / 3 + 2 * c / 3 for k in KAP]
xi2.append(k3 + (g3c + k3) * eps + 2 * g3c / 3 + 2 * c / 3)
tau2 = 3 * max(xi2)
tau3 = max(tau2 * (k3 + (g3c + k3) * eps) + 2 * g3c * c + 2 * c ** 2,
           tau2 * (kt + (5 + 4 * eps) * eps) + 6 * (1 + eps) * c + 2 * (2 + eps) * c ** 2)
rhs = f3up + eps * tau3                 # e^2 h(1) = 1
print("tau_2 <=", sh(tau2, 3, True), " tau_3 <=", sh(tau3, 3, True), " RHS <=", sh(rhs, upw=True))
assert T3lo > rhs
print("Proposition N certified: T_3 > V(z)(f_3(1)+eps*tau_3*e^2*h(1)) with K=1.")

# ---- the frame note profile (sifting primes from 41) ----
l41, l43, l47, l53 = ln_iv(41), ln_iv(43), ln_iv(47), ln_iv(53)
KH = dn(Fr(40, 39) * l41[0] / l43[1])
rho = dn(1 - l47[1] / l53[0])
print("K_H >=", sh(KH), " rho_* >=", sh(rho), " K_H+rho_* >=", sh(KH + rho),
      " K_C >= 40/39 =", sh(Fr(40, 39)))
assert KH + rho > 1 + Fr(1, 74)
```

**Expected output and sanity checks.**
- `T3/V(z) >= 0.519262` (hand value 0.51926).
- `f_3(1) <= 0.482623`. The exact value is about $0.2955$, consistent with $\tilde F(1)\approx2e^\gamma$.
- `tau_2 <= 11.688`, `tau_3 <= 20.291`, `RHS <= 0.502916`, followed by the certification line.
- `K_H >= 1.012653`, `rho_* >= 0.030260`, `K_H+rho_* >= 1.042913`, `K_C >= 1.025641`.
- Quick cross‑checks: $\log10007\approx9.21104$, $\log829\approx6.72022$, $\log53\approx3.97029$, and $f_2(2)=(3\log3-2)/2=0.647918$.