## Statement

**Setting.** Fix a slab $[X_{lo},X_{hi})$ and integers $z<y$ with $zy^4\ge X_{hi}$ and $y^5>X_{hi}$. Let $Q_1$ be the first $a$ odd primes, with largest element $p_a$. Let $P_2$ be the set of all primes in $[p_a+1,z)$. This is the *ambient* set and does not depend on $N$.

Fix block endpoints, which are integers
$$z=z_0>z_1>\dots>z_{r-1}>z_r:=p_a+1 .$$
Put $B_i=P_2\cap[z_i,z_{i-1})$ and $T_i=B_1\cup\dots\cup B_i=P_2\cap[z_i,z)$. Each $T_i$ is an *upper segment* of $P_2$, and $T_r=P_2$.

Fix integer caps $0\le m_1\le\dots\le m_r$. For a squarefree $d$ composed of primes of $P_2$, let
$$\chi(d)=\mathbf 1\big[\forall i:\ \omega_{T_i}(d)\le m_i\big].$$

For $T\subseteq P_2$ (in practice $T=P_2'=P_2\setminus\{p\mid N\}$) write:
- $w_p=g(p)=1/(p-1)$, $g(d)=\prod_{p\mid d}w_p$, $V(T)=\prod_{p\in T}(1-w_p)$;
- $T_{\ge p}=\{\ell\in T:\ell\ge p\}$ and $T_{<p}=\{\ell\in T:\ell<p\}$;
- $G_\chi(T)=\sum_{d\mid P(T)}\mu(d)\chi(d)g(d)$ and $R_\chi(T)=G_\chi(T)/V(T)$.

A **boundary pair** for $T$ is a pair $(p,d')$ with $p\in T$, $d'\mid P(T)$, every prime of $d'$ larger than $p$, $\chi(d')=1$ and $\chi(pd')=0$.

**Theorem A (sieve inequality, parity rule).** Suppose every $m_i$ with $m_i<|T_i|$ satisfies $m_i\equiv m\pmod 2$. For squarefree $n\mid P(T)$:
$$\sum_{d\mid n}\mu(d)\chi(d)=\mathbf 1[n=1]+(-1)^m\,\#\{(p,d')\text{ boundary}:\ pd'\mid n,\ (n,P(T_{<p}))=1\}.$$
- All relevant caps even: $\sum_{d|n}\mu\chi\ge\mathbf 1[n=1]$, which is an upper-bound sieve.
- All relevant caps odd: $\sum_{d|n}\mu\chi\le\mathbf 1[n=1]$, which is a lower-bound sieve.

With exact inclusion–exclusion on $Q_1'$, put $\lambda_d=\mu(d)\chi(d_{P_2})$ for $d\mid P(Q_1')P(P_2')$. Then $\sum_{d|n}\lambda_d=\mathbf 1[(n,Q_1')=1]\sum_{d\mid (n,P(P_2'))}\mu\chi$. So the note's §2 inequalities hold with $R_{odd},R_{even}$ replaced by $R_{\chi^-}$ and $R_{\chi^+}$.

**Lemma B (main term).**
1. $\sum_d\lambda_d g(d)=V(Q_1')\,G_\chi(P_2')$.
2. DP formula: $G_\chi(T)=\sum_{(j_1,\dots,j_r):\ j_1+\dots+j_i\le m_i\ \forall i}\ \prod_i(-1)^{j_i}e_{j_i}(w_p:p\in B_i\cap T)$.
3. Brun expansion: $R_\chi(T)=1+(-1)^mE_\chi(T)$, where $E_\chi(T)=\sum_{(p,d')\ \text{boundary}}g(pd')/V(T_{\ge p})\ \ge 0$.

**Lemma C (monotonicity).** Let $T'=T\setminus\{\ell\}$, with the same $\chi$. Then $0\le E_\chi(T')\le E_\chi(T)$. Hence:
- $R_{\chi^-}$ (odd caps) can only increase when primes dividing $N$ are removed;
- $R_{\chi^+}$ (even caps) can only decrease.

**Lemma D (analytic bound, itself monotone).**
$$E_\chi(T)\le\sum_{i:\,m_i<|T_i|}\frac{e_{m_i+1}(T_i\cap T)}{V(T_i\cap T)}\le\sum_i\frac{S_i^{m_i+1}}{(m_i+1)!\,V_i},$$
where $S_i\ge\sum_{p\in T_i}w_p$ and $0<V_i\le V(T_i)$. The right side, with $S_i,V_i$ taken for the ambient $T_i$, bounds $E_\chi(P_2')$ for every $N$.

**Lemma E (level and count).**
1. Every $d\ne1$ with $\chi(d)=1$ satisfies $d<\prod_{i=1}^r z_{i-1}^{\,m_i-m_{i-1}}=:\mathcal M_\chi$, with $m_0=0$.
2. $\#\{d\mid P(Q_1')P(P_2'):\lambda_d\ne0\}\le 2^a\sum_{\text{admissible }(j_i)}\prod_i\binom{n_i}{j_i}$, for any $n_i\ge|B_i|$.
3. $\sum_{\chi(d)=1}\mu^2(d)/\varphi(d)$ over $d\mid P(Q_1')P(P_2')$ is at most $\prod_{p\in Q_1}\frac{p}{p-1}\cdot e^{S(P_2)}$.

**Corollary F (replaces Lemma 2(b) of the note).** Let $\chi^-$ have odd caps and $\chi^+$ even caps. Define
$$b:=1-E^-_{\rm bd}-\tfrac12(1+E^+_{\rm bd})\,\Sigma_q,$$
where:
- $E^\pm_{\rm bd}$ are the Lemma D bounds on the ambient blocks;
- $\Sigma_q\ge\sum_{z\le q<y}\frac1{q-1}$ over all primes in $[z,y)$.

If $b>0$, then for every even $N\in[X_{lo},X_{hi})$ the main term of (1.1) is at least $|A|\,V_N\,b\ge|A|\,V_{\rm full}\,b$. The level conditions are:
- $\prod Q_1\cdot\mathcal M_{\chi^-}\le\lfloor\sqrt{X_{lo}}\rfloor$;
- $(y-1)\prod Q_1\cdot\mathcal M_{\chi^+}\le\lfloor\sqrt{X_{lo}}\rfloor$.

Under these, every modulus used is $<\sqrt N$ and coprime to $N$, so (∗) applies.

## Proof

**Step 1 (χ is downward closed).** If $e\mid d$, then $\omega_{T_i}(e)\le\omega_{T_i}(d)$ for every $i$. Hence $\chi(d)=1\Rightarrow\chi(e)=1$. Also $\chi(1)=1$ because $m_i\ge0$.

**Step 2 (unique decomposition of excluded $d$).** Let $d\mid P(T)$ with $\chi(d)=0$, and list its primes $q_1>q_2>\dots>q_k$. Let $j$ be minimal with $\chi(q_1\cdots q_j)=0$; it exists and $j\ge1$.

Put $d'=q_1\cdots q_{j-1}$, $p=q_j$ and $e=d/(pd')$. Then $(p,d')$ is a boundary pair and $e\mid P(T_{<p})$.

Conversely, take any boundary pair $(p,d')$ and any $e\mid P(T_{<p})$, and set $d=epd'$. Then $\chi(d)=0$ by Step 1, since $pd'\mid d$. Scanning $d$ from its largest prime recovers exactly $(p,d')$, because $\chi(d')=1$ and every prefix of $d'$ has $\chi=1$ by Step 1. So the map is a bijection.

**Step 3 (parity lemma).** Let $(p,d')$ be a boundary pair. Then $\omega(d')=m_i$ for some $i$ with $m_i<|T_i|$.

Since $\chi(pd')=0$, there is an $i$ with $\omega_{T_i}(pd')>m_i\ge\omega_{T_i}(d')$. This forces $p\in T_i$ and $\omega_{T_i}(d')=m_i$. Because $T_i$ is an upper segment containing $p$ and all primes of $d'$ exceed $p$, we have $d'\subseteq T_i$. So $\omega(d')=m_i$. Also $|T_i|\ge m_i+1$.

Under the parity hypothesis this gives $\mu(pd')=(-1)^{m_i+1}=(-1)^{m+1}$.

**Step 4 (Theorem A).** For squarefree $n\mid P(T)$ we have $\sum_{d|n}\mu(d)=\mathbf 1[n=1]$. So
$$\sum_{d|n}\mu\chi=\mathbf 1[n=1]-\sum_{d|n,\chi(d)=0}\mu(d).$$
By Step 2, the second sum equals $\sum_{(p,d'):\,pd'|n}\mu(pd')\sum_{e\mid (n,P(T_{<p}))}\mu(e)$. The inner sum is $\mathbf 1[(n,P(T_{<p}))=1]$. Step 3 then gives the identity. The sign statements follow because the count is $\ge0$.

With the $Q_1'$ factor, $\lambda$ is a product of the full Möbius function on $Q_1'$ and $\mu\chi$ on $P_2'$. Hence
$$\sum_{d|n}\lambda_d=\mathbf 1[(n,P(Q_1'))=1]\sum_{d|(n,P(P_2'))}\mu\chi.$$
For $a\in A$, take $n=\gcd(a,P(Q_1')P(P_2'))$. Then $(a,P(z))=1$ iff $n=1$. This gives:
- $S(A,P(z))\ge\sum_d\lambda^-_d|A_d|$ for odd caps;
- $S(A_q,P(z))\le\sum_d\lambda^+_d|A_{qd}|$ for even caps.

After this point the decomposition into main terms, $r(d)$, $r(qd)$ and $r(q)$ is exactly the note's §3, item 6.

**Step 5 (Lemma B).**
- Part 1: $g=1/\varphi$ is multiplicative on squarefree odd $d$, and $\lambda$ factorises over $Q_1'$ and $P_2'$.
- Part 2: $\chi(d)$ depends only on the vector $(\omega_{B_i}(d))_i$. Grouping $d$ by this vector gives $\prod_i(-1)^{j_i}e_{j_i}(B_i\cap T)$.
- Part 3: repeat Step 4 with $g$ in place of the indicator. We have $\sum_{d|P(T)}\mu g=V(T)$, and by Step 2, $\sum_{\chi(d)=0}\mu(d)g(d)=\sum_{(p,d')}\mu(pd')g(pd')V(T_{<p})$. With Step 3 this gives $G_\chi=V(T)+(-1)^m\sum g(pd')V(T_{<p})$. Dividing by $V(T)=V(T_{<p})V(T_{\ge p})$ gives the claim. Every term is $\ge0$ because $0<1-w_p<1$ for odd $p$.

**Step 6 (Lemma C).**
- $\chi$ is a fixed function on subsets of the ambient $P_2$. Its conditions $\chi(d')=1$, $\chi(pd')=0$ and $p<\min d'$ do not refer to $T$.
- So the boundary pairs of $T'$ are exactly the boundary pairs of $T$ that avoid $\ell$.
- For such a pair, $T'_{\ge p}\subseteq T_{\ge p}$, and every factor lies in $(0,1)$. Hence $V(T'_{\ge p})\ge V(T_{\ge p})$, and each term weakly decreases.
- The pairs involving $\ell$ disappear, and their terms are $\ge0$.

This is exactly the analogue of the note's Lemma 2(a). The case $r=1$ recovers it.

**Step 7 (Lemma D).**
- Assign each boundary pair the least $i$ from Step 3. Then $pd'\subseteq T_i\cap T$, $|pd'|=m_i+1$, and $p=\min(pd')$. So for fixed $i$ the map $(p,d')\mapsto pd'$ is injective.
- Also $T_{\ge p}\subseteq T_i\cap T$, because $T_i$ is an upper segment containing $p$. Hence $V(T_{\ge p})\ge V(T_i\cap T)$.
- Summing gives $E\le\sum_i e_{m_i+1}(T_i\cap T)/V(T_i\cap T)$.
- Maclaurin: $S^k=\sum_{\text{ordered }k\text{-tuples}}\ge k!\,e_k$.
- Monotonicity: $S(T_i\cap P_2')\le S(T_i)$ and $V(T_i\cap P_2')\ge V(T_i)$. So the ambient bound covers every $N$, independently of Lemma C. Lemma C is only needed if an exact DP value of $E_\chi(P_2)$ is used, as in an "exact branch".

**Step 8 (Lemma E).**
1. Let $d$ be admissible, with primes $q_1>q_2>\dots$. The primes of $d$ in $T_{i-1}$ are its largest ones, and there are at most $m_{i-1}$ of them. So for $k>m_{i-1}$ we have $q_k<z_{i-1}$. In addition $q_k<z=z_0$ always, and $k\le m_r$ because $T_r=P_2$. Hence $d\le\prod_i (z_{i-1}-1)^{m_i-m_{i-1}}<\mathcal M_\chi$.
2. Group by the vector $(j_i)$; there are $\binom{|B_i|}{j_i}\le\binom{n_i}{j_i}$ choices in block $i$, and $2^a$ choices of the $Q_1$ part.
3. The sum is at most $\prod_{Q_1}(1+\frac1{p-1})\prod_{P_2}(1+w_p)\le\prod_{Q_1}\frac p{p-1}\,e^{S(P_2)}$.

**Step 9 (Corollary F).** Let $\Sigma'_q=\sum_{q\in[z,y)\cap\mathbf P}\frac{1}{q-1}$. By Steps 4–7, for the given $N$,
$$R_{\chi^-}(P_2')-\tfrac12R_{\chi^+}(P_2')\Sigma'_q\ \ge\ (1-E^-_{\rm bd})-\tfrac12(1+E^+_{\rm bd})\Sigma_q=b.$$
This uses $R_{\chi^+}\ge1>0$ and $\Sigma'_q\le\Sigma_q$.

The main term of (1.1) is $|A|\,V_N\times$(this bracket). If $b>0$, then $V_N\ge V_{\rm full}$ gives the claim. The moduli are:
- $d<\prod Q_1\cdot\mathcal M_{\chi^-}\le\sqrt{X_{lo}}\le\sqrt N$;
- $qd<(y-1)\prod Q_1\cdot\mathcal M_{\chi^+}\le\sqrt N$.

Both are coprime to $N$ because only primes not dividing $N$ are sieved, and both are $\ge3$ when $\ne1$.

**Step 10 (error terms).** These are as in the note's §3, item 6, with the counts of Lemma E. All of the following are normalised by $N/\log N$, with $\rho(X)$ the per-modulus bound (∗) divided by $N/\log N$ at $X=X_{lo}$:
- lower sieve: $\#\{d\}^-\cdot\rho(X_{lo})$;
- upper sieve: $\tfrac12\pi(y)\,\rho(X_{lo})\,(\#\{d\}^+ + \text{Lemma E.3} + 1+E^+_{\rm bd})$;
- $q^2$ term: $\log X_{hi}/(2(z-1))$.

### Numerical estimates and recommended parameters (hand computation, NOT certified)

**Common inputs.** Take $M=27$ and $a=8$, so $Q_1=\{3,\dots,23\}$ with $\log\prod Q_1=18.530$. P₂ starts at 29.
- From $zy^4\ge N$: $\log y\approx\frac{M-1}{4M}\log N$, so $\Sigma_q\approx\log\frac{M-1}4=1.8718$ and $\tfrac12\Sigma_q=0.9359$.
- The level available at the worst $q$ is $s^+=(\tfrac12\log N-\log y-\log Q_1)/\log z$.
- I used $S(T_i)\approx\log(1/t_i)$ (with $T_i=[z^{t_i},z)$) and $V(T_i)\approx t_i$. For $T_r$ I used $S\approx\log\log z+B-\sum_{p\le23}1/p+0.008$ and $V\approx e^{-S-0.006}$.

**Calibration at $10^{238.7}$, old method.** Here $\log z=20.36$, $s^+=6.09$, $S(P_2)\approx1.784$, $V\approx0.167$.
- Single block with cap 6: $E^+\le1.784^7/7!/0.167\approx0.068$, so $b\approx0.064-0.936\cdot0.068\approx3\cdot10^{-4}$ and net $\approx V_{\rm full}b\approx10^{-5}$.
- This matches the observed collapse of the old ladder (nets $10^{-5}\to3\cdot10^{-7}$).

**Blocks at $10^{238.7}$.** Use caps $(4,8)$ with $t_1=0.52$ (level $4+4\cdot0.52=6.08\le6.09$).
- $E^+\le0.654^5/5!/0.52+1.784^9/9!/0.167\approx1.9\cdot10^{-3}+3.0\cdot10^{-3}=4.9\cdot10^{-3}$.
- So $b\approx0.059$.

**$N=10^{300}$.** Here $\log z=25.58$ and $s^+=6.276$.
- Upper caps $(4,8)$ with $t_1=0.55$: $E^+\lesssim1.2\cdot10^{-3}+2.013^9/9!/0.133\approx0.0124$.
- Lower: pure order 11 (level $11\le s^-=12.78$), $E^-\approx7\cdot10^{-5}$.
- $b\approx1-0.00007-0.9359\cdot1.0124\approx0.052$.
- $V_{\rm full}\approx2C_2e^{-\gamma}/\log z\approx0.029$, so net $\approx1.5\cdot10^{-3}$.

**$N=10^{400}$.** Here $\log z=34.11$ and $s^+=6.457$.
- Two blocks $(4,8)$ is insufficient: $E^+\approx0.05$.
- Three blocks $(4,8,10)$ with $t_1=0.5$ and $t_2=0.225$ (level $4+2+0.45\le6.457$) give
  $E^+\lesssim2.67\cdot10^{-3}+1.4917^9/9!/0.225+2.30^{11}/11!/0.0997\approx2.7\cdot10^{-3}+4.5\cdot10^{-4}+2.4\cdot10^{-3}=5.5\cdot10^{-3}$.
- Lower order 11: $E^-\approx5\cdot10^{-4}$.
- $b\approx0.058$, $V_{\rm full}\approx0.0217$, net $\approx1.3\cdot10^{-3}$.

**Remainders at $10^{400}$.**
- Moduli for the upper sieve: about $e^{189}$. Number of $q$: about $e^{216}$.
- Normalised error $\lesssim0.15\cdot e^{189+216+13.7-460.5}\approx e^{-44}$.
- At $10^{238}$ it is about $e^{-35}$.
- Both are negligible for any $c_\pi\le10^{10}$.

**Conclusion.** The relative errors (0.5–1.3%) are well within the required ~3%. The method should reach $10^{400}$ with margin; the binding quantity is the slack $1-\tfrac12\Sigma_q\approx0.064$.

**Recommendation.**
- $M=27$, $a=8$, lower caps $(11)$.
- Upper caps $(4,8)$ from $10^{238}$ to about $10^{330}$ (where the 2-block $E^+$ reaches about 0.025).
- Upper caps $(4,8,10)$ beyond that.
- Choose $z_1$ on a grid and make the last free endpoint maximal under the exact level check. Larger $z_i$ shrinks $T_i$, which lowers the error, so maximal is optimal.
- Slabs of one decade cost about 0.034 level units at $10^{400}$. Optional improvements: $q$-dependent parameters (split $[z,y)$), and an exact DP branch for small blocks.

## What is not proved here

- The numbers in the estimates subsection are hand estimates with floats and approximate Mertens values. They are not certified; only the script output would be.
- The draft script below has been superseded for certification by `k4/certificate/all_even_1p4_ext/regime2_brun.py` (which uses `all_even_1p4`'s outward-rounded interval arithmetic, certified `grh_remainder_coeff`, Schoenfeld RH bound, and `[JS]`/`[BJS]` Mertens bounds).
- EXTERNAL INPUTS:
  1. Rosser–Schoenfeld (1962): $|\sum_{p\le x}1/p-\log\log x-B|<1/(2\log^2x)$ for $x\ge286$, and $\pi(x)<1.25506\,x/\log x$ for $x>1$.
  2. The note's (∗) with its constant $c_\pi(X_{lo})$. The script uses a **placeholder** `C_PI = 10`, which is not a proven value and must be replaced by the package's value. Since the remainders are about $e^{-35}$, any value up to $10^{10}$ would not change the outcome.
  3. $|A|>N/\log N$, the $q^2$ bound, and the $E_q$ decomposition, all from the note §1 and §3.
- Not done: reproducing the old ladder exactly, the exact DP branch, and $q$-dependent block parameters.

## Checks a referee should make

1. **Step 3:** $T_i$ must be an upper segment, which uses $B_1$ = largest primes. The parity hypothesis is only needed for $i$ with $m_i<|T_i|$.
2. **Step 7:** the bound uses $V(T_i)$, not $V(P_2)$. Check that $T_{\ge p}\subseteq T_i$.
3. **Level:** check that $\mathcal M_\chi$ uses $z_{i-1}$ with exponent $m_i-m_{i-1}$, and that the script's exact integer assertion matches it.
4. **Sanity run 1:** caps `(6,)` on $[10^{238.6},10^{238.7})$ should give $b$ near 0. Expect net of order $10^{-6}$ or negative, because the Maclaurin bound is cruder than the old exact branch.
5. **Sanity run 2:** $\Sigma_q\approx\log((M-1)/4)$, and $V_{\rm full}\approx 1.3203\,e^{-\gamma}/\log z$.
6. **Contiguity:** the ladder's first slab starts at $10^{238}$, below the old top $10^{238.7}$, and its last slab ends at or above $10^{400}$.

```python
#!/usr/bin/env python3
"""
brun_blocks_slab.py -- Regime 2 slab certifier with the Brun block sieve
(Theorem A, Lemmas B-E, Corollary F of this section).

Certified path: exact ints/Fractions, Decimal with directed rounding
(DN=floor, UP=ceiling).  ln/exp (correctly rounded half-even) are widened
by two ulps outward.  Powers are done by repeated UP multiplication.

Bounds used (each one is an upper or lower bound as named):
  M_lo(x) <= sum_{p<x} 1/p <= M_up(x)     exact for x<=PB+1, else RS-M
  S_up(u,v) >= sum_{u<=p<v} 1/(p-1)        uses sum_{p>=U} 1/(p(p-1)) <= 1/(U-1)
  V_lo(u,v) <= prod_{u<=p<v} (1-1/(p-1))   uses log(1-x) >= -x-x^2 (0<=x<=1/2)
                                          and sum_{p>=U} 1/(p-1)^2 <= 1/(U-2)
  E_bound >= E_chi(P2') for every N       (Lemma D)
EXTERNAL INPUTS: RS-M (x>=286), RS-pi, the note's (*) with C_PI, and
|A|>N/log N.
C_PI BELOW IS A PLACEHOLDER (NOT PROVEN); REPLACE BY THE PACKAGE c_pi(X_lo).
"""
import sys
from bisect import bisect_left, bisect_right
from fractions import Fraction as Fr
from math import comb, isqrt, factorial
from decimal import Decimal as D, Context, ROUND_FLOOR, ROUND_CEILING

PREC = 50
DN = Context(prec=PREC, rounding=ROUND_FLOOR)
UP = Context(prec=PREC, rounding=ROUND_CEILING)
C_PI = Fr(10)                        # PLACEHOLDER, see docstring
B_LO = D('0.26149721284764278375')   # Meissel-Mertens constant, lower
B_HI = D('0.26149721284764278376')   # Meissel-Mertens constant, upper
PB = 10**6


def ln_lo(x):  return DN.next_minus(DN.next_minus(DN.ln(D(x))))
def ln_up(x):  return UP.next_plus(UP.next_plus(UP.ln(D(x))))
def exp_lo(x): return DN.next_minus(DN.next_minus(DN.exp(D(x))))
def exp_up(x): return UP.next_plus(UP.next_plus(UP.exp(D(x))))
def q_up(f):   f = Fr(f); return UP.divide(D(f.numerator), D(f.denominator))


def pow_up(s, k):
    """Upper bound for s**k, s >= 0."""
    r = D(1)
    for _ in range(k):
        r = UP.multiply(r, s)
    return r


INV16PI_UP = q_up(Fr(1) / (16 * Fr(314159, 100000)))   # pi > 3.14159


def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, isqrt(n) + 1):
        if s[i]:
            s[i*i::i] = bytearray(len(range(i*i, n + 1, i)))
    return [i for i in range(n + 1) if s[i]]


PR = primes_upto(PB)
PP_LO, PP_HI, PW_LO, PW_HI = [D(0)], [D(0)], [D(0)], [D(0)]  # prefix 1/p, 1/(p-1)
PV_LO, PV_HI = [D(1)], [D(1)]          # prefix prod (p-2)/(p-1), p=2 -> factor 1
for p in PR:
    PP_LO.append(DN.add(PP_LO[-1], DN.divide(D(1), D(p))))
    PP_HI.append(UP.add(PP_HI[-1], UP.divide(D(1), D(p))))
    PW_LO.append(DN.add(PW_LO[-1], DN.divide(D(1), D(p - 1))))
    PW_HI.append(UP.add(PW_HI[-1], UP.divide(D(1), D(p - 1))))
    f_lo = D(1) if p == 2 else DN.divide(D(p - 2), D(p - 1))
    f_hi = D(1) if p == 2 else UP.divide(D(p - 2), D(p - 1))
    PV_LO.append(DN.multiply(PV_LO[-1], f_lo))
    PV_HI.append(UP.multiply(PV_HI[-1], f_hi))


def iroot(n, k):
    """floor(n^(1/k)), exact."""
    if n < 2:
        return n
    x = 1 << ((n.bit_length() + k - 1) // k)
    while True:
        y = ((k - 1) * x + n // x**(k - 1)) // k
        if y >= x:
            break
        x = y
    while x**k > n:
        x -= 1
    while (x + 1)**k <= n:
        x += 1
    return x


def iroot_ceil(n, k):
    r = iroot(n, k)
    return r if r**k == n else r + 1


def M_lo(x):
    """Lower bound for sum_{p<x} 1/p."""
    if x <= PB + 1:
        return PP_LO[bisect_left(PR, x)]
    L = ln_lo(x)
    sub = UP.add(UP.divide(D(1), DN.multiply(D(2), DN.multiply(L, L))),
                 UP.divide(D(1), D(x)))                       # 1/(2log^2)+1/x
    return DN.subtract(DN.add(ln_lo(L), B_LO), sub)


def M_up(x):
    """Upper bound for sum_{p<x} 1/p (<= sum_{p<=x})."""
    if x <= PB + 1:
        return PP_HI[bisect_left(PR, x)]
    Ll = ln_lo(x)
    t = UP.add(ln_up(ln_up(x)), B_HI)
    return UP.add(t, UP.divide(D(1), DN.multiply(D(2), DN.multiply(Ll, Ll))))


def _tail_S(u, v):
    """Upper bound for sum over primes in [max(u,PB+1), v) of 1/(p-1); 0 if empty."""
    if v <= PB + 1:
        return D(0), None
    U = max(u, PB + 1)
    t = UP.add(UP.subtract(M_up(v), M_lo(U)), UP.divide(D(1), D(U - 1)))
    return t, U


def S_up(u, v):
    """Upper bound for sum_{u<=p<v} 1/(p-1), u>=3."""
    hi = min(v, PB + 1)
    s = D(0)
    if u < hi:
        s = UP.subtract(PW_HI[bisect_left(PR, hi)], PW_LO[bisect_left(PR, u)])
    t, _ = _tail_S(u, v)
    return UP.add(s, t)


def V_lo(u, v):
    """Lower bound for prod_{u<=p<v} (1-1/(p-1)), u>=3."""
    hi = min(v, PB + 1)
    prod = D(1)
    if u < hi:
        prod = DN.divide(PV_LO[bisect_left(PR, hi)], PV_HI[bisect_left(PR, u)])
    t, U = _tail_S(u, v)
    if U is not None:
        tail = UP.add(t, UP.divide(D(1), D(U - 2)))
        prod = DN.multiply(prod, exp_lo(DN.minus(tail)))
    assert prod > 0
    return prod


def pi_up_le(x):
    """Upper bound for #{p <= x}."""
    if x <= PB:
        return bisect_right(PR, x)
    v = UP.multiply(D('1.25506'), UP.divide(D(x), ln_lo(x)))
    return int(v.to_integral_value(rounding=ROUND_CEILING))


def n_block(lo, hi):
    """Upper bound for #primes in [lo, hi)."""
    if hi <= PB + 1:
        return bisect_left(PR, hi) - bisect_left(PR, lo)
    return pi_up_le(hi)


def E_bound(caps, ends):
    """Lemma D: sum_i S(T_i)^(m_i+1)/(m_i+1)!/V(T_i), T_i=[ends[i], z)."""
    z = ends[0]
    tot = D(0)
    for i in range(1, len(ends)):
        k = caps[i - 1] + 1
        S = S_up(ends[i], z)
        term = UP.divide(UP.divide(pow_up(S, k), D(factorial(k))), V_lo(ends[i], z))
        tot = UP.add(tot, term)
    return tot


def modbound(caps, ends):
    """Lemma E.1: every admissible d < this."""
    r, prev = 1, 0
    for i, m in enumerate(caps):
        r *= ends[i] ** (m - prev)
        prev = m
    return r


def adm_count(caps, sizes):
    """sum over admissible (j_i) of prod comb(n_i, j_i) (exact int)."""
    dp = {0: 1}
    for m, n in zip(caps, sizes):
        new = {}
        for c, v in dp.items():
            for j in range(0, m - c + 1):
                new[c + j] = new.get(c + j, 0) + v * comb(n, j)
        dp = new
    return sum(dp.values())


def candidate_ends(caps, z, pa1, budget):
    """Yield block endpoint lists; the last free endpoint is maximal under the level."""
    r = len(caps)
    c = [caps[0]] + [caps[i] - caps[i - 1] for i in range(1, r)]
    assert all(ci >= 1 for ci in c)
    if r == 1:
        if z**c[0] <= budget:
            yield [z, pa1]
    elif r == 2:
        rest = budget // z**c[0]
        if rest:
            z1 = min(iroot(rest, c[1]), z)
            if z1 > pa1:
                yield [z, z1, pa1]
    elif r == 3:
        for k in range(30, 81, 2):
            t = Fr(k, 100)
            z1 = iroot(z**t.numerator, t.denominator)
            if z1 <= pa1:
                continue
            rest = budget // (z**c[0] * z1**c[1])
            if rest:
                z2 = min(iroot(rest, c[2]), z1)
                if z2 > pa1:
                    yield [z, z1, z2, pa1]


def best_blocks(caps_list, z, pa1, budget, parity):
    best = None
    for caps in caps_list:
        assert all(m % 2 == parity for m in caps)       # Theorem A parity rule
        for ends in candidate_ends(caps, z, pa1, budget):
            E = E_bound(caps, ends)
            if best is None or E < best[0]:
                best = (E, caps, ends)
    return best


def rem_norm(X):
    """(*) / (N/log N), decreasing in N, evaluated at X_lo."""
    L = ln_up(X); L2 = UP.multiply(L, L)
    c = UP.add(q_up(C_PI), INV16PI_UP)
    t1 = UP.divide(UP.multiply(c, L2), D(isqrt(X)))
    t2 = UP.divide(UP.multiply(q_up(Fr(13841, 10000)), L2),
                   DN.multiply(D(X), ln_lo(ln_lo(X))))
    return UP.add(t1, t2)


LOW_CAPS = [(11,), (9, 13), (11, 13)]
UPP_CAPS = [(4, 8), (6, 8), (4, 8, 10), (4, 6, 10), (4, 8, 12)]


def certify_slab(X_lo, X_hi, M, a):
    """Returns a dict with certified main/err/net, or None if not certified."""
    odd = PR[1:]
    Q1 = odd[:a]
    pa1 = Q1[-1] + 1
    prodQ1 = 1
    ratio = Fr(1)
    for p in Q1:
        prodQ1 *= p
        ratio *= Fr(p, p - 1)
    z = iroot_ceil(X_hi, M)
    y = max(iroot_ceil(-(-X_hi // z), 4), iroot(X_hi, 5) + 1)
    assert z * y**4 >= X_hi and y**5 > X_hi and y > z > PB + 1 and X_lo > 286
    sq = isqrt(X_lo)
    lo = best_blocks(LOW_CAPS, z, pa1, sq // prodQ1, 1)
    up = best_blocks(UPP_CAPS, z, pa1, sq // (prodQ1 * (y - 1)), 0)
    if lo is None or up is None:
        return None
    Em, cl, el = lo
    Ep, cu, eu = up
    assert prodQ1 * modbound(cl, el) <= sq                # level, exact
    assert (y - 1) * prodQ1 * modbound(cu, eu) <= sq      # level for q*d, exact
    Sq = S_up(z, y)
    neg = UP.multiply(UP.multiply(D('0.5'), UP.add(D(1), Ep)), Sq)
    b = DN.subtract(DN.subtract(D(1), Em), neg)
    if not b > 0:
        return None
    main = DN.multiply(V_lo(3, z), b)
    rem = rem_norm(X_lo)
    sz_l = [n_block(el[i + 1], el[i]) for i in range(len(cl))]
    sz_u = [n_block(eu[i + 1], eu[i]) for i in range(len(cu))]
    cnt_l = 2**a * adm_count(cl, sz_l)
    cnt_u = 2**a * adm_count(cu, sz_u)
    sip = UP.multiply(q_up(ratio), exp_up(S_up(pa1, z)))   # Lemma E.3
    err = UP.multiply(D(cnt_l), rem)
    inner = UP.add(UP.add(D(cnt_u), sip), UP.add(D(1), Ep))
    err = UP.add(err, UP.multiply(UP.multiply(D('0.5'), D(pi_up_le(y))),
                                  UP.multiply(rem, inner)))
    err = UP.add(err, UP.divide(ln_up(X_hi), D(2 * (z - 1))))     # q^2 term
    net = DN.subtract(main, err)
    if not net > 0:
        return None
    return dict(M=M, a=a, low=cl, up=cu, ends_up=eu, Em=Em, Ep=Ep, b=b,
                main=main, err=err, net=net)


def best_certify(X_lo, X_hi):
    best = None
    for M in (26, 27, 28):
        for a in (6, 7, 8, 9):
            r = certify_slab(X_lo, X_hi, M, a)
            if r and (best is None or r['net'] > best['net']):
                best = r
    return best


def show(X_lo, X_hi, r):
    lg = lambda X: f"{ln_lo(X) / ln_up(10):.3f}"
    if r is None:
        print(f"[10^{lg(X_lo)}, 10^{lg(X_hi)}): NOT certified")
        return
    print(f"[10^{lg(X_lo)}, 10^{lg(X_hi)}): M={r['M']} a={r['a']} "
          f"low={r['low']} up={r['up']} E-<={r['Em']:.3e} E+<={r['Ep']:.3e} "
          f"b>={r['b']:.4e} main>={r['main']:.4e} err<={r['err']:.3e} "
          f"net>={r['net']:.4e}")


def ladder(e0=238, e1=400):
    X, n = 10**e0, 0
    while X < 10**e1:
        for num, den in ((10, 1), (5, 1), (2, 1), (5, 4), (11, 10)):
            Xh = X * num // den
            r = best_certify(X, Xh)
            if r:
                show(X, Xh, r)
                X, n = Xh, n + 1
                break
        else:
            print("STUCK at", X)
            return
    print("ladder complete:", n, "slabs, contiguous by construction")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "ladder":
        ladder()
    else:
        for X_lo, X_hi in ((10**238, 2 * 10**238), (10**300, 2 * 10**300),
                           (10**399, 10**400)):
            show(X_lo, X_hi, best_certify(X_lo, X_hi))
```

**Expected output.** The estimates above predict the following orders of magnitude. The printed digits are cosmetic, since the certified comparisons are the asserted Decimal inequalities.

| Slab | Upper caps | $E^+$ | $b$ | net |
|---|---|---|---|---|
| $10^{238}$ | `(4, 8)` | ≈ 0.005 | ≈ 0.06 | ≈ 2·10⁻³ |
| $10^{300}$ | `(4, 8)` | ≈ 0.012 | ≈ 0.05 | ≈ 1.5·10⁻³ |
| $10^{399}$ | `(4, 8, 10)` | ≈ 0.006 | ≈ 0.057 | ≈ 1.2·10⁻³ |

In every slab the error should be below 10⁻¹⁵ apart from the $q^2$ term. The optimiser may pick $M=26$ or 28, or $a\ne8$, if that gives a larger net. If any slab prints "NOT certified", first check that `z > PB+1` holds and that the level budget allows the chosen caps.