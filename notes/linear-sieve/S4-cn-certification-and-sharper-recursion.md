## Statement

**Notation.** These are exactly as in S.2 of the core section.

- $f_1(s)=(3-s)/s$ on $[1,3]$ and $f_1=0$ on $(3,\infty)$.
- $sf_n(s)=\int_s^\infty f_{n-1}(t-1)\,dt$ for $n$ even with $s\ge2$, and for $n$ odd with $s\ge3$.
- $sf_n(s)=\int_3^\infty f_{n-1}(t-1)\,dt$ for $n\ge3$ odd with $1\le s\le3$.
- $a_n:=1$ if $n$ is odd and $a_n:=2$ if $n$ is even, so that $f_n$ is defined on $[a_n,\infty)$.
- $\delta:=1/1000$.
- $M_n:=\sup_{s\ge a_n} f_n(s)/(2e^2h(s))$. Hence (Fn) holds with $c_n$ if and only if $c_n^{\,n-1}\ge M_n$.

**Proposition 1 (structure of $f_n$).** For every $n\ge1$:

- (a) $f_n$ is finite, nonnegative and nonincreasing on $[a_n,\infty)$.
- (b) $f_n(s)=0$ for $s\ge n+2$.
- (c) $h$ is positive and nonincreasing on $[1,\infty)$.
- (d) For odd $n\ge3$, $f_n(s)=3f_n(3)/s$ on $[1,3]$. Hence $\sup_{[1,2]}f_n/(2e^2h)=f_n(1)/2=3f_n(3)/2$.
- (e) For even $n\ge4$ and $2\le s\le4$:
$$sf_n(s)=3f_{n-1}(3)\log\frac{3}{s-1}+\int_4^\infty f_{n-1}(t-1)\,dt\qquad\text{([BJS] eq:f4).}$$
- (f) $sf_2(s)=s-3\log(s-1)+3\log3-4$ on $[2,4]$ ([BJS] eq:f2). Moreover
$$M_2=\frac{f_2(2)}{2}=\frac{3\log3-2}{4}=0.3239592\ldots,$$
so $c_2=0.33$ is admissible and the optimal $c_2$ is $0.32396$.

**Theorem 2 (certification).** Fix $N\ge2$. Define the arrays $U_n[i]$ for $n=1,\dots,N$ as follows. The grid point attached to index $i$ is $x^{(n)}_i:=a_n+i\delta$, for $0\le i\le L_n-1$, with
$$L_n:=1000(n+2-a_n)+1 .$$
Let $R[j]$ and $W[j]$ ($0\le j\le 1000(N+1)$) be any numbers with
$$R[j]\ \ge\ \frac1{2e^2h(1+j\delta)},\qquad W[j]\ \ge\ \frac{\delta}{1+j\delta}=\frac1{1000+j}.$$
Define $S_{n-1}[k]$ to be any upper bound for $\sum_{k'\ge k}U_{n-1}[k']$. Put:

- $U_1[i]\ge (2000-i)/(1000+i)$;
- for even $n$: $U_n[i]\ge S_{n-1}[i]\,W[i+1000]$;
- for odd $n\ge3$: $U_n[i]\ge S_{n-1}[0]\,W[i]$ for $i<2000$, and $U_n[i]\ge S_{n-1}[i-2000]\,W[i]$ for $i\ge2000$.

Then $f_n(x^{(n)}_i)\le U_n[i]$ for all $n$ and $i$. Moreover
$$M_n\ \le\ \widehat M_n:=\max_{0\le i\le L_n-2}U_n[i]\,R[j_n(i)+1],\qquad j_n(i):=i+1000(a_n-1).$$
Consequently (Fn) holds with $c_n:=$ any $k/10^4\ge \widehat M_n^{1/(n-1)}$. No tail bound is needed: by Prop. 1(b) the grid covers the whole support, i.e. $s_{\max}=n+2$.

**Theorem 3 (sharper recursion; replaces the $c$-terms of [BJS] eq:tau).** For $n\ge2$ and a range $I$, put
$$p_{n}(I):=\sup_{s\in I}\frac{f_{n-1}(s-1)}{2e^2h(s)},\qquad q_n(I):=\sup_{s\in I}\frac{f_n(s)}{2e^2h(s)}.$$
The ranges are: $I_{s_0}=[s_0,s_0+0.2]$ for $s_0\in\{2,\dots,2.8\}$, $I_3=[3,\infty)$, and $\tilde I=[1,3]$.

Suppose Theorem A of the core section holds. Then it still holds if, in the definition of $\tau_n$:

- $\tau_{n-1}\xi_{s_0}$ is replaced by
$$\tau_{n-1}\bigl(\kappa_{s_0}+(\gamma_{s_0}+\kappa_{s_0})\varepsilon\bigr)+2p_n(I_{s_0})+2q_n(I_{s_0});$$
- $\tau_{n-1}\tilde\xi$ is replaced by
$$\tau_{n-1}\bigl(\tilde\kappa+(5+4\varepsilon)\varepsilon\bigr)+3(1+\varepsilon)f_{n-1}(2)+2(2+\varepsilon)q_n(\tilde I).$$

Any upper bounds for $p,q,f_{n-1}(2)$ may be used, e.g. the cell bounds of Theorem 2. Each new term is $\le$ the old one, so the new $\tau_n$ are never larger.

For $n=2$ the exact values are:

- $p_2(I_{s_0})=\dfrac{(4-s_0)e^{s_0-2}}{2(s_0-1)}$ for $s_0<3$ (so $=1$ at $s_0=2$), and $p_2(I_3)=e/4$;
- $q_2(I_{s_0})=f_2(s_0)/(2e^{2-s_0})$ for $s_0<3$, and $q_2(I_3)=e(3\log\tfrac32-1)/6=0.0980\ldots$.

Hence
$$\tau_2=\max\bigl(5.530\ldots+3(\gamma_2+\kappa_2)\varepsilon,\ \ldots\bigr).$$
In particular, the ξ₃ candidate is $4.06\ldots+O(\varepsilon)$, instead of the old $\tau_1\xi_3\ge9.75$.

## Proof

**Step 1 (soundness review of [BJS] §EXPS: what is done there).** [BJS] proceed as follows.

- They derive eq:f2 and eq:f4.
- They claim $f_n$ is decreasing and $f_n(t)=0$ for $t\ge n+2$.
- They bound $\int_\sigma^\infty f_{n-1}(t-1)dt$ by the left Riemann sum (eq:sigmaapprox) with mesh $10^{-3}$, where $\sigma=\max(3,s)$ (odd $n$) or $\max(4,s)$ (even $n$).
- They iterate this on the grids $1+i/1000$ (odd $n$) and $2+i/1000$ (even $n$).
- They bound $f_n/h$ on $[x_i,x_{i+1}]$ by $f_n(x_i)/h(x_{i+1})$ and round $c_n$ up to two decimals.

Steps 2–5 prove every structural claim used. The method is mathematically sound. The defects are only these:

- (i) floating point arithmetic without outward rounding;
- (ii) the stored $f_{n-1}(x_i)$ are themselves approximations, and their being *upper* bounds is not stated or checked;
- (iii) the computation is unpublished.

So Table `tab:cn1` is plausible but uncertified. Theorem 2 removes (i)–(iii).

**Step 2 (Prop. 1(a),(b), by induction).**

*Base case $n=1$.* $f_1=(3-s)/s=3/s-1$ is nonnegative and decreasing on $[1,3]$, equals $0$ at $s=3$, and is $0$ after. So (a) and (b) hold, since $1+2=3$.

*Induction step.* Assume (a),(b) for $n-1$.

- The function $g(t):=f_{n-1}(t-1)$ is defined where needed:
  - for even $n$ and $t\ge s\ge2$, we have $t-1\ge1=a_{n-1}$;
  - for odd $n$ and $t\ge3$, we have $t-1\ge2=a_{n-1}$.
- $g$ is nonnegative and bounded by $f_{n-1}(a_{n-1})$, and it vanishes for $t\ge n+2$. So $I(s):=\int_s^\infty g$ is finite, nonnegative and nonincreasing.
- Then $f_n(s)=I(s)\cdot(1/s)$ is a product of two nonnegative nonincreasing functions, hence nonincreasing.
- For odd $n$ on $[1,3]$, $f_n=I(3)/s$ is nonincreasing. At $s=3$ both formulas give $I(3)/3$, so $f_n$ is nonincreasing on all of $[1,\infty)$.
- For $s\ge n+2$: $t\ge s$ gives $t-1\ge n+1$, so $g(t)=0$ and $I(s)=0$. Since $n+2\ge5>3$, the odd rule on $[1,3]$ is irrelevant here.

**Step 3 (Prop. 1(c)).** $h$ is piecewise defined.

- It equals $e^{-2}$ on $[1,2]$ and $e^{-s}$ on $[2,3]$; these agree at $2$.
- On $[3,\infty)$ it equals $3e^{-s}/s$, which agrees with $e^{-3}$ at $3$.
- Each piece is positive and nonincreasing.

So $h$ is positive and nonincreasing.

**Step 4 (Prop. 1(d),(e),(f)).**

*(d).* On $[1,3]$, $f_n(s)=3f_n(3)/s$. On $[1,2]$, $2e^2h=2$, so the ratio is $3f_n(3)/(2s)$, maximal at $s=1$.

*(e).* For $s\in[2,4]$, split $\int_s^\infty=\int_s^4+\int_4^\infty$. For $t\in[s,4]$ we have $t-1\in[1,3]$, where $f_{n-1}(t-1)=3f_{n-1}(3)/(t-1)$ by (d) applied to odd $n-1\ge3$. Integrating gives $3f_{n-1}(3)\log(3/(s-1))$.

*(f), formula.*
$$sf_2(s)=\int_s^4\frac{4-t}{t-1}dt=\int_{s-1}^3\frac{3-u}{u}du=3\log\frac3{s-1}-(4-s).$$

*(f), location of the maximum.* Put $\varphi(s):=sf_2(s)$, so that $\varphi'(s)=(s-4)/(s-1)$.

- **On $[2,3]$.** The ratio is $G(s)=e^{s-2}\varphi(s)/(2s)$, with
$$(\log G)'=1-\tfrac1s+\tfrac{\varphi'}{\varphi}.$$
  - On $[2,2.5]$: $|\varphi'|\ge1$ and $\varphi\le\varphi(2)=1.2959$. So $\varphi'/\varphi\le-0.77<-(1-1/s)$, since $1-1/s\le0.6$.
  - On $[2.5,3]$: $|\varphi'|\ge\tfrac12$ and $\varphi\le\varphi(2.5)=0.5795$. So $\varphi'/\varphi\le-0.86<-2/3$.

  Hence $G$ is decreasing on $[2,3]$.
- **On $[3,4]$.** The ratio is $e^{s-2}\varphi(s)/6$, with $(\log)'=1+\varphi'/\varphi$. For $t\ge s$ we have $(4-t)/(t-1)\le(4-s)/(s-1)$, so
$$\varphi(s)=\int_s^4\frac{4-t}{t-1}dt\le(4-s)|\varphi'(s)|\le|\varphi'(s)|\quad(s\ge3).$$
  So this ratio is nonincreasing on $[3,4]$.
- **On $[4,\infty)$.** $f_2=0$.

Therefore $M_2=G(2)=\varphi(2)/4=(3\log3-2)/4$.

**Step 5 (cell bound).** Let $s\in[x_i,x_{i+1}]$. By Steps 2–3:

- $f_n(s)\le f_n(x_i)\le U_n[i]$;
- $h(s)\ge h(x_{i+1})>0$.

Hence $f_n(s)/(2e^2h(s))\le U_n[i]/(2e^2h(x_{i+1}))\le U_n[i]R[\cdot]$.

The cells $[x_i,x_{i+1}]$ for $0\le i\le L_n-2$ cover $[a_n,n+2]$, and $f_n=0$ beyond $n+2$. So the maximum over cells bounds $M_n$.

The index of $x_{i+1}$ in the $R$-table, where $x=1+j\delta$, is $j=i+1+1000(a_n-1)$.

**Step 6 (quadrature inequality).** Let $u_k=a_{n-1}+k\delta$. By monotonicity, on $[u_k,u_{k+1}]$ we have $f_{n-1}\le f_{n-1}(u_k)\le U_{n-1}[k]$. The last grid point of level $n-1$ is $u=n+1$, beyond which $f_{n-1}=0$. Hence for every grid index $k_0$:
$$\int_{u_{k_0}}^\infty f_{n-1}(u)\,du\le\delta\sum_{k\ge k_0}U_{n-1}[k]\le\delta S_{n-1}[k_0].$$
Including the last term $U_{n-1}[L-1]$ only adds a nonnegative amount.

**Step 7 (index bookkeeping in Theorem 2).**

*Even $n$.* Here $x=2+i\delta$ and $s-1=1+i\delta=u_i$ on the odd grid. Both grids have $1000n+1$ points. So
$$f_n(x)=\frac{1}{x}\int_{u_i}^\infty f_{n-1}\le \frac{\delta}{x}\,S_{n-1}[i],$$
and $\delta/x=1/(2000+i)\le W[i+1000]$.

*Odd $n\ge 3$, $x\ge3$.* Here $x=1+i\delta$ with $i\ge2000$, and $x-1=2+(i-2000)\delta$ is index $i-2000$ of the even grid. The index ranges agree: $1000(n+1)-2000=1000(n-1)$, which is the last index of the even grid.

*Odd $n\ge 3$, $x<3$.* Here $f_n(x)=I(3)/x\le\delta S_{n-1}[0]/x$, and $\delta/x=1/(1000+i)\le W[i]$.

*Level $n=1$.* $f_1(1+i\delta)=(2000-i)/(1000+i)$ exactly.

This proves $f_n(x_i)\le U_n[i]$ by induction, using Step 6.

**Step 8 (the $R$ and $W$ tables).** For $x=1+j\delta$:
$$\frac{1}{2e^2h(x)}=\begin{cases}\tfrac12, & j\le1000,\\[2pt] \tfrac12e^{(j-1000)\delta}, & 1000\le j\le2000,\\[2pt] \tfrac{x}{6}e^{(j-1000)\delta}, & j\ge2000.\end{cases}$$
The cases agree at $j=1000$ and at $j=2000$.

- Let $E\ge e^{\delta}$ be the Taylor sum $\sum_{k\le12}\delta^k/k!$ plus the remainder bound $2\delta^{13}/13!$. This is valid since $\sum_{k\ge m}x^k/k!\le 2x^m/m!$ for $0\le x\le\frac12$.
- Then $E^{k}\ge e^{k\delta}$, and products of upper bounds of positive numbers, rounded up, are upper bounds.

All arithmetic is in `decimal` with `ROUND_CEILING`, at 40 significant digits. Every operation used is $+$, $\times$ or $\div$ on nonnegative operands, and is increasing in each argument; for $\div$ the only divisors are the exact integers $2$, $6000$ and $1000+j$. Hence every computed number is $\ge$ its exact counterpart.

`Decimal(int)` construction is exact. Relative rounding is $10^{-39}$ per operation, so only sharpness is affected, never validity.

**Step 9 (from $\widehat M_n$ to $c_n$).** The certified $c_n$ is the least $k/10^4$ with $(k/10^4)^{n-1}\ge\widehat M_n$. This is decided in exact `Fraction` arithmetic by binary search. Then $c_n^{\,n-1}\ge\widehat M_n\ge M_n$, so (Fn) holds.

Two remarks:

- For the $\tau$ recursion it is better to feed $\widehat M_n$ itself in place of $c_n^{n-1}$.
- The paper's step "$c_n\le$ table value" is reproduced exactly when the printed flag is `OK`.

**Step 10 (cost).** Per level $n$ there are $L_n\approx1000n$ grid points. Each requires about 4 C-level `Decimal` operations: the suffix sum via `accumulate`, the product with $W$, and two products with $R$.

- Total: $\approx4\sum_{n\le500}1000n\approx5\cdot10^8$ operations.
- Expected time: a few minutes, at roughly $0.1$–$0.3\,\mu$s per operation.
- Memory: at most about four lists of $5\cdot10^5$ `Decimal`s.

The cut-off $s_{\max}=n+2$ is exact (Prop. 1(b)).

**Step 11 (Theorem 3).** The proof of Theorem A uses $f_{n-1}$ and $f_n$ only through four inequalities. In [BJS] these are (eq:Tn3), (eq:Tn1) and the first and third displays of the odd case; I assume the core section's proof is the same.

- **(α)** $(K-1)f_{n-1}(s-1)\le\varepsilon f_{n-1}(s-1)$, which [BJS] then bound by $\varepsilon\,2e^2c_{n-1}^{n-2}\gamma h(s)$.
  - Instead use directly $f_{n-1}(s-1)\le 2p_n(I)e^2h(s)$ for $s\in I$.
  - This gives $\le 2p_n(I)/\tau_{n-1}\cdot h_{n-1}(s)$.
  - Since $p_n(I)\le\gamma_{s_0}c_{n-1}^{n-2}$ by the old argument (Lemma `hsm1` with corrected $\gamma$), the new term is not larger.
- **(β)** $(K-1)f_n(s)\le\varepsilon f_n(s)\le\varepsilon\,2q_n(I)e^2h(s)=2q_n(I)/\tau_{n-1}\cdot h_{n-1}(s)$. Also $q_n\le c_n^{n-1}$.
- **(γ)** For odd $n$ and $s\in[1,3]$: $\frac{3K}{s}(K-1)f_{n-1}(2)\le3\varepsilon(1+\varepsilon)f_{n-1}(2)\cdot\frac1s$.
  - We have $\sup_{[1,3]}\frac{1}{s\,e^2h(s)}=1$: on $[1,2]$ it equals $1/s\le1$, and on $[2,3]$ it equals $e^{s-2}/s\le e/3<1$.
  - Hence the term is $\le 3(1+\varepsilon)f_{n-1}(2)/\tau_{n-1}\cdot h_{n-1}(s)$.
  - Old: $6(1+\varepsilon)c_{n-1}^{n-2}$, which is not smaller, because $f_{n-1}(2)\le2e^2c_{n-1}^{n-2}h(2)=2c_{n-1}^{n-2}$.
- **(δ)** $\frac{K^2}{s}\int_3^\infty f_{n-1}(t-1)dt=K^2f_n(s)$ and $(K^2-1)f_n(s)\le\varepsilon(2+\varepsilon)f_n(s)$. This gives $\le 2(2+\varepsilon)q_n(\tilde I)/\tau_{n-1}\cdot h_{n-1}(s)$.

The $h_{n-1}$-terms ($\kappa$, $\gamma$, $\tilde\kappa$) are unchanged. Strictness of the final inequality comes, as before, from $K<1+\varepsilon$ multiplying the strictly positive $h_{n-1}$-terms.

*The $n=2$ values.* $f_1(s-1)=(4-s)/(s-1)$ on $[2,4]$.

- On $[2,3]$ the ratio is $(4-s)e^{s-2}/(2(s-1))$, with log-derivative $1-\frac{3}{(4-s)(s-1)}<0$ because $(4-s)(s-1)\le\frac94$. So the supremum on $I_{s_0}$ is attained at $s_0$.
- On $[3,4]$ the ratio is $(4-s)se^{s-2}/(6(s-1))$, with log-derivative $1+\frac1s-\frac1{4-s}-\frac1{s-1}<0$. So $p_2(I_3)=e/4$.
- The values of $q_2$ follow from Step 4.

Numerically, for the ξ₂ and ξ₃ candidates:
$$\tau_1\xi_2^{\rm new}=3\cdot0.9607+3(\gamma_2+\kappa_2)\varepsilon+2+0.6479=5.530+3(\gamma_2+\kappa_2)\varepsilon,$$
$$\tau_1\xi_3^{\rm new}=2.5047+3(\gamma_3+\kappa_3)\varepsilon+1.3591+0.1961=4.060+3(\gamma_3+\kappa_3)\varepsilon.$$

For $s_0=2.2$ I hand-checked $\approx5.23+O(\varepsilon)$, below the ξ₂ candidate. The candidates $s_0=2.4,2.6,2.8$ were **not** evaluated by hand; the script's `step_new` takes the maximum over all of $\Sigma$, so $\tau_2$ is decided by its output (expected near $5.6$ at $\varepsilon=1/100$ if ξ₂ dominates).

The comparison $\tau_2\ge9.75$ in core item 5 is due entirely to the crude $2\gamma_3=8e/3$.

## Code

```python
#!/usr/bin/env python3
"""Certified upper bounds for f_n (BJS eq:f11,f22,odd), M_n = sup f_n/(2e^2 h) and c_n,
n = 2..NMAX (default 500), plus tau recursions (old form with certified M_n; sharpened form).

Certified quantities (all arithmetic: decimal, 40 digits, ROUND_CEILING; every operation is
+,*,/ on nonnegative operands, increasing in each argument, divisors exact integers):
  U[i]  >= f_n(a_n + i/1000)               (left Riemann sums, f_{n-1} nonincreasing)
  R[j]  >= 1/(2 e^2 h(1 + j/1000)),  W[j] >= 1/(1000+j) = delta/(1+j delta)
  M_n   <= max_i U[i]*R[j(x_{i+1})]       (f_n nonincr., h nonincr.)   => (Fn) with c_n^(n-1) >= M_n
  p[s0] >= sup_{s in I_s0} f_{n-1}(s-1)/(2e^2h(s)),  q[s0] >= sup_{s in I_s0} f_n(s)/(2e^2h(s)),
  qt >= sup_{[1,3]} f_n/(2e^2h) (n odd), f2 >= f_{n-1}(2) (n odd).
f_n = 0 on [n+2, oo), so the grid [a_n, n+2] is exhaustive (no tail bound needed).
"""
import sys
from decimal import Decimal as D, getcontext, ROUND_CEILING
from fractions import Fraction as Fr
from itertools import accumulate
from operator import mul

getcontext().prec = 40
getcontext().rounding = ROUND_CEILING

CN_TABLE = [(2, 2, 33), (3, 3, 39), (4, 4, 45), (5, 5, 51), (6, 6, 54), (7, 7, 57), (8, 8, 58),
            (9, 10, 61), (11, 12, 63), (13, 13, 64), (14, 14, 65), (15, 18, 66), (19, 20, 67),
            (21, 26, 68), (27, 34, 69), (35, 46, 70), (47, 82, 71), (83, 345, 72), (346, 500, 73)]
S0_IDX = {Fr(2): 0, Fr(22, 10): 200, Fr(24, 10): 400, Fr(26, 10): 600, Fr(28, 10): 800}


def table_c(n):
    for a, b, v in CN_TABLE:
        if a <= n <= b:
            return Fr(v, 100)
    return None


def exp_milli_up():
    """Upper bound for e^(1/1000): Taylor to degree 12 plus 2 x^13/13! (valid for 0<=x<=1/2)."""
    x, s, t = Fr(1, 1000), Fr(0), Fr(1)
    for k in range(13):
        s += t
        t = t * x / (k + 1)
    s += 2 * t
    return D(s.numerator) / D(s.denominator)          # ceiling division


def tables(J):
    """R[j] >= 1/(2e^2 h(1+j/1000)), W[j] >= 1/(1000+j), 0 <= j <= J."""
    E = exp_milli_up()
    R, W = [None] * (J + 1), [None] * (J + 1)
    half, pw = D(1) / D(2), D(1)
    for j in range(J + 1):
        W[j] = D(1) / D(1000 + j)
        if j <= 1000:
            R[j] = half
        else:
            pw = pw * E                                 # >= e^{(j-1000)/1000}
            R[j] = pw / 2 if j <= 2000 else pw * D(1000 + j) / D(6000)
    return R, W


def certify(NMAX):
    R, W = tables(1000 * (NMAX + 1))
    U = [D(2000 - i) / D(1000 + i) for i in range(2001)]          # f_1 on 1 + i/1000
    CO = {}
    for n in range(2, NMAX + 1):
        S = list(accumulate(reversed(U)))
        S.reverse()                                              # S[k] >= sum_{k'>=k} U[k']
        co = {'p': {}, 'q': {}}
        if n % 2 == 0:
            L = 1000 * n + 1                                     # x = 2 + i/1000, i < L
            Un = list(map(mul, S, W[1000:1000 + L]))
            rn = list(map(mul, Un[:L - 1], R[1001:1000 + L]))    # cell i -> x_{i+1}: j = i+1001
            ro = list(map(mul, U[:L - 1], R[1001:1000 + L]))     # f_{n-1}(s-1), s-1 = 1 + i/1000
            for s0, a in S0_IDX.items():
                co['q'][s0] = max(rn[a:a + 200])
                co['p'][s0] = max(ro[a:a + 200])
            co['q'][Fr(3)] = max(rn[1000:])
            co['p'][Fr(3)] = max(ro[1000:])
        else:
            L = 1000 * (n + 1) + 1                               # x = 1 + i/1000, i < L
            Un = [S[0] * W[i] for i in range(2000)] + list(map(mul, S, W[2000:L]))
            rn = list(map(mul, Un[:L - 1], R[1:L]))
            co['qt'] = max(rn[:2000])
            co['q'][Fr(3)] = max(rn[2000:])
            co['p'][Fr(3)] = max(map(mul, U[0:L - 2001], R[2001:L]))   # s-1 = 2 + (i-2000)/1000
            co['f2'] = U[0]                                      # >= f_{n-1}(2)
        co['M'] = max(rn)
        CO[n] = co
        U = Un
    return CO


def c_up(M, n):
    """Least k/10^4 with (k/10^4)^(n-1) >= M (exact Fractions); None if M > 1."""
    Mf = Fr(M)
    if Mf > 1:
        return None
    lo, hi = 0, 10000
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if Fr(mid, 10000) ** (n - 1) >= Mf:
            hi = mid
        else:
            lo = mid
    return Fr(hi, 10000)


# ---------------- tau recursion (constants as in our tau script) ----------------
DIGITS = 40
SCALE = 10 ** DIGITS


def up(x):
    x = Fr(x)
    return Fr(-((-x.numerator * SCALE) // x.denominator), SCALE)


def exp_up(x, terms=60):
    x = Fr(x)
    assert 0 <= x <= 1
    s, t = Fr(0), Fr(1)
    for k in range(terms):
        s += t
        t = t * x / (k + 1)
    return up(s + 2 * t)


KAPPA = {Fr(2): Fr(9607, 10000), Fr(22, 10): Fr(9557, 10000), Fr(24, 10): Fr(9457, 10000),
         Fr(26, 10): Fr(9261, 10000), Fr(28, 10): Fr(8914, 10000), Fr(3): Fr(8349, 10000)}
KAPPA_T = Fr(9214, 10000)
E_UP = exp_up(1)
GAMMA = {s: exp_up(s - Fr(18, 10)) for s in KAPPA if s < 3}
GAMMA[Fr(3)] = up(4 * E_UP / 3)
C = Fr(9607, 10000)


def check_majorant(eps):
    A = KAPPA[Fr(2)] + (GAMMA[Fr(2)] + KAPPA[Fr(2)]) * eps
    ok = all(KAPPA[s] + (GAMMA[s] + KAPPA[s]) * eps <= A for s in KAPPA)
    ok = ok and KAPPA_T + (5 + 4 * eps) * eps <= A and A < 1
    ok = ok and all(GAMMA[s] <= GAMMA[Fr(3)] for s in GAMMA) and 6 * (1 + eps) <= 2 * GAMMA[Fr(3)]
    return ok, A


def run(k, step, nmax=6000):
    eps = Fr(1, k)
    ok, A = check_majorant(eps)
    if not ok:
        return None
    tau, sums, first = Fr(3), [Fr(0), Fr(3)], []
    for n in range(2, nmax + 1):
        tau = up(max(step(n, tau, eps)))
        sums[n % 2] += tau
        if n <= 3:
            first.append(tau)
    B = 2 * GAMMA[Fr(3)] + 2 * (2 + eps) * C
    tail = up((A * tau + B * up(C ** (nmax - 1)) / (1 - C)) / (1 - A))
    return sums[1] + tail, sums[0] + tail, first


def make_steps(CO, NMAX, nmax=6000):
    CP = [Fr(1), Fr(1)]
    for n in range(2, nmax + 1):
        CP.append(up(CP[-1] * C))                    # CP[n] >= 0.9607^(n-1)
    Mf = {n: up(Fr(CO[n]['M'])) for n in CO}

    def Mof(n):                                      # admissible bound for c_n^(n-1)
        return Fr(1) if n == 1 else (Mf[n] if n <= NMAX else CP[n])

    def old(n, tau, eps):
        a, b = Mof(n - 1), Mof(n)
        if n % 2 == 0:
            return [tau * (KAPPA[s] + (GAMMA[s] + KAPPA[s]) * eps) + 2 * GAMMA[s] * a + 2 * b for s in KAPPA]
        s = Fr(3)
        return [tau * (KAPPA[s] + (GAMMA[s] + KAPPA[s]) * eps) + 2 * GAMMA[s] * a + 2 * b,
                tau * (KAPPA_T + (5 + 4 * eps) * eps) + 6 * (1 + eps) * a + 2 * (2 + eps) * b]

    def new(n, tau, eps):
        if n > NMAX:
            return old(n, tau, eps)
        co = CO[n]
        P = {s: up(Fr(v)) for s, v in co['p'].items()}
        Q = {s: up(Fr(v)) for s, v in co['q'].items()}
        if n % 2 == 0:
            return [tau * (KAPPA[s] + (GAMMA[s] + KAPPA[s]) * eps) + 2 * P[s] + 2 * Q[s] for s in KAPPA]
        s = Fr(3)
        return [tau * (KAPPA[s] + (GAMMA[s] + KAPPA[s]) * eps) + 2 * P[s] + 2 * Q[s],
                tau * (KAPPA_T + (5 + 4 * eps) * eps) + 3 * (1 + eps) * up(Fr(co['f2']))
                + 2 * (2 + eps) * up(Fr(co['qt']))]
    return old, new


def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    CO = certify(NMAX)
    print("n | certified c_n (4 dp, up) | [BJS] c_n | M_n upper (8 sig) | flag")
    getcontext().prec = 8
    for n in range(2, NMAX + 1):
        M = +CO[n]['M']                               # re-rounded up to 8 digits
        c = c_up(CO[n]['M'], n)
        t = table_c(n)
        flag = "OK" if (c is not None and t is not None and c <= t) else "TABLE NOT CONFIRMED"
        print(n, "|", "%.4f" % c if c is not None else ">1", "|", t and "%.2f" % t, "|", M, "|", flag)
    getcontext().prec = 40
    old, new = make_steps(CO, NMAX)
    for k in (74, 100, 200):
        for name, st in (("old recursion, certified M_n", old), ("sharpened recursion (Thm 3)", new)):
            r = run(k, st)
            if r is None:
                print(k, name, "not applicable")
            else:
                print("1/eps=%d %s: C1<=%.3f C2<=%.3f tau2<=%.4f tau3<=%.4f" %
                      (k, name, float(r[0]) + 5e-4, float(r[1]) + 5e-4,
                       float(r[2][0]) + 5e-5, float(r[2][1]) + 5e-5))


if __name__ == "__main__":
    main()
```

**What the output should look like (not run).**

- **$n=2$.** $M_2\approx0.32453$, so the certified $c_2$ is $0.3246$.
  - This exceeds the exact $0.3239592$ only by mesh effects: the left sum adds about $\delta/2\cdot f_1(1)$ to $\int_1^3f_1=1.29584$, and the cell factor is $e^{0.001}$.
  - Sanity check: $U_2[0]\approx0.648419$, whereas $f_2(2)=0.647918$.
- **$n=3$.** The supremum on $[1,2]$ is $f_3(1)/2=\tfrac12\int_2^4f_2$. A Simpson estimate gives $\int_2^4f_2\approx0.2955$. So expect $M_3\approx0.148$ and $c_3\approx0.385$, against the table's $0.39$.
- **Expected flags.** I expect `OK` throughout, because the certified values use the same scheme as [BJS] and are rounded to 4 decimals rather than 2. Any `TABLE NOT CONFIRMED` line refutes the table at that $n$.
- **Old recursion with certified $M_n$.** Since $M_n\le c_n^{n-1}$, this gives values at most those of our earlier run with the table, i.e. $\le349.85$ at $1/100$, provided all flags are `OK`.
- **Sharpened recursion.** It must give $\tau_2\approx5.6$ at $\varepsilon=1/100$, provided the ξ₂ candidate is the maximum (Step 11), and smaller $C_i$.
- **Runtime.** About $5\cdot10^8$ `Decimal` operations, i.e. minutes. Run with argument `40` first, which takes seconds.

## What is not proved here

- No output is claimed. The script has not been run, so the certified $c_n$ for $n\ge3$, and both sets of $C_i$, are unknown until it is executed. Only $c_2$ (exact) and the $n=2$ quantities of Theorem 3 are proved by hand.
- Theorem 3 is proved only relative to Theorem A of the core section. It assumes that the proof of Theorem A uses $f_{n-1}$ and $f_n$ only through the four inequalities (α)–(δ), as in the displayed [BJS] proof. I did not re-derive the underlying [BJS] eq. (Tneq) / Lemma 9.8 recursion.
- Whether the sharpened $C_1(1/100)$ falls to 276 (the value in [BJS] Table `tab:fF`) is not decided here.

## Checks a referee should make

1. Check the index maps in Step 7. In particular, for odd $n$ the even-grid index is $i-2000$, not $i-1000$. Check the slice lengths in `certify`: `W[2000:L]` has $1000(n-1)+1$ entries, matching `S`.
2. Confirm that `R[1000]` and `R[2000]` are consistent across the piecewise formula (both $\tfrac12$, resp. $\approx e/2$), and that $E\ge e^{0.001}$.
3. Check that $n=2$ prints $0.3246$ and $M_2\in[0.32396,0.3246]$.
4. Run with `NMAX=40`, then with mesh $1/2000$ (change 1000→2000 consistently). The certified values must decrease toward the true $M_n$.
5. Check that the sharpened $\tau_2$ at $\varepsilon\to0$ is close to $5.53$ (×1.001 mesh factor), and that every sharpened $\tau_n\le$ old $\tau_n$ (Theorem 3).