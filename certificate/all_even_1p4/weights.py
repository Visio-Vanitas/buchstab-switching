"""The weighted inequality (1.1) and the Bonferroni sieve weights (the note, section 1-2).

Weighted inequality (note section 1).  For real z < y with z y^4 >= N and
y^5 > N, put w(a) = 1 - (1/2)#{q in [z,y) : q | a} - (1/2)#{q in [z,y) : q^2 | a}
on a in A with (a, P(z)) = 1.  Then w(a) > 0 implies Omega(a) <= 4, so

    pi_4(N) >= S(A,P(z)) - 1/2 sum_{z<=q<y} S(A_q,P(z)) - 1/2 sum_{z<=q<y} |A_{q^2}|.    (1.1)

Sieve weights (note section 2, Lemma 1).  With w_p = 1/(p-1) and
g_m(T) = sum_{j<=m} (-1)^j e_j(w_p : p in T), the truncation of
prod (1 - w_p) at order m is a lower bound (m odd) or an upper bound (m even);
R_m(T) = g_m(T)/V_2(T), V_2(T) = prod_{p in T} (1 - w_p).
"""

from __future__ import annotations

from .checks import CheckList
from .interval import ONE, Iv
from .primes import factorial


def require_weight_conditions(checks: CheckList, z: int, y: int, x_hi: int) -> None:
    """Record the integer conditions under which (1.1) holds for every N < x_hi.

    z y^4 >= x_hi > N and y^5 > x_hi > N, and z < y (exact integer checks).
    """
    checks.require("weights: y^5 > X_hi", "note s1 (1.1)", y ** 5, ">", x_hi, y=y)
    checks.require("weights: z*y^4 >= X_hi", "note s1 (1.1)", z * (y ** 4), ">=", x_hi, z=z, y=y)
    checks.require("weights: y > z", "note s1 (1.1)", y, ">", z, z=z, y=y)


def elementary_symmetric(weights: list[Iv], max_k: int) -> list[Iv]:
    """Enclosures of e_0, ..., e_max_k of the given weights (e_0 = 1)."""
    e = [Iv(0)] * (max_k + 1)
    e[0] = ONE
    for w in weights:
        for k in range(max_k, 0, -1):
            e[k] = e[k] + w * e[k - 1]
    return e


def alternating_partial_sum(e: list[Iv], m: int) -> Iv:
    """g_m = sum_{j=0}^{m} (-1)^j e_j."""
    out = Iv(0)
    for j in range(m + 1):
        out = out + (e[j] if j % 2 == 0 else -e[j])
    return out


def bonferroni_tail_upper(s1: Iv, order: int) -> Iv:
    """Upper end bounds e_{order+1}(w) <= S1^(order+1)/(order+1)!, S1 = sum of the weights."""
    return (s1 ** (order + 1)) / Iv(factorial(order + 1))


def truncated_exp_sum(x: Iv, m: int) -> Iv:
    """sum_{j=0}^{m} x^j/j!; with x >= sum of weights it bounds sum_{j<=m} e_j from above."""
    out = Iv(0)
    fact_j = 1
    for j in range(m + 1):
        if j > 0:
            fact_j *= j
        out = out + (x ** j) / Iv(fact_j)
    return out
