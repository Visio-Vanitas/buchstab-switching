"""One-sided bounds for the linear-sieve functions F, f and h ([BJS] Theorem 6, Lemma 19).

Each function takes an interval s and returns a bound valid for EVERY s' >= s.lo,
using the monotonicity of the function (F decreasing, f increasing, [JS] section 2;
h non-increasing by its definition).  The callers rely on exactly this uniformity.
"""

from __future__ import annotations

from decimal import Decimal

from .constants import E_GAMMA
from .elementary import exp_iv, ln_iv
from .interval import ONE, TWO, Iv, neg_exact

F_QUADRATURE_POINTS = 200
"""Number of right-endpoint Riemann points in the F integral."""


def F_upper(s: Iv) -> Iv:
    """Upper end bounds F(s') for every s' >= s.lo > 1.

    F(s) = 2e^gamma/s on (0, 3].  On [3, 5]: sF(s) = 2e^gamma (1 + int_2^{s-1} log(t-1)/t dt)
    (from (sF)' = f(s-1) and f on [2, 4]; note 0.1).  log(t-1)/t is increasing on [2, 4]
    (note 0.4), so the right-endpoint Riemann sum with 200 points bounds the integral from
    above.  For s > 5, F(s) <= F(5).
    """
    s0 = s.lo
    if s0 <= 1:
        raise ValueError(f"F(s) bound needs s > 1, got {s0}")
    if s0 <= 3:
        return TWO * E_GAMMA / Iv(s0)
    s_cap = min(s0, Decimal(5))
    a = TWO
    b = Iv(s_cap) - ONE
    n = F_QUADRATURE_POINTS
    h = (b - a) / Iv(n)
    total = Iv(0)
    for i in range(1, n + 1):
        t = a + Iv(i) * h
        total = total + ln_iv(t - ONE) / t
    return (TWO * E_GAMMA / Iv(s_cap)) * (ONE + total * h)


def f_lower(s: Iv) -> Iv:
    """Lower end bounds f(s') for every s' >= s.lo.

    f = 0 on (0, 2]; f(s) = 2e^gamma log(s-1)/s on [2, 4]; for s > 4, f(s) >= f(4).
    (Using f(4) for s > 4 is the original's conservative choice and is kept.)
    """
    s0 = s.lo
    if s0 <= 2:
        return Iv(0)
    s_cap = Iv(min(s0, Decimal(4)))
    return TWO * E_GAMMA * ln_iv(s_cap - ONE) / s_cap


def h_upper(s: Iv) -> Iv:
    """Upper end bounds h(s') for every s' >= s.lo: h = e^-2 on [1,2], e^-s on [2,3], 3e^-s/s on [3,inf)."""
    s0 = s.lo
    if s0 <= 2:
        return exp_iv(Iv(-2))
    if s0 <= 3:
        return exp_iv(Iv(neg_exact(s0)))
    return (Iv(3) / Iv(s0)) * exp_iv(Iv(neg_exact(s0)))
