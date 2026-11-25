"""Rigorous enclosures of the real constants used by the certificate.

All are computed here from first principles in interval arithmetic; none is
typed in as a decimal approximation.

=============  ==============================================================
``PI``         Machin: pi = 4 (4 arctan(1/5) - arctan(1/239))
``GAMMA``      Euler's constant, Euler-Maclaurin with M = 1000 and B_2..B_16
``E_GAMMA``    e^gamma;  ``E_NEG_GAMMA`` = e^-gamma
``C2_TWIN``    twin-prime constant C_2 = prod_{p>2} (1 - 1/(p-1)^2)
``M0``         Meissel-Mertens constant M_0 = gamma + sum_p (log(1-1/p) + 1/p)
``U_C``        U_c = 2 e^-gamma C_2 <= U_N  (the note, section 0.5)
``LI2``        li(2) (used in [JS] Lemma 5.1)
``LI_E5``      li(e^5) (used for li(x) < x/(log x - 2), note section 0.4)
=============  ==============================================================
"""

from __future__ import annotations

from fractions import Fraction

from .elementary import LN2, atan_inv_iv, exp_iv, ln_iv
from .interval import ONE, TWO, Iv, neg_exact
from .primes import P_CUT, PRIMES

PI = Iv(4) * (Iv(4) * atan_inv_iv(5, 80) - atan_inv_iv(239, 40))


def _gamma() -> Iv:
    """gamma = H_M - log M - 1/(2M) + sum_{j=1}^{8} B_{2j}/(2j M^{2j}) + R, M = 1000.

    |R| <= |B_18|/(18 M^18) (Euler-Maclaurin remainder bounded by the next term).
    """
    m = 1000
    harmonic = Iv(0)
    for k in range(1, m + 1):
        harmonic = harmonic + ONE / Iv(k)
    ln_m = ln_iv(Iv(m))
    bernoulli = (
        Fraction(1, 6),        # B_2
        Fraction(-1, 30),      # B_4
        Fraction(1, 42),       # B_6
        Fraction(-1, 30),      # B_8
        Fraction(5, 66),       # B_10
        Fraction(-691, 2730),  # B_12
        Fraction(7, 6),        # B_14
        Fraction(-3617, 510),  # B_16
    )
    b18_abs = Fraction(43867, 798)
    corr = Iv(0)
    m2 = m * m
    pow_m = m2
    for idx, b in enumerate(bernoulli):
        two_j = 2 * (idx + 1)
        corr = corr + Iv.from_fraction(b / (two_j * pow_m))
        pow_m *= m2
    rem_bound = Iv.from_fraction(b18_abs / (18 * pow_m))
    rem = Iv(neg_exact(rem_bound.hi), rem_bound.hi)
    return harmonic - ln_m - Iv.from_fraction(Fraction(1, 2 * m)) + corr + rem


GAMMA = _gamma()
E_GAMMA = exp_iv(GAMMA)
E_NEG_GAMMA = exp_iv(-GAMMA)


def _twin_prime_and_mertens() -> tuple[Iv, Iv]:
    """Enclosures of C_2 and M_0 from the primes <= P_CUT plus explicit tails.

    C_2:  prod_{p > P_CUT} (1 - 1/(p-1)^2) >= 1 - sum_{n >= P_CUT} 1/n^2 > 1 - 1/(P_CUT-1),
          and the factor is <= 1.
    M_0:  for p > P_CUT, log(1-1/p) + 1/p = -sum_{k>=2} 1/(k p^k) lies in [-1/(p(p-1)), 0],
          and sum_{p > P_CUT} 1/(p(p-1)) <= 1/P_CUT < 1/(P_CUT-1).
    """
    c2_fin = Iv(1)
    m0_corr = Iv(0)
    for p in PRIMES:
        if p > 2:
            c2_fin = c2_fin * Iv.from_fraction(Fraction((p - 1) * (p - 1) - 1, (p - 1) * (p - 1)))
        inv_p = ONE / Iv(p)
        m0_corr = m0_corr + ln_iv(ONE - inv_p) + inv_p
    tail_c2 = ONE - ONE / Iv(P_CUT - 1)
    c2 = Iv((c2_fin * tail_c2).lo, c2_fin.hi)
    tail_m0 = Iv((-ONE / Iv(P_CUT - 1)).lo, 0)
    m0 = GAMMA + m0_corr + tail_m0
    return c2, m0


C2_TWIN, M0 = _twin_prime_and_mertens()
U_C = TWO * E_NEG_GAMMA * C2_TWIN


def li_exp_iv(u: Iv) -> Iv:
    """Enclosure of li(e^u) for 0 < u < 10.

    li(e^u) = gamma + log u + sum_{k>=1} u^k/(k k!)  (li = principal value of
    int_0^x dt/log t).  After 59 terms the tail sum_{k>=60} u^k/(k k!) is at most
    (u^60/60!)/(60 (1 - u/61)), which is added as [0, that].
    """
    if u.hi >= 10:
        raise ValueError("li_exp_iv is only set up for u < 10")
    n = 60
    s = GAMMA + ln_iv(u)
    term = u
    for k in range(1, n):
        s = s + term / Iv(k)
        term = term * u / Iv(k + 1)
    tail = term / (Iv(n) * (ONE - u / Iv(n + 1)))
    return s + Iv(0, tail.hi)


LI2 = li_exp_iv(LN2)
LI_E5 = li_exp_iv(Iv(5))
E5_OVER_3 = exp_iv(Iv(5)) / Iv(3)
"""e^5/3; the certificate checks li(e^5) < e^5/3 (note section 0.4)."""

