"""Interval enclosures of log, exp, real powers and arctan(1/m).

Each function returns an ``Iv`` that contains the exact value for every point
of its argument.  Series are summed in interval arithmetic and an explicit
interval for the truncation error is added; the bound on that error is stated
next to it.  Two steps choose an integer by a cheap estimate (the scaling
exponent for log and exp); the estimate is never trusted: the reduced
argument is re-checked in interval arithmetic before the series is used.
"""

from __future__ import annotations

from decimal import ROUND_CEILING, ROUND_FLOOR, ROUND_HALF_EVEN, Context, Decimal, localcontext
from fractions import Fraction

from .interval import ERROR_TRAPS, ONE, TWO, Iv, add_dir, div_dir, neg_exact, sub_dir


def _ln2() -> Iv:
    """ln 2 = 2 sum_{k>=0} 1/((2k+1) 3^(2k+1)).

    After 100 terms the tail is < 2/(201 * 3^201)/(1 - 1/9) < 1e-97; an interval
    [0, 1e-95] is added for it before doubling.
    """
    s = Iv(0)
    pow3 = 3
    for k in range(100):
        s = s + Iv.from_fraction(Fraction(1, (2 * k + 1) * pow3))
        pow3 *= 9
    tail = Iv(Decimal(0), Decimal("1e-95"))
    return TWO * (s + tail)


LN2 = _ln2()
"""Enclosure of log 2."""


def _ln_point(x: Decimal) -> Iv:
    """Enclosure of log x for a positive Decimal x.

    x = 2^k m with m in [0.75, 1.5] (checked in intervals), then
    log m = 2 artanh(u), u = (m-1)/(m+1), |u| <= 0.21 (checked), summed to 70
    terms; the tail is <= 2 * 0.21^141/(141 (1 - 0.21^2)) < 1e-95, covered by +-1e-90.
    """
    if x <= 0:
        raise ValueError(f"ln of non-positive {x}")
    if x == 1:
        return Iv(0)
    k = 0
    m = Iv(x)
    # Choice of a power of 2 near x from the decimal exponent (an integer; exact).
    k_est = int(x.adjusted() * 3321928 // 1000000)
    if k_est > 0:
        m = m / Iv(Decimal(1 << k_est))
        k += k_est
    elif k_est < 0:
        m = m * Iv(Decimal(1 << (-k_est)))
        k += k_est
    half = Iv(Decimal("0.5"))
    while m.hi > Decimal("1.5"):
        m = m * half
        k += 1
    while m.lo < Decimal("0.75"):
        m = m * TWO
        k -= 1
    u = (m - ONE) / (m + ONE)
    if u.abs_hi() > Decimal("0.21"):
        raise ArithmeticError(f"ln reduction failed: m={m}, u={u}")
    u2 = u * u
    term = u
    s = Iv(0)
    for j in range(70):
        s = s + term / Iv(2 * j + 1)
        term = term * u2
    err = Decimal("1e-90")
    ln_m = TWO * s + Iv(neg_exact(err), err)
    return ln_m + Iv(k) * LN2


def ln_iv(x: Iv) -> Iv:
    """Enclosure of log on [x.lo, x.hi] (log is increasing): [low end at lo, high end at hi]."""
    return Iv(_ln_point(x.lo).lo, _ln_point(x.hi).hi)


def _exp_point(x: Decimal) -> Iv:
    """Enclosure of e^x for a Decimal x.

    x = k log 2 + r with |r| <= 0.4 (checked in intervals); Taylor series to 60
    terms, tail <= 0.4^60/(60! (1 - 0.4/61)) < 2e-106, covered by +-1e-90.
    """
    if x == 0:
        return Iv(1)
    # Choice of k ~ x/log 2 (an integer); |r| <= 0.4 is re-checked below.
    with localcontext(Context(prec=30, rounding=ROUND_HALF_EVEN, traps=ERROR_TRAPS)):
        k = int((x / LN2.lo).to_integral_value())
    r = Iv(x) - Iv(k) * LN2
    while r.hi > Decimal("0.4"):
        k += 1
        r = Iv(x) - Iv(k) * LN2
    while r.lo < Decimal("-0.4"):
        k -= 1
        r = Iv(x) - Iv(k) * LN2
    s = Iv(1)
    term = Iv(1)
    for j in range(1, 60):
        term = term * r / Iv(j)
        s = s + term
    err = Decimal("1e-90")
    exp_r = s + Iv(neg_exact(err), err)
    if k >= 0:
        return exp_r * Iv(Decimal(1 << k))
    return exp_r / Iv(Decimal(1 << (-k)))


def exp_iv(x: Iv) -> Iv:
    """Enclosure of exp on [x.lo, x.hi] (exp is increasing)."""
    return Iv(_exp_point(x.lo).lo, _exp_point(x.hi).hi)


def pow_real_iv(base: Iv, exponent: Iv) -> Iv:
    """Enclosure of base^exponent = exp(exponent * log base), base > 0."""
    return exp_iv(exponent * ln_iv(base))


def atan_inv_iv(m: int, terms: int) -> Iv:
    """Enclosure of arctan(1/m), m >= 2 an integer.

    arctan(1/m) = sum_k (-1)^k / ((2k+1) m^(2k+1)) is alternating with
    decreasing terms, so a partial sum with an even number n of terms is a
    lower bound and one with n + 1 terms an upper bound.  Denominators are exact
    ints; the only roundings are the directed divisions and additions below.
    """
    s_lo = Decimal(0)
    s_hi = Decimal(0)
    n_lo = 2 * (terms // 2)
    n_hi = n_lo + 1
    pow_m = m
    m2 = m * m
    for k in range(n_hi):
        denom = Decimal(pow_m * (2 * k + 1))
        if k % 2 == 0:
            if k < n_lo:
                s_lo = add_dir(s_lo, div_dir(Decimal(1), denom, ROUND_FLOOR), ROUND_FLOOR)
            s_hi = add_dir(s_hi, div_dir(Decimal(1), denom, ROUND_CEILING), ROUND_CEILING)
        else:
            if k < n_lo:
                s_lo = sub_dir(s_lo, div_dir(Decimal(1), denom, ROUND_CEILING), ROUND_FLOOR)
            s_hi = sub_dir(s_hi, div_dir(Decimal(1), denom, ROUND_FLOOR), ROUND_CEILING)
        pow_m = pow_m * m2
    return Iv(s_lo, s_hi)
