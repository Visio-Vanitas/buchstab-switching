"""Bounds for sums over primes and for pi(x), derived from the cited results.

Notation (the note, section 0.2): E_<(x) := sum_{p<x} 1/p - log log x - M0.
"""

from __future__ import annotations

from decimal import Decimal

from .cited import (
    MERTENS_TEN12,
    bjs_lemma_16_numerator,
    mertens_cap,
    mertens_large_coeff,
    mertens_lower_coeff,
    schoenfeld_denominator,
)
from .constants import M0, PI
from .elementary import ln_iv
from .interval import TWO, Iv

TEN12 = Iv(MERTENS_TEN12)


def mertens_upper_error(x: Iv, log_x: Iv) -> Decimal:
    """An upper bound for E_<(t), uniform for every real t in [x.lo, x.hi] (x.lo > exp(8.9)).

    On t <= 1e12: min([BJS] Lemma 16 at t = x.lo, which is decreasing in t; [JS] (3.2)).
    On t > 1e12:  [JS] (3.3) at t = max(x.lo, 1e12), decreasing in t.
    (Lemma 16 bounds sum_{p<=t}, which is >= sum_{p<t}.)
    """
    cap = mertens_cap(log_x.lo)
    bounds = []
    if x.lo <= TEN12.lo:
        t0 = Iv(x.lo)
        numerator = bjs_lemma_16_numerator(x.lo, min(x.hi, TEN12.lo))
        b16 = (Iv(numerator) / (t0.sqrt() * ln_iv(t0))).hi
        bounds.append(min(b16, cap))
    if x.hi > TEN12.lo:
        t_start = max(x.lo, TEN12.lo)
        t0 = Iv(t_start)
        bounds.append((Iv(mertens_large_coeff(t_start)) / ln_iv(t0)).hi)
    return max(bounds)


def sum_inv_p_upper(x: Iv, log_x: Iv) -> Iv:
    """Upper end bounds sum_{p<t} 1/p for every t in x: log log x + M0 + E, E = mertens_upper_error."""
    e = mertens_upper_error(x, log_x)
    return ln_iv(log_x) + M0 + Iv(e)


def sum_inv_p_lower(x: Iv, log_x: Iv) -> Iv:
    """Lower end bounds sum_{p<x} 1/p ([JS] (3.1)): log log x + M0 - 2.964e-6/log x, x >= 2."""
    err = Iv(mertens_lower_coeff(x.lo)) / log_x
    return ln_iv(log_x) + M0 - err


def prime_count_upper(x: Iv, log_x: Iv, x_min: int) -> Iv:
    """Upper end bounds pi(x): x/(log x - 2) + sqrt(x) log x/(8 pi).

    pi(x) <= li(x) + sqrt(x) log x/(8 pi) ([BS] Lemma 1, RH, x >= 2657) and
    li(x) < x/(log x - 2) for x >= e^5 (note section 0.4; li(e^5) < e^5/3 is a
    check of the run).  ``x_min`` is an exact integer lower bound of x.
    """
    if not log_x.lo >= 5:
        raise ValueError(f"li(x) < x/(log x - 2) needs x >= e^5, log x >= {log_x.lo}")
    return x / (log_x - TWO) + x.sqrt() * log_x / (Iv(schoenfeld_denominator(x_min)) * PI)
