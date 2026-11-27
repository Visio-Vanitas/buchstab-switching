"""
Pure integer prime tables, Euler-Mascheroni / pi / C_2 / M_0 enclosures,
and Selberg convolution constants in outward-rounded `Iv`.
"""

from __future__ import annotations

import bisect
from decimal import Decimal
from fractions import Fraction

from .interval import Iv, exp_iv, floor_root_int, ln_iv

P_BIG_LIMIT = 18_000_000
P_CUT = 1_000_000
P_PREFIX_MAX = 250_000


def sieve_primes(limit: int) -> list[int]:
    """Pure integer Eratosthenes sieve up to `limit`."""
    flags = bytearray([1]) * (limit + 1)
    flags[0] = flags[1] = 0
    r = floor_root_int(limit, 2)
    for i in range(2, r + 1):
        if flags[i]:
            flags[i * i :: i] = bytearray(len(flags[i * i :: i]))
    return [i for i in range(limit + 1) if flags[i]]


PRIMES_BIG = sieve_primes(P_BIG_LIMIT)
PRIMES = PRIMES_BIG[: bisect.bisect_right(PRIMES_BIG, P_CUT)]
ODD_PRIMES = PRIMES[1:]  # p >= 3
PRIMES_PRE = PRIMES_BIG[: bisect.bisect_right(PRIMES_BIG, P_PREFIX_MAX)]


def _compute_pi_iv() -> Iv:
    """Machin's formula `pi = 16 arctan(1/5) - 4 arctan(1/239)`."""
    def atan_inv(m: int) -> Iv:
        m2 = m * m
        s = Iv(0, 0)
        k = 0
        p = Iv(1, 1) / Iv(m, m)
        while True:
            term = p / Iv(2 * k + 1, 2 * k + 1)
            if term.hi < Decimal("1e-88"):
                return s + Iv.sym(term.hi)
            s = s + term if k % 2 == 0 else s - term
            p = p / Iv(m2, m2)
            k += 1

    return Iv(16, 16) * atan_inv(5) - Iv(4, 4) * atan_inv(239)


def _compute_gamma_iv() -> Iv:
    """Euler-Maclaurin on `H_1000 - ln(1000)` with rigorous alternating remainder."""
    n = 1000
    hn = Iv(0, 0)
    for k in range(1, n + 1):
        hn = hn + Iv.from_frac(Fraction(1, k))
    base = hn - ln_iv(Iv(n, n)) - Iv.from_frac(Fraction(1, 2 * n))
    b_terms = [
        Fraction(1, 12),
        Fraction(-1, 120),
        Fraction(1, 252),
        Fraction(-1, 240),
        Fraction(1, 132),
        Fraction(-691, 32760),
        Fraction(1, 12),
    ]
    n2 = n * n
    cur_pow = n2
    for c in b_terms[:-1]:
        base = base + Iv.from_frac(c) / Iv(cur_pow, cur_pow)
        cur_pow *= n2
    err_iv = Iv.from_frac(b_terms[-1]) / Iv(cur_pow, cur_pow)
    err = err_iv.hi if err_iv.hi >= 0 else (-err_iv).hi
    return base + Iv.sym(err)


def _li_exp_iv(u: Iv) -> Iv:
    """Convergent Ramanujan-Soldner series for `li(e^u)` on `u < 10`."""
    n_terms = 120
    s = GAMMA + ln_iv(u)
    term = u
    for k in range(1, n_terms + 1):
        s = s + term / Iv(k, k)
        term = term * u / Iv(k + 1, k + 1)
    assert u.hi < Decimal(10)
    tail = term / (Iv(n_terms, n_terms) * (Iv(1, 1) - u / Iv(n_terms + 1, n_terms + 1)))
    return s + Iv(Decimal(0), tail.hi)


def _compute_c2_and_m0() -> tuple[Iv, Iv]:
    """Twin-prime constant `C_2` and Meissel-Mertens `M_0` over `p <= P_CUT = 10^6` + tail."""
    prod_p = Iv(1, 1)
    for p in ODD_PRIMES:
        prod_p = prod_p * Iv.from_frac(Fraction((p - 1) ** 2 - 1, (p - 1) ** 2))
    tail_c2 = Iv(1, 1) / Iv(2 * P_CUT, 2 * P_CUT)
    c2_iv = prod_p * Iv(Iv(1, 1).lo - tail_c2.hi, Decimal(1))

    s_m0 = GAMMA
    for p in PRIMES:
        s_m0 = s_m0 + ln_iv(Iv.from_frac(Fraction(p - 1, p))) + Iv.from_frac(Fraction(1, p))
    tail_m0_lo = -(Iv(1, 1) / Iv(P_CUT - 1, P_CUT - 1))
    m0_iv = s_m0 + Iv(tail_m0_lo.lo, Decimal(0))
    return c2_iv, m0_iv


def _compute_selberg_constants() -> tuple[Iv, Iv, Iv]:
    """Constants `H_{1/4}`, `C_J`, and `H_tilde = prod_{p>2} (1 + 1/(p(p-1)))`."""
    prod_h = Iv(1, 1)
    prod_ht = Iv(1, 1)
    h_cut = 100_000
    for p in ODD_PRIMES:
        if p <= h_cut:
            p_iv = Iv(p, p)
            p12 = p_iv.sqrt()
            p14 = p12.sqrt()
            num = Iv(2, 2) * p14 + p12
            den = p_iv * Iv(p - 2, p - 2)
            prod_h = prod_h * (Iv(1, 1) + num / den)
        prod_ht = prod_ht * (Iv(1, 1) + Iv.from_frac(Fraction(1, p * (p - 1))))

    hc_iv = Iv(h_cut, h_cut)
    c_tail = (Iv(1, 1) + Iv(2, 2) / hc_iv.sqrt().sqrt()) / (Iv(1, 1) - Iv(2, 2) / hc_iv)
    tail_h = c_tail / (Iv(h_cut - 1, h_cut - 1)).sqrt()
    h_sigma = prod_h * exp_iv(tail_h)

    crit_val = Iv(2, 2) / exp_iv(Iv(1, 1) + Iv.from_str("0.5") * ALPHA0)
    assert crit_val.hi < ALPHA0.lo
    c_j = (ALPHA0 + C_F0) * h_sigma
    h_tilde = prod_ht * exp_iv(Iv(1, 1) / Iv(2 * (P_CUT - 1), 2 * (P_CUT - 1)))
    return h_sigma, c_j, h_tilde


PI = _compute_pi_iv()
LN2 = ln_iv(Iv(2, 2))
E2 = exp_iv(Iv(2, 2))
GAMMA = _compute_gamma_iv()
E_GAMMA = exp_iv(GAMMA)
E_NEG_GAMMA = exp_iv(-GAMMA)

C2_TWIN, M0_CONST = _compute_c2_and_m0()
U_CONST = Iv(2, 2) * C2_TWIN
H0_CONST = Iv(2, 2) / U_CONST
LI2 = _li_exp_iv(LN2)

ALPHA0 = (GAMMA + LN2) / Iv(2, 2)
C_F0 = Iv.from_str("0.78")
H_SIGMA, C_J_CONST, H_TILDE = _compute_selberg_constants()
