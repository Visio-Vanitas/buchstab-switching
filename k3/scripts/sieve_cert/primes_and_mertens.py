"""
Prime prefix sums, Grenie-Molteni AP error c_pi(X), Rosser-Schoenfeld /
Johnston-Starichkova Mertens bounds, and strictly two-variable eps_sup(p_*).
"""

from __future__ import annotations

import bisect
from decimal import Decimal
from fractions import Fraction

from .constants import (
    C2_TWIN,
    LI2,
    M0_CONST,
    ODD_PRIMES,
    P_CUT,
    P_PREFIX_MAX,
    PI,
    PRIMES,
    PRIMES_PRE,
)
from .interval import D_ZERO, Iv, clamp_pos_iv, exp_iv, ln_iv, sub_ceil

LN_1E12 = ln_iv(Iv(10 ** 12, 10 ** 12))
TWIN_RECIP = Iv(1, 1) / C2_TWIN

# Precompute prefix products/sums on PRIMES_PRE (up to 250_000) for O(1) exact lookups
def _build_prefix_tables():
    # Precompute prefix V_full(x) = prod_{3 <= p < x} (1 - 1/(p-1)) over PRIMES_PRE
    pref_inv_p = [Iv(0, 0)] * (len(PRIMES_PRE) + 1)
    pref_v_full = [Iv(1, 1)] * (len(PRIMES_PRE) + 1)
    s = Iv(0, 0)
    v_cur = Iv(1, 1)
    for i, p in enumerate(PRIMES_PRE):
        s = s + Iv.from_frac(Fraction(1, p))
        pref_inv_p[i + 1] = s
        if p >= 3:
            v_cur = v_cur * Iv.from_frac(Fraction(p - 2, p - 1))
        pref_v_full[i + 1] = v_cur

    # Cumulative 1/p^2, 1/(p(p-1)), 1/(p-1)^2, twin-prime prefix, and theta_odd for p* <= 1000
    pref_twin = {}
    pref_s2_all = {}
    pref_theta_odd = {}
    pref_pp1 = {}
    pref_pm1_sq = {}
    cur_tp = Iv(1, 1)
    cur_s2 = Iv.from_frac(Fraction(1, 4))  # 1/2^2
    cur_th = Iv(0, 0)
    cur_pp1 = Iv(0, 0)
    cur_pm1_sq = Iv(0, 0)
    for idx_o, p in enumerate(ODD_PRIMES):
        if p <= 1000:
            pref_twin[p] = cur_tp
            pref_s2_all[p] = cur_s2
            pref_theta_odd[p] = cur_th
            cur_th = cur_th + ln_iv(Iv(p, p))
        if idx_o <= 100:
            pref_pp1[idx_o] = cur_pp1
            pref_pm1_sq[idx_o] = cur_pm1_sq
        cur_tp = cur_tp * Iv.from_frac(Fraction((p - 1) ** 2, p * (p - 2)))
        cur_s2 = cur_s2 + Iv.from_frac(Fraction(1, p * p))
        cur_pp1 = cur_pp1 + Iv.from_frac(Fraction(1, p * (p - 1)))
        cur_pm1_sq = cur_pm1_sq + Iv.from_frac(Fraction(1, (p - 1) ** 2))
    inv_p2_all = cur_s2 + Iv.from_frac(Fraction(1, P_CUT))
    inv_pp1_all = cur_pp1 + Iv.from_frac(Fraction(1, P_CUT))
    inv_pm1_sq_all = cur_pm1_sq + Iv.from_frac(Fraction(1, P_CUT - 1))
    return (
        pref_inv_p,
        pref_v_full,
        pref_twin,
        pref_s2_all,
        pref_theta_odd,
        inv_p2_all,
        pref_pp1,
        pref_pm1_sq,
        inv_pp1_all,
        inv_pm1_sq_all,
    )


(
    INV_P_PREFIX,
    V_FULL_PREFIX,
    PREFIX_TWIN,
    PREFIX_S2_ALL,
    PREFIX_THETA_ODD,
    INV_P2_ALL,
    PREFIX_PP1,
    PREFIX_PM1_SQ,
    INV_PP1_ALL,
    INV_PM1_SQ_ALL,
) = _build_prefix_tables()


def v_full_exact_lt(w: int) -> Iv:
    """Exact precomputed `V_full(w) = prod_{3 <= p < w} (1 - 1/(p-1))` for `w <= P_PREFIX_MAX`."""
    assert w <= P_PREFIX_MAX
    idx = bisect.bisect_left(PRIMES_PRE, w)
    return V_FULL_PREFIX[idx]


# Precompute exact Mertens prime excursions up to 25_000 for two-variable eps_sup
def _build_mertens_excursions():
    recs: list[tuple[int, Decimal, Decimal]] = []
    e101 = exp_iv(Iv.from_str("10.1"))
    tail_up_101 = (Iv(2, 2) / (e101.sqrt() * Iv.from_str("10.1"))).hi
    for idx, p in enumerate(PRIMES_PRE):
        if p > 25_000:
            break
        if p >= 29:
            llp = ln_iv(ln_iv(Iv(p, p)))
            before = INV_P_PREFIX[idx]
            after = INV_P_PREFIX[idx + 1]
            recs.append((p, (after - llp - M0_CONST).hi, (before - llp - M0_CONST).lo))
    return recs, tail_up_101


_MERTENS_RECS, _MERTENS_TAIL_UP_101 = _build_mertens_excursions()


def c_pi_iv(log_x: Iv) -> Iv:
    """Grenie-Molteni (2019) / Johnston-Starichkova Lemma 5.1 explicit AP constant `c_pi(X)`."""
    sqrt_x = exp_iv(Iv.from_str("0.5") * log_x)
    t1 = Iv(3, 3) / (Iv(8, 8) * PI)
    t2 = (Iv(6, 6) + Iv(1, 1) / PI) / (Iv(4, 4) * log_x)
    t3 = Iv(6, 6) / (log_x ** 2)
    t4 = LI2 / (sqrt_x * log_x)
    return t1 + t2 + t3 + t4


def sum_inv_p_ub(z: Iv, log_z: Iv) -> Iv:
    """Upper bound on `sum_{p < z} 1/p` (exact up to `P_PREFIX_MAX`, Lemma 3.2 above)."""
    if z.hi <= Decimal(P_PREFIX_MAX):
        hi_int = int(z.hi)
        if Decimal(hi_int) < z.hi:
            idx = bisect.bisect_right(PRIMES_PRE, hi_int)
        else:
            idx = bisect.bisect_left(PRIMES_PRE, hi_int)
        return INV_P_PREFIX[idx]
    llz = ln_iv(log_z)
    if z.lo > Decimal("1e12"):
        err = Iv.from_str("6.836e-6") / log_z
    elif log_z.lo > Decimal(10):
        err = Iv(2, 2) / (z.sqrt() * log_z)
    elif log_z.lo > Decimal("8.9"):
        err = Iv.from_str("1.614e-3")
    else:
        raise ValueError(f"z too small for analytic Mertens ub: {z}")
    return llz + M0_CONST + err


def sum_inv_p_lb(z: Iv, log_z: Iv) -> Iv:
    """Lower bound on `sum_{p < z} 1/p` (exact on `[2, P_PREFIX_MAX]`, Lemma 3.2 above)."""
    if z.lo <= Decimal(P_PREFIX_MAX):
        idx = bisect.bisect_left(PRIMES_PRE, int(z.lo))
        return INV_P_PREFIX[idx]
    llz = ln_iv(log_z)
    err = Iv.from_str("2.964e-6") / log_z
    return llz + M0_CONST - err


def pi_ub_iv(z: Iv, log_z: Iv) -> Iv:
    """Upper bound on `pi(z)`."""
    if z.hi <= Decimal(P_CUT):
        cnt = bisect.bisect_right(PRIMES, int(z.hi))
        return Iv(cnt, cnt)
    if log_z.lo >= Decimal(5):
        return z / (log_z - Iv(2, 2)) + z.sqrt() * log_z / (Iv(8, 8) * PI)
    return Iv.from_str("1.25506") * z / log_z


def epd_norm_iv(x_lo_iv: Iv, log_x_lo: Iv) -> Iv:
    """Upper bound on `|r(d)| / (N / log N)` for `3 <= d <= sqrt(N)` and `N >= x_lo`."""
    assert log_x_lo.lo > Decimal("4.5")
    sqrt_x = x_lo_iv.sqrt()
    cp = c_pi_iv(log_x_lo)
    omega_ub = Iv.from_str("1.3841") * log_x_lo / ln_iv(log_x_lo)
    return (cp + Iv(1, 1) / (Iv(16, 16) * PI)) * (log_x_lo ** 2) / sqrt_x + (omega_ub * log_x_lo) / x_lo_iv


def li_ratio_ub(x_lo_iv: Iv, log_x_lo: Iv) -> Iv:
    """Upper bound on `li(N) / |A_N|` valid uniformly for all `N >= x_lo >= 4 * 10^18`."""
    sqrt_x = x_lo_iv.sqrt()
    omega_ub = Iv.from_str("1.3841") * log_x_lo / ln_iv(log_x_lo)
    rel_loss = (sqrt_x * (log_x_lo ** 2) / (Iv(8, 8) * PI) + omega_ub * log_x_lo) / x_lo_iv
    assert rel_loss.hi < Decimal("0.5")
    return Iv(1, 1) / (Iv(1, 1) - rel_loss)


def eps_sup_two_var(pstar: int) -> Iv:
    """
    Strictly order-respecting two-variable uniform upper bound on:
      `sup_{pstar <= w < z1 < inf} (prod_{w <= p < z1} (1 - 1/(p-1))^-1 / (ln z1 / ln w) - 1)`.
    Tracks running minimum of `(sum_{p < w} 1/p - ln ln w - M_0)` before evaluating
    `sum_{p <= z1} 1/p - ln ln z1 - M_0` across `[pstar, 25_000]`, joined with
    Johnston-Starichkova Lemma 3.2 for `x > 25_000 > e^{10.1}` and `w >= pstar`.
    """
    assert pstar >= 29 and pstar in PREFIX_TWIN
    sub = [r for r in _MERTENS_RECS if r[0] >= pstar]
    min_lo_so_far = sub[0][2]
    max_diff = D_ZERO
    for _, after_hi, before_lo in sub:
        if before_lo < min_lo_so_far:
            min_lo_so_far = before_lo
        diff = sub_ceil(after_hi, min_lo_so_far)
        if diff > max_diff:
            max_diff = diff
    min_lo_all = min(
        min_lo_so_far,
        (-(Iv.from_str("2.964e-6") / ln_iv(Iv(pstar, pstar)))).hi,
    )
    tail_diff = sub_ceil(_MERTENS_TAIL_UP_101, min_lo_all)
    if tail_diff > max_diff:
        max_diff = tail_diff

    tp_tail = TWIN_RECIP / PREFIX_TWIN[pstar]
    s2_tail = INV_P2_ALL - PREFIX_S2_ALL[pstar]
    x = Iv.from_frac(Fraction(1, pstar))
    c_p = (-ln_iv(Iv(1, 1) - x) - x) / (x * x)
    return tp_tail * exp_iv(Iv(max_diff, max_diff) + c_p * s2_tail) - Iv(1, 1)


def eps_large_u_two_var(ln_u: Iv) -> Iv:
    """Uniform two-variable bound for `p1 >= u` when `u > e^{10.1}`."""
    if ln_u.lo <= Decimal("10.1"):
        return Iv.from_str("0.5")
    u_exp = exp_iv(ln_u)
    tail_err = Iv.from_str("2.0002") / u_exp
    if ln_u.lo > LN_1E12.hi:
        mert = (Iv.from_str("6.836e-6") + Iv.from_str("2.964e-6")) / ln_u
    else:
        up = Iv(2, 2) / (exp_iv(ln_u * Iv.from_frac(Fraction(1, 2))) * ln_u)
        cap_1e12 = Iv.from_str("6.836e-6") / LN_1E12
        mert = Iv(max(up.lo, cap_1e12.lo), max(up.hi, cap_1e12.hi)) + Iv.from_str("2.964e-6") / ln_u
    return exp_iv(tail_err + mert) - Iv(1, 1)
