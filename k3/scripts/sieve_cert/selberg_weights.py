"""
Pre-sieve-free Selberg `Lambda^2` weights, exact `J_odd(m)` table,
2-prime inclusion-exclusion `J_full(z, xi)` lower bound, and monotone asymptotic `V * J` helper.
"""

from __future__ import annotations

from decimal import Decimal
from fractions import Fraction

from .constants import ALPHA0, C_F0, C_J_CONST, E_NEG_GAMMA, H0_CONST
from .interval import D_ZERO, Iv, clamp_pos_iv, exp_iv, ln_iv, max_iv, pow_real_iv
from .primes_and_mertens import sum_inv_p_lb, sum_inv_p_ub

N_J_PRE = 5000


def _build_j_odd_exact() -> list[Iv]:
    """Precompute exact `J_odd(m) = sum_{d<=m, 2∤d} mu^2(d)/prod_{p|d}(p-2)` for `0 <= m <= 5000`."""
    vals = [Iv(0, 0)] * (N_J_PRE + 1)
    cur = Iv(0, 0)
    for d in range(1, N_J_PRE + 1):
        if d & 1:
            tmp = d
            ok = True
            den = 1
            p = 3
            while p * p <= tmp:
                if tmp % p == 0:
                    tmp //= p
                    if tmp % p == 0:
                        ok = False
                        break
                    den *= p - 2
                p += 2
            if ok:
                if tmp > 1:
                    den *= tmp - 2
                cur = cur + Iv.from_frac(Fraction(1, den))
        vals[d] = cur
    return vals


J_ODD_EXACT = _build_j_odd_exact()


def j_odd_lb(xi: Iv) -> Iv:
    """Outward-rounded lower bound on `J_odd(xi)` valid for all real `xi >= 1`."""
    if xi.lo < 1:
        return Iv(0, 0)
    if xi.lo < N_J_PRE:
        return J_ODD_EXACT[int(xi.lo)]
    asym = H0_CONST * (Iv.from_str("0.5") * ln_iv(xi) + ALPHA0)
    err = C_J_CONST / (xi.sqrt().sqrt())
    return max_iv(J_ODD_EXACT[N_J_PRE], asym - err)


def j_odd_ub(xi: Iv) -> Iv:
    """Outward-rounded upper bound on `J_odd(xi)` valid for all real `xi >= 1`."""
    if xi.hi < 1:
        return Iv(0, 0)
    if xi.hi < N_J_PRE:
        return J_ODD_EXACT[int(xi.hi)]
    asym = H0_CONST * (Iv.from_str("0.5") * ln_iv(xi) + ALPHA0)
    err = C_J_CONST / (xi.sqrt().sqrt())
    return asym + err


def j_full_lb_z3(z_iv: Iv, xi_iv: Iv, k1: int = 24, k2: int = 8) -> Iv:
    """
    Rigorous lower bound on `J_full(z, xi)` for `1 <= xi < z^3` via exact 0-, 1-, and 2-prime
    inclusion-exclusion over primes `>= z`, returning `j_odd_lb(xi)` when `xi < z`.
    """
    if xi_iv.lo < 1:
        return Iv(0, 0)
    if xi_iv.hi < z_iv.lo:
        return j_odd_lb(xi_iv)
    assert xi_iv.hi < (z_iv ** 3).lo

    res = j_odd_lb(xi_iv)
    ratio1 = pow_real_iv(xi_iv / z_iv, Iv.from_frac(Fraction(1, k1)))
    cur = z_iv
    for k in range(k1):
        nxt = xi_iv if k == k1 - 1 else cur * ratio1
        w0 = Iv(cur.lo, cur.lo)
        w1 = Iv(nxt.hi, nxt.hi)
        if w1.hi < w0.lo:
            w1 = w0
        w1p = w1 + Iv(1, 1)
        mert_diff = clamp_pos_iv(sum_inv_p_ub(w1p, ln_iv(w1p)) - sum_inv_p_lb(w0, ln_iv(w0)))
        tail_pm2 = Iv(2, 2) / (w0 - Iv(2, 2))
        res = res - j_odd_ub(xi_iv / w0) * (mert_diff + tail_pm2)
        cur = nxt

    z2 = z_iv * z_iv
    if xi_iv.lo > z2.hi:
        sq = xi_iv.sqrt()
        r2 = pow_real_iv(sq / z_iv, Iv.from_frac(Fraction(1, k2)))
        c1 = z_iv
        for i in range(k2):
            n1 = sq if i == k2 - 1 else c1 * r2
            a0 = Iv(c1.lo, c1.lo)
            a1 = Iv(n1.hi, n1.hi)
            hi_p2 = Iv((xi_iv / a1).lo, (xi_iv / a1).lo)
            if hi_p2.lo > a1.hi:
                s1 = clamp_pos_iv(sum_inv_p_lb(a1, ln_iv(a1)) - sum_inv_p_ub(a0, ln_iv(a0)))
                if s1.lo > 0:
                    r3 = pow_real_iv(hi_p2 / a1, Iv.from_frac(Fraction(1, k2)))
                    c2 = a1
                    for j in range(k2):
                        n2 = hi_p2 if j == k2 - 1 else c2 * r3
                        b0 = Iv(c2.lo, c2.lo)
                        b1 = Iv(n2.hi, n2.hi)
                        if b1.hi > b0.lo:
                            s2 = clamp_pos_iv(sum_inv_p_lb(b1, ln_iv(b1)) - sum_inv_p_ub(b0, ln_iv(b0)))
                            if s2.lo > 0:
                                res = res + s1 * s2 * j_odd_lb(xi_iv / (a1 * b1))
                        c2 = n2
            c1 = n1
    return res


def vj_monotone_lb_iv(
    log_x: Iv, m_iv: Iv, r_exp: Iv, delta_v: Iv, log_z_override: Iv | None = None
) -> Iv:
    """
    Monotone non-decreasing lower bound on `V_N(z) * J_full(z, z^r_exp)` valid for all
    `N >= X_LS` when `z = floor(N^(1/M))`, `0 < r_exp < 3`, and `z^r_exp >= 5000`.
    """
    log_z = (log_x / m_iv) if log_z_override is None else log_z_override
    xi_iv = exp_iv(r_exp * log_z)
    assert xi_iv.lo >= N_J_PRE

    v_times_logz_lb = (Iv(2, 2) / H0_CONST) * (Iv(2, 2) * E_NEG_GAMMA / (Iv(2, 2) / H0_CONST)) * (Iv(1, 1) - delta_v)
    # Simplify: V_N(z) * log z >= U_min * e^-gamma * (1 - delta_V), wait: H0 = 2/U_min => U_min * e^-gamma * H0 = 2 * e^-gamma!
    v_coeff = (Iv(2, 2) / H0_CONST) * E_NEG_GAMMA * (Iv(1, 1) - delta_v)
    xi_m14 = Iv(1, 1) / (xi_iv.sqrt().sqrt())
    j_over_logz = r_exp / (Iv(2, 2) / H0_CONST) - (C_J_CONST * xi_m14) / log_z

    if r_exp.hi <= 1:
        return v_coeff * j_over_logz

    k1 = 32
    dt = (r_exp - Iv(1, 1)) / Iv(k1, k1)
    for k in range(k1):
        t0 = Iv(1, 1) + Iv(k, k) * dt
        t1 = Iv(1, 1) + Iv(k + 1, k + 1) * dt
        w0 = exp_iv(t0 * log_z)
        w1 = exp_iv(t1 * log_z)
        err_hi = Iv.from_str("6.836e-6") if w0.lo > Decimal("1e12") else Iv(2, 2) / w0.sqrt()
        mert_ub = (
            ln_iv(t1 / t0)
            + err_hi / (t1 * log_z)
            + Iv.from_str("2.964e-6") / (t0 * log_z)
            + Iv(2, 2) / (w0 - Iv(2, 2))
            + Iv(1, 1) / w1
        )
        rem_t = r_exp - t0
        xi_rem = exp_iv(rem_t * log_z)
        err_top = (C_J_CONST / (xi_rem.sqrt().sqrt())) if xi_rem.lo >= N_J_PRE else C_J_CONST
        j_rem_ub = rem_t / (Iv(2, 2) / H0_CONST) + (H0_CONST * ALPHA0 + err_top) / log_z
        j_over_logz = j_over_logz - mert_ub * j_rem_ub

    if r_exp.lo > 2:
        k2 = 10
        dt2 = (Iv.from_str("0.5") * r_exp - Iv(1, 1)) / Iv(k2, k2)
        for i in range(k2):
            a0 = Iv(1, 1) + Iv(i, i) * dt2
            a1 = Iv(1, 1) + Iv(i + 1, i + 1) * dt2
            wa0 = exp_iv(a0 * log_z)
            e1 = Iv.from_str("2.964e-6") / (a1 * log_z) + (
                (Iv.from_str("6.836e-6") if wa0.lo > Decimal("1e12") else Iv(2, 2) / wa0.sqrt()) / (a0 * log_z)
            )
            s1 = clamp_pos_iv(ln_iv(a1 / a0) - e1)
            if s1.lo <= 0:
                continue
            hi_t2 = r_exp - a1
            if hi_t2.lo <= a1.hi:
                continue
            dt3 = (hi_t2 - a1) / Iv(k2, k2)
            for j in range(k2):
                b0 = a1 + Iv(j, j) * dt3
                b1 = a1 + Iv(j + 1, j + 1) * dt3
                wb0 = exp_iv(b0 * log_z)
                e2 = Iv.from_str("2.964e-6") / (b1 * log_z) + (
                    (Iv.from_str("6.836e-6") if wb0.lo > Decimal("1e12") else Iv(2, 2) / wb0.sqrt()) / (b0 * log_z)
                )
                s2 = clamp_pos_iv(ln_iv(b1 / b0) - e2)
                rem_t2 = r_exp - a1 - b1
                if s2.lo <= 0 or rem_t2.lo <= 0:
                    continue
                xi_rem2 = exp_iv(rem_t2 * log_z)
                if xi_rem2.lo >= N_J_PRE:
                    j_rem_lb = clamp_pos_iv(rem_t2 / (Iv(2, 2) / H0_CONST) - (C_J_CONST / (xi_rem2.sqrt().sqrt())) / log_z)
                    j_over_logz = j_over_logz + s1 * s2 * j_rem_lb

    return v_coeff * j_over_logz
