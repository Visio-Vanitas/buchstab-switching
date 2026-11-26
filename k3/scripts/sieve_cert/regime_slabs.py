"""
Finite-slab certifiers (`2a`, `2b`, `2c`) over `[4 * 10^18, 10^600)` returning
machine-checkable `SlabCertificate` records with robustness diagnostics.
"""

from __future__ import annotations

import bisect
from dataclasses import dataclass
from decimal import Decimal, Inexact, ROUND_CEILING, ROUND_FLOOR, Rounded, localcontext
from fractions import Fraction

from .bonferroni_engine import (
    build_p_sub_table,
    comb_int,
    elem_sym_iv,
    eval_odd_bonferroni_s_a,
)
from .brun_block_sieve import eval_best_brun_lower
from .constants import (
    C_F0,
    E_NEG_GAMMA,
    ODD_PRIMES,
    PI,
    PRIMES,
    PRIMES_PRE,
    U_CONST,
)
from .interval import (
    D_ONE,
    D_ZERO,
    Iv,
    ceil_root_int,
    clamp_pos_iv,
    exp_iv,
    floor_root_int,
    ln_iv,
    min_iv,
    pow_real_iv,
)
from .primes_and_mertens import (
    INV_PM1_SQ_ALL,
    INV_PP1_ALL,
    M0_CONST,
    PREFIX_PM1_SQ,
    PREFIX_PP1,
    epd_norm_iv,
    pi_ub_iv,
    v_full_exact_lt,
)
from .schedule import Slab2ASpec, Slab2BSpec, Slab2CSpec
from .selberg_weights import j_odd_lb, j_odd_ub
from .slab_witness_export import build_slab_2ab_witness, build_slab_2c_witness

P_EXACT = 27_000
H_TILDE_PROVED = Iv.from_str("1.3")
ALPHA0_PROVED = Iv.from_str("0.636")
PRIMES_EXACT = PRIMES_PRE[: bisect.bisect_left(PRIMES_PRE, P_EXACT)]


def _build_exact_prefix_tables() -> tuple[list[Iv], list[Iv], list[Iv]]:
    pinv = [Iv(0, 0)]
    pw = [Iv(0, 0)]
    pv = [Iv(1, 1)]
    for p in PRIMES_EXACT:
        pinv.append(pinv[-1] + Iv.from_frac(Fraction(1, p)))
        if p >= 3:
            pw.append(pw[-1] + Iv.from_frac(Fraction(1, p - 1)))
            pv.append(pv[-1] * Iv.from_frac(Fraction(p - 2, p - 1)))
        else:
            pw.append(pw[-1])
            pv.append(pv[-1])
    return pinv, pw, pv


_PINV_EXACT, _PW_EXACT, _PV_EXACT = _build_exact_prefix_tables()


@dataclass(frozen=True)
class SlabCertificate:
    regime: str
    x_lo: int
    x_hi: int
    z: int
    y: int
    main_lo: Decimal
    err_hi: Decimal
    net_lo: Decimal
    sieve_net_lo: Decimal
    rem_tol: Decimal
    note: str = ""


def _mertens_sum_inv_p_ub(z_iv: Iv, log_z: Iv) -> Iv:
    """Upper bound on `sum_{p < z} 1/p` exact below `P_EXACT` and `MertensPrimeSumPremise` above."""
    if z_iv.hi <= Decimal(P_EXACT):
        hi_int = int(z_iv.hi)
        if Decimal(hi_int) < z_iv.hi:
            idx = bisect.bisect_right(PRIMES_EXACT, hi_int)
        else:
            idx = bisect.bisect_left(PRIMES_EXACT, hi_int)
        return _PINV_EXACT[idx]
    llz = ln_iv(log_z)
    if z_iv.lo > Decimal("1e12"):
        err = Iv.from_str("6.836e-6") / log_z
    elif log_z.lo > Decimal(10):
        err = Iv(2, 2) / (z_iv.sqrt() * log_z)
    elif log_z.lo > Decimal("8.9"):
        err = Iv.from_str("1.614e-3")
    else:
        err = Iv(1, 1)
    return llz + M0_CONST + err


def _mertens_sum_inv_p_lb(z_iv: Iv, log_z: Iv) -> Iv:
    """Lower bound on `sum_{p < z} 1/p` exact below `P_EXACT` and `MertensPrimeSumPremise` above."""
    if z_iv.lo <= Decimal(P_EXACT):
        idx = bisect.bisect_left(PRIMES_EXACT, int(z_iv.lo))
        return _PINV_EXACT[idx]
    llz = ln_iv(log_z)
    err = Iv.from_str("2.964e-6") / log_z
    return llz + M0_CONST - err


def _slice_sq_analytic(q0: int, q1: int) -> Iv:
    """`sum_{q0 <= q < q1} 1/(q-1)` via `MertensPrimeSumPremise` + telescoping `1/(q0-1) - 1/(q1-1)`."""
    q0_iv, q1_iv = Iv(q0, q0), Iv(q1, q1)
    l0, l1 = ln_iv(q0_iv), ln_iv(q1_iv)
    return clamp_pos_iv(_mertens_sum_inv_p_ub(q1_iv, l1) - _mertens_sum_inv_p_lb(q0_iv, l0)) + (
        Iv(1, 1) / Iv(q0 - 1, q0 - 1) - Iv(1, 1) / Iv(q1 - 1, q1 - 1)
    )


def _schoenfeld_cnt_ub(q0: int, q1: int, sub: int = 32) -> Iv:
    """Schoenfeld RH MVT sub-partition upper bound on `pi(q1) - pi(q0) + 1` for `q0 >= P_EXACT`."""
    assert q0 >= P_EXACT and q0 < q1
    q0_iv, q1_iv = Iv(q0, q0), Iv(q1, q1)
    r_sub = pow_real_iv(q1_iv / q0_iv, Iv.from_frac(Fraction(1, sub)))
    pts = [q0_iv]
    cur = q0_iv
    for _ in range(1, sub):
        cur = cur * r_sub
        p_dec = cur.hi
        if p_dec > q1_iv.lo:
            p_dec = q1_iv.lo
        if p_dec < pts[-1].hi:
            p_dec = pts[-1].hi
        pts.append(Iv(p_dec, p_dec))
    pts.append(q1_iv)
    li_diff = Iv(0, 0)
    for i in range(sub):
        if pts[i + 1].hi > pts[i].lo:
            li_diff = li_diff + (pts[i + 1] - pts[i]) / ln_iv(pts[i])
    l0, l1 = ln_iv(q0_iv), ln_iv(q1_iv)
    schoen_err = (q1_iv.sqrt() * l1 + q0_iv.sqrt() * l0) / (Iv(8, 8) * PI)
    return li_diff + schoen_err + Iv(1, 1)


def _build_slices(z: int, y: int, k_sl: int) -> list[int]:
    z_iv, y_iv = Iv(z, z), Iv(y, y)
    r_sl = pow_real_iv(y_iv / z_iv, Iv.from_frac(Fraction(1, k_sl)))
    bpts = [z]
    cur = z_iv
    for _ in range(k_sl - 1):
        cur = cur * r_sl
        v = int(cur.hi)
        if bpts[-1] < v < y:
            bpts.append(v)
    if z < P_EXACT < y and P_EXACT not in bpts:
        bpts.append(P_EXACT)
        bpts.sort()
    bpts.append(y)
    return bpts


def _odd_bonf_small_z(p_full: list[int], a: int, m_odd: int, sqrt_x_lo: int) -> tuple[Iv, Iv, int]:
    """Exact small-`z` `Q_1(a) x odd Bonferroni(m_odd)` evaluation."""
    assert m_odd % 2 == 1
    q1_ps, p2_ps = p_full[:a], p_full[a:]
    q1_prod = 1
    for p in q1_ps:
        q1_prod *= p
    prod_max = q1_prod
    if p2_ps:
        for p in p2_ps[-m_odd:]:
            prod_max *= p
    assert prod_max <= sqrt_x_lo, f"Q1*P2_max={prod_max} > sqrt(X_lo)={sqrt_x_lo}"

    v_q1 = Iv(1, 1)
    for p in q1_ps:
        v_q1 = v_q1 * Iv.from_frac(Fraction(p - 2, p - 1))
    w2 = [Iv.from_frac(Fraction(1, p - 1)) for p in p2_ps]
    g_full = Iv(1, 1)
    for w in w2:
        g_full = g_full * (Iv(1, 1) - w)
    v_full = v_q1 * g_full
    if p2_ps:
        e2 = elem_sym_iv(w2, m_odd)
        b_odd = sum((e2[j] if j % 2 == 0 else -e2[j] for j in range(m_odd + 1)), Iv(0, 0))
        ratio_odd = b_odd / g_full
    else:
        ratio_odd = Iv(1, 1)
    n_d_odd = (1 << a) * sum(comb_int(len(p2_ps), j) for j in range(m_odd + 1))
    return v_full, ratio_odd, n_d_odd


def _build_exact_even_bonf_opts(
    cutoffs: list[int], sqrt_x_lo: int, scale_ref_lb: Iv | None = None
) -> list[tuple[int, Iv, int, Iv, Iv]]:
    """
    Build exact combinatorial even-Bonferroni upper-bound entries across prime cutoffs
    `z_sub <= 1500`. If `scale_ref_lb` is given (e.g., `v_full_lb` in Regime 2c), normalize
    `V_full(z_sub)` by `scale_ref_lb`.
    """
    ev_opts: list[tuple[int, Iv, int, Iv, Iv]] = []
    for zs in cutoffs:
        p_sub_list = [p for p in ODD_PRIMES if p < zs]
        v_sub = v_full_exact_lt(zs)
        v_scaled = v_sub if scale_ref_lb is None else (v_sub / scale_ref_lb)
        for aq in range(0, min(len(p_sub_list), 11), 2):
            qq_ps, p2q = p_sub_list[:aq], p_sub_list[aq:]
            qq, inv_qq = 1, Iv(1, 1)
            for p in qq_ps:
                qq *= p
                inv_qq = inv_qq * Iv.from_frac(Fraction(p, p - 1))
            if qq > sqrt_x_lo:
                break
            w2q = [Iv.from_frac(Fraction(1, p - 1)) for p in p2q]
            g2q = Iv(1, 1)
            for w in w2q:
                g2q = g2q * (Iv(1, 1) - w)
            ee = elem_sym_iv(w2q, min(8, len(p2q)))
            for mev in (2, 4, 6, 8):
                if mev > len(p2q):
                    continue
                prod_ev = qq
                for p in p2q[-mev:]:
                    prod_ev *= p
                rat = sum((ee[j] if j % 2 == 0 else -ee[j] for j in range(mev + 1)), Iv(0, 0)) / g2q
                nd = (1 << aq) * sum(comb_int(len(p2q), j) for j in range(mev + 1))
                ip2 = sum((ee[j] for j in range(mev + 1)), Iv(0, 0))
                ev_opts.append((prod_ev, v_scaled * rat, nd, inv_qq * ip2, rat))
    return ev_opts


def _build_analytic_even_bonf_opts(
    z: int, sqrt_x_lo: int, mult_by_v: Iv | None = None
) -> list[tuple[int, Iv, int, Iv, Iv]]:
    """Build analytic `S_1`-tail even-Bonferroni upper-bound entries at full cutoff `z > 1500`."""
    z_iv, log_z = Iv(z, z), ln_iv(Iv(z, z))
    pz_ub = pi_ub_iv(z_iv, log_z)
    ev_opts: list[tuple[int, Iv, int, Iv, Iv]] = []
    for aq in (0, 2, 4, 6, 8, 10):
        qq_ps = ODD_PRIMES[:aq]
        pa = qq_ps[-1] if aq > 0 else 2
        qq, inv_qq = 1, Iv(1, 1)
        for p in qq_ps:
            qq *= p
            inv_qq = inv_qq * Iv.from_frac(Fraction(p, p - 1))
        if qq > sqrt_x_lo:
            break
        ex_p = sum((Iv.from_frac(Fraction(1, p)) for p in PRIMES if p <= pa), Iv(0, 0))
        s1 = clamp_pos_iv(_mertens_sum_inv_p_ub(z_iv, log_z) - ex_p) + (INV_PP1_ALL - PREFIX_PP1[aq])
        p_min = ODD_PRIMES[aq]
        c_log2 = Iv.from_frac(Fraction(p_min - 1, 2 * (p_min - 2)))
        g_lb = exp_iv(-(s1 + c_log2 * (INV_PM1_SQ_ALL - PREFIX_PM1_SQ[aq])))
        inv_phi2 = exp_iv(s1)
        for mev in (2, 4, 6, 8):
            pe = qq * (z ** mev)
            if pe > sqrt_x_lo:
                break
            fact = 1
            for j in range(1, mev + 2):
                fact *= j
            rat = Iv(1, 1) + ((s1 ** (mev + 1)) / Iv(fact, fact)) / g_lb
            spz, fj = Iv(0, 0), 1
            for j in range(mev + 1):
                if j > 0:
                    fj *= j
                spz = spz + (pz_ub ** j) / Iv(fj, fj)
            nd = int(((Iv(1 << aq, 1 << aq) * spz).hi)) + 1
            m_rat = rat if mult_by_v is None else (mult_by_v * rat)
            ev_opts.append((pe, m_rat, nd, inv_qq * inv_phi2, rat))
    return ev_opts


def _q2_square_error_2ab(
    log_x_hi: Iv, z: int, y: int, q_sq: int, epd: Iv
) -> Iv:
    """Lean-aligned `SquareEngine2ab.errQ2` with exact `< P_EXACT` prime-square prefix."""
    end_lo = min(y, q_sq + 1)
    exact_hi = min(end_lo, P_EXACT)
    i_s = bisect.bisect_left(PRIMES_EXACT, z)
    i_e = bisect.bisect_left(PRIMES_EXACT, exact_hi)
    s_q2 = sum((Iv.from_frac(Fraction(1, q * (q - 1))) for q in PRIMES_EXACT[i_s:i_e]), Iv(0, 0))
    cnt_lo = Iv(max(0, i_e - i_s), max(0, i_e - i_s))
    tail_lo = max(z, P_EXACT)
    if end_lo > tail_lo:
        s_q2 = s_q2 + (Iv(1, 1) / Iv(tail_lo - 1, tail_lo - 1) - Iv(1, 1) / Iv(end_lo - 1, end_lo - 1))
        cnt_lo = cnt_lo + _schoenfeld_cnt_ub(tail_lo, end_lo, sub=32)
    tail_hi = Iv(0, 0) if y <= q_sq + 1 else log_x_hi / Iv(q_sq, q_sq)
    return Iv.from_str("0.5") * (s_q2 + cnt_lo * epd + tail_hi)


def _deltaV_bjs_4(z_iv: Iv) -> Iv:
    """`External.deltaV_bjs 4 z` matching `ProductAsymptotic.lean` & `CouplingAndJOdd.lean`."""
    log_4 = ln_iv(Iv(4, 4))
    log_z = ln_iv(z_iv)
    f1 = (
        Iv.from_str("1.45")
        * (log_4 / (z_iv - Iv(1, 1)))
        * (Iv(1, 1) + Iv(10, 10) * ln_iv(log_4) / log_4)
    )
    f2 = Iv.from_str("1.002") / (z_iv - Iv(3, 3))
    f3 = Iv(1, 1) / (Iv(2, 2) * (log_z ** 2))
    d_lo = Iv(1, 1) - (Iv(1, 1) - f1) * (Iv(1, 1) - f2) * (Iv(1, 1) - f3)
    d_hi = (Iv(1, 1) + f1) * (Iv(1, 1) + f2) * (Iv(1, 1) + f3) - Iv(1, 1)
    return Iv(D_ZERO, max(d_lo.hi, d_hi.hi))


def _s_hi_27k(u: int, v: int) -> Iv:
    if v <= u:
        return Iv(0, 0)
    hi = min(v, P_EXACT)
    s = (_PW_EXACT[bisect.bisect_left(PRIMES_EXACT, hi)] - _PW_EXACT[bisect.bisect_left(PRIMES_EXACT, u)]) if u < hi else Iv(0, 0)
    if v > P_EXACT:
        ut = max(u, P_EXACT)
        vi, ui = Iv(v, v), Iv(ut, ut)
        t = (
            clamp_pos_iv(_mertens_sum_inv_p_ub(vi, ln_iv(vi)) - _mertens_sum_inv_p_lb(ui, ln_iv(ui)))
            + Iv(1, 1) / Iv(ut - 1, ut - 1)
            - Iv(1, 1) / Iv(v - 1, v - 1)
        )
        s = s + t
    return Iv(D_ZERO, s.hi)


def _v_lo_27k(u: int, v: int) -> Iv:
    if v <= u:
        return Iv(1, 1)
    hi = min(v, P_EXACT)
    prod = (_PV_EXACT[bisect.bisect_left(PRIMES_EXACT, hi)] / _PV_EXACT[bisect.bisect_left(PRIMES_EXACT, u)]) if u < hi else Iv(1, 1)
    if v > P_EXACT:
        ut = max(u, P_EXACT)
        vi, ui = Iv(v, v), Iv(ut, ut)
        t = (
            clamp_pos_iv(_mertens_sum_inv_p_ub(vi, ln_iv(vi)) - _mertens_sum_inv_p_lb(ui, ln_iv(ui)))
            + Iv(1, 1) / Iv(ut - 1, ut - 1)
            - Iv(1, 1) / Iv(v - 1, v - 1)
        )
        prod = prod * exp_iv(-(t + Iv(1, 1) / Iv(ut - 2, ut - 2)))
    return Iv(prod.lo, D_ONE)


def _e_bound_27k(caps: tuple[int, ...], ends: tuple[int, ...]) -> Iv:
    """Brun block remainder bound using `P_EXACT` + `MertensPrimeSumPremise`."""
    z = ends[0]
    tot = Iv(0, 0)
    fact, prev_k = 1, 0
    for i in range(1, len(ends)):
        k = caps[i - 1] + 1
        while prev_k < k:
            prev_k += 1
            fact *= prev_k
        tot = tot + (_s_hi_27k(ends[i], z) ** k) / (Iv(fact, fact) * _v_lo_27k(ends[i], z))
    return Iv(D_ZERO, tot.hi)


def _j_full_lb_z3_27k(z_iv: Iv, xi_iv: Iv, k1: int = 12, k2: int = 4) -> Iv:
    """`J_full(z, xi)` lower bound aligned with `P_EXACT = 27000` + `MertensPrimeSumPremise`."""
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
        w0, w1 = Iv(cur.lo, cur.lo), Iv(nxt.hi, nxt.hi)
        if w1.hi < w0.lo:
            w1 = w0
        w1p = w1 + Iv(1, 1)
        mert_diff = clamp_pos_iv(_mertens_sum_inv_p_ub(w1p, ln_iv(w1p)) - _mertens_sum_inv_p_lb(w0, ln_iv(w0)))
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
            a0, a1 = Iv(c1.lo, c1.lo), Iv(n1.hi, n1.hi)
            hi_p2 = Iv((xi_iv / a1).lo, (xi_iv / a1).lo)
            if hi_p2.lo > a1.hi:
                s1 = clamp_pos_iv(_mertens_sum_inv_p_lb(a1, ln_iv(a1)) - _mertens_sum_inv_p_ub(a0, ln_iv(a0)))
                if s1.lo > 0:
                    r3 = pow_real_iv(hi_p2 / a1, Iv.from_frac(Fraction(1, k2)))
                    c2 = a1
                    for j in range(k2):
                        n2 = hi_p2 if j == k2 - 1 else c2 * r3
                        b0, b1 = Iv(c2.lo, c2.lo), Iv(n2.hi, n2.hi)
                        if b1.hi > b0.lo:
                            s2 = clamp_pos_iv(_mertens_sum_inv_p_lb(b1, ln_iv(b1)) - _mertens_sum_inv_p_ub(b0, ln_iv(b0)))
                            if s2.lo > 0:
                                res = res + s1 * s2 * j_odd_lb(xi_iv / (a1 * b1))
                        c2 = n2
            c1 = n1
    return res


def _align_budget(main_raw: Decimal, err_raw: Decimal, w_main: Decimal, w_err: Decimal) -> tuple[Decimal, Decimal, Decimal]:
    pad = Decimal("1e-9")
    q24 = Decimal("1e-24")
    with localcontext() as ctx:
        ctx.traps[Inexact] = False
        ctx.traps[Rounded] = False
        main_lo = min(main_raw, w_main - pad).quantize(q24, rounding=ROUND_FLOOR)
        err_hi = max(err_raw, w_err + pad).quantize(q24, rounding=ROUND_CEILING)
    return main_lo, err_hi, main_lo - err_hi


def certify_slab_2a(spec: Slab2ASpec) -> SlabCertificate:
    """Exact prime slices + `P_sub`/EvenBonf over `[4 * 10^18, 2 * 10^23)` (normalized by `|A_N|`)."""
    z = spec.z
    assert z <= P_EXACT
    y = max(ceil_root_int(spec.x_hi + 1, 4), ceil_root_int((spec.x_hi + z - 1) // z, 3))
    assert y**4 > spec.x_hi and z * (y**3) >= spec.x_hi

    x_lo_iv, x_hi_iv = Iv(spec.x_lo, spec.x_lo), Iv(spec.x_hi, spec.x_hi)
    log_x_lo, log_x_hi = ln_iv(x_lo_iv), ln_iv(x_hi_iv)
    sqrt_x_lo = floor_root_int(spec.x_lo, 2)
    q_sq = floor_root_int(spec.x_lo, 4)

    p_full = [p for p in ODD_PRIMES if p < z]
    v_full, ratio_odd, n_d_odd = _odd_bonf_small_z(p_full, spec.a, spec.m_odd, sqrt_x_lo)
    epd = epd_norm_iv(x_lo_iv, log_x_lo)
    rem_a = Iv(n_d_odd, n_d_odd) * epd

    cutoffs = sorted(set([c for c in (11, 17, 23, 29, 37) if c <= z] + [z]))
    ev_opts = _build_exact_even_bonf_opts(cutoffs, sqrt_x_lo, scale_ref_lb=None)
    p_sub = build_p_sub_table(p_full)

    if z < P_EXACT < y:
        bpts = _build_slices(z, P_EXACT, 48)[:-1] + _build_slices(P_EXACT, y, 4)
    else:
        bpts = _build_slices(z, y, 64)

    sum_aq, err_aq = Iv(0, 0), Iv(0, 0)
    for idx in range(len(bpts) - 1):
        q0, q1 = bpts[idx], bpts[idx + 1]
        if q1 <= P_EXACT:
            j0 = bisect.bisect_left(PRIMES_EXACT, q0)
            j1 = bisect.bisect_left(PRIMES_EXACT, q1)
            cnt = j1 - j0
            if cnt == 0:
                continue
            sq = sum((Iv.from_frac(Fraction(1, q - 1)) for q in PRIMES_EXACT[j0:j1]), Iv(0, 0))
            cnt_iv = Iv(cnt, cnt)
            q_max = PRIMES_EXACT[j1 - 1]
        else:
            assert q0 >= P_EXACT
            sq = _slice_sq_analytic(q0, q1)
            cnt_iv = _schoenfeld_cnt_ub(q0, q1, sub=32)
            q_max = q1 - 1

        best_tot, best_main, best_err = None, Iv(0, 0), Iv(0, 0)
        for prod, v_s, ip_s, k_sub in p_sub:
            if q_max * prod > sqrt_x_lo:
                break
            m_sl = sq * v_s
            e_sl = cnt_iv * (Iv(1 << k_sub, 1 << k_sub) + ip_s + Iv(1, 1)) * epd
            tot_sl = m_sl + e_sl
            if best_tot is None or tot_sl.hi < best_tot.hi:
                best_tot, best_main, best_err = tot_sl, m_sl, e_sl
        for prod_ev, v_rat, nd_ev, ip_ev, rat in ev_opts:
            if q_max * prod_ev > sqrt_x_lo:
                continue
            m_sl = sq * v_rat
            e_sl = cnt_iv * (Iv(nd_ev, nd_ev) + ip_ev + rat) * epd
            if best_tot is None or (m_sl + e_sl).hi < best_tot.hi:
                best_tot, best_main, best_err = m_sl + e_sl, m_sl, e_sl
        sum_aq = sum_aq + best_main
        err_aq = err_aq + best_err

    err_q2 = _q2_square_error_2ab(log_x_hi, z, y, q_sq, epd)
    main_norm = v_full * ratio_odd - Iv.from_str("0.5") * sum_aq
    tot_err = rem_a + Iv.from_str("0.5") * err_aq + err_q2 + log_x_lo / x_lo_iv
    net = main_norm - tot_err
    assert net.lo > 0, f"2a [{spec.x_lo}, {spec.x_hi}) failed: {net}"
    w_res = build_slab_2ab_witness("2a", spec)
    main_lo, err_hi, net_lo = _align_budget(main_norm.lo, tot_err.hi, w_res.main_lo_dec, w_res.err_hi_dec)
    assert net_lo > 0, f"2a [{spec.x_lo}, {spec.x_hi}) witness-aligned failed: main={main_lo}, err={err_hi}"
    return SlabCertificate(
        regime="2a",
        x_lo=spec.x_lo,
        x_hi=spec.x_hi,
        z=z,
        y=y,
        main_lo=main_lo,
        err_hi=err_hi,
        net_lo=net_lo,
        sieve_net_lo=min((Iv(net_lo, net_lo) / v_full).lo, w_res.sieve_net_lo_dec),
        rem_tol=(Iv(main_lo, main_lo) / Iv(err_hi, err_hi)).lo,
    )


def certify_slab_2b(spec: Slab2BSpec) -> SlabCertificate:
    """
    Odd Bonferroni + hybrid `{P_sub, multi-cutoff even Bonferroni}` slices over
    `[2 * 10^23, 10^84)` (normalized by `|A_N|`).
    """
    z = ceil_root_int(spec.x_hi, spec.m_div)
    assert z <= P_EXACT
    y = max(ceil_root_int(spec.x_hi + 1, 4), ceil_root_int((spec.x_hi + z - 1) // z, 3))
    assert y**4 > spec.x_hi and z * (y**3) >= spec.x_hi

    x_lo_iv, x_hi_iv = Iv(spec.x_lo, spec.x_lo), Iv(spec.x_hi, spec.x_hi)
    log_x_lo, log_x_hi = ln_iv(x_lo_iv), ln_iv(x_hi_iv)
    sqrt_x_lo = floor_root_int(spec.x_lo, 2)
    q_sq = floor_root_int(spec.x_lo, 4)

    p_full = [p for p in ODD_PRIMES if p < z]
    v_full, ratio_odd, n_d_odd = _odd_bonf_small_z(p_full, spec.a, spec.m_odd, sqrt_x_lo)
    epd = epd_norm_iv(x_lo_iv, log_x_lo)
    rem_a = Iv(n_d_odd, n_d_odd) * epd

    cutoffs = sorted(set([c for c in (29, 89, 251, 600, 1500) if c < z] + ([z] if z <= 1500 else [])))
    ev_clean = _build_exact_even_bonf_opts(cutoffs, sqrt_x_lo, scale_ref_lb=None)
    if z > 1500:
        ev_clean.extend(_build_analytic_even_bonf_opts(z, sqrt_x_lo, mult_by_v=v_full))

    p_sub = build_p_sub_table(p_full[:18])
    bpts = _build_slices(z, y, 56)
    sum_aq, err_aq = Iv(0, 0), Iv(0, 0)
    for idx in range(len(bpts) - 1):
        q0, q1 = bpts[idx], bpts[idx + 1]
        if q1 <= P_EXACT:
            j0 = bisect.bisect_left(PRIMES_EXACT, q0)
            j1 = bisect.bisect_left(PRIMES_EXACT, q1)
            cnt = j1 - j0
            if cnt == 0:
                continue
            sq = sum((Iv.from_frac(Fraction(1, q - 1)) for q in PRIMES_EXACT[j0:j1]), Iv(0, 0))
            num_q_sl = Iv(cnt, cnt)
            q_max = PRIMES_EXACT[j1 - 1]
        else:
            assert q0 >= P_EXACT
            sq = _slice_sq_analytic(q0, q1)
            num_q_sl = _schoenfeld_cnt_ub(q0, q1, sub=32)
            q_max = q1 - 1

        best_main = sq
        best_err = num_q_sl * Iv(2, 2) * epd
        best_tot = best_main + best_err
        for prod, v_s, ip_s, k_sub in p_sub[1:]:
            if q_max * prod > sqrt_x_lo:
                break
            m_sl = sq * v_s
            e_sl = num_q_sl * (Iv(1 << k_sub, 1 << k_sub) + ip_s + Iv(1, 1)) * epd
            if (m_sl + e_sl).hi < best_tot.hi:
                best_tot, best_main, best_err = m_sl + e_sl, m_sl, e_sl
        for prod_ev, v_rat, nd_ev, ip_ev, rat in ev_clean:
            if q_max * prod_ev > sqrt_x_lo:
                continue
            m_sl = sq * v_rat
            e_sl = num_q_sl * (Iv(nd_ev, nd_ev) + ip_ev + rat) * epd
            if (m_sl + e_sl).hi < best_tot.hi:
                best_tot, best_main, best_err = m_sl + e_sl, m_sl, e_sl
        sum_aq = sum_aq + best_main
        err_aq = err_aq + best_err

    err_q2 = _q2_square_error_2ab(log_x_hi, z, y, q_sq, epd)
    main_norm = v_full * ratio_odd - Iv.from_str("0.5") * sum_aq
    tot_err = rem_a + Iv.from_str("0.5") * err_aq + err_q2 + log_x_lo / x_lo_iv
    net = main_norm - tot_err
    assert net.lo > 0, f"2b [{spec.x_lo}, {spec.x_hi}) failed: {net}"
    w_res = build_slab_2ab_witness("2b", spec)
    main_lo, err_hi, net_lo = _align_budget(main_norm.lo, tot_err.hi, w_res.main_lo_dec, w_res.err_hi_dec)
    assert net_lo > 0, f"2b [{spec.x_lo}, {spec.x_hi}) witness-aligned failed: main={main_lo}, err={err_hi}"
    return SlabCertificate(
        regime="2b",
        x_lo=spec.x_lo,
        x_hi=spec.x_hi,
        z=z,
        y=y,
        main_lo=main_lo,
        err_hi=err_hi,
        net_lo=net_lo,
        sieve_net_lo=min((Iv(net_lo, net_lo) / v_full).lo, w_res.sieve_net_lo_dec),
        rem_tol=(Iv(main_lo, main_lo) / Iv(err_hi, err_hi)).lo,
    )


def certify_slab_2c(spec: Slab2CSpec) -> SlabCertificate:
    """
    Hybrid transition/middle-bridge certifier over `[10^84, 10^600)` normalized by
    `|A_N| * V_N(z)` and 1-for-1 aligned with `SlabSieveEngineWiring.lean`:
      - Lower `S(A_N)`: `max(OddBonferroni, BrunBlock)`
      - Upper `S(A_{N,q})`: per-slice `min(EvenBonf multi-z_sub/analytic,
        Adaptive Selberg J_full)`.
    """
    z = ceil_root_int(spec.x_hi, spec.m_div)
    y = max(ceil_root_int(spec.x_hi + 1, 4), ceil_root_int((spec.x_hi + z - 1) // z, 3))
    assert y**4 > spec.x_hi and z * (y**3) >= spec.x_hi and P_EXACT <= z <= y

    x_lo_iv, x_hi_iv = Iv(spec.x_lo, spec.x_lo), Iv(spec.x_hi, spec.x_hi)
    log_x_lo, log_x_hi = ln_iv(x_lo_iv), ln_iv(x_hi_iv)
    z_iv, log_z = Iv(z, z), ln_iv(Iv(z, z))
    epd = epd_norm_iv(x_lo_iv, log_x_lo)
    sqrt_x_lo = floor_root_int(spec.x_lo, 2)
    sqrt_x_lo_iv = exp_iv(Iv.from_str("0.5") * log_x_lo)

    v_full_lb = (Iv(1, 1) - _deltaV_bjs_4(z_iv)) * U_CONST * E_NEG_GAMMA / log_z

    # Best normalized lower bound for S(A_N) / (|A_N| * V_N(z)): max(OddBonferroni, BrunBlock)
    best_sa: tuple[Iv, Iv, str] | None = None
    for mo in (7, 9, 11):
        z_mo = z**mo
        if z_mo > sqrt_x_lo:
            break
        qp = 1
        for a in range(0, 35):
            if a > 0:
                qp *= ODD_PRIMES[a - 1]
            if qp * z_mo > sqrt_x_lo:
                break
            ev = eval_odd_bonferroni_s_a(z, a, mo, sqrt_x_lo)
            r_norm = (ev.n_moduli * epd) / v_full_lb
            if best_sa is None or (ev.ratio_odd - r_norm).lo > (best_sa[0] - best_sa[1]).lo:
                best_sa = (ev.ratio_odd, r_norm, f"Bonf(a={a},m={mo})")
    brun_res = eval_best_brun_lower(z, sqrt_x_lo, epd, v_full_lb)
    if brun_res is not None:
        ratio_low_27k = Iv(1, 1) - _e_bound_27k(brun_res.caps, brun_res.ends)
        caps_tag = ",".join(str(c) for c in brun_res.caps)
        if best_sa is None or (ratio_low_27k - brun_res.r_norm).lo > (best_sa[0] - best_sa[1]).lo:
            best_sa = (ratio_low_27k, brun_res.r_norm, f"Brun(a={brun_res.a},caps=({caps_tag}))")
    assert best_sa is not None, f"No admissible lower sieve on 2c [{spec.x_lo}, {spec.x_hi})"
    sa_norm, rem_a_norm, sa_tag = best_sa

    # Upper-sieve S(A_{N,q}) / (|A_N| * V_N(z)) across 48 geometric slices of [z, y)
    bpts = _build_slices(z, y, 48)
    z_cap = pow_real_iv(z_iv, Iv.from_str("2.97"))

    sub_cutoffs = [c for c in (29, 89, 251, 600, 1500) if c < z]
    ev_opts = _build_exact_even_bonf_opts(sub_cutoffs, sqrt_x_lo, scale_ref_lb=v_full_lb)
    ev_opts.extend(_build_analytic_even_bonf_opts(z, sqrt_x_lo, mult_by_v=None))

    l4 = log_x_lo**4
    mq_cands = [sqrt_x_lo_iv / (Iv.from_str(ks) * l4) for ks in ("0.002", "0.008", "0.03", "0.15", "0.8")]
    jf_cache: dict[tuple[Decimal, Decimal], Iv] = {}

    sum_aq, err_aq = Iv(0, 0), Iv(0, 0)
    cnt_bonf = cnt_sel = 0
    for idx in range(len(bpts) - 1):
        q0, q1 = bpts[idx], bpts[idx + 1]
        q1_iv = Iv(q1, q1)
        sq = _slice_sq_analytic(q0, q1)
        num_q_sl = _schoenfeld_cnt_ub(q0, q1, sub=32)
        q_max = q1 - 1

        bm_n = sq / v_full_lb
        be_n = (num_q_sl * Iv(2, 2) * epd) / v_full_lb
        bt_n = bm_n + be_n
        tag = "bonf"

        for pe, m_rat, nd, ip2, rat in ev_opts:
            if q_max * pe > sqrt_x_lo:
                continue
            ms = sq * m_rat
            es = (num_q_sl * (Iv(nd, nd) + ip2 + rat) * epd) / v_full_lb
            if (ms + es).hi < bt_n.hi:
                bt_n, bm_n, be_n, tag = ms + es, ms, es, "bonf"

        for h_q in mq_cands:
            xi_q = min_iv(z_cap, (h_q / q1_iv).sqrt())
            if xi_q.lo < 1:
                continue
            jf_key = (xi_q.lo, xi_q.hi)
            jf = jf_cache.get(jf_key)
            if jf is None:
                jf = _j_full_lb_z3_27k(z_iv, xi_q, k1=12, k2=4)
                jf_cache[jf_key] = jf
            if jf.lo <= 0:
                continue
            ms = sq / (v_full_lb * jf)
            xi2 = xi_q * xi_q
            s3c = min_iv(num_q_sl * xi2, sq * h_q)
            # Odd squarefree sum_{L<=X, 2∤L} mu^2(L) 3^{omega(L)} <= 1/16 * X * (ln X + 6)^2 with X = xi_q^2
            es1 = Iv.from_str("0.0625") * s3c * ((Iv(2, 2) * ln_iv(xi_q) + Iv(6, 6)) ** 2) * epd
            f0 = Iv.from_str("0.5") * ln_iv(xi2) + ALPHA0_PROVED + C_F0 / xi2
            es = (es1 + num_q_sl * (Iv(1, 1) + (H_TILDE_PROVED * f0) ** 3) * epd) / v_full_lb
            if (ms + es).hi < bt_n.hi:
                bt_n, bm_n, be_n, tag = ms + es, ms, es, "sel"

        if tag == "bonf":
            cnt_bonf += 1
        else:
            cnt_sel += 1
        sum_aq = sum_aq + bm_n
        err_aq = err_aq + be_n

    q_sq = floor_root_int(spec.x_lo, 4)
    err_q2 = _q2_square_error_2ab(log_x_hi, z, y, q_sq, epd) / v_full_lb
    err_one = (log_x_lo / x_lo_iv) / v_full_lb
    main_norm = sa_norm - Iv.from_str("0.5") * sum_aq
    tot_err = rem_a_norm + Iv.from_str("0.5") * err_aq + err_q2 + err_one
    net = main_norm - tot_err
    assert net.lo > 0, f"2c [{spec.x_lo}, {spec.x_hi}) failed: main={main_norm}, err={tot_err}, net={net}"
    w_res = build_slab_2c_witness(spec)
    main_lo, err_hi, net_lo = _align_budget(main_norm.lo, tot_err.hi, w_res.main_lo_dec, w_res.err_hi_dec)
    assert net_lo > 0, f"2c [{spec.x_lo}, {spec.x_hi}) witness-aligned failed: main={main_lo}, err={err_hi}"
    return SlabCertificate(
        regime="2c",
        x_lo=spec.x_lo,
        x_hi=spec.x_hi,
        z=z,
        y=y,
        main_lo=main_lo,
        err_hi=err_hi,
        net_lo=net_lo,
        sieve_net_lo=net_lo,
        rem_tol=(Iv(main_lo, main_lo) / Iv(err_hi, err_hi)).lo,
        note=w_res.note,
    )
