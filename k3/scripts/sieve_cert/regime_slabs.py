"""
Finite-slab certifiers (`2a`, `2b`, `2c`) over `[4 * 10^18, 10^600)` returning
machine-checkable `SlabCertificate` records with robustness diagnostics.
"""

from __future__ import annotations

import bisect
from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction

from .bonferroni_engine import (
    build_p_sub_table,
    comb_int,
    elem_sym_iv,
    eval_odd_bonferroni_s_a,
)
from .constants import (
    ALPHA0,
    C_F0,
    E_NEG_GAMMA,
    H_TILDE,
    ODD_PRIMES,
    P_PREFIX_MAX,
    PI,
    PRIMES,
    PRIMES_BIG,
    U_CONST,
)
from .interval import (
    Iv,
    ceil_root_int,
    clamp_pos_iv,
    exp_iv,
    floor_root_int,
    fmt_dec,
    ln_iv,
    min_iv,
    pow_real_iv,
)
from .linear_sieve import (
    compute_n_term,
    f_lin_lb,
    F_sieve_iv,
    finite_buchstab_even_err_hi,
    finite_buchstab_odd_err_hi,
)
from .primes_and_mertens import (
    INV_PM1_SQ_ALL,
    INV_PP1_ALL,
    PREFIX_PM1_SQ,
    PREFIX_PP1,
    epd_norm_iv,
    li_ratio_ub,
    pi_ub_iv,
    sum_inv_p_lb,
    sum_inv_p_ub,
    v_full_exact_lt,
)
from .schedule import Slab2ASpec, Slab2BSpec, Slab2CSpec
from .selberg_weights import j_full_lb_z3

SCALE_INT = 10**40


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
        s1 = clamp_pos_iv(sum_inv_p_ub(z_iv, log_z) - ex_p) + (INV_PP1_ALL - PREFIX_PP1[aq])
        c_log2 = Iv(1, 1) / (Iv(2, 2) * (Iv(1, 1) - Iv(1, 1) / Iv(max(pa, 3), max(pa, 3))))
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


def _q2_square_error_raw(
    x_lo_iv: Iv, log_x_hi: Iv, z: int, y: int, q_sq: int, li_r: Iv, epd: Iv
) -> Iv:
    """Upper bound on `(1/2) sum_{z <= q < y} |A_{N, q^2}| / |A_N|`."""
    y_iv = Iv(y, y)
    if y <= q_sq + 1:
        return Iv.from_str("0.5") * (li_r / Iv(z - 1, z - 1) + pi_ub_iv(y_iv, ln_iv(y_iv)) * epd)
    qsq_iv = Iv(q_sq, q_sq)
    return Iv.from_str("0.5") * (
        li_r / Iv(z - 1, z - 1)
        + pi_ub_iv(qsq_iv, ln_iv(qsq_iv)) * epd
        + log_x_hi * (Iv(1, 1) / qsq_iv + pi_ub_iv(y_iv, ln_iv(y_iv)) / x_lo_iv)
    )


def certify_slab_2a(spec: Slab2ASpec) -> SlabCertificate:
    """Exact prime slices + `P_sub` IE over `[4 * 10^18, 2 * 10^23)` (normalized by `|A_N|`)."""
    z = spec.z
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

    bpts = _build_slices(z, y, 64)
    p_sub = build_p_sub_table(p_full)
    sum_aq, err_aq = Iv(0, 0), Iv(0, 0)
    for idx in range(len(bpts) - 1):
        j0 = bisect.bisect_left(PRIMES_BIG, bpts[idx])
        j1 = bisect.bisect_left(PRIMES_BIG, bpts[idx + 1])
        cnt = j1 - j0
        if cnt == 0:
            continue
        s_scaled = sum((SCALE_INT + q - 2) // (q - 1) for q in PRIMES_BIG[j0:j1])
        sq = Iv.from_frac(Fraction(s_scaled, SCALE_INT))
        q_max = PRIMES_BIG[j1 - 1]
        cnt_iv = Iv(cnt, cnt)
        best_tot, best_main, best_err = None, Iv(0, 0), Iv(0, 0)
        for prod, v_s, ip_s, k_sub in p_sub:
            if q_max * prod > sqrt_x_lo:
                break
            m_sl = sq * v_s
            e_sl = cnt_iv * (Iv(1 << k_sub, 1 << k_sub) + ip_s + Iv(1, 1)) * epd
            tot_sl = m_sl + e_sl
            if best_tot is None or tot_sl.hi < best_tot.hi:
                best_tot, best_main, best_err = tot_sl, m_sl, e_sl
        sum_aq = sum_aq + best_main
        err_aq = err_aq + best_err

    i_start, i_end = bisect.bisect_left(PRIMES_BIG, z), bisect.bisect_left(PRIMES_BIG, y)
    s_q2_g, c_q2_g, s_q2_e, c_q2_e = 0, 0, 0, 0
    for q in PRIMES_BIG[i_start:i_end]:
        if q <= q_sq:
            s_q2_g += (SCALE_INT + q * (q - 1) - 1) // (q * (q - 1))
            c_q2_g += 1
        else:
            s_q2_e += (SCALE_INT + q * q - 1) // (q * q)
            c_q2_e += 1
    li_r = li_ratio_ub(x_lo_iv, log_x_lo)
    err_q2 = Iv.from_str("0.5") * (
        li_r * Iv.from_frac(Fraction(s_q2_g, SCALE_INT))
        + Iv(c_q2_g, c_q2_g) * epd
        + log_x_hi * (Iv.from_frac(Fraction(s_q2_e, SCALE_INT)) + Iv(c_q2_e, c_q2_e) / x_lo_iv)
    )
    main_norm = v_full * ratio_odd - Iv.from_str("0.5") * sum_aq
    tot_err = rem_a + Iv.from_str("0.5") * err_aq + err_q2 + log_x_lo / x_lo_iv
    net = main_norm - tot_err
    assert net.lo > 0, f"2a [{spec.x_lo}, {spec.x_hi}) failed: {net}"
    return SlabCertificate(
        regime="2a",
        x_lo=spec.x_lo,
        x_hi=spec.x_hi,
        z=z,
        y=y,
        main_lo=main_norm.lo,
        err_hi=tot_err.hi,
        net_lo=net.lo,
        sieve_net_lo=(net / v_full).lo,
        rem_tol=(main_norm / tot_err).lo,
    )


def certify_slab_2b(spec: Slab2BSpec) -> SlabCertificate:
    """
    Odd Bonferroni + hybrid `{P_sub, multi-cutoff even Bonferroni}` slices over
    `[2 * 10^23, 10^84)` (normalized by `|A_N|`).
    """
    z = ceil_root_int(spec.x_hi, spec.m_div)
    assert z <= P_PREFIX_MAX
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
        q0_iv, q1_iv = Iv(q0, q0), Iv(q1, q1)
        if q1 <= P_PREFIX_MAX:
            j0 = bisect.bisect_left(PRIMES_BIG, q0)
            j1 = bisect.bisect_left(PRIMES_BIG, q1)
            cnt = j1 - j0
            if cnt == 0:
                continue
            sq = sum((Iv.from_frac(Fraction(1, q - 1)) for q in PRIMES_BIG[j0:j1]), Iv(0, 0))
            num_q_sl = Iv(cnt, cnt)
            q_max = PRIMES_BIG[j1 - 1]
        else:
            sq = clamp_pos_iv(sum_inv_p_ub(q1_iv, ln_iv(q1_iv)) - sum_inv_p_lb(q0_iv, ln_iv(q0_iv))) + Iv(1, 1) / q0_iv
            if q0 <= P_PREFIX_MAX:
                cnt_lo = bisect.bisect_left(PRIMES_BIG, q0)
                num_q_sl = pi_ub_iv(q1_iv, ln_iv(q1_iv)) - Iv(cnt_lo, cnt_lo)
            else:
                l0, l1 = ln_iv(q0_iv), ln_iv(q1_iv)
                num_q_sl = (q1_iv - q0_iv) / l0 + (q1_iv.sqrt() * l1 + q0_iv.sqrt() * l0) / (Iv(8, 8) * PI)
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

    li_r = li_ratio_ub(x_lo_iv, log_x_lo)
    err_q2 = _q2_square_error_raw(x_lo_iv, log_x_hi, z, y, q_sq, li_r, epd)

    main_norm = v_full * ratio_odd - Iv.from_str("0.5") * sum_aq
    tot_err = rem_a + Iv.from_str("0.5") * err_aq + err_q2 + log_x_lo / x_lo_iv
    net = main_norm - tot_err
    assert net.lo > 0, f"2b [{spec.x_lo}, {spec.x_hi}) failed: {net}"
    return SlabCertificate(
        regime="2b",
        x_lo=spec.x_lo,
        x_hi=spec.x_hi,
        z=z,
        y=y,
        main_lo=main_norm.lo,
        err_hi=tot_err.hi,
        net_lo=net.lo,
        sieve_net_lo=(net / v_full).lo,
        rem_tol=(main_norm / tot_err).lo,
    )


def certify_slab_2c(spec: Slab2CSpec) -> SlabCertificate:
    """
    Hybrid transition/middle-bridge certifier over `[10^84, 10^600)` normalized by
    `|A_N| * V_N(z)`:
      - Lower `S(A_N)`: `max(OddBonferroni, Finite-Terminating Buchstab f(s_A) - E_even)`
      - Upper `S(A_{N,q})`: per-slice `min(EvenBonf multi-z_sub, Clamped-dq Buchstab F+E_odd,
        Adaptive-K_sel pre-sieve-free Selberg J_full)`.
    """
    z = ceil_root_int(spec.x_hi, spec.m_div)
    y = max(ceil_root_int(spec.x_hi + 1, 4), ceil_root_int((spec.x_hi + z - 1) // z, 3))
    assert y**4 > spec.x_hi and z * (y**3) >= spec.x_hi and 2 <= z <= y

    x_lo_iv, x_hi_iv = Iv(spec.x_lo, spec.x_lo), Iv(spec.x_hi, spec.x_hi)
    log_x_lo, log_x_hi = ln_iv(x_lo_iv), ln_iv(x_hi_iv)
    z_iv, y_iv, log_z = Iv(z, z), Iv(y, y), ln_iv(Iv(z, z))
    epd = epd_norm_iv(x_lo_iv, log_x_lo)
    sqrt_x_lo = floor_root_int(spec.x_lo, 2)
    sqrt_x_lo_iv = exp_iv(Iv.from_str("0.5") * log_x_lo)

    eta_z = (Iv.from_str("6.836e-6") / log_z) if z > 10**12 else (Iv(2, 2) / (z_iv.sqrt() * log_z))
    v_full_lb = (U_CONST * E_NEG_GAMMA / log_z) * exp_iv(-eta_z - Iv(1, 1) / Iv(z - 2, z - 2))

    # Best normalized lower bound for S(A_N) / (|A_N| * V_N(z))
    h1 = sqrt_x_lo_iv / (Iv(spec.k1_div, spec.k1_div) * (log_x_lo ** 2))
    qp1 = 1
    for p in ODD_PRIMES:
        if p < spec.p1_star:
            qp1 *= p
    d1 = min_iv(h1 / Iv(qp1, qp1), pow_real_iv(z_iv, Iv.from_str("5.20")))
    best_sa: tuple[Iv, Iv, str] | None = None
    if d1.lo > (z_iv ** 2).hi:
        ln_d1 = ln_iv(d1)
        s_a_iv = ln_d1 / log_z
        nt1 = compute_n_term(spec.p1_star, int(d1.hi) + 1)
        if nt1 <= 105:
            ee = finite_buchstab_even_err_hi(
                spec.p1_star, Iv(ln_d1.lo, ln_d1.lo), Iv(log_z.hi, log_z.hi), nt1, s_a_iv.lo
            )
            m_bjs = f_lin_lb(Iv(s_a_iv.lo, s_a_iv.lo)) - ee
            r_bjs = (((Iv(4, 4) / (PI * PI)) * h1 + h1.sqrt()) * epd) / v_full_lb
            best_sa = (m_bjs, r_bjs, f"BJS({spec.p1_star},nt={nt1},s={fmt_dec(s_a_iv.lo, 2)})")

    for mo in (7, 9):
        for a in (2, 4, 6, 8, 10):
            qp = 1
            for p in ODD_PRIMES[:a]:
                qp *= p
            if qp * (z ** mo) <= sqrt_x_lo:
                ev = eval_odd_bonferroni_s_a(z, a, mo, sqrt_x_lo)
                r_norm = (ev.n_moduli * epd) / v_full_lb
                if best_sa is None or (ev.ratio_odd - r_norm).lo > (best_sa[0] - best_sa[1]).lo:
                    best_sa = (ev.ratio_odd, r_norm, f"Bonf(a={a},m={mo})")
    assert best_sa is not None
    sa_norm, rem_a_norm, sa_tag = best_sa

    # Upper-sieve S(A_{N,q}) / (|A_N| * V_N(z)) across 48 geometric slices of [z, y)
    bpts = _build_slices(z, y, 48)
    li_r = li_ratio_ub(x_lo_iv, log_x_lo)
    z_cap = pow_real_iv(z_iv, Iv.from_str("2.97"))

    h_2 = sqrt_x_lo_iv / (Iv(spec.k2_div, spec.k2_div) * (log_x_lo ** 2))
    qp2 = 1
    for p in ODD_PRIMES:
        if p < spec.p2_star:
            qp2 *= p
    d2_base = h_2 / Iv(qp2, qp2)
    dq_cap = pow_real_iv(z_iv, Iv.from_str("4.90"))

    sub_cutoffs = [c for c in (29, 89, 251, 600, 1500) if c < z]
    ev_opts = _build_exact_even_bonf_opts(sub_cutoffs, sqrt_x_lo, scale_ref_lb=v_full_lb)
    ev_opts.extend(_build_analytic_even_bonf_opts(z, sqrt_x_lo, mult_by_v=None))

    l4 = log_x_lo ** 4
    mq_cands = [sqrt_x_lo_iv / (Iv.from_str(ks) * l4) for ks in ("0.002", "0.008", "0.03", "0.15", "0.8")]

    sum_aq, err_aq = Iv(0, 0), Iv(0, 0)
    cnt_bonf = cnt_bjs = cnt_sel = 0
    for idx in range(len(bpts) - 1):
        q0, q1 = bpts[idx], bpts[idx + 1]
        q0_iv, q1_iv = Iv(q0, q0), Iv(q1, q1)
        sq = clamp_pos_iv(sum_inv_p_ub(q1_iv, ln_iv(q1_iv)) - sum_inv_p_lb(q0_iv, ln_iv(q0_iv))) + Iv(1, 1) / q0_iv
        num_q_sl = pi_ub_iv(q1_iv, ln_iv(q1_iv))
        q_max = q1 - 1

        bm_n = sq / v_full_lb
        be_n = (num_q_sl * Iv(2, 2) * epd) / v_full_lb
        bt_n = bm_n + be_n
        tag = "bonf"

        for pe, m_rat, nd, ip2, rat in ev_opts:
            if q_max * pe > sqrt_x_lo:
                continue
            ms = li_r * sq * m_rat
            es = (num_q_sl * (Iv(nd, nd) + ip2 + rat) * epd) / v_full_lb
            if (ms + es).hi < bt_n.hi:
                bt_n, bm_n, be_n, tag = ms + es, ms, es, "bonf"

        dq = min_iv(d2_base / q1_iv, dq_cap)
        if dq.lo >= z_iv.hi:
            ln_dq = ln_iv(dq)
            sq_iv = ln_dq / log_z
            if sq_iv.lo >= 1 and sq_iv.hi <= Decimal("4.95"):
                nt2 = compute_n_term(spec.p2_star, int(dq.hi) + 1)
                if nt2 <= 105:
                    eo = finite_buchstab_odd_err_hi(spec.p2_star, Iv(ln_dq.lo, ln_dq.lo), nt2, sq_iv.lo)
                    mb = li_r * sq * (F_sieve_iv(Iv(sq_iv.lo, sq_iv.lo)) + eo)
                    rem_b_sf = (Iv(4, 4) / (PI * PI)) * sq * h_2 + num_q_sl * (h_2 / q0_iv).sqrt()
                    rem_b_odd = Iv.from_str("0.5") * sq * h_2 + num_q_sl
                    rem_b = (min_iv(rem_b_sf, rem_b_odd) * epd) / v_full_lb
                    if (mb + rem_b).hi < bt_n.hi:
                        bt_n, bm_n, be_n, tag = mb + rem_b, mb, rem_b, "bjs"

        for h_q in mq_cands:
            xi_q = min_iv(z_cap, (h_q / q1_iv).sqrt())
            if xi_q.lo < 1:
                continue
            jf = j_full_lb_z3(z_iv, xi_q, k1=12, k2=4)
            if jf.lo <= 0:
                continue
            ms = li_r * sq / (v_full_lb * jf)
            xi2 = xi_q * xi_q
            s3c = min_iv(num_q_sl * xi2, sq * h_q)
            # Odd squarefree sum_{L<=X, 2∤L} mu^2(L) 3^{omega(L)} <= 1/16 * X * (ln X + 6)^2 with X = xi_q^2
            es1 = Iv.from_str("0.0625") * s3c * ((Iv(2, 2) * ln_iv(xi_q) + Iv(6, 6)) ** 2) * epd
            f0 = Iv.from_str("0.5") * ln_iv(xi2) + ALPHA0 + C_F0 / xi2
            es = (es1 + num_q_sl * (Iv(1, 1) + (H_TILDE * f0) ** 3) * epd) / v_full_lb
            if (ms + es).hi < bt_n.hi:
                bt_n, bm_n, be_n, tag = ms + es, ms, es, "sel"

        if tag == "bonf":
            cnt_bonf += 1
        elif tag == "bjs":
            cnt_bjs += 1
        else:
            cnt_sel += 1
        sum_aq = sum_aq + bm_n
        err_aq = err_aq + be_n

    q_sq = floor_root_int(spec.x_lo, 4)
    err_q2 = _q2_square_error_raw(x_lo_iv, log_x_hi, z, y, q_sq, li_r, epd) / v_full_lb
    err_one = (log_x_lo / x_lo_iv) / v_full_lb
    main_norm = sa_norm - Iv.from_str("0.5") * sum_aq
    tot_err = rem_a_norm + Iv.from_str("0.5") * err_aq + err_q2 + err_one
    net = main_norm - tot_err
    assert net.lo > 0, f"2c [{spec.x_lo}, {spec.x_hi}) failed: main={main_norm}, err={tot_err}, net={net}"
    note = f"{sa_tag} (F:{cnt_bonf} B:{cnt_bjs} S:{cnt_sel})"
    return SlabCertificate(
        regime="2c",
        x_lo=spec.x_lo,
        x_hi=spec.x_hi,
        z=z,
        y=y,
        main_lo=main_norm.lo,
        err_hi=tot_err.hi,
        net_lo=net.lo,
        sieve_net_lo=net.lo,
        rem_tol=(main_norm / tot_err).lo,
        note=note,
    )
