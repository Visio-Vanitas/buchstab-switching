"""
Pure-integer binary proof-by-reflection Lean 4 witness exporter & Bool-verifier
mirror for all 127 Regime 2 slabs (`2a`: 21, `2b`: 40, `2c`: 66). Zero `float`, zero `math`.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
import re

from .bonferroni_engine import comb_int
from .brun_block_sieve import _BRUN_LOW_CAPS, _candidate_ends, adm_count
from .dyadic_mirror import (
    A0_UB_DY,
    DYADIC_BIAS,
    DY_13841_UB,
    DY_13E1_UB,
    DY_16PI_LO4,
    DY_2964_UB,
    DY_6836_UB,
    DY_78E2_UB,
    DY_8PI_LO4,
    DY_FOUR,
    DY_LI2_UB,
    DY_LOG27000_HI,
    DY_LOG27000_LO,
    DY_ONE,
    DY_PI_LO4,
    DY_SEVEN,
    DY_SIX,
    DY_THREE,
    DY_TWO,
    DY_ZERO,
    LOG_W_DUMMY,
    ODD_PRIMES_EXACT,
    ODD_PRIME_ENTRIES,
    P_EXACT,
    V_PREFIX_27000_LB,
    Dyadic,
    calc_j_full_lb_2c_dy,
    check_log_dyadic,
    div_dyadic_lb,
    elem_sym_interval64,
    elem_sym_sums_dy,
    exact_inv_mul_pred_sum_ub,
    exact_inv_pred_sq_sum_ub,
    exact_inv_sub_one_sum_ub,
    exact_prime_count,
    exact_prod_one_sub_inv_pred_lb,
    exact_prod_one_sub_inv_pred_ub,
    exp_ub_dyadic,
    inv_phi_entries_ub,
    log_witness_and_bounds,
    solve_ble_mul_lb,
    solve_mul_ub_ble,
    sqrt_ceil_dyadic,
    sqrt_floor_dyadic,
    sum_g1_entries_ub,
    sum_g2_entries_ub,
    sum_pow_div_fact_ub,
    tree_filter_range,
    v2_entries_lb,
    v2_entries_ub,
)
from .interval import Iv, ceil_root_int, floor_root_int, pow_real_iv
from .schedule import SLABS_2A, SLABS_2B, SLABS_2C, Slab2ASpec, Slab2BSpec, Slab2CSpec

SMALL_ODD_ENTRIES_40 = ODD_PRIME_ENTRIES[:40]
SMALL_ODD_PRIMES_40 = ODD_PRIMES_EXACT[:40]


def _fact(n: int) -> int:
    r = 1
    for j in range(2, n + 1):
        r *= j
    return r


def _prod(ps: list[int]) -> int:
    r = 1
    for p in ps:
        r *= p
    return r


def _nat_log(n: int) -> tuple[dict, Dyadic, Dyadic]:
    return log_witness_and_bounds(Dyadic.of_nat(n))


def _check_sqrt_lb(x: Dyadic, s: Dyadic) -> bool:
    return s.mul_ub(s).ble(x)


def _check_sqrt_ub(x: Dyadic, s: Dyadic) -> bool:
    return x.ble(s.mul_lb(s))


def _dyadic_sqrt_lb(x: Dyadic) -> Dyadic:
    if x.m == 0:
        return DY_ZERO
    e_rel = x.e - DYADIC_BIAS
    sh = 82 + (e_rel & 1)
    half_e = (e_rel - sh) // 2
    if DYADIC_BIAS + half_e < 0:
        return DY_ZERO
    scaled = x.m << sh
    g = 1 << ((scaled.bit_length() - 1) // 2 + 1)
    while True:
        gn = (g + scaled // g) >> 1
        if gn >= g:
            break
        g = gn
    return Dyadic(g, DYADIC_BIAS + half_e).trim_lb(80)


def build_epd_witness(x_lo: int, log_lo: Dyadic, log_hi: Dyadic) -> tuple[Dyadic, dict, Dyadic]:
    sq_lb, sq_ub = sqrt_floor_dyadic(x_lo), sqrt_ceil_dyadic(x_lo)
    w_llx, llx_lb, _ = log_witness_and_bounds(log_lo)
    t_pi = solve_ble_mul_lb(DY_SEVEN, DY_16PI_LO4)
    t_inv_pi = solve_ble_mul_lb(DY_ONE, DY_PI_LO4)
    t_log1 = solve_ble_mul_lb(DY_SIX.add(t_inv_pi), DY_FOUR.mul_lb(log_lo))
    t_log2 = solve_ble_mul_lb(DY_SIX, log_lo.mul_lb(log_lo))
    t_li2 = solve_ble_mul_lb(DY_LI2_UB, sq_lb.mul_lb(log_lo))
    c_sum = t_pi.add(t_log1.add(t_log2.add(t_li2)))
    log_hi2 = log_hi.mul_ub(log_hi)
    epd1 = solve_ble_mul_lb(c_sum.mul_ub(log_hi2), sq_lb)
    epd2 = solve_ble_mul_lb(DY_13841_UB.mul_ub(log_hi2), Dyadic.of_nat(x_lo).mul_lb(llx_lb))
    epd_ub = epd1.add(epd2).trim_ub(80)
    loss1 = solve_ble_mul_lb(sq_ub.mul_ub(log_hi2), DY_8PI_LO4)
    loss2 = solve_ble_mul_lb(DY_13841_UB.mul_ub(log_hi2), llx_lb)
    rel_loss = solve_ble_mul_lb(loss1.add(loss2), Dyadic.of_nat(x_lo))
    li_ub = solve_ble_mul_lb(DY_ONE, DY_ONE.sub_lb(rel_loss))
    ew = {
        "xLoSqrtLb": sq_lb, "xLoSqrtUb": sq_ub, "wLLX": w_llx, "llxLb": llx_lb,
        "tPi": t_pi, "tInvPi": t_inv_pi, "tLog1": t_log1, "tLog2": t_log2,
        "tLi2": t_li2, "epd1": epd1, "epd2": epd2,
    }
    return epd_ub, ew, li_ub


def build_analytic_range_witness(
    a: int, b: int, a_lo: Dyadic, a_hi: Dyadic, b_lo: Dyadic, b_hi: Dyadic
) -> tuple[Dyadic, Dyadic, dict]:
    ratio_ub = solve_ble_mul_lb(b_hi, a_lo)
    if not DY_ONE.ble(ratio_ub):
        ratio_ub = DY_ONE
    w_ll, _, ll_ratio_ub = log_witness_and_bounds(ratio_ub)
    a_sq_ub, b_sq_ub = sqrt_ceil_dyadic(a), sqrt_ceil_dyadic(b)
    if 10**12 < b:
        b_sq_lb = DY_ZERO
        hi_err_ub = solve_ble_mul_lb(DY_6836_UB, b_lo)
    else:
        b_sq_lb = sqrt_floor_dyadic(b)
        hi_err_ub = solve_ble_mul_lb(DY_TWO, b_sq_lb.mul_lb(b_lo))
    lo_err_ub = solve_ble_mul_lb(DY_2964_UB, a_lo)
    tail_pred_ub = solve_ble_mul_lb(DY_ONE, Dyadic.of_nat(a - 1))
    sq_an = ll_ratio_ub.add(hi_err_ub.add(lo_err_ub.add(tail_pred_ub)))
    pm0 = solve_ble_mul_lb(Dyadic.of_nat(b - a), a_lo)
    pr0 = solve_ble_mul_lb(b_sq_ub.mul_ub(b_hi).add(a_sq_ub.mul_ub(a_hi)), DY_8PI_LO4)
    cnt0 = pm0.add(pr0.add(DY_ONE))
    pm1 = solve_ble_mul_lb(Dyadic.of_nat(b), b_lo.sub_lb(DY_TWO))
    pr1 = solve_ble_mul_lb(b_sq_ub.mul_ub(b_hi), DY_8PI_LO4)
    cnt1 = pm1.add(DY_LI2_UB.add(pr1))
    if cnt0.ble(cnt1):
        use_s, pm, pr, cnt_an = False, pm0, pr0, cnt0
    else:
        use_s, pm, pr, cnt_an = True, pm1, pr1, cnt1
    aw = {
        "wLL": w_ll, "ratioUb": ratio_ub, "llRatioUb": ll_ratio_ub,
        "aSqrtUb": a_sq_ub, "bSqrtUb": b_sq_ub, "bSqrtLb": b_sq_lb,
        "loErrUb": lo_err_ub, "hiErrUb": hi_err_ub, "tailPredUb": tail_pred_ub,
        "piUseSingle": use_s, "piMainUb": pm, "piRemUb": pr,
    }
    return sq_an, cnt_an, aw


def build_slice_bounds(
    q0: int, q1: int, l0_lo: Dyadic, l0_hi: Dyadic, l1_lo: Dyadic, l1_hi: Dyadic
) -> tuple[Dyadic, Dyadic, dict | None]:
    if q1 <= q0:
        return DY_ZERO, DY_ZERO, None
    if q1 <= P_EXACT:
        return exact_inv_sub_one_sum_ub(q0, q1).trim_ub(80), Dyadic.of_nat(exact_prime_count(q0, q1)), None
    if P_EXACT <= q0:
        sq_an, cnt_an, aw = build_analytic_range_witness(q0, q1, l0_lo, l0_hi, l1_lo, l1_hi)
        return sq_an.trim_ub(80), cnt_an.trim_ub(80), aw
    sq_an, cnt_an, aw = build_analytic_range_witness(P_EXACT, q1, DY_LOG27000_LO, DY_LOG27000_HI, l1_lo, l1_hi)
    sq_ex = exact_inv_sub_one_sum_ub(q0, P_EXACT)
    cnt_ex = Dyadic.of_nat(exact_prime_count(q0, P_EXACT))
    return sq_ex.add(sq_an).trim_ub(80), cnt_ex.add(cnt_an).trim_ub(80), aw


def build_mertens_tail(
    u: int, v: int, u_lo: Dyadic, u_hi: Dyadic, v_lo: Dyadic, v_hi: Dyadic, need_g: bool
) -> dict:
    if v <= u:
        return {"uLogLb": u_lo, "uLogUb": u_hi, "vLogLb": v_lo, "vLogUb": v_hi, "anW": None,
                "s1Ub": DY_ZERO, "s2Ub": DY_ZERO, "piUb": 0, "c2Ub": DY_ZERO, "gLb": DY_ONE if need_g else DY_ZERO}
    if v <= P_EXACT:
        s1 = exact_inv_sub_one_sum_ub(u, v).trim_ub(80)
        s2 = exact_inv_pred_sq_sum_ub(u, v).trim_ub(80)
        pi_u = exact_prime_count(u, v)
        g_lb = exact_prod_one_sub_inv_pred_lb(u, v).trim_lb(80) if (need_g and 3 <= u) else DY_ZERO
        return {"uLogLb": u_lo, "uLogUb": u_hi, "vLogLb": v_lo, "vLogUb": v_hi, "anW": None,
                "s1Ub": s1, "s2Ub": s2, "piUb": pi_u, "c2Ub": DY_ZERO, "gLb": g_lb}
    if P_EXACT <= u:
        s1_an, cnt_an, aw = build_analytic_range_witness(u, v, u_lo, u_hi, v_lo, v_hi)
        s1 = s1_an.trim_ub(80)
        s2 = solve_ble_mul_lb(DY_ONE, Dyadic.of_nat(u - 2))
        pi_u = cnt_an.ceil_nat()
        if need_g:
            c2 = solve_ble_mul_lb(Dyadic.of_nat(u - 1), Dyadic.of_nat(2 * (u - 2)))
            oke, e_ub = exp_ub_dyadic(s1.add(c2.mul_ub(s2)))
            assert oke
            g_lb = solve_mul_ub_ble(DY_ONE, e_ub)
        else:
            c2, g_lb = DY_ZERO, DY_ZERO
        return {"uLogLb": u_lo, "uLogUb": u_hi, "vLogLb": v_lo, "vLogUb": v_hi, "anW": aw,
                "s1Ub": s1, "s2Ub": s2, "piUb": pi_u, "c2Ub": c2, "gLb": g_lb}
    s1_ex = exact_inv_sub_one_sum_ub(u, P_EXACT)
    s2_ex = exact_inv_pred_sq_sum_ub(u, P_EXACT)
    cnt_ex = exact_prime_count(u, P_EXACT)
    s1_an, cnt_an, aw = build_analytic_range_witness(P_EXACT, v, DY_LOG27000_LO, DY_LOG27000_HI, v_lo, v_hi)
    s1 = s1_ex.add(s1_an).trim_ub(80)
    s2_tail = solve_ble_mul_lb(DY_ONE, Dyadic.of_nat(26998))
    s2 = s2_ex.add(s2_tail).trim_ub(80)
    while not (s2_ex.add(s2.sub_lb(s2_ex)).ble(s2) and DY_ONE.ble(s2.sub_lb(s2_ex).mul_lb(Dyadic.of_nat(26998)))):
        s2 = Dyadic(s2.m + 1, s2.e).trim_ub(80)
    pi_u = Dyadic.of_nat(cnt_ex).add(cnt_an).ceil_nat()
    if need_g and 3 <= u:
        c2 = solve_ble_mul_lb(Dyadic.of_nat(26999), Dyadic.of_nat(53996))
        oke, e_ub = exp_ub_dyadic(s1_an.add(c2.mul_ub(s2.sub_lb(s2_ex))))
        assert oke
        g_lb = solve_mul_ub_ble(exact_prod_one_sub_inv_pred_lb(u, P_EXACT), e_ub)
    else:
        c2, g_lb = DY_ZERO, DY_ZERO
    return {"uLogLb": u_lo, "uLogUb": u_hi, "vLogLb": v_lo, "vLogUb": v_hi, "anW": aw,
            "s1Ub": s1, "s2Ub": s2, "piUb": pi_u, "c2Ub": c2, "gLb": g_lb}


DUMMY_MERTENS_TAIL = build_mertens_tail(0, 0, DY_ZERO, DY_ZERO, DY_ZERO, DY_ZERO, False)


def _analytic_v2_lb_entries(p2e: list[dict]) -> tuple[Dyadic, Dyadic]:
    if not p2e:
        return DY_ZERO, DY_ONE
    p0 = p2e[0]["p"]
    c2 = solve_ble_mul_lb(Dyadic.of_nat(p0 - 1), Dyadic.of_nat(2 * (p0 - 2)))
    s1, s2 = sum_g1_entries_ub(p2e), sum_g2_entries_ub(p2e)
    oke, e_ub = exp_ub_dyadic(s1.add(c2.mul_ub(s2)))
    assert oke
    return c2, solve_mul_ub_ble(DY_ONE, e_ub)


def _build_slices_geom(z: int, y: int, k_sl: int) -> list[int]:
    r_sl = pow_real_iv(Iv(y, y) / Iv(z, z), Iv.from_frac(Fraction(1, k_sl)))
    bpts, cur = [z], Iv(z, z)
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


@dataclass(frozen=True)
class Witness2abResult:
    slab: dict
    main_lo_dec: Decimal
    err_hi_dec: Decimal
    sieve_net_lo_dec: Decimal


@dataclass(frozen=True)
class Witness2cResult:
    slab: dict
    main_lo_dec: Decimal
    err_hi_dec: Decimal
    note: str


_CUTOFF_2AB_CACHE: dict[int, list[tuple]] = {}


def _get_exact_ev_opts(cutoffs: tuple[int, ...]) -> list[tuple]:
    out = []
    for zs in cutoffs:
        if zs not in _CUTOFF_2AB_CACHE:
            es = tree_filter_range(3, zs)
            ps = [e["p"] for e in es]
            v_sub_ub = exact_prod_one_sub_inv_pred_ub(3, zs).trim_ub(80)
            opts = []
            for aq in range(0, min(len(ps), 11), 2):
                q1e, p2e = es[:aq], es[aq:]
                q1, p2 = ps[:aq], ps[aq:]
                qq, inv_qq = _prod(q1), inv_phi_entries_ub(q1e)
                dp = elem_sym_interval64(p2e, min(8, len(p2e)))
                g_p2_lb = v2_entries_lb(p2e)
                c2_ub, g_sub_lb = _analytic_v2_lb_entries(p2e)
                for mev in (1, 2, 3, 4):
                    k = 2 * mev
                    if k > len(p2):
                        continue
                    prod_ev = qq * _prod(p2[-k:])
                    if not p2e:
                        rat_ub, ip2_ub = DY_ONE, inv_qq.trim_ub(80)
                    else:
                        e_lo, e_hi, o_lo, o_hi = elem_sym_sums_dy(dp[: k + 1])
                        if not o_lo.ble(e_hi):
                            rat_ub = DY_ZERO
                        else:
                            rat_ub = solve_ble_mul_lb(e_hi.sub_lb(o_lo), g_p2_lb)
                            while not e_hi.ble(o_lo.add(rat_ub.mul_lb(g_p2_lb))):
                                rat_ub = Dyadic(rat_ub.m + 1, rat_ub.e).trim_ub(80)
                        ip2_ub = inv_qq.mul_ub(e_hi.add(o_hi)).trim_ub(80)
                    nd_ev = (1 << aq) * sum(comb_int(len(p2), j) for j in range(k + 1))
                    opts.append((prod_ev, v_sub_ub, rat_ub, ip2_ub, nd_ev, zs, aq, mev, 1, c2_ub, g_sub_lb, DY_ZERO))
            _CUTOFF_2AB_CACHE[zs] = opts
        out.extend(_CUTOFF_2AB_CACHE[zs])
    return out


def _p_sub_opts(es_full: list[dict], sqrt_x_lo: int) -> list[tuple]:
    opts, prod = [], 1
    for k_sub, e in enumerate(es_full, 1):
        p = e["p"]
        prod *= p
        if prod > sqrt_x_lo:
            break
        v_sub_ub = exact_prod_one_sub_inv_pred_ub(3, p + 1).trim_ub(80)
        ip2_ub = inv_phi_entries_ub(es_full[:k_sub]).trim_ub(80)
        opts.append((prod, v_sub_ub, DY_ONE, ip2_ub, 1 << k_sub, p + 1, k_sub, 0, 1, DY_ZERO, DY_ONE, DY_ZERO))
    return opts


def _analytic_ev_opts_2ab(z: int, sqrt_x_lo: int) -> list[tuple]:
    es = tree_filter_range(3, z)
    ps = [e["p"] for e in es]
    v_sub_ub = exact_prod_one_sub_inv_pred_ub(3, z).trim_ub(80)
    opts = []
    for aq in (0, 2, 4, 6, 8, 10):
        if aq >= len(ps):
            break
        q1e, p2e = es[:aq], es[aq:]
        q1, p2 = ps[:aq], ps[aq:]
        qq = _prod(q1)
        if qq > sqrt_x_lo:
            break
        s1_ub = sum_g1_entries_ub(p2e)
        c2_ub, g_sub_lb = _analytic_v2_lb_entries(p2e)
        oke, e_s1 = exp_ub_dyadic(s1_ub)
        assert oke
        ip2_ub = inv_phi_entries_ub(q1e).mul_ub(e_s1).trim_ub(80)
        for mev in (1, 2, 3, 4):
            k = 2 * mev
            if k > len(p2) or (prod_ev := qq * _prod(p2[-k:])) > sqrt_x_lo:
                continue
            err_den = Dyadic.of_nat(_fact(k + 1)).mul_lb(g_sub_lb)
            err_ub = solve_ble_mul_lb(s1_ub.pow_ub(k + 1), err_den)
            rat_ub = DY_ONE.add(err_ub).trim_ub(80)
            nd_ev = (1 << aq) * sum(comb_int(len(p2), j) for j in range(k + 1))
            opts.append((prod_ev, v_sub_ub, rat_ub, ip2_ub, nd_ev, z, aq, mev, 2, c2_ub, g_sub_lb, err_ub))
    return opts


def _mk_sl2ab(
    q0, q1, kind, zs, aq, mev, nd, dm, w0, w1, aw, sq, cnt, l0, l1,
    ip2, vsub, gsub, rat, c2, err, msl, esl
) -> dict:
    return {
        "q0": q0, "q1": q1, "kind": kind, "zSub": zs, "aQ": aq, "mEv": mev, "nD": nd, "dMax": dm,
        "wQ0Log": w0, "wQ1Log": w1, "anW": aw, "sqUb": sq, "cntUb": cnt,
        "logQ0Lb": l0[0], "logQ0Ub": l0[1], "logQ1Lb": l1[0], "logQ1Ub": l1[1],
        "ip2": ip2, "vSubUb": vsub, "gSubLb": gsub, "ratUb": rat, "c2Ub": c2, "errUb": err,
        "mSl": msl, "eSl": esl,
    }


def build_slab_2ab_witness(reg: str, spec: Slab2ASpec | Slab2BSpec) -> Witness2abResult:
    z = spec.z if isinstance(spec, Slab2ASpec) else ceil_root_int(spec.x_hi, spec.m_div)
    y = max(ceil_root_int(spec.x_hi + 1, 4), ceil_root_int((spec.x_hi + z - 1) // z, 3))
    sqrt_x_lo, q_sq = floor_root_int(spec.x_lo, 2), floor_root_int(spec.x_lo, 4)
    w_xlo, x_lo_lb, x_lo_ub = _nat_log(spec.x_lo)
    w_xhi, _, x_hi_ub = _nat_log(spec.x_hi)
    epd_ub, epd_w, _ = build_epd_witness(spec.x_lo, x_lo_lb, x_lo_ub)
    es = tree_filter_range(3, z)
    ps = [e["p"] for e in es]
    q1, p2, p2e, k_odd = ps[: spec.a], ps[spec.a :], es[spec.a :], spec.m_odd
    d_max = _prod(q1) * _prod(p2[-k_odd:] if k_odd > 0 else [])
    n_d = (1 << spec.a) * sum(comb_int(len(p2), j) for j in range(k_odd + 1))
    v_full_lb = exact_prod_one_sub_inv_pred_lb(3, z).trim_lb(80)
    v_full_ub = exact_prod_one_sub_inv_pred_ub(3, z).trim_ub(80)
    if not p2e:
        rat_lb, use_ana, g_lb, c2_ub, err_ub = DY_ONE, False, DY_ZERO, DY_ZERO, DY_ZERO
    elif z <= 1500:
        e_lo, _, _, o_hi = elem_sym_sums_dy(elem_sym_interval64(p2e, k_odd))
        g_p2_ub = v2_entries_ub(p2e)
        rat_lb = solve_mul_ub_ble(e_lo.sub_lb(o_hi), g_p2_ub)
        while rat_lb.m > 0 and not rat_lb.mul_ub(g_p2_ub).add(o_hi).ble(e_lo):
            rat_lb = Dyadic(rat_lb.m - 1, rat_lb.e)
        use_ana, g_lb, c2_ub, err_ub = False, DY_ZERO, DY_ZERO, DY_ZERO
    else:
        c2_ub, g_lb = _analytic_v2_lb_entries(p2e)
        s1_ub = sum_g1_entries_ub(p2e)
        err_den = Dyadic.of_nat(_fact(k_odd + 1)).mul_lb(g_lb)
        err_ub = solve_ble_mul_lb(s1_ub.pow_ub(k_odd + 1), err_den)
        rat_lb = DY_ONE.sub_lb(err_ub).trim_lb(80)
        use_ana = True
    if reg == "2a":
        cutoffs = tuple(sorted(set([c for c in (11, 17, 23, 29, 37) if c <= z] + [z])))
        bpts = (_build_slices_geom(z, P_EXACT, 48)[:-1] + _build_slices_geom(P_EXACT, y, 4)) if z < P_EXACT < y else _build_slices_geom(z, y, 64)
        ev_opts = _p_sub_opts(es, sqrt_x_lo) + _get_exact_ev_opts(cutoffs)
    else:
        cutoffs = tuple(sorted(set([c for c in (29, 89, 251, 600, 1500) if c < z] + ([z] if z <= 1500 else []))))
        bpts = _build_slices_geom(z, y, 56)
        ev_opts = _p_sub_opts(es[:18], sqrt_x_lo) + _get_exact_ev_opts(cutoffs) + (_analytic_ev_opts_2ab(z, sqrt_x_lo) if z > 1500 else [])
    slices_w, sum_m, sum_e = [], DY_ZERO, DY_ZERO
    for q0, q1s in zip(bpts[:-1], bpts[1:]):
        w0, l0_lo, l0_hi = _nat_log(q0) if P_EXACT <= q0 else (LOG_W_DUMMY, DY_ZERO, DY_ZERO)
        w1, l1_lo, l1_hi = _nat_log(q1s) if P_EXACT < q1s else (LOG_W_DUMMY, DY_ZERO, DY_ZERO)
        sq_ub, cnt_ub, aw = build_slice_bounds(q0, q1s, l0_lo, l0_hi, l1_lo, l1_hi)
        q_max, best = q1s - 1, None
        if q_max * q_max <= spec.x_lo:
            m0, e0 = sq_ub, cnt_ub.mul_ub(epd_ub).trim_ub(80)
            best = (m0.add(e0), _mk_sl2ab(q0, q1s, 0, 0, 0, 0, 0, 0, w0, w1, aw, sq_ub, cnt_ub,
                                          (l0_lo, l0_hi), (l1_lo, l1_hi), DY_ZERO, DY_ZERO, DY_ZERO, DY_ZERO, DY_ZERO, DY_ZERO, m0, e0))
        for pe, v_sub_ub, rat_ub, ip2_ub, nd_ev, zs, aq, mev, kind, c2_s, g_sub_lb, err_s in ev_opts:
            if q_max * pe > sqrt_x_lo:
                continue
            m_sl = sq_ub.mul_ub(v_sub_ub).mul_ub(rat_ub).trim_ub(80)
            e_sl = cnt_ub.mul_ub(Dyadic.of_nat(nd_ev).add(ip2_ub.add(rat_ub))).mul_ub(epd_ub).trim_ub(80)
            if best is None or m_sl.add(e_sl).blt(best[0]):
                best = (m_sl.add(e_sl), _mk_sl2ab(q0, q1s, kind, zs, aq, mev, nd_ev, pe, w0, w1, aw, sq_ub, cnt_ub,
                                                  (l0_lo, l0_hi), (l1_lo, l1_hi), ip2_ub, v_sub_ub, g_sub_lb, rat_ub, c2_s, err_s, m_sl, e_sl))
        assert best is not None
        slices_w.append(best[1])
        sum_m, sum_e = sum_m.add(best[1]["mSl"]), sum_e.add(best[1]["eSl"])
    q_end = min(y, q_sq + 1)
    s_ex = exact_inv_mul_pred_sum_ub(z, min(q_end, P_EXACT))
    inv_tail_ub = solve_ble_mul_lb(DY_ONE, Dyadic.of_nat(P_EXACT - 1)) if P_EXACT < q_end else DY_ZERO
    s_q2_ub = (s_ex.add(inv_tail_ub) if P_EXACT < q_end else s_ex).trim_ub(80)
    w_end, e_lo, e_hi = _nat_log(q_end) if P_EXACT < q_end else (LOG_W_DUMMY, DY_ZERO, DY_ZERO)
    _, cnt_lo_ub, an_end_w = build_slice_bounds(z, q_end, x_lo_lb, x_lo_ub, e_lo, e_hi)
    tail_q2_ub = DY_ZERO if y <= q_sq + 1 else solve_ble_mul_lb(x_hi_ub, Dyadic.of_nat(q_sq))
    inner_ub = s_q2_ub.add(cnt_lo_ub.mul_ub(epd_ub).add(DY_ZERO if y <= q_sq + 1 else tail_q2_ub))
    err_q2_ub = inner_ub.div_pow2_ub(1).trim_ub(80)
    main_dy = v_full_lb.mul_lb(rat_lb).sub_lb(sum_m.div_pow2_ub(1))
    err_dy = Dyadic.of_nat(n_d).mul_ub(epd_ub).add(err_q2_ub).add(sum_e.div_pow2_ub(1))
    snet_dy = div_dyadic_lb(main_dy.sub_lb(err_dy), v_full_ub)
    slab_w = {
        "xLoLogLb": x_lo_lb, "xLoLogUb": x_lo_ub, "xHiLogUb": x_hi_ub,
        "wXLoLog": w_xlo, "wXHiLog": w_xhi, "epdUb": epd_ub, "epdW": epd_w,
        "lower": {"a": spec.a, "mOdd": (k_odd - 1) // 2, "nD": n_d, "dMax": d_max,
                  "useAnalytic": use_ana, "ratLb": rat_lb, "vFullLb": v_full_lb,
                  "vFullUb": v_full_ub, "gLb": g_lb, "c2Ub": c2_ub, "errUb": err_ub},
        "slices": slices_w,
        "square": {"qSq": q_sq, "sQ2Ub": s_q2_ub, "cntLoUb": cnt_lo_ub, "logEndLb": e_lo, "logEndUb": e_hi,
                   "wLogEnd": w_end, "anEndW": an_end_w, "invTailUb": inv_tail_ub, "tailQ2Ub": tail_q2_ub, "errQ2Ub": err_q2_ub},
    }
    return Witness2abResult(slab_w, main_dy.to_dec_floor(18), err_dy.to_dec_ceil(18), snet_dy.to_dec_floor(18))


def build_slab_2c_witness(spec: Slab2CSpec) -> Witness2cResult:
    z = ceil_root_int(spec.x_hi, spec.m_div)
    y = max(ceil_root_int(spec.x_hi + 1, 4), ceil_root_int((spec.x_hi + z - 1) // z, 3))
    sqrt_x_lo, q_sq = floor_root_int(spec.x_lo, 2), floor_root_int(spec.x_lo, 4)
    w_xlo, x_lo_lb, x_lo_ub = _nat_log(spec.x_lo)
    w_xhi, _, x_hi_ub = _nat_log(spec.x_hi)
    w_z, z_lo, z_hi = _nat_log(z)
    epd_ub, epd_w, li_r_ub = build_epd_witness(spec.x_lo, x_lo_lb, x_lo_ub)
    if z <= P_EXACT:
        v_full_w = None
        v_full_lb = exact_prod_one_sub_inv_pred_lb(3, z).trim_lb(80)
    else:
        v_full_w = build_mertens_tail(P_EXACT, z, DY_LOG27000_LO, DY_LOG27000_HI, z_lo, z_hi, True)
        v_full_lb = V_PREFIX_27000_LB.mul_lb(v_full_w["gLb"]).trim_lb(80)
    best_low = None
    for mo_k in (7, 9, 11):
        z_k, qp = z**mo_k, 1
        if z_k > sqrt_x_lo:
            break
        for a in range(35):
            if a > 0:
                qp *= SMALL_ODD_PRIMES_40[a - 1]
            p_min = SMALL_ODD_PRIMES_40[a]
            if qp * z_k > sqrt_x_lo or p_min >= z:
                break
            tw = build_mertens_tail(p_min, z, DY_ZERO, DY_ZERO, z_lo, z_hi, True)
            s1_ub, g_lb, pi_z_ub = tw["s1Ub"], tw["gLb"], Dyadic.of_nat(tw["piUb"])
            err_den = Dyadic.of_nat(_fact(mo_k + 1)).mul_lb(g_lb)
            err_ub = solve_ble_mul_lb(s1_ub.pow_ub(mo_k + 1), err_den)
            if err_ub.ble(DY_ONE):
                rat_lb = DY_ONE.sub_lb(err_ub).trim_lb(80)
                nd_fact_ub = sum_pow_div_fact_ub(pi_z_ub, mo_k)
                n_d = nd_fact_ub.mul_pow2(a).ceil_nat()
                rem_norm = solve_ble_mul_lb(Dyadic.of_nat(n_d).mul_ub(epd_ub), v_full_lb)
                score = rat_lb.sub_lb(rem_norm)
                if best_low is None or best_low[0].blt(score):
                    lo_cand = {
                        "isBrun": False, "a": a, "mOdd": (mo_k - 1) // 2, "ends": [], "caps": [],
                        "nD": n_d, "dMax": qp * z_k, "tail": tw, "c2Ub": tw["c2Ub"], "errUb": err_ub,
                        "ndFactUb": nd_fact_ub, "piZUb": pi_z_ub, "gLb": g_lb, "s1Ub": s1_ub,
                        "ratLb": rat_lb, "remANormUb": rem_norm, "brunSteps": [],
                    }
                    best_low = (score, lo_cand, f"Bonf(a={a},m={mo_k})")
    log_cache: dict[int, tuple[dict, Dyadic, Dyadic]] = {z: (w_z, z_lo, z_hi)}
    tail_z_cache: dict[int, dict] = {}

    def get_log(x: int) -> tuple[dict, Dyadic, Dyadic]:
        if x < P_EXACT:
            return LOG_W_DUMMY, DY_ZERO, DY_ZERO
        if x not in log_cache:
            log_cache[x] = _nat_log(x)
        return log_cache[x]

    def get_tail_z(nxt: int) -> dict:
        if nxt not in tail_z_cache:
            _, n_lo, n_hi = get_log(nxt)
            tail_z_cache[nxt] = build_mertens_tail(nxt, z, n_lo, n_hi, z_lo, z_hi, True)
        return tail_z_cache[nxt]

    for a in (0, 2, 4, 6, 8, 10, 12):
        qp = _prod(SMALL_ODD_PRIMES_40[:a])
        pa1 = 3 if a == 0 else SMALL_ODD_PRIMES_40[a - 1] + 1
        if pa1 >= z or qp >= sqrt_x_lo:
            break
        budget, local_best = sqrt_x_lo // qp, None
        for caps in _BRUN_LOW_CAPS:
            for ends in _candidate_ends(caps, z, pa1, budget):
                e_tot, terms = DY_ZERO, []
                for i in range(1, len(ends)):
                    tw_z = get_tail_z(ends[i])
                    err_den = Dyadic.of_nat(_fact(caps[i - 1] + 1)).mul_lb(tw_z["gLb"])
                    term_ub = solve_ble_mul_lb(tw_z["s1Ub"].pow_ub(caps[i - 1] + 1), err_den)
                    terms.append((tw_z, term_ub))
                    e_tot = e_tot.add(term_ub)
                if e_tot.ble(DY_ONE) and (local_best is None or e_tot.blt(local_best[0])):
                    local_best = (e_tot, caps, ends, terms)
        if local_best is not None:
            e_tot, caps, ends, terms = local_best
            steps, szs = [], []
            for idx_b, (cur, nxt, cap) in enumerate(zip(ends, ends[1:], caps)):
                w_nxt, n_lo, n_hi = get_log(nxt) if P_EXACT <= nxt else (LOG_W_DUMMY, DY_ZERO, DY_ZERO)
                if cur == z:
                    w_cur, c_lo, c_hi = LOG_W_DUMMY, z_lo, z_hi
                elif P_EXACT < cur:
                    w_cur, c_lo, c_hi = get_log(cur)
                else:
                    w_cur, c_lo, c_hi = LOG_W_DUMMY, DY_ZERO, DY_ZERO
                b_tail = build_mertens_tail(nxt, cur, n_lo, n_hi, c_lo, c_hi, False)
                t_tail, term_ub = terms[idx_b]
                szs.append(b_tail["piUb"])
                steps.append({
                    "cur": cur, "nxt": nxt, "cap": cap, "blockCnt": b_tail["piUb"],
                    "wCurLog": w_cur, "wNxtLog": w_nxt, "bTail": b_tail, "tTail": t_tail, "termUb": term_ub,
                })
            n_d = (1 << a) * adm_count(caps, szs)
            mod_b, prev = 1, 0
            for idx_b, m_cap in enumerate(caps):
                mod_b, prev = mod_b * (ends[idx_b] ** (m_cap - prev)), m_cap
            rat_lb = DY_ONE.sub_lb(e_tot).trim_lb(80)
            rem_norm = solve_ble_mul_lb(Dyadic.of_nat(n_d).mul_ub(epd_ub), v_full_lb)
            score = rat_lb.sub_lb(rem_norm)
            if best_low is None or best_low[0].blt(score):
                lo_cand = {
                    "isBrun": True, "a": a, "mOdd": 0, "ends": list(ends), "caps": list(caps),
                    "nD": n_d, "dMax": qp * mod_b, "tail": DUMMY_MERTENS_TAIL,
                    "c2Ub": DY_ZERO, "errUb": DY_ZERO, "ndFactUb": DY_ZERO, "piZUb": DY_ZERO,
                    "gLb": DY_ZERO, "s1Ub": DY_ZERO, "ratLb": rat_lb, "remANormUb": rem_norm,
                    "brunSteps": steps,
                }
                best_low = (score, lo_cand, f"Brun(a={a},caps=({','.join(str(c) for c in caps)}))")
    assert best_low is not None
    _, lo_w, sa_tag = best_low
    bpts, ev_2c = _build_slices_geom(z, y, 48), []
    for zs in (29, 89, 251, 600, 1500):
        if zs < z:
            for pe, v_sub_ub, rat_ub, ip2_ub, nd_ev, _, aq, mev, _, c2_s, g_sub_lb, err_s in _get_exact_ev_opts((zs,)):
                if pe <= sqrt_x_lo:
                    m_rat_ub = solve_ble_mul_lb(v_sub_ub.mul_ub(rat_ub), v_full_lb)
                    ev_2c.append((pe, zs, aq, mev, nd_ev, ip2_ub, v_sub_ub, g_sub_lb, rat_ub, m_rat_ub, c2_s, err_s, None))
    for aq in (0, 2, 4, 6, 8, 10):
        p_min, qq = SMALL_ODD_PRIMES_40[aq], _prod(SMALL_ODD_PRIMES_40[:aq])
        if p_min >= z or qq > sqrt_x_lo:
            break
        tw = build_mertens_tail(p_min, z, DY_ZERO, DY_ZERO, z_lo, z_hi, True)
        s1_ub, g_sub_lb = tw["s1Ub"], tw["gLb"]
        oke, e_s1 = exp_ub_dyadic(s1_ub)
        assert oke
        ip2_ub = inv_phi_entries_ub(SMALL_ODD_ENTRIES_40[:aq]).mul_ub(e_s1).trim_ub(80)
        for mev in (1, 2, 3, 4):
            k, pe = 2 * mev, qq * (z ** (2 * mev))
            if pe > sqrt_x_lo:
                break
            err_den = Dyadic.of_nat(_fact(k + 1)).mul_lb(g_sub_lb)
            err_ub = solve_ble_mul_lb(s1_ub.pow_ub(k + 1), err_den)
            rat_ub = DY_ONE.add(err_ub).trim_ub(80)
            nd_ev = sum_pow_div_fact_ub(Dyadic.of_nat(tw["piUb"]), k).mul_pow2(aq).ceil_nat()
            ev_2c.append((pe, z, aq, mev, nd_ev, ip2_ub, DY_ZERO, g_sub_lb, rat_ub, rat_ub, tw["c2Ub"], err_ub, tw))
    l4 = x_lo_ub.pow_ub(4)
    hq_cands = []
    for num_k, den_k in ((2, 1000), (8, 1000), (3, 100), (15, 100), (8, 10)):
        k_dy = solve_ble_mul_lb(Dyadic.of_nat(num_k), Dyadic.of_nat(den_k))
        hq = div_dyadic_lb(epd_w["xLoSqrtLb"], k_dy.mul_ub(l4))
        while hq.m > 0 and not hq.mul_ub(hq).ble(Dyadic.of_nat(spec.x_lo)):
            hq = Dyadic(hq.m - 1, hq.e)
        if hq.m > 0:
            hq_cands.append(hq)
    z_cap_iv = pow_real_iv(Iv(z, z), Iv.from_frac(Fraction(297, 100)))
    z_cap_dy = Dyadic.of_nat(min(int(z_cap_iv.lo), z**3 - 1)).trim_lb(80)
    jf_cache: dict[tuple[int, int], tuple[dict, Dyadic, Dyadic, Dyadic]] = {}
    slices_w, sum_m, sum_e, cnt_bonf, cnt_sel = [], DY_ZERO, DY_ZERO, 0, 0
    for q0, q1s in zip(bpts[:-1], bpts[1:]):
        w0, l0_lo, l0_hi = get_log(q0) if P_EXACT <= q0 else (LOG_W_DUMMY, DY_ZERO, DY_ZERO)
        w1, l1_lo, l1_hi = get_log(q1s) if P_EXACT < q1s else (LOG_W_DUMMY, DY_ZERO, DY_ZERO)
        sq_ub, cnt_ub, aw = build_slice_bounds(q0, q1s, l0_lo, l0_hi, l1_lo, l1_hi)
        q_max, best = q1s - 1, None
        for pe, zs, aq, mev, nd_ev, ip2_ub, v_sub_ub, g_sub_lb, rat_ub, m_rat_ub, c2_s, err_s, tail_w in ev_2c:
            if q_max * pe > sqrt_x_lo:
                continue
            m_sl = sq_ub.mul_ub(m_rat_ub).trim_ub(80)
            e_num = cnt_ub.mul_ub(Dyadic.of_nat(nd_ev).add(ip2_ub.add(rat_ub))).mul_ub(epd_ub)
            e_sl = solve_ble_mul_lb(e_num, v_full_lb)
            if best is None or m_sl.add(e_sl).blt(best[0]):
                mode = {"isSelberg": False, "zSub": zs, "aQ": aq, "mEv": mev, "nD": nd_ev, "dMax": pe,
                        "ip2": ip2_ub, "vSubUb": v_sub_ub, "gSubLb": g_sub_lb, "ratUb": rat_ub,
                        "mRatUb": m_rat_ub, "c2Ub": c2_s, "errUb": err_s, "tailW": tail_w}
                best = (m_sl.add(e_sl), {"q0": q0, "q1": q1s, "wQ0Log": w0, "wQ1Log": w1, "anW": aw,
                                         "logQ0Lb": l0_lo, "logQ0Ub": l0_hi, "logQ1Lb": l1_lo, "logQ1Ub": l1_hi,
                                         "sqUb": sq_ub, "cntUb": cnt_ub, "mSl": m_sl, "eSl": e_sl, "mode": mode})
        for hq in hq_cands:
            xi = _dyadic_sqrt_lb(div_dyadic_lb(hq, Dyadic.of_nat(q_max)))
            if z_cap_dy.blt(xi):
                xi = z_cap_dy
            while xi.m > 0 and not Dyadic.of_nat(q_max).mul_ub(xi.mul_ub(xi)).ble(hq):
                xi = Dyadic(xi.m - 1, xi.e).trim_lb(80)
            if not (DY_ONE.ble(xi) and xi.blt(Dyadic.of_nat(z**3))):
                continue
            xi_key = (xi.m, xi.e)
            if xi_key not in jf_cache:
                w_xi, xlo, xhi = log_witness_and_bounds(xi)
                jf_cache[xi_key] = (w_xi, xlo, xhi, calc_j_full_lb_2c_dy(z, z_lo, z_hi, xi, xlo, xhi))
            w_xi, xi_lo, xi_hi, jf_lb = jf_cache[xi_key]
            if jf_lb.m <= 0:
                continue
            m_sl = solve_ble_mul_lb(sq_ub, v_full_lb.mul_lb(jf_lb))
            s3c_a, s3c_b = cnt_ub.mul_ub(xi.mul_ub(xi)), sq_ub.mul_ub(hq)
            s3c = (s3c_a if s3c_a.ble(s3c_b) else s3c_b).trim_ub(80)
            es1 = s3c.div_pow2_ub(4).mul_ub(xi_hi.mul_pow2(1).add(DY_SIX).pow_ub(2).mul_ub(epd_ub)).trim_ub(80)
            inv78 = solve_ble_mul_lb(DY_78E2_UB, xi.mul_lb(xi))
            f0 = xi_hi.add(A0_UB_DY.add(inv78)).trim_ub(80)
            e_num = es1.add(cnt_ub.mul_ub(DY_ONE.add(DY_13E1_UB.mul_ub(f0).pow_ub(3))).mul_ub(epd_ub))
            e_sl = solve_ble_mul_lb(e_num, v_full_lb)
            if best is None or m_sl.add(e_sl).blt(best[0]):
                mode = {"isSelberg": True, "hQ": hq, "xiQLb": xi, "xiQUb": xi, "xiQLogLb": xi_lo, "xiQLogUb": xi_hi,
                        "jfLb": jf_lb, "s3cUb": s3c, "es1Ub": es1, "f0Ub": f0, "invXiSq78Ub": inv78, "wXiLog": w_xi}
                best = (m_sl.add(e_sl), {"q0": q0, "q1": q1s, "wQ0Log": w0, "wQ1Log": w1, "anW": aw,
                                         "logQ0Lb": l0_lo, "logQ0Ub": l0_hi, "logQ1Lb": l1_lo, "logQ1Ub": l1_hi,
                                         "sqUb": sq_ub, "cntUb": cnt_ub, "mSl": m_sl, "eSl": e_sl, "mode": mode})
        assert best is not None
        cnt_sel += int(best[1]["mode"]["isSelberg"])
        cnt_bonf += int(not best[1]["mode"]["isSelberg"])
        slices_w.append(best[1])
        sum_m, sum_e = sum_m.add(best[1]["mSl"]), sum_e.add(best[1]["eSl"])
    q_end = min(y, q_sq + 1)
    if z <= P_EXACT:
        s_ex = exact_inv_mul_pred_sum_ub(z, min(q_end, P_EXACT))
        inv_tail_ub = solve_ble_mul_lb(DY_ONE, Dyadic.of_nat(P_EXACT - 1)) if P_EXACT < q_end else DY_ZERO
        s_q2_ub = (s_ex.add(inv_tail_ub) if P_EXACT < q_end else s_ex).trim_ub(80)
    else:
        inv_tail_ub = DY_ZERO
        s_q2_ub = solve_ble_mul_lb(DY_ONE, Dyadic.of_nat(z - 1))
    w_end, e_lo, e_hi = get_log(q_end) if P_EXACT < q_end else (LOG_W_DUMMY, DY_ZERO, DY_ZERO)
    _, cnt_lo_ub, an_end_w = build_slice_bounds(z, q_end, z_lo, z_hi, e_lo, e_hi)
    tail_q2_ub = DY_ZERO if y <= q_sq + 1 else solve_ble_mul_lb(x_hi_ub, Dyadic.of_nat(q_sq))
    inner_ub = s_q2_ub.add(cnt_lo_ub.mul_ub(epd_ub).add(DY_ZERO if y <= q_sq + 1 else tail_q2_ub))
    err_q2_ub = inner_ub.div_pow2_ub(1).trim_ub(80)
    err_q2_norm = solve_ble_mul_lb(err_q2_ub, v_full_lb)
    main_dy = lo_w["ratLb"].sub_lb(sum_m.div_pow2_ub(1))
    err_dy = lo_w["remANormUb"].add(err_q2_norm).add(sum_e.div_pow2_ub(1))
    slab_w = {
        "xLoLogLb": x_lo_lb, "xLoLogUb": x_lo_ub, "xHiLogUb": x_hi_ub, "zLogLb": z_lo, "zLogUb": z_hi,
        "wXLoLog": w_xlo, "wXHiLog": w_xhi, "wZLog": w_z, "epdUb": epd_ub, "epdW": epd_w,
        "liRatioUb": li_r_ub, "vFullLb": v_full_lb, "vFullW": v_full_w,
        "lower": lo_w, "slices": slices_w,
        "square": {"qSq": q_sq, "sQ2Ub": s_q2_ub, "cntLoUb": cnt_lo_ub, "logEndLb": e_lo, "logEndUb": e_hi,
                   "wLogEnd": w_end, "anEndW": an_end_w, "invTailUb": inv_tail_ub, "tailQ2Ub": tail_q2_ub, "errQ2Ub": err_q2_ub},
        "errQ2NormUb": err_q2_norm,
    }
    return Witness2cResult(slab_w, main_dy.to_dec_floor(18), err_dy.to_dec_ceil(18), f"{sa_tag} (F:{cnt_bonf} S:{cnt_sel})")


# --- Exact Lean Bool Verifier Mirrors ---

def check_epd_witness_py(x_lo: int, log_lo: Dyadic, log_hi: Dyadic, epd_ub: Dyadic, w: dict) -> bool:
    llx_ub = w["llxLb"].add(DY_ONE)
    c_sum = w["tPi"].add(w["tLog1"].add(w["tLog2"].add(w["tLi2"])))
    log_hi2 = log_hi.mul_ub(log_hi)
    return (
        4 * 10**18 <= x_lo and DY_THREE.ble(log_lo) and log_lo.ble(log_hi)
        and _check_sqrt_lb(Dyadic.of_nat(x_lo), w["xLoSqrtLb"]) and w["xLoSqrtLb"].m > 0
        and _check_sqrt_ub(Dyadic.of_nat(x_lo), w["xLoSqrtUb"])
        and check_log_dyadic(log_lo, w["wLLX"], w["llxLb"], llx_ub) and w["llxLb"].m > 0
        and DY_SEVEN.ble(w["tPi"].mul_lb(DY_16PI_LO4))
        and DY_ONE.ble(w["tInvPi"].mul_lb(DY_PI_LO4))
        and DY_SIX.add(w["tInvPi"]).ble(w["tLog1"].mul_lb(DY_FOUR.mul_lb(log_lo)))
        and DY_SIX.ble(w["tLog2"].mul_lb(log_lo.mul_lb(log_lo)))
        and DY_LI2_UB.ble(w["tLi2"].mul_lb(w["xLoSqrtLb"].mul_lb(log_lo)))
        and c_sum.mul_ub(log_hi2).ble(w["epd1"].mul_lb(w["xLoSqrtLb"]))
        and DY_13841_UB.mul_ub(log_hi2).ble(w["epd2"].mul_lb(Dyadic.of_nat(x_lo).mul_lb(w["llxLb"])))
        and w["epd1"].add(w["epd2"]).ble(epd_ub)
    )


def check_analytic_range_py(
    a: int, b: int, a_lo: Dyadic, a_hi: Dyadic, b_lo: Dyadic, b_hi: Dyadic, sq_ub: Dyadic, cnt_ub: Dyadic, w: dict
) -> bool:
    ok_hi = (DY_6836_UB.ble(w["hiErrUb"].mul_lb(b_lo)) if 10**12 < b else (
        _check_sqrt_lb(Dyadic.of_nat(b), w["bSqrtLb"]) and w["bSqrtLb"].m > 0
        and DY_TWO.ble(w["hiErrUb"].mul_lb(w["bSqrtLb"].mul_lb(b_lo)))))
    ok_pi = ((Dyadic.of_nat(b - a).ble(w["piMainUb"].mul_lb(a_lo))
              and w["bSqrtUb"].mul_ub(b_hi).add(w["aSqrtUb"].mul_ub(a_hi)).ble(w["piRemUb"].mul_lb(DY_8PI_LO4))
              and w["piMainUb"].add(w["piRemUb"].add(DY_ONE)).ble(cnt_ub))
             if not w["piUseSingle"] else
             (b_lo.sub_lb(DY_TWO).m > 0
              and Dyadic.of_nat(b).ble(w["piMainUb"].mul_lb(b_lo.sub_lb(DY_TWO)))
              and w["bSqrtUb"].mul_ub(b_hi).ble(w["piRemUb"].mul_lb(DY_8PI_LO4))
              and w["piMainUb"].add(DY_LI2_UB.add(w["piRemUb"])).ble(cnt_ub)))
    return (
        P_EXACT <= a < b and DY_THREE.blt(a_lo) and a_lo.ble(a_hi) and b_lo.ble(b_hi) and DY_THREE.blt(b_lo)
        and DY_ONE.ble(w["ratioUb"]) and b_hi.ble(w["ratioUb"].mul_lb(a_lo))
        and check_log_dyadic(w["ratioUb"], w["wLL"], DY_ZERO, w["llRatioUb"])
        and _check_sqrt_ub(Dyadic.of_nat(a), w["aSqrtUb"]) and _check_sqrt_ub(Dyadic.of_nat(b), w["bSqrtUb"])
        and DY_2964_UB.ble(w["loErrUb"].mul_lb(a_lo)) and ok_hi
        and DY_ONE.ble(w["tailPredUb"].mul_lb(Dyadic.of_nat(a - 1)))
        and w["llRatioUb"].add(w["hiErrUb"].add(w["loErrUb"].add(w["tailPredUb"]))).ble(sq_ub) and ok_pi
    )


def check_slice_bounds_py(
    q0: int, q1: int, l0_lo: Dyadic, l0_hi: Dyadic, l1_lo: Dyadic, l1_hi: Dyadic, sq_ub: Dyadic, cnt_ub: Dyadic, aw: dict | None
) -> bool:
    if q1 <= q0:
        return True
    if q1 <= P_EXACT:
        return exact_inv_sub_one_sum_ub(q0, q1).ble(sq_ub) and Dyadic.of_nat(exact_prime_count(q0, q1)).ble(cnt_ub)
    if aw is None:
        return False
    if P_EXACT <= q0:
        return check_analytic_range_py(q0, q1, l0_lo, l0_hi, l1_lo, l1_hi, sq_ub, cnt_ub, aw)
    sq_ex, cnt_ex = exact_inv_sub_one_sum_ub(q0, P_EXACT), Dyadic.of_nat(exact_prime_count(q0, P_EXACT))
    sq_an = aw["llRatioUb"].add(aw["hiErrUb"].add(aw["loErrUb"].add(aw["tailPredUb"])))
    cnt_an = aw["piMainUb"].add(aw["piRemUb"].add(DY_ONE)) if not aw["piUseSingle"] else aw["piMainUb"].add(DY_LI2_UB.add(aw["piRemUb"]))
    return (check_analytic_range_py(P_EXACT, q1, DY_LOG27000_LO, DY_LOG27000_HI, l1_lo, l1_hi, sq_an, cnt_an, aw)
            and sq_ex.add(sq_an).ble(sq_ub) and cnt_ex.add(cnt_an).ble(cnt_ub))


def check_mertens_tail_py(u: int, v: int, u_lo: Dyadic, u_hi: Dyadic, v_lo: Dyadic, v_hi: Dyadic, w: dict) -> bool:
    if v <= u:
        return w["gLb"].ble(DY_ONE)
    if v <= P_EXACT:
        return (exact_inv_sub_one_sum_ub(u, v).ble(w["s1Ub"]) and exact_inv_pred_sq_sum_ub(u, v).ble(w["s2Ub"])
                and exact_prime_count(u, v) <= w["piUb"]
                and (w["gLb"].ble(exact_prod_one_sub_inv_pred_lb(u, v)) if (3 <= u and w["gLb"].m > 0) else True))
    if w["anW"] is None:
        return False
    aw = w["anW"]
    if P_EXACT <= u:
        if not (check_analytic_range_py(u, v, u_lo, u_hi, v_lo, v_hi, w["s1Ub"], Dyadic.of_nat(w["piUb"]), aw)
                and DY_ONE.ble(w["s2Ub"].mul_lb(Dyadic.of_nat(u - 2)))):
            return False
        if w["gLb"].m > 0:
            oke, e_ub = exp_ub_dyadic(w["s1Ub"].add(w["c2Ub"].mul_ub(w["s2Ub"])))
            return Dyadic.of_nat(u - 1).ble(w["c2Ub"].mul_lb(Dyadic.of_nat(2 * (u - 2)))) and oke and w["gLb"].mul_ub(e_ub).ble(DY_ONE)
        return True
    s1_ex, s2_ex, cnt_ex = exact_inv_sub_one_sum_ub(u, P_EXACT), exact_inv_pred_sq_sum_ub(u, P_EXACT), exact_prime_count(u, P_EXACT)
    s1_an = aw["llRatioUb"].add(aw["hiErrUb"].add(aw["loErrUb"].add(aw["tailPredUb"])))
    cnt_an = aw["piMainUb"].add(aw["piRemUb"].add(DY_ONE)) if not aw["piUseSingle"] else aw["piMainUb"].add(DY_LI2_UB.add(aw["piRemUb"]))
    if not (check_analytic_range_py(P_EXACT, v, DY_LOG27000_LO, DY_LOG27000_HI, v_lo, v_hi, s1_an, cnt_an, aw)
            and s1_ex.add(s1_an).ble(w["s1Ub"]) and s2_ex.add(w["s2Ub"].sub_lb(s2_ex)).ble(w["s2Ub"])
            and DY_ONE.ble(w["s2Ub"].sub_lb(s2_ex).mul_lb(Dyadic.of_nat(26998)))
            and Dyadic.of_nat(cnt_ex).add(cnt_an).ble(Dyadic.of_nat(w["piUb"]))):
        return False
    if 3 <= u and w["gLb"].m > 0:
        oke, e_ub = exp_ub_dyadic(s1_an.add(w["c2Ub"].mul_ub(w["s2Ub"].sub_lb(s2_ex))))
        return (Dyadic.of_nat(26999).ble(w["c2Ub"].mul_lb(Dyadic.of_nat(53996))) and oke
                and w["gLb"].mul_ub(e_ub).ble(exact_prod_one_sub_inv_pred_lb(u, P_EXACT)))
    return True


def _check_analytic_v2_lb_py(p2e: list[dict], c2_ub: Dyadic, g_lb: Dyadic) -> bool:
    if not p2e:
        return g_lb.m > 0 and g_lb.ble(DY_ONE)
    p0 = p2e[0]["p"]
    oke, e_ub = exp_ub_dyadic(sum_g1_entries_ub(p2e).add(c2_ub.mul_ub(sum_g2_entries_ub(p2e))))
    return g_lb.m > 0 and Dyadic.of_nat(p0 - 1).ble(c2_ub.mul_lb(Dyadic.of_nat(2 * (p0 - 2)))) and oke and g_lb.mul_ub(e_ub).ble(DY_ONE)


def _check_slice_rat_exact_py(p2e: list[dict], mev: int, rat_ub: Dyadic) -> bool:
    if not p2e:
        return DY_ONE.ble(rat_ub)
    _, e_hi, o_lo, _ = elem_sym_sums_dy(elem_sym_interval64(p2e, 2 * mev))
    g_lb = v2_entries_lb(p2e)
    return g_lb.m > 0 and e_hi.ble(o_lo.add(rat_ub.mul_lb(g_lb)))


def _check_slice_rat_analytic_py(p2e: list[dict], mev: int, c2_ub: Dyadic, g_lb: Dyadic, err_ub: Dyadic, rat_ub: Dyadic) -> bool:
    if not _check_analytic_v2_lb_py(p2e, c2_ub, g_lb):
        return False
    if not p2e:
        return DY_ONE.ble(rat_ub)
    k = 2 * mev
    err_den = Dyadic.of_nat(_fact(k + 1)).mul_lb(g_lb)
    return sum_g1_entries_ub(p2e).pow_ub(k + 1).ble(err_ub.mul_lb(err_den)) and DY_ONE.add(err_ub).ble(rat_ub)


def _check_cert_valid(c: dict) -> bool:
    return (c["den"] > 0 and c["net_num"] > 0 and c["err_num"] > 0 and c["net_num"] + c["err_num"] <= c["main_num"]
            and c["X_lo"] < c["X_hi"] and 2 <= c["z"] <= c["y"] and c["X_hi"] <= c["y"] ** 4
            and c["X_hi"] <= c["z"] * (c["y"] ** 3) and 4 * 10**18 <= c["X_lo"])


def verify_slab_2ab_bool(c: dict, w: dict) -> bool:
    if not (_check_cert_valid(c) and c["z"] < P_EXACT
            and check_log_dyadic(Dyadic.of_nat(c["X_lo"]), w["wXLoLog"], w["xLoLogLb"], w["xLoLogUb"])
            and check_log_dyadic(Dyadic.of_nat(c["X_hi"]), w["wXHiLog"], DY_ZERO, w["xHiLogUb"])
            and check_epd_witness_py(c["X_lo"], w["xLoLogLb"], w["xLoLogUb"], w["epdUb"], w["epdW"])):
        return False
    lo, es = w["lower"], tree_filter_range(3, c["z"])
    ps = [e["p"] for e in es]
    q1, p2, p2e, k_lo = ps[: lo["a"]], ps[lo["a"] :], es[lo["a"] :], 2 * lo["mOdd"] + 1
    if not (c["z"] <= P_EXACT and lo["a"] <= len(ps)
            and _prod(q1) * _prod(p2[-k_lo:] if k_lo > 0 else []) <= lo["dMax"] and lo["dMax"] ** 2 <= c["X_lo"]
            and (1 << lo["a"]) * sum(comb_int(len(p2), j) for j in range(k_lo + 1)) <= lo["nD"]
            and lo["vFullLb"].ble(exact_prod_one_sub_inv_pred_lb(3, c["z"]))
            and exact_prod_one_sub_inv_pred_ub(3, c["z"]).ble(lo["vFullUb"])):
        return False
    if not lo["useAnalytic"]:
        if not p2e:
            if not lo["ratLb"].ble(DY_ONE):
                return False
        else:
            e_lo, _, _, o_hi = elem_sym_sums_dy(elem_sym_interval64(p2e, k_lo))
            if not lo["ratLb"].mul_ub(v2_entries_ub(p2e)).add(o_hi).ble(e_lo):
                return False
    else:
        if not _check_analytic_v2_lb_py(p2e, lo["c2Ub"], lo["gLb"]):
            return False
        if not p2e:
            if not lo["ratLb"].ble(DY_ONE):
                return False
        else:
            err_den = Dyadic.of_nat(_fact(k_lo + 1)).mul_lb(lo["gLb"])
            if not (sum_g1_entries_ub(p2e).pow_ub(k_lo + 1).ble(lo["errUb"].mul_lb(err_den))
                    and lo["ratLb"].add(lo["errUb"]).ble(DY_ONE)):
                return False
    cur, sum_m, sum_e = c["z"], DY_ZERO, DY_ZERO
    for sl in w["slices"]:
        if sl["q0"] != cur or sl["q0"] > sl["q1"]:
            return False
        cur = sl["q1"]
        if P_EXACT <= sl["q0"] and not check_log_dyadic(Dyadic.of_nat(sl["q0"]), sl["wQ0Log"], sl["logQ0Lb"], sl["logQ0Ub"]):
            return False
        if P_EXACT < sl["q1"] and not check_log_dyadic(Dyadic.of_nat(sl["q1"]), sl["wQ1Log"], sl["logQ1Lb"], sl["logQ1Ub"]):
            return False
        if not check_slice_bounds_py(sl["q0"], sl["q1"], sl["logQ0Lb"], sl["logQ0Ub"], sl["logQ1Lb"], sl["logQ1Ub"], sl["sqUb"], sl["cntUb"], sl["anW"]):
            return False
        if sl["kind"] == 0:
            if not ((sl["q1"] - 1) ** 2 <= c["X_lo"] and sl["sqUb"].ble(sl["mSl"]) and sl["cntUb"].mul_ub(w["epdUb"]).ble(sl["eSl"])):
                return False
        else:
            ess = tree_filter_range(3, sl["zSub"])
            pss = [e["p"] for e in ess]
            q1e_s, p2e_s = ess[: sl["aQ"]], ess[sl["aQ"] :]
            q1_s, p2_s, k_s = pss[: sl["aQ"]], pss[sl["aQ"] :], 2 * sl["mEv"]
            if not (sl["zSub"] <= c["z"] and sl["zSub"] <= P_EXACT and sl["aQ"] <= len(pss)
                    and _prod(q1_s) * _prod(p2_s[-k_s:] if k_s > 0 else []) <= sl["dMax"]
                    and ((sl["q1"] - 1) * sl["dMax"]) ** 2 <= c["X_lo"]
                    and (1 << sl["aQ"]) * sum(comb_int(len(p2_s), j) for j in range(k_s + 1)) <= sl["nD"]
                    and exact_prod_one_sub_inv_pred_ub(3, sl["zSub"]).ble(sl["vSubUb"])):
                return False
            if sl["kind"] == 1:
                _, e_hi, _, o_hi = elem_sym_sums_dy(elem_sym_interval64(p2e_s, k_s))
                if not (inv_phi_entries_ub(q1e_s).mul_ub(e_hi.add(o_hi)).ble(sl["ip2"])
                        and _check_slice_rat_exact_py(p2e_s, sl["mEv"], sl["ratUb"])):
                    return False
            elif sl["kind"] == 2:
                oke, e_s1 = exp_ub_dyadic(sum_g1_entries_ub(p2e_s))
                if not (_check_slice_rat_analytic_py(p2e_s, sl["mEv"], sl["c2Ub"], sl["gSubLb"], sl["errUb"], sl["ratUb"])
                        and oke and inv_phi_entries_ub(q1e_s).mul_ub(e_s1).ble(sl["ip2"])):
                    return False
            else:
                return False
            if not (sl["sqUb"].mul_ub(sl["vSubUb"]).mul_ub(sl["ratUb"]).ble(sl["mSl"])
                    and sl["cntUb"].mul_ub(Dyadic.of_nat(sl["nD"]).add(sl["ip2"].add(sl["ratUb"]))).mul_ub(w["epdUb"]).ble(sl["eSl"])):
                return False
        sum_m, sum_e = sum_m.add(sl["mSl"]), sum_e.add(sl["eSl"])
    if cur != c["y"]:
        return False
    sq, q_end = w["square"], min(c["y"], w["square"]["qSq"] + 1)
    s_ex = exact_inv_mul_pred_sum_ub(c["z"], min(q_end, P_EXACT))
    s_ok = ((DY_ONE.ble(sq["invTailUb"].mul_lb(Dyadic.of_nat(P_EXACT - 1))) and s_ex.add(sq["invTailUb"]).ble(sq["sQ2Ub"]))
            if P_EXACT < q_end else s_ex.ble(sq["sQ2Ub"]))
    if not (1 <= sq["qSq"] and sq["qSq"] ** 4 <= c["X_lo"] and s_ok):
        return False
    if P_EXACT < q_end and not check_log_dyadic(Dyadic.of_nat(q_end), sq["wLogEnd"], sq["logEndLb"], sq["logEndUb"]):
        return False
    if c["y"] > sq["qSq"] + 1 and not w["xHiLogUb"].ble(sq["tailQ2Ub"].mul_lb(Dyadic.of_nat(sq["qSq"]))):
        return False
    tail_q2 = DY_ZERO if c["y"] <= sq["qSq"] + 1 else sq["tailQ2Ub"]
    if not (check_slice_bounds_py(c["z"], q_end, w["xLoLogLb"], w["xLoLogUb"], sq["logEndLb"], sq["logEndUb"], Dyadic.of_nat(1000), sq["cntLoUb"], sq["anEndW"])
            and sq["sQ2Ub"].add(sq["cntLoUb"].mul_ub(w["epdUb"]).add(tail_q2)).ble(sq["errQ2Ub"].add(sq["errQ2Ub"]))):
        return False
    rem_a = Dyadic.of_nat(lo["nD"]).mul_ub(w["epdUb"])
    two_err = rem_a.add(sq["errQ2Ub"]).add(rem_a.add(sq["errQ2Ub"]))
    return (Dyadic.of_nat(2 * c["main_num"]).add(Dyadic.of_nat(c["den"]).mul_ub(sum_m)).ble(Dyadic.of_nat(2 * c["den"]).mul_lb(lo["vFullLb"].mul_lb(lo["ratLb"])))
            and two_err.add(sum_e).mul_ub(Dyadic.of_nat(c["den"])).ble(Dyadic.of_nat(2 * c["err_num"])))


def verify_slab_2c_bool(c: dict, w: dict) -> bool:
    if not (_check_cert_valid(c)
            and check_log_dyadic(Dyadic.of_nat(c["X_lo"]), w["wXLoLog"], w["xLoLogLb"], w["xLoLogUb"])
            and check_log_dyadic(Dyadic.of_nat(c["X_hi"]), w["wXHiLog"], DY_ZERO, w["xHiLogUb"])
            and check_log_dyadic(Dyadic.of_nat(c["z"]), w["wZLog"], w["zLogLb"], w["zLogUb"])
            and check_epd_witness_py(c["X_lo"], w["xLoLogLb"], w["xLoLogUb"], w["epdUb"], w["epdW"])
            and w["vFullLb"].m > 0):
        return False
    if c["z"] <= P_EXACT:
        if not w["vFullLb"].ble(exact_prod_one_sub_inv_pred_lb(3, c["z"])):
            return False
    else:
        if w["vFullW"] is None or not (w["vFullW"]["gLb"].m > 0
                and check_mertens_tail_py(P_EXACT, c["z"], DY_LOG27000_LO, DY_LOG27000_HI, w["zLogLb"], w["zLogUb"], w["vFullW"])
                and w["vFullLb"].ble(V_PREFIX_27000_LB.mul_lb(w["vFullW"]["gLb"]))):
            return False
    lo = w["lower"]
    if lo["a"] >= 40:
        return False
    p_min, q1p = SMALL_ODD_PRIMES_40[lo["a"]], _prod(SMALL_ODD_PRIMES_40[: lo["a"]])
    if not lo["isBrun"]:
        k = 2 * lo["mOdd"] + 1
        err_den = Dyadic.of_nat(_fact(k + 1)).mul_lb(lo["gLb"])
        if not (k < 16 and p_min < c["z"] and q1p * (c["z"] ** k) <= lo["dMax"] and lo["dMax"] ** 2 <= c["X_lo"]
                and check_mertens_tail_py(p_min, c["z"], DY_ZERO, DY_ZERO, w["zLogLb"], w["zLogUb"], lo["tail"])
                and lo["tail"]["s1Ub"].ble(lo["s1Ub"]) and Dyadic.of_nat(lo["tail"]["piUb"]).ble(lo["piZUb"])
                and sum_pow_div_fact_ub(lo["piZUb"], k).mul_pow2(lo["a"]).ble(Dyadic.of_nat(lo["nD"]))
                and lo["gLb"].m > 0 and lo["gLb"].ble(lo["tail"]["gLb"])
                and lo["s1Ub"].pow_ub(k + 1).ble(lo["errUb"].mul_lb(err_den))
                and lo["ratLb"].add(lo["errUb"]).ble(DY_ONE)
                and Dyadic.of_nat(lo["nD"]).mul_ub(w["epdUb"]).ble(lo["remANormUb"].mul_lb(w["vFullLb"]))):
            return False
    else:
        ends, caps = lo["ends"], lo["caps"]
        p_a = 2 if lo["a"] == 0 else SMALL_ODD_PRIMES_40[lo["a"] - 1]
        mod_b, prev = 1, 0
        for idx_b, m_cap in enumerate(caps):
            mod_b, prev = mod_b * (ends[idx_b] ** (m_cap - prev)), m_cap
        if not (len(caps) >= 1 and len(ends) == len(caps) + 1 and len(lo["brunSteps"]) == len(caps)
                and ends[0] == c["z"] and all(ends[i] > ends[i + 1] for i in range(len(caps)))
                and p_a < ends[-1] <= p_min < c["z"] and all(m % 2 == 1 for m in caps)
                and all(caps[i] <= caps[i + 1] for i in range(len(caps) - 1))
                and q1p * mod_b <= lo["dMax"] and lo["dMax"] ** 2 <= c["X_lo"]):
            return False
        szs, e_tot = [], DY_ZERO
        for cur, nxt, cap, st in zip(ends, ends[1:], caps, lo["brunSteps"]):
            nxt_lo, nxt_hi = st["bTail"]["uLogLb"], st["bTail"]["uLogUb"]
            cur_lo = w["zLogLb"] if cur == c["z"] else st["bTail"]["vLogLb"]
            cur_hi = w["zLogUb"] if cur == c["z"] else st["bTail"]["vLogUb"]
            if P_EXACT <= nxt and not check_log_dyadic(Dyadic.of_nat(nxt), st["wNxtLog"], nxt_lo, nxt_hi):
                return False
            if cur != c["z"] and P_EXACT < cur and not check_log_dyadic(Dyadic.of_nat(cur), st["wCurLog"], cur_lo, cur_hi):
                return False
            if not (check_mertens_tail_py(nxt, cur, nxt_lo, nxt_hi, cur_lo, cur_hi, st["bTail"])
                    and check_mertens_tail_py(nxt, c["z"], nxt_lo, nxt_hi, w["zLogLb"], w["zLogUb"], st["tTail"])):
                return False
            err_den = Dyadic.of_nat(_fact(cap + 1)).mul_lb(st["tTail"]["gLb"])
            if not (st["tTail"]["gLb"].m > 0 and st["tTail"]["s1Ub"].pow_ub(cap + 1).ble(st["termUb"].mul_lb(err_den))):
                return False
            szs.append(st["bTail"]["piUb"])
            e_tot = e_tot.add(st["termUb"])
        if not ((1 << lo["a"]) * adm_count(caps, szs) <= lo["nD"] and lo["ratLb"].add(e_tot).ble(DY_ONE)
                and Dyadic.of_nat(lo["nD"]).mul_ub(w["epdUb"]).ble(lo["remANormUb"].mul_lb(w["vFullLb"]))):
            return False
    cur_q, sum_m, sum_e = c["z"], DY_ZERO, DY_ZERO
    for sl in w["slices"]:
        if sl["q0"] != cur_q or sl["q0"] > sl["q1"]:
            return False
        cur_q = sl["q1"]
        if P_EXACT <= sl["q0"] and not check_log_dyadic(Dyadic.of_nat(sl["q0"]), sl["wQ0Log"], sl["logQ0Lb"], sl["logQ0Ub"]):
            return False
        if P_EXACT < sl["q1"] and not check_log_dyadic(Dyadic.of_nat(sl["q1"]), sl["wQ1Log"], sl["logQ1Lb"], sl["logQ1Ub"]):
            return False
        if not check_slice_bounds_py(sl["q0"], sl["q1"], sl["logQ0Lb"], sl["logQ0Ub"], sl["logQ1Lb"], sl["logQ1Ub"], sl["sqUb"], sl["cntUb"], sl["anW"]):
            return False
        md = sl["mode"]
        if md["isSelberg"]:
            jf_req = calc_j_full_lb_2c_dy(c["z"], w["zLogLb"], w["zLogUb"], md["xiQLb"], md["xiQLogLb"], md["xiQLogUb"])
            s3c_ok = sl["cntUb"].mul_ub(md["xiQLb"].mul_ub(md["xiQLb"])).ble(md["s3cUb"]) or sl["sqUb"].mul_ub(md["hQ"]).ble(md["s3cUb"])
            es1_lhs = md["s3cUb"].div_pow2_ub(4).mul_ub(md["xiQLogUb"].mul_pow2(1).add(DY_SIX).pow_ub(2).mul_ub(w["epdUb"]))
            f0_lhs = md["xiQLogUb"].add(A0_UB_DY.add(md["invXiSq78Ub"]))
            e_num = md["es1Ub"].add(sl["cntUb"].mul_ub(DY_ONE.add(DY_13E1_UB.mul_ub(md["f0Ub"]).pow_ub(3))).mul_ub(w["epdUb"]))
            if not (md["xiQLb"].ble(md["xiQUb"])
                    and Dyadic.of_nat(sl["q1"] - 1).mul_ub(md["xiQUb"].mul_ub(md["xiQUb"])).ble(md["hQ"])
                    and md["hQ"].mul_ub(md["hQ"]).ble(Dyadic.of_nat(c["X_lo"]))
                    and c["z"] >= 3 and md["jfLb"].m > 0 and DY_ONE.ble(md["xiQLb"])
                    and check_log_dyadic(md["xiQLb"], md["wXiLog"], md["xiQLogLb"], md["xiQLogUb"])
                    and md["jfLb"].ble(jf_req)
                    and sl["sqUb"].ble(sl["mSl"].mul_lb(w["vFullLb"].mul_lb(md["jfLb"])))
                    and s3c_ok and es1_lhs.ble(md["es1Ub"])
                    and DY_78E2_UB.ble(md["invXiSq78Ub"].mul_lb(md["xiQLb"].mul_lb(md["xiQLb"])))
                    and f0_lhs.ble(md["f0Ub"]) and e_num.ble(sl["eSl"].mul_lb(w["vFullLb"]))):
                return False
        else:
            if not (sl["cntUb"].mul_ub(Dyadic.of_nat(md["nD"]).add(md["ip2"].add(md["ratUb"]))).mul_ub(w["epdUb"]).ble(sl["eSl"].mul_lb(w["vFullLb"]))
                    and sl["sqUb"].mul_ub(md["mRatUb"]).ble(sl["mSl"])):
                return False
            if md["zSub"] <= P_EXACT:
                ess = tree_filter_range(3, md["zSub"])
                pss = [e["p"] for e in ess]
                q1e_s, p2e_s = ess[: md["aQ"]], ess[md["aQ"] :]
                q1_s, p2_s, k_s = pss[: md["aQ"]], pss[md["aQ"] :], 2 * md["mEv"]
                oke, e_s1 = exp_ub_dyadic(sum_g1_entries_ub(p2e_s))
                _, e_hi, _, o_hi = elem_sym_sums_dy(elem_sym_interval64(p2e_s, k_s))
                ip_ok = (oke and inv_phi_entries_ub(q1e_s).mul_ub(e_s1).ble(md["ip2"])) or inv_phi_entries_ub(q1e_s).mul_ub(e_hi.add(o_hi)).ble(md["ip2"])
                rat_ok = _check_slice_rat_analytic_py(p2e_s, md["mEv"], md["c2Ub"], md["gSubLb"], md["errUb"], md["ratUb"]) or _check_slice_rat_exact_py(p2e_s, md["mEv"], md["ratUb"])
                if not (md["zSub"] <= c["z"] and md["aQ"] <= len(pss)
                        and _prod(q1_s) * _prod(p2_s[-k_s:] if k_s > 0 else []) <= md["dMax"]
                        and ((sl["q1"] - 1) * md["dMax"]) ** 2 <= c["X_lo"]
                        and (1 << md["aQ"]) * sum(comb_int(len(p2_s), j) for j in range(k_s + 1)) <= md["nD"]
                        and ip_ok and rat_ok and exact_prod_one_sub_inv_pred_ub(3, md["zSub"]).ble(md["vSubUb"])
                        and md["vSubUb"].mul_ub(md["ratUb"]).ble(md["mRatUb"].mul_lb(w["vFullLb"]))):
                    return False
            else:
                if md["aQ"] >= 40 or md["tailW"] is None:
                    return False
                tw = md["tailW"]
                pm, ks, q1ps = SMALL_ODD_PRIMES_40[md["aQ"]], 2 * md["mEv"], _prod(SMALL_ODD_PRIMES_40[: md["aQ"]])
                oke, e_s1 = exp_ub_dyadic(tw["s1Ub"])
                err_den = Dyadic.of_nat(_fact(ks + 1)).mul_lb(md["gSubLb"])
                if not (ks < 16 and md["zSub"] == c["z"] and pm < c["z"] and q1ps * (c["z"] ** ks) <= md["dMax"]
                        and ((sl["q1"] - 1) * md["dMax"]) ** 2 <= c["X_lo"]
                        and check_mertens_tail_py(pm, c["z"], DY_ZERO, DY_ZERO, w["zLogLb"], w["zLogUb"], tw)
                        and oke and md["gSubLb"].m > 0 and md["gSubLb"].ble(tw["gLb"])
                        and sum_pow_div_fact_ub(Dyadic.of_nat(tw["piUb"]), ks).mul_pow2(md["aQ"]).ble(Dyadic.of_nat(md["nD"]))
                        and inv_phi_entries_ub(SMALL_ODD_ENTRIES_40[: md["aQ"]]).mul_ub(e_s1).ble(md["ip2"])
                        and tw["s1Ub"].pow_ub(ks + 1).ble(md["errUb"].mul_lb(err_den))
                        and DY_ONE.add(md["errUb"]).ble(md["ratUb"]) and md["ratUb"].ble(md["mRatUb"])):
                    return False
        sum_m, sum_e = sum_m.add(sl["mSl"]), sum_e.add(sl["eSl"])
    if cur_q != c["y"]:
        return False
    sq, q_end = w["square"], min(c["y"], w["square"]["qSq"] + 1)
    if c["z"] <= P_EXACT:
        s_ex = exact_inv_mul_pred_sum_ub(c["z"], min(q_end, P_EXACT))
        s_ok = ((DY_ONE.ble(sq["invTailUb"].mul_lb(Dyadic.of_nat(P_EXACT - 1))) and s_ex.add(sq["invTailUb"]).ble(sq["sQ2Ub"]))
                if P_EXACT < q_end else s_ex.ble(sq["sQ2Ub"]))
    else:
        s_ok = DY_ONE.ble(sq["sQ2Ub"].mul_lb(Dyadic.of_nat(c["z"] - 1)))
    if not (1 <= sq["qSq"] and sq["qSq"] ** 4 <= c["X_lo"] and s_ok):
        return False
    if P_EXACT < q_end and not check_log_dyadic(Dyadic.of_nat(q_end), sq["wLogEnd"], sq["logEndLb"], sq["logEndUb"]):
        return False
    if c["y"] > sq["qSq"] + 1 and not w["xHiLogUb"].ble(sq["tailQ2Ub"].mul_lb(Dyadic.of_nat(sq["qSq"]))):
        return False
    tail_q2 = DY_ZERO if c["y"] <= sq["qSq"] + 1 else sq["tailQ2Ub"]
    if not (check_slice_bounds_py(c["z"], q_end, w["zLogLb"], w["zLogUb"], sq["logEndLb"], sq["logEndUb"], Dyadic.of_nat(1000), sq["cntLoUb"], sq["anEndW"])
            and sq["sQ2Ub"].add(sq["cntLoUb"].mul_ub(w["epdUb"]).add(tail_q2)).ble(sq["errQ2Ub"].add(sq["errQ2Ub"]))
            and sq["errQ2Ub"].ble(w["errQ2NormUb"].mul_lb(w["vFullLb"]))):
        return False
    return (Dyadic.of_nat(2 * c["main_num"]).add(Dyadic.of_nat(c["den"]).mul_ub(sum_m)).ble(Dyadic.of_nat(2 * c["den"]).mul_lb(lo["ratLb"]))
            and lo["remANormUb"].add(w["errQ2NormUb"]).mul_pow2(1).add(sum_e).mul_ub(Dyadic.of_nat(c["den"])).ble(Dyadic.of_nat(2 * c["err_num"])))


# --- Slice Merging Compression & Compact Lean Formatting ---

def _rebuild_slice_2ab(q0: int, q1s: int, ref: dict, epd_ub: Dyadic) -> dict:
    w0, l0_lo, l0_hi = _nat_log(q0) if P_EXACT <= q0 else (LOG_W_DUMMY, DY_ZERO, DY_ZERO)
    w1, l1_lo, l1_hi = _nat_log(q1s) if P_EXACT < q1s else (LOG_W_DUMMY, DY_ZERO, DY_ZERO)
    sq_ub, cnt_ub, aw = build_slice_bounds(q0, q1s, l0_lo, l0_hi, l1_lo, l1_hi)
    if ref["kind"] == 0:
        m0, e0 = sq_ub, cnt_ub.mul_ub(epd_ub).trim_ub(80)
        return _mk_sl2ab(q0, q1s, 0, 0, 0, 0, 0, 0, w0, w1, aw, sq_ub, cnt_ub,
                         (l0_lo, l0_hi), (l1_lo, l1_hi), DY_ZERO, DY_ZERO, DY_ZERO, DY_ZERO, DY_ZERO, DY_ZERO, m0, e0)
    m_sl = sq_ub.mul_ub(ref["vSubUb"]).mul_ub(ref["ratUb"]).trim_ub(80)
    e_sl = cnt_ub.mul_ub(Dyadic.of_nat(ref["nD"]).add(ref["ip2"].add(ref["ratUb"]))).mul_ub(epd_ub).trim_ub(80)
    return _mk_sl2ab(q0, q1s, ref["kind"], ref["zSub"], ref["aQ"], ref["mEv"], ref["nD"], ref["dMax"],
                     w0, w1, aw, sq_ub, cnt_ub, (l0_lo, l0_hi), (l1_lo, l1_hi),
                     ref["ip2"], ref["vSubUb"], ref["gSubLb"], ref["ratUb"], ref["c2Ub"], ref["errUb"], m_sl, e_sl)


def _compress_2ab_slices(cert: dict, w: dict) -> dict:
    epd_ub, x_lo, lo, sq = w["epdUb"], cert["X_lo"], w["lower"], w["square"]
    rem_a = Dyadic.of_nat(lo["nD"]).mul_ub(epd_ub)
    two_err = rem_a.add(sq["errQ2Ub"]).add(rem_a.add(sq["errQ2Ub"]))
    main_rhs = Dyadic.of_nat(2 * cert["den"]).mul_lb(lo["vFullLb"].mul_lb(lo["ratLb"]))
    err_rhs = Dyadic.of_nat(2 * cert["err_num"])

    def ok_budget(sls: list[dict]) -> bool:
        sm = se = DY_ZERO
        for s in sls:
            sm, se = sm.add(s["mSl"]), se.add(s["eSl"])
        return (Dyadic.of_nat(2 * cert["main_num"]).add(Dyadic.of_nat(cert["den"]).mul_ub(sm)).ble(main_rhs)
                and two_err.add(se).mul_ub(Dyadic.of_nat(cert["den"])).ble(err_rhs))

    sls: list[dict] = []
    for sl in w["slices"]:
        if sls and sl["q1"] <= P_EXACT and (sls[-1]["kind"], sls[-1]["zSub"], sls[-1]["aQ"], sls[-1]["mEv"]) == (sl["kind"], sl["zSub"], sl["aQ"], sl["mEv"]):
            sls[-1] = _rebuild_slice_2ab(sls[-1]["q0"], sl["q1"], sl, epd_ub)
        else:
            sls.append(sl)
    while len(sls) > 1:
        best_merge = None
        for i in range(len(sls) - 1):
            a, b = sls[i], sls[i + 1]
            cands = [b]
            if (a["kind"] == 0 and (b["q1"] - 1) ** 2 <= x_lo) or (a["kind"] != 0 and ((b["q1"] - 1) * a["dMax"]) ** 2 <= x_lo):
                cands.append(a)
            old_m = a["mSl"].add(b["mSl"]).to_dec_ceil(18)
            old_e = a["eSl"].add(b["eSl"]).to_dec_ceil(18)
            for ref in cands:
                cand = _rebuild_slice_2ab(a["q0"], b["q1"], ref, epd_ub)
                trial = sls[:i] + [cand] + sls[i + 2 :]
                if ok_budget(trial):
                    delta = (cand["mSl"].to_dec_ceil(18) - old_m) + (cand["eSl"].to_dec_ceil(18) - old_e)
                    key = (delta, cand["kind"], cand["zSub"])
                    if best_merge is None or key < best_merge[0]:
                        best_merge = (key, i, cand)
        if best_merge is None:
            break
        _, idx, cand = best_merge
        sls = sls[:idx] + [cand] + sls[idx + 2 :]
    return dict(w, slices=sls)


def _rebuild_slice_2c(q0: int, q1s: int, ref: dict, epd_ub: Dyadic, v_full_lb: Dyadic) -> dict:
    w0, l0_lo, l0_hi = _nat_log(q0) if P_EXACT <= q0 else (LOG_W_DUMMY, DY_ZERO, DY_ZERO)
    w1, l1_lo, l1_hi = _nat_log(q1s) if P_EXACT < q1s else (LOG_W_DUMMY, DY_ZERO, DY_ZERO)
    sq_ub, cnt_ub, aw = build_slice_bounds(q0, q1s, l0_lo, l0_hi, l1_lo, l1_hi)
    md = ref["mode"]
    if md["isSelberg"]:
        m_sl = solve_ble_mul_lb(sq_ub, v_full_lb.mul_lb(md["jfLb"]))
        s3c_a, s3c_b = cnt_ub.mul_ub(md["xiQLb"].mul_ub(md["xiQLb"])), sq_ub.mul_ub(md["hQ"])
        s3c = (s3c_a if s3c_a.ble(s3c_b) else s3c_b).trim_ub(80)
        es1 = s3c.div_pow2_ub(4).mul_ub(md["xiQLogUb"].mul_pow2(1).add(DY_SIX).pow_ub(2).mul_ub(epd_ub)).trim_ub(80)
        e_num = es1.add(cnt_ub.mul_ub(DY_ONE.add(DY_13E1_UB.mul_ub(md["f0Ub"]).pow_ub(3))).mul_ub(epd_ub))
        e_sl = solve_ble_mul_lb(e_num, v_full_lb)
        new_md = dict(md, s3cUb=s3c, es1Ub=es1)
    else:
        m_sl = sq_ub.mul_ub(md["mRatUb"]).trim_ub(80)
        e_num = cnt_ub.mul_ub(Dyadic.of_nat(md["nD"]).add(md["ip2"].add(md["ratUb"]))).mul_ub(epd_ub)
        e_sl = solve_ble_mul_lb(e_num, v_full_lb)
        new_md = md
    return {"q0": q0, "q1": q1s, "wQ0Log": w0, "wQ1Log": w1, "anW": aw,
            "logQ0Lb": l0_lo, "logQ0Ub": l0_hi, "logQ1Lb": l1_lo, "logQ1Ub": l1_hi,
            "sqUb": sq_ub, "cntUb": cnt_ub, "mSl": m_sl, "eSl": e_sl, "mode": new_md}


def _compress_2c_slices(cert: dict, w: dict) -> dict:
    epd_ub, v_full_lb, x_lo, lo = w["epdUb"], w["vFullLb"], cert["X_lo"], w["lower"]
    main_rhs = Dyadic.of_nat(2 * cert["den"]).mul_lb(lo["ratLb"])
    err_rhs = Dyadic.of_nat(2 * cert["err_num"])
    two_base = lo["remANormUb"].add(w["errQ2NormUb"]).mul_pow2(1)

    def ok_budget(sls: list[dict]) -> bool:
        sm = se = DY_ZERO
        for s in sls:
            sm, se = sm.add(s["mSl"]), se.add(s["eSl"])
        return (Dyadic.of_nat(2 * cert["main_num"]).add(Dyadic.of_nat(cert["den"]).mul_ub(sm)).ble(main_rhs)
                and two_base.add(se).mul_ub(Dyadic.of_nat(cert["den"])).ble(err_rhs))

    sls = list(w["slices"])
    while len(sls) > 1:
        best_merge = None
        for i in range(len(sls) - 1):
            a, b = sls[i], sls[i + 1]
            am = a["mode"]
            cands = [b]
            if (am["isSelberg"] and Dyadic.of_nat(b["q1"] - 1).mul_ub(am["xiQUb"].mul_ub(am["xiQUb"])).ble(am["hQ"])) or (
                (not am["isSelberg"]) and ((b["q1"] - 1) * am["dMax"]) ** 2 <= x_lo
            ):
                cands.append(a)
            old_m = a["mSl"].add(b["mSl"]).to_dec_ceil(18)
            old_e = a["eSl"].add(b["eSl"]).to_dec_ceil(18)
            for ref in cands:
                cand = _rebuild_slice_2c(a["q0"], b["q1"], ref, epd_ub, v_full_lb)
                trial = sls[:i] + [cand] + sls[i + 2 :]
                if ok_budget(trial):
                    delta = (cand["mSl"].to_dec_ceil(18) - old_m) + (cand["eSl"].to_dec_ceil(18) - old_e)
                    cm = cand["mode"]
                    key = (delta, 0 if cm["isSelberg"] else 1, 0 if cm["isSelberg"] else cm["zSub"])
                    if best_merge is None or key < best_merge[0]:
                        best_merge = (key, i, cand)
        if best_merge is None:
            break
        _, idx, cand = best_merge
        sls = sls[:idx] + [cand] + sls[idx + 2 :]
    return dict(w, slices=sls)


def _fd(x: Dyadic) -> str:
    return f"(d {x.m} {x.e})"


def _flw(w: dict) -> str:
    return f"(lw {w['b']} {w['mU']})"


def _fb(b: bool) -> str:
    return "true" if b else "false"


def _faw(w: dict | None) -> str:
    if w is None:
        return "none"
    return (f"(some (aw {_flw(w['wLL'])} {_fd(w['ratioUb'])} {_fd(w['llRatioUb'])} {_fd(w['aSqrtUb'])} "
            f"{_fd(w['bSqrtUb'])} {_fd(w['bSqrtLb'])} {_fd(w['loErrUb'])} {_fd(w['hiErrUb'])} "
            f"{_fd(w['tailPredUb'])} {_fb(w['piUseSingle'])} {_fd(w['piMainUb'])} {_fd(w['piRemUb'])}))")


def _few(w: dict) -> str:
    return (f"(ew {_fd(w['xLoSqrtLb'])} {_fd(w['xLoSqrtUb'])} {_flw(w['wLLX'])} {_fd(w['llxLb'])} "
            f"{_fd(w['tPi'])} {_fd(w['tInvPi'])} {_fd(w['tLog1'])} {_fd(w['tLog2'])} "
            f"{_fd(w['tLi2'])} {_fd(w['epd1'])} {_fd(w['epd2'])})")


def _fmt_mt(w: dict) -> str:
    return (f"(mt {_fd(w['uLogLb'])} {_fd(w['uLogUb'])} {_fd(w['vLogLb'])} {_fd(w['vLogUb'])} "
            f"{_faw(w['anW'])} {_fd(w['s1Ub'])} {_fd(w['s2Ub'])} {w['piUb']} {_fd(w['c2Ub'])} {_fd(w['gLb'])})")


def _fmt_opt_mt(w: dict | None) -> str:
    return "none" if w is None else f"(some {_fmt_mt(w)})"


def _fsq(sq: dict) -> str:
    return (f"(sqw {sq['qSq']} {_fd(sq['sQ2Ub'])} {_fd(sq['cntLoUb'])} {_fd(sq['logEndLb'])} "
            f"{_fd(sq['logEndUb'])} {_flw(sq['wLogEnd'])} {_faw(sq['anEndW'])} "
            f"{_fd(sq['invTailUb'])} {_fd(sq['tailQ2Ub'])} {_fd(sq['errQ2Ub'])})")


def _fsl2ab(sl: dict) -> str:
    return (f"(s2ab {sl['q0']} {sl['q1']} {sl['kind']} {sl['zSub']} {sl['aQ']} {sl['mEv']} {sl['nD']} {sl['dMax']} "
            f"{_flw(sl['wQ0Log'])} {_flw(sl['wQ1Log'])} {_faw(sl['anW'])} {_fd(sl['sqUb'])} {_fd(sl['cntUb'])} "
            f"{_fd(sl['logQ0Lb'])} {_fd(sl['logQ0Ub'])} {_fd(sl['logQ1Lb'])} {_fd(sl['logQ1Ub'])} "
            f"{_fd(sl['ip2'])} {_fd(sl['vSubUb'])} {_fd(sl['gSubLb'])} {_fd(sl['ratUb'])} "
            f"{_fd(sl['c2Ub'])} {_fd(sl['errUb'])} {_fd(sl['mSl'])} {_fd(sl['eSl'])})")


def _fsl2c(sl: dict) -> str:
    md = sl["mode"]
    if md["isSelberg"]:
        m_str = (f"(ms {_fd(md['hQ'])} {_fd(md['xiQLb'])} {_fd(md['xiQUb'])} {_fd(md['xiQLogLb'])} "
                 f"{_fd(md['xiQLogUb'])} {_fd(md['jfLb'])} {_fd(md['s3cUb'])} {_fd(md['es1Ub'])} "
                 f"{_fd(md['f0Ub'])} {_fd(md['invXiSq78Ub'])} {_flw(md['wXiLog'])})")
    else:
        m_str = (f"(mb {md['zSub']} {md['aQ']} {md['mEv']} {md['nD']} {md['dMax']} {_fd(md['ip2'])} "
                 f"{_fd(md['vSubUb'])} {_fd(md['gSubLb'])} {_fd(md['ratUb'])} {_fd(md['mRatUb'])} "
                 f"{_fd(md['c2Ub'])} {_fd(md['errUb'])} {_fmt_opt_mt(md['tailW'])})")
    return (f"(s2c {sl['q0']} {sl['q1']} {_flw(sl['wQ0Log'])} {_flw(sl['wQ1Log'])} {_faw(sl['anW'])} "
            f"{_fd(sl['logQ0Lb'])} {_fd(sl['logQ0Ub'])} {_fd(sl['logQ1Lb'])} {_fd(sl['logQ1Ub'])} "
            f"{_fd(sl['sqUb'])} {_fd(sl['cntUb'])} {_fd(sl['mSl'])} {_fd(sl['eSl'])} {m_str})")


def _pack_items(items: list[str], per_line: int = 2) -> list[str]:
    return ["      " + ", ".join(items[i : i + per_line]) + ("," if i + per_line < len(items) else "")
            for i in range(0, len(items), per_line)]


def _fmt_slab_2ab(w: dict) -> list[str]:
    lo = w["lower"]
    lo_str = (f"(l2ab {lo['a']} {lo['mOdd']} {lo['nD']} {lo['dMax']} {_fb(lo['useAnalytic'])} "
              f"{_fd(lo['ratLb'])} {_fd(lo['vFullLb'])} {_fd(lo['vFullUb'])} "
              f"{_fd(lo['gLb'])} {_fd(lo['c2Ub'])} {_fd(lo['errUb'])})")
    hdr = (f"  (w2ab {_fd(w['xLoLogLb'])} {_fd(w['xLoLogUb'])} {_fd(w['xHiLogUb'])} "
           f"{_flw(w['wXLoLog'])} {_flw(w['wXHiLog'])} {_fd(w['epdUb'])} {_few(w['epdW'])}")
    return [hdr, f"    {lo_str}", "    [", *_pack_items([_fsl2ab(s) for s in w["slices"]], 2), "    ]", f"    {_fsq(w['square'])})"]


def _fmt_slab_2c(w: dict) -> list[str]:
    lo = w["lower"]
    ends_s = "[" + ", ".join(str(x) for x in lo["ends"]) + "]"
    caps_s = "[" + ", ".join(str(x) for x in lo["caps"]) + "]"
    bsteps = [
        f"(bs {st['cur']} {st['nxt']} {st['cap']} {st['blockCnt']} {_flw(st['wCurLog'])} {_flw(st['wNxtLog'])} "
        f"{_fmt_mt(st['bTail'])} {_fmt_mt(st['tTail'])} {_fd(st['termUb'])})"
        for st in lo["brunSteps"]
    ]
    bs_str = "[" + ", ".join(bsteps) + "]"
    lo_str = (f"(l2c {_fb(lo['isBrun'])} {lo['a']} {lo['mOdd']} {ends_s} {caps_s} {lo['nD']} {lo['dMax']} "
              f"{_fmt_mt(lo['tail'])} {_fd(lo['c2Ub'])} {_fd(lo['errUb'])} {_fd(lo['ndFactUb'])} "
              f"{_fd(lo['piZUb'])} {_fd(lo['gLb'])} {_fd(lo['s1Ub'])} {_fd(lo['ratLb'])} {_fd(lo['remANormUb'])} {bs_str})")
    hdr = (f"  (w2c {_fd(w['xLoLogLb'])} {_fd(w['xLoLogUb'])} {_fd(w['xHiLogUb'])} {_fd(w['zLogLb'])} {_fd(w['zLogUb'])} "
           f"{_flw(w['wXLoLog'])} {_flw(w['wXHiLog'])} {_flw(w['wZLog'])} {_fd(w['epdUb'])} {_few(w['epdW'])} "
           f"{_fd(w['liRatioUb'])} {_fd(w['vFullLb'])} {_fmt_opt_mt(w['vFullW'])}")
    return [hdr, f"    {lo_str}", "    [", *_pack_items([_fsl2c(s) for s in w["slices"]], 2), "    ]",
            f"    {_fsq(w['square'])} {_fd(w['errQ2NormUb'])})"]


def _parse_data_lean(root: Path) -> list[dict]:
    pat = re.compile(
        r"\{\s*X_lo\s*:=\s*(\d+),\s*X_hi\s*:=\s*(\d+),\s*z\s*:=\s*(\d+),\s*y\s*:=\s*(\d+),"
        r"\s*main_num\s*:=\s*(\d+),\s*err_num\s*:=\s*(\d+),\s*net_num\s*:=\s*(\d+),\s*den\s*:=\s*(\d+)\s*\}"
    )
    txt = (root / "BuchstabSwitching/Certificates/Data.lean").read_text(encoding="utf-8")
    return [{k: int(m.group(i)) for i, k in enumerate(("X_lo", "X_hi", "z", "y", "main_num", "err_num", "net_num", "den"), 1)}
            for m in pat.finditer(txt)]


_SHARD_ABBREVS = [
    "private abbrev d := Dyadic.mk",
    "private abbrev lw := LogWitness.mk",
    "private abbrev aw := AnalyticRangeWitness.mk",
    "private abbrev ew := EpdWitness.mk",
    "private abbrev mt := MertensTailWitness.mk",
    "private abbrev bs := BrunStepWitness.mk",
    "private abbrev sqw := Square2abWitness.mk",
    "private abbrev l2ab := Lower2abWitness.mk",
    "private abbrev s2ab := Slice2abWitness.mk",
    "private abbrev w2ab := Slab2abWitness.mk",
    "private abbrev l2c := Lower2cWitness.mk",
    "private abbrev ms := Slice2cMode.selberg",
    "private abbrev mb := Slice2cMode.evenBonf",
    "private abbrev s2c := Slice2cWitness.mk",
    "private abbrev w2c := Slab2cWitness.mk",
]


def _write_shard(out_path: Path, def_name: str, ty_name: str, blocks: list[list[str]]) -> None:
    lines = [
        "import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstDefs",
        "",
        "set_option maxRecDepth 200000",
        "",
        "/-!",
        f"# Machine-Generated Binary Witness Shard `{def_name}`",
        "Auto-generated by `scripts/sieve_cert/slab_witness_export.py`. Do not edit by hand.",
        "-/",
        "",
        "namespace BuchstabSwitching.SieveInst",
        "",
        *_SHARD_ABBREVS,
        "",
        f"def {def_name} : List {ty_name} := [",
    ]
    for idx, blk in enumerate(blocks):
        lines.extend(blk[:-1] + [blk[-1] + ("," if idx + 1 < len(blocks) else "")])
    lines.extend(["]", "", "end BuchstabSwitching.SieveInst", ""])
    assert len(lines) <= 700, f"{out_path.name} exceeded 700 lines: {len(lines)}"
    out_path.write_text("\n".join(lines), encoding="utf-8")


def export_all_witnesses(root: Path) -> None:
    certs = _parse_data_lean(root)
    assert len(certs) == len(SLABS_2A) + len(SLABS_2B) + len(SLABS_2C)
    bridge_dir, w2a, w2b, w2c, off = root / "BuchstabSwitching/Sieve/Regime2SlabBridge", [], [], [], 0
    for i, sp in enumerate(SLABS_2A):
        res = build_slab_2ab_witness("2a", sp)
        slab_c = _compress_2ab_slices(certs[off + i], res.slab)
        assert verify_slab_2ab_bool(certs[off + i], slab_c), f"2a-{i+1:02d} failed Lean Bool check"
        w2a.append(_fmt_slab_2ab(slab_c))
    off += len(SLABS_2A)
    for i, sp in enumerate(SLABS_2B):
        res = build_slab_2ab_witness("2b", sp)
        slab_c = _compress_2ab_slices(certs[off + i], res.slab)
        assert verify_slab_2ab_bool(certs[off + i], slab_c), f"2b-{i+1:02d} failed Lean Bool check"
        w2b.append(_fmt_slab_2ab(slab_c))
    off += len(SLABS_2B)
    for i, sp in enumerate(SLABS_2C):
        res = build_slab_2c_witness(sp)
        slab_c = _compress_2c_slices(certs[off + i], res.slab)
        assert verify_slab_2c_bool(certs[off + i], slab_c), f"2c-{i+1:02d} failed Lean Bool check"
        w2c.append(_fmt_slab_2c(slab_c))
    for fname, dname, ty, blks in [
        ("SlabCertInstData2a1.lean", "witnesses2a1", "Slab2abWitness", w2a[:10]),
        ("SlabCertInstData2a2.lean", "witnesses2a2", "Slab2abWitness", w2a[10:]),
        ("SlabCertInstData2b1.lean", "witnesses2b1", "Slab2abWitness", w2b[:10]),
        ("SlabCertInstData2b2.lean", "witnesses2b2", "Slab2abWitness", w2b[10:20]),
        ("SlabCertInstData2b3.lean", "witnesses2b3", "Slab2abWitness", w2b[20:30]),
        ("SlabCertInstData2b4.lean", "witnesses2b4", "Slab2abWitness", w2b[30:]),
        ("SlabCertInstData2c1.lean", "witnesses2c1", "Slab2cWitness", w2c[:11]),
        ("SlabCertInstData2c2.lean", "witnesses2c2", "Slab2cWitness", w2c[11:22]),
        ("SlabCertInstData2c3.lean", "witnesses2c3", "Slab2cWitness", w2c[22:33]),
        ("SlabCertInstData2c4.lean", "witnesses2c4", "Slab2cWitness", w2c[33:44]),
        ("SlabCertInstData2c5.lean", "witnesses2c5", "Slab2cWitness", w2c[44:55]),
        ("SlabCertInstData2c6.lean", "witnesses2c6", "Slab2cWitness", w2c[55:]),
    ]:
        _write_shard(bridge_dir / fname, dname, ty, blks)
        print(f"Wrote {fname} ({len(blks)} slabs)")


if __name__ == "__main__":
    export_all_witnesses(Path(__file__).resolve().parents[2])
