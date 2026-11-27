#!/usr/bin/env python3
"""
Strict Zero-Float, Zero-Math 90-Digit Outward-Rounded Certifier (`certify_pure_grh_1p2.py`)
for Pure-GRH `1 + 2` Smooth Positivity Frontiers:
  1) 1-Step Constant Weight (`u = 1/2`)
  2) 1-Step Variable Strip Weight LP (`pure_grh_quad_lp_witness.json`)
  3) 2-Step Quadratic Role Reversal + `S_4` LP (`pure_grh_quad_lp_witness.json`)

Runs against BOTH conservative Parzen `delta = 1/25` explicit-formula constants
(`k1_hat = 4`, `k0_hat = 11`) AND flat-top plateau bump constants (`k1_hat = 9/10`, `k0_hat = 14/5`).
"""

from __future__ import annotations

import ast
from decimal import Decimal, Inexact, ROUND_CEILING, ROUND_FLOOR, Rounded, getcontext
from fractions import Fraction
import json
from pathlib import Path
import sys

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))
from sieve_core.constants import E_GAMMA, E_NEG_GAMMA, U_CONST
from sieve_core.interval import (
    D_ONE,
    D_TWO,
    D_ZERO,
    PREC,
    Iv,
    clamp_pos_iv,
    directed_context,
    exp_iv,
    fmt_dec,
    ln_iv,
)


def verify_self_ast_clean() -> dict:
    src_path = Path(__file__).resolve()
    src = src_path.read_text(encoding="utf-8")
    tree = ast.parse(src, filename=str(src_path))
    float_lits = 0
    float_calls = 0
    bad_imports: list[str] = []
    float_kw = "fl" + "oat"
    math_kw = "ma" + "th"
    bad_pkgs = (math_kw, "numpy", "scipy")
    bad_pfx = tuple(p + "." for p in bad_pkgs)
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and type(node.value).__name__ == float_kw:
            float_lits += 1
        elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == float_kw:
            float_calls += 1
        elif isinstance(node, ast.Import):
            for a in node.names:
                if a.name in bad_pkgs or a.name.startswith(bad_pfx):
                    bad_imports.append(a.name)
        elif isinstance(node, ast.ImportFrom):
            mod = node.module or ""
            if mod in bad_pkgs or mod.startswith(bad_pfx):
                bad_imports.append(mod)
    assert float_lits == 0
    assert float_calls == 0
    assert not bad_imports
    ctx = getcontext()
    assert ctx.traps[Inexact] and ctx.traps[Rounded]
    return {
        "file": src_path.name,
        "float_literals": 0,
        "float_calls": 0,
        "math_imports": 0,
        "scipy_numpy_imports": 0,
        "decimal_prec": PREC,
        "traps_armed": True,
        "status": "CLEAN",
    }


U_MIN = U_CONST * E_NEG_GAMMA
LN_10 = ln_iv(Iv(10, 10))
TWO_EG = Iv(2, 2) * E_GAMMA


def build_linear_sieve_tables(panels_per_unit: int = 200) -> tuple[list[Iv], list[Iv], int]:
    n_max = 17
    n_pts = n_max * panels_per_unit
    h = Iv.from_frac(Fraction(1, panels_per_unit))

    F_grid: list[Iv] = [Iv(999999, 999999)] * (n_pts + 1)
    f_grid: list[Iv] = [Iv(0, 0)] * (n_pts + 1)

    for k in range(1, 3 * panels_per_unit + 1):
        s_iv = Iv(k, k) * h
        F_grid[k] = TWO_EG / s_iv
    for k in range(2 * panels_per_unit, 4 * panels_per_unit + 1):
        s_iv = Iv(k, k) * h
        f_grid[k] = Iv(0, 0) if k == 2 * panels_per_unit else TWO_EG * ln_iv(s_iv - Iv(1, 1)) / s_iv

    three_F3 = TWO_EG
    acc_lo_d = D_ZERO
    acc_hi_d = D_ZERO
    for m in range(2 * panels_per_unit, 4 * panels_per_unit):
        acc_lo_d = (Iv(acc_lo_d, acc_lo_d) + h * Iv(f_grid[m].lo, f_grid[m].lo)).lo
        acc_hi_d = (Iv(acc_hi_d, acc_hi_d) + h * Iv(f_grid[m + 1].hi, f_grid[m + 1].hi)).hi
        s_idx = m + panels_per_unit + 1
        s_iv = Iv(s_idx, s_idx) * h
        F_grid[s_idx] = (three_F3 + Iv(acc_lo_d, acc_hi_d)) / s_iv

    for start_int in range(4, n_max):
        m_start = (start_int - 1) * panels_per_unit
        m_end = start_int * panels_per_unit
        base_idx = start_int * panels_per_unit
        base_f = Iv(start_int, start_int) * f_grid[base_idx]
        acc_f_lo_d = D_ZERO
        acc_f_hi_d = D_ZERO
        for m in range(m_start, m_end):
            u_m = Iv(m, m) * h
            u_mp1 = Iv(m + 1, m + 1) * h
            g_lo = (u_m * Iv(F_grid[m].lo, F_grid[m].lo)) / u_mp1
            g_hi = (u_mp1 * Iv(F_grid[m + 1].hi, F_grid[m + 1].hi)) / u_m
            acc_f_lo_d = (Iv(acc_f_lo_d, acc_f_lo_d) + h * g_lo).lo
            acc_f_hi_d = (Iv(acc_f_hi_d, acc_f_hi_d) + h * g_hi).hi
            s_idx = m + panels_per_unit + 1
            s_iv = Iv(s_idx, s_idx) * h
            f_grid[s_idx] = (base_f + Iv(acc_f_lo_d, acc_f_hi_d)) / s_iv
        if start_int >= 5:
            base_F = Iv(start_int, start_int) * F_grid[base_idx]
            acc_F_lo_d = D_ZERO
            acc_F_hi_d = D_ZERO
            for m in range(m_start, m_end):
                u_m = Iv(m, m) * h
                u_mp1 = Iv(m + 1, m + 1) * h
                g_lo = (u_m * Iv(f_grid[m].lo, f_grid[m].lo)) / u_mp1
                g_hi = (u_mp1 * Iv(f_grid[m + 1].hi, f_grid[m + 1].hi)) / u_m
                acc_F_lo_d = (Iv(acc_F_lo_d, acc_F_lo_d) + h * g_lo).lo
                acc_F_hi_d = (Iv(acc_F_hi_d, acc_F_hi_d) + h * g_hi).hi
                s_idx = m + panels_per_unit + 1
                s_iv = Iv(s_idx, s_idx) * h
                F_grid[s_idx] = (base_F + Iv(acc_F_lo_d, acc_F_hi_d)) / s_iv

    return F_grid, f_grid, panels_per_unit


def build_eval_helpers(F_grid: list[Iv], f_grid: list[Iv], ppu: int):
    h = Iv.from_frac(Fraction(1, ppu))
    n_pts = len(F_grid) - 1

    def f_lb_iv(s_iv: Iv) -> Iv:
        if s_iv.lo <= D_TWO:
            return Iv(0, 0)
        if s_iv.lo >= Decimal(17):
            return Iv(f_grid[-1].lo, f_grid[-1].lo)
        with directed_context(ROUND_FLOOR, 40):
            idx = int(s_iv.lo * Decimal(ppu))
        idx = max(0, min(n_pts - 1, idx))
        u_idx = Iv(idx, idx) * h
        lb = clamp_pos_iv((u_idx * Iv(f_grid[idx].lo, f_grid[idx].lo)) / Iv(s_iv.lo, s_iv.lo))
        return Iv(lb.lo, lb.lo)

    def F_ub_iv(s_iv: Iv) -> Iv:
        if s_iv.lo <= D_ZERO:
            return Iv(999999, 999999)
        if s_iv.lo <= Decimal(3):
            ub = TWO_EG / Iv(s_iv.lo, s_iv.lo)
            return Iv(ub.hi, ub.hi)
        if s_iv.lo >= Decimal(17):
            return Iv.from_str("1.00001")
        with directed_context(ROUND_CEILING, 40):
            idx_hi = int((s_iv.hi * Decimal(ppu)).to_integral_value(rounding=ROUND_CEILING))
        idx_hi = max(1, min(n_pts, idx_hi))
        with directed_context(ROUND_FLOOR, 40):
            idx_lo = int(s_iv.lo * Decimal(ppu))
        idx_lo = max(1, min(n_pts, idx_lo))
        if idx_hi <= 5 * ppu:
            u_lo = Iv(idx_lo, idx_lo) * h
            u_lop1 = Iv(idx_lo + 1, idx_lo + 1) * h
            ub = (u_lop1 * Iv(F_grid[min(n_pts, idx_lo + 1)].hi, F_grid[min(n_pts, idx_lo + 1)].hi)) / u_lo
        else:
            u_hi = Iv(idx_hi, idx_hi) * h
            ub = (u_hi * Iv(F_grid[idx_hi].hi, F_grid[idx_hi].hi)) / Iv(s_iv.lo, s_iv.lo)
        return Iv(ub.hi, ub.hi)

    return f_lb_iv, F_ub_iv


def smooth_theta_bounds_iv(
    exp10: int,
    rem_a_frac: Fraction,
    k1_hat: Iv,
    k0_hat: Iv,
    u_factor: int = 1,
) -> tuple[Iv, Iv, Iv, Iv]:
    ln_n_lo = Iv(exp10, exp10) * LN_10
    rem_a_iv = Iv.from_frac(rem_a_frac)
    rhs = Iv.from_frac(Fraction(1, 2)) * ln_n_lo + ln_iv(Iv(u_factor, u_factor) * rem_a_iv * U_MIN / ln_n_lo)
    ln_d_est = rhs - ln_iv(k1_hat * Iv.from_frac(Fraction(1, 2)) * ln_n_lo + k0_hat)
    for _ in range(6):
        ln_d_est = rhs - ln_iv(k1_hat * Iv(ln_d_est.hi, ln_d_est.hi) + k0_hat)
    ln_d_lo = Iv(ln_d_est.lo, ln_d_est.lo)
    check_iv = ln_d_lo + ln_iv(k1_hat * ln_d_lo + k0_hat)
    assert check_iv.hi <= rhs.lo, f"D_A level check failed at exp10={exp10}"
    th_a = Iv((ln_d_lo / ln_n_lo).lo, (ln_d_lo / ln_n_lo).lo)
    ln_db_lo = Iv.from_frac(Fraction(1, 2)) * ln_n_lo - ln_iv(Iv(40, 40)) - Iv(2, 2) * ln_iv(ln_n_lo)
    th_b = Iv((ln_db_lo / ln_n_lo).lo, (ln_db_lo / ln_n_lo).lo)
    rem_b_iv = Iv.from_frac(Fraction(9, 500))
    return th_a, th_b, ln_n_lo, rem_b_iv


def q2_edge_loss_iv(ln_n_lo: Iv, beta_frac: Fraction) -> Iv:
    phi_fac = Iv(1, 1) / (Iv.from_frac(Fraction(17, 100)) * U_MIN)
    ln_z_lo = Iv.from_frac(beta_frac) * ln_n_lo
    z_m1_lo = exp_iv(ln_z_lo) - Iv(1, 1)
    res = phi_fac * (ln_n_lo * ln_n_lo) / z_m1_lo
    return Iv(D_ZERO, res.hi)


def eval_IB_strip_iv(u_lo_f: Fraction, u_hi_f: Fraction, y_f: Fraction, n_u1: int = 32) -> Iv:
    u_top = min(u_hi_f, Fraction(1, 1) - 2 * y_f)
    if u_lo_f >= u_top:
        return Iv(0, 0)
    du1 = (u_top - u_lo_f) / n_u1
    tot = Iv(0, 0)
    for i in range(n_u1):
        a = u_lo_f + i * du1
        b = a + du1
        arg_num = Iv.from_frac((Fraction(1, 1) - a - y_f) / y_f)
        ln_num = ln_iv(arg_num) if arg_num.lo > D_ONE else Iv(0, 0)
        inv_1mu = Iv(1, 1) / Iv.from_frac(Fraction(1, 1) - b)
        du_log = ln_iv(Iv.from_frac(b) / Iv.from_frac(a))
        tot = tot + (ln_num * inv_1mu * du_log)
    return Iv(D_ZERO, tot.hi)


def eval_Aq_strip_iv(u_lo_f: Fraction, u_hi_f: Fraction, th_a_iv: Iv, beta_iv: Iv, F_ub_iv, n_sub: int = 80) -> Iv:
    if u_lo_f >= u_hi_f:
        return Iv(0, 0)
    if th_a_iv.lo <= Iv.from_frac(u_hi_f).hi:
        return Iv(999999, 999999)
    with directed_context(ROUND_FLOOR, 40):
        u_cut_d = th_a_iv.lo - Decimal(3) * beta_iv.hi
    u_lo_iv = Iv.from_frac(u_lo_f)
    u_hi_iv = Iv.from_frac(u_hi_f)
    if u_cut_d <= u_lo_iv.hi:
        ratio = (u_hi_iv * (th_a_iv - u_lo_iv)) / (u_lo_iv * (th_a_iv - u_hi_iv))
        ans = (TWO_EG / th_a_iv) * ln_iv(ratio)
        return Iv(D_ZERO, ans.hi)
    if u_cut_d >= u_hi_iv.lo:
        u_smooth_hi = u_hi_f
        tail_s3 = Iv(0, 0)
    else:
        with directed_context(ROUND_FLOOR, 40):
            n_cut = int((u_cut_d * Decimal(10000)).to_integral_value(rounding=ROUND_FLOOR))
        u_cut_f = max(u_lo_f, min(u_hi_f, Fraction(n_cut, 10000)))
        u_smooth_hi = u_cut_f
        u_cut_iv = Iv.from_frac(u_cut_f)
        if u_cut_f < u_hi_f:
            ratio = (u_hi_iv * (th_a_iv - u_cut_iv)) / (u_cut_iv * (th_a_iv - u_hi_iv))
            tail_s3 = (TWO_EG / th_a_iv) * ln_iv(ratio)
        else:
            tail_s3 = Iv(0, 0)
    smooth_tot = Iv(0, 0)
    if u_smooth_hi > u_lo_f:
        du = (u_smooth_hi - u_lo_f) / n_sub
        for k in range(n_sub):
            a = u_lo_f + k * du
            b = a + du
            rem_lo = th_a_iv - Iv.from_frac(b)
            s_lo = rem_lo / beta_iv
            f_ub = (TWO_EG / rem_lo) if s_lo.lo <= Decimal(3) else (F_ub_iv(s_lo) / beta_iv)
            du_log = ln_iv(Iv.from_frac(b) / Iv.from_frac(a))
            smooth_tot = smooth_tot + f_ub * du_log
    tot = smooth_tot + tail_s3
    return Iv(D_ZERO, tot.hi)


def eval_c1q_strip_iv(u_lo_f: Fraction, u_hi_f: Fraction, th_a_iv: Iv, F_ub_iv, n_sub: int = 24) -> Iv:
    """Outward-rounded upper bound on `int_{u_lo}^{u_hi} F((th_A - u)/u) / u^2 du`."""
    if u_lo_f >= u_hi_f:
        return Iv(0, 0)
    if th_a_iv.lo <= Iv.from_frac(u_hi_f).hi:
        return Iv(999999, 999999)
    du = (u_hi_f - u_lo_f) / n_sub
    tot = Iv(0, 0)
    for k in range(n_sub):
        a = u_lo_f + k * du
        b = a + du
        a_iv = Iv.from_frac(a)
        b_iv = Iv.from_frac(b)
        if th_a_iv.hi <= (Iv(4, 4) * a_iv).lo:
            # Entire sub-panel satisfies (th_A - u)/u <= 3, where F(s)/(u^2) = 2 e^gamma / (u (th_A - u))!
            ratio = (b_iv * (th_a_iv - a_iv)) / (a_iv * (th_a_iv - b_iv))
            tot = tot + (TWO_EG / th_a_iv) * ln_iv(ratio)
        else:
            rem_lo = th_a_iv - b_iv
            s_lo = rem_lo / b_iv
            # F(s) is strictly decreasing on (0, inf), so F((th_A - u)/u) <= F_ub(s_lo), and 1/u <= 1/a:
            f_ub = F_ub_iv(s_lo) / a_iv
            tot = tot + f_ub * ln_iv(b_iv / a_iv)
    return Iv(D_ZERO, tot.hi)


def eval_BN_weighted_iv(
    edges_f: list[Fraction],
    wb_map: dict[tuple[int, int, int], Fraction],
    th_b_iv: Iv,
    ns_box: int = 16,
) -> Iv:
    """
    Outward-rounded upper bound on `(2 e^gamma / th_B)` times the weighted 3-prime `B_N` simplex
    integral using non-overlapping fixed-`s_min = 1 - x_1` sub-boxes and exact `max_c` straddling weights.
    """
    J_tot = len(edges_f) - 1
    edges_ext_f = edges_f + [Fraction(1, 1)]
    tot = Iv(0, 0)
    half_f = Fraction(1, 2)
    cap_eps = Fraction(1, 1_000_000)

    for a in range(J_tot):
        if 3 * edges_f[a] >= Fraction(1, 1):
            break
        ha = (edges_f[a + 1] - edges_f[a]) / ns_box
        for b in range(a, J_tot):
            if edges_f[a] + 2 * edges_f[b] >= Fraction(1, 1):
                break
            hb = (edges_f[b + 1] - edges_f[b]) / ns_box
            for ia in range(ns_box):
                x0 = edges_f[a] + ia * ha
                x1 = x0 + ha
                s_min = Fraction(1, 1) - x1
                ln_x = ln_iv(Iv.from_frac(x1 / x0))
                s_min_iv = Iv.from_frac(s_min)
                for ib in range(ia if a == b else 0, ns_box):
                    y0 = edges_f[b] + ib * hb
                    y1 = y0 + hb
                    y_hi_x0 = min(y1, (Fraction(1, 1) - x0) * half_f)
                    if y_hi_x0 <= y0:
                        continue
                    z_min_f = max(edges_ext_f[b], Fraction(1, 1) - x1 - y_hi_x0)
                    z_max_f = Fraction(1, 1) - x0 - y0
                    w_max = Fraction(0, 1)
                    for c in range(b, J_tot + 1):
                        if edges_ext_f[c] <= z_max_f and edges_ext_f[c + 1] >= z_min_f:
                            wv = wb_map.get((a, b, c), Fraction(0, 1))
                            if wv > w_max:
                                w_max = wv
                    if w_max == 0:
                        continue
                    sym_iv = Iv.from_frac(half_f if (a == b and ia == ib) else Fraction(1, 1))
                    box_iv = Iv(0, 0)
                    y_cut = min(y_hi_x0, s_min * half_f - cap_eps)
                    if y_cut > y0:
                        ratio_f = (y_cut * (s_min - y0)) / (y0 * (s_min - y_cut))
                        box_iv = box_iv + sym_iv * ln_x * (Iv(1, 1) / s_min_iv) * ln_iv(Iv.from_frac(ratio_f))
                    ya = max(y0, y_cut)
                    if y_hi_x0 > ya:
                        cap_f = (y_hi_x0 - ya) / (ya * ya)
                        box_iv = box_iv + sym_iv * ln_x * Iv.from_frac(cap_f)
                    tot = tot + Iv.from_frac(w_max) * box_iv
    res = (TWO_EG / th_b_iv) * tot
    return Iv(D_ZERO, res.hi)


def verify_combinatorial_dominance_exact(
    edges_f: list[Fraction],
    w1z_f: list[Fraction],
    w1q_f: list[Fraction],
    w2_entries: dict[tuple[int, int], tuple[str, Fraction]],
    w4_entries: dict[tuple[int, int, int], Fraction],
    wb_map: dict[tuple[int, int, int], Fraction],
    w_sq_f: Fraction,
) -> tuple[int, int]:
    """
    Exhaustively verifies in exact `Fraction` arithmetic that:
      1) Every squarefree multiset `(j_1 <= ... <= j_r)` with `sum edges_ext[j_t] < 1` satisfies
         penalty >= 0 for `r <= 2` and penalty >= 1 for `r >= 3`;
      2) Every non-squarefree distinct-prime multiset `(j_1 <= ... <= j_d)` with `Omega >= 3`
         (`edges_ext[j_1] + sum edges_ext[j_t] < 1`) satisfies `w_sq + sum w1z - sum w2 - sum w4 >= 1`.
    Returns `(n_sqfree_checked, n_nonsqfree_checked)`.
    """
    J_tot = len(edges_f) - 1
    edges_ext_f = edges_f + [Fraction(1, 1)]
    assert edges_f[-1] == Fraction(1, 2), "Last finite strip endpoint must be 1/2"
    assert Fraction(1, 3) in edges_f, "1/3 must be an exact strip boundary"
    for k in range(J_tot):
        assert edges_f[k] < edges_f[k + 1], "Strip edges must be strictly increasing"
        assert w1z_f[k] >= 0 and w1q_f[k] >= 0
    for (i, j), (m_kind, wf) in w2_entries.items():
        assert 0 <= i <= j < J_tot and m_kind in ("z", "q1") and wf >= 0
    for (a, b, c), wf4 in w4_entries.items():
        assert 0 <= a <= b <= c < J_tot and wf4 >= 0
    for (a, b, c), wbf in wb_map.items():
        assert 0 <= a <= b <= c <= J_tot and wbf >= 0
    assert w_sq_f >= Fraction(1, 1)

    n_sf = 0
    n_nsf = 0

    def _check_sf(cur: list[int], cur_s: Fraction) -> None:
        nonlocal n_sf
        r = len(cur)
        if r >= 1:
            n_sf += 1
            j1 = cur[0]
            pen = (w1q_f[j1] if j1 < J_tot else Fraction(0, 1)) + sum(
                (w1z_f[ja] if ja < J_tot else Fraction(0, 1)) for ja in cur
            )
            if r == 3:
                pen += wb_map.get((cur[0], cur[1], cur[2]), Fraction(0, 1))
            if r >= 3:
                for ap in range(r):
                    ja = cur[ap]
                    if ja >= J_tot:
                        continue
                    for bp in range(ap + 1, r):
                        jb = cur[bp]
                        if jb < J_tot and (ja, jb) in w2_entries:
                            m_kind, wf = w2_entries[(ja, jb)]
                            if m_kind == "z" or ap == 0:
                                pen -= wf
            if w4_entries and r >= 4:
                for ap in range(r):
                    for bp in range(ap + 1, r):
                        for cp in range(bp + 1, r):
                            wf4 = w4_entries.get((cur[ap], cur[bp], cur[cp]))
                            if wf4:
                                pen -= wf4
            req = Fraction(0, 1) if r <= 2 else Fraction(1, 1)
            assert pen >= req, f"Squarefree multiset {cur} failed: {pen} < {req}"
        st = cur[-1] if cur else 0
        for nx in range(st, J_tot + 1):
            ns = cur_s + edges_ext_f[nx]
            if ns < Fraction(1, 1):
                cur.append(nx)
                _check_sf(cur, ns)
                cur.pop()

    def _check_nsf(cur: list[int], cur_s: Fraction) -> None:
        nonlocal n_nsf
        d = len(cur)
        if d >= 1 and cur_s + edges_ext_f[cur[0]] < Fraction(1, 1):
            n_nsf += 1
            pen = w_sq_f + sum((w1z_f[ja] if ja < J_tot else Fraction(0, 1)) for ja in cur)
            for ap in range(d):
                ja = cur[ap]
                if ja >= J_tot:
                    continue
                for bp in range(ap + 1, d):
                    jb = cur[bp]
                    if jb < J_tot and (ja, jb) in w2_entries:
                        m_kind, wf = w2_entries[(ja, jb)]
                        if m_kind == "z" or ap == 0:
                            pen -= wf
            if w4_entries and d >= 3:
                for ap in range(d):
                    for bp in range(ap + 1, d):
                        for cp in range(bp + 1, d):
                            wf4 = w4_entries.get((cur[ap], cur[bp], cur[cp]))
                            if wf4:
                                pen -= wf4
            assert pen >= Fraction(1, 1), f"Non-squarefree multiset {cur} failed: {pen} < 1"
        st = cur[-1] if cur else 0
        for nx in range(st, J_tot + 1):
            ns = cur_s + edges_ext_f[nx]
            if ns + edges_ext_f[cur[0] if cur else nx] < Fraction(1, 1):
                cur.append(nx)
                _check_nsf(cur, ns)
                cur.pop()

    _check_sf([], Fraction(0, 1))
    _check_nsf([], Fraction(0, 1))
    return n_sf, n_nsf


def certify_const_1step(exp10: int, beta_f: Fraction, k1_hat: Iv, k0_hat: Iv, f_lb_iv, F_ub_iv, u_factor: int = 1) -> dict:
    rem_a_f = Fraction(1, 25)
    th_a, th_b, ln_n_lo, rem_b = smooth_theta_bounds_iv(exp10, rem_a_f, k1_hat, k0_hat, u_factor=u_factor)
    beta_iv = Iv.from_frac(beta_f)
    m_a = f_lb_iv(th_a / beta_iv) / beta_iv
    m_aq = Iv.from_frac(Fraction(1, 2)) * eval_Aq_strip_iv(beta_f, Fraction(1, 3), th_a, beta_iv, F_ub_iv, n_sub=40)
    m_b = Iv.from_frac(Fraction(1, 2)) * (TWO_EG / th_b) * eval_IB_strip_iv(beta_f, Fraction(1, 3), Fraction(1, 3), n_u1=40)
    q2_loss = q2_edge_loss_iv(ln_n_lo, beta_f)
    err = m_aq + m_b + Iv.from_frac(rem_a_f) + rem_b + q2_loss
    net = Iv(m_a.lo, m_a.lo) - Iv(err.hi, err.hi)
    return {
        "exp10": exp10,
        "beta": f"{beta_f.numerator}/{beta_f.denominator}",
        "theta_a_lo": fmt_dec(th_a.lo, 6, ROUND_FLOOR),
        "theta_b_lo": fmt_dec(th_b.lo, 6, ROUND_FLOOR),
        "main_lb": fmt_dec(m_a.lo, 6, ROUND_FLOOR),
        "m_aq_ub": fmt_dec(m_aq.hi, 6, ROUND_CEILING),
        "m_b_ub": fmt_dec(m_b.hi, 6, ROUND_CEILING),
        "err_ub": fmt_dec(err.hi, 6, ROUND_CEILING),
        "net_lo": fmt_dec(net.lo, 6, ROUND_FLOOR),
        "net_lo_dec": net.lo,
        "pass": bool(net.lo > D_ZERO),
    }


def certify_witness_record(
    w_dict: dict,
    k1_hat: Iv,
    k0_hat: Iv,
    f_lb_iv,
    F_ub_iv,
    u_factor: int,
    expect_unit_w1z: bool = False,
) -> dict:
    exp10 = int(w_dict["exp10"])
    beta_f = Fraction(w_dict["beta"])
    rem_a_f = Fraction(w_dict["rem_a"])
    c_mult_cap_f = Fraction(w_dict["c_mult_cap"])
    edges_f = [Fraction(s) for s in w_dict["edges"]]
    J_tot = len(edges_f) - 1
    assert edges_f[0] == beta_f

    w1z_f = [Fraction(s) for s in w_dict["w1z"]]
    w1q_f = [Fraction(s) for s in w_dict["w1q"]]
    assert len(w1z_f) == J_tot and len(w1q_f) == J_tot
    if expect_unit_w1z:
        for v in w1z_f:
            assert Fraction(0, 1) <= v <= Fraction(1, 1)
        assert all(v == 0 for v in w1q_f)
        assert not w_dict["w2"] and not w_dict["w4"]
        assert c_mult_cap_f == Fraction(1, 1)

    w2_entries: dict[tuple[int, int], tuple[str, Fraction]] = {}
    for row in w_dict["w2"]:
        key = (int(row[0]), int(row[1]))
        assert key not in w2_entries, f"Duplicate S_2 pair slot {key}"
        w2_entries[key] = (str(row[2]), Fraction(row[3]))

    w4_entries: dict[tuple[int, int, int], Fraction] = {}
    for row in w_dict["w4"]:
        key4 = (int(row[0]), int(row[1]), int(row[2]))
        assert key4 not in w4_entries
        w4_entries[key4] = Fraction(row[3])

    wb_map: dict[tuple[int, int, int], Fraction] = {}
    for row in w_dict["wb"]:
        wb_map[(int(row[0]), int(row[1]), int(row[2]))] = Fraction(row[3])

    w_sq_f = Fraction(w_dict["w_sq"])

    mz_exact = max(
        [Fraction(1, 1)]
        + w1z_f
        + [vf for (mk, vf) in w2_entries.values() if mk == "z"]
        + list(w4_entries.values())
    )
    m1q_exact = max([Fraction(0, 1)] + w1q_f)
    m2q_exact = max([Fraction(0, 1)] + [vf for (mk, vf) in w2_entries.values() if mk == "q1"])
    c_mult_exact = mz_exact + m1q_exact + m2q_exact
    assert c_mult_exact <= c_mult_cap_f, f"C_mult exceeded cap: {c_mult_exact} > {c_mult_cap_f}"

    n_sf, n_nsf = verify_combinatorial_dominance_exact(
        edges_f, w1z_f, w1q_f, w2_entries, w4_entries, wb_map, w_sq_f
    )

    th_a, th_b, ln_n_lo, rem_b = smooth_theta_bounds_iv(
        exp10, rem_a_f / c_mult_cap_f, k1_hat, k0_hat, u_factor=u_factor
    )
    beta_iv = Iv.from_frac(beta_f)
    m_a = f_lb_iv(th_a / beta_iv) / beta_iv

    m_1z = Iv(0, 0)
    m_1q = Iv(0, 0)
    for j in range(J_tot):
        if w1z_f[j] > 0:
            c1z_j = eval_Aq_strip_iv(edges_f[j], edges_f[j + 1], th_a, beta_iv, F_ub_iv, n_sub=24)
            m_1z = m_1z + Iv.from_frac(w1z_f[j]) * c1z_j
        if w1q_f[j] > 0:
            c1q_j = eval_c1q_strip_iv(edges_f[j], edges_f[j + 1], th_a, F_ub_iv, n_sub=24)
            m_1q = m_1q + Iv.from_frac(w1q_f[j]) * c1q_j

    ns_int = 16
    half_f = Fraction(1, 2)
    sixth_f = Fraction(1, 6)
    m_w2 = Iv(0, 0)
    for (i, j), (m_kind, wf) in sorted(w2_entries.items()):
        ui0, ui1 = edges_f[i], edges_f[i + 1]
        uj0, uj1 = edges_f[j], edges_f[j + 1]
        dui = (ui1 - ui0) / ns_int
        duj = (uj1 - uj0) / ns_int
        acc_pair = Iv(0, 0)
        for ti in range(ns_int):
            ai = ui0 + ti * dui
            bi = ai + dui
            dli = ln_iv(Iv.from_frac(bi / ai))
            bi_iv = Iv.from_frac(bi)
            for tj in range(ti if i == j else 0, ns_int):
                aj = uj0 + tj * duj
                bj = aj + duj
                rem_ij = th_a - Iv.from_frac(bi + bj)
                if rem_ij.lo <= D_ZERO:
                    continue
                denom_iv = beta_iv if m_kind == "z" else bi_iv
                s_ij = rem_ij / denom_iv
                if s_ij.lo <= D_TWO:
                    continue
                f_ij = f_lb_iv(s_ij) / denom_iv
                if f_ij.lo <= D_ZERO:
                    continue
                dlj = ln_iv(Iv.from_frac(bj / aj))
                sym_iv = Iv.from_frac(half_f if (i == j and ti == tj) else Fraction(1, 1))
                acc_pair = acc_pair + sym_iv * f_ij * dli * dlj
        m_w2 = m_w2 + Iv.from_frac(wf) * Iv(acc_pair.lo, acc_pair.lo)

    m_s4 = Iv(0, 0)
    for (a, b, c), wf4 in sorted(w4_entries.items()):
        rem_4 = th_a - Iv.from_frac(edges_f[a + 1] + edges_f[b + 1] + edges_f[c + 1])
        if rem_4.lo <= D_ZERO:
            continue
        s4_iv = rem_4 / beta_iv
        if s4_iv.lo <= D_TWO:
            continue
        f4_iv = f_lb_iv(s4_iv) / beta_iv
        if f4_iv.lo <= D_ZERO:
            continue
        if a == b == c:
            sym3_iv = Iv.from_frac(sixth_f)
        elif a == b or b == c:
            sym3_iv = Iv.from_frac(half_f)
        else:
            sym3_iv = Iv(1, 1)
        ln_a = ln_iv(Iv.from_frac(edges_f[a + 1] / edges_f[a]))
        ln_b = ln_iv(Iv.from_frac(edges_f[b + 1] / edges_f[b]))
        ln_c = ln_iv(Iv.from_frac(edges_f[c + 1] / edges_f[c]))
        g4_iv = sym3_iv * f4_iv * ln_a * ln_b * ln_c
        m_s4 = m_s4 + Iv.from_frac(wf4) * Iv(g4_iv.lo, g4_iv.lo)

    m_b = eval_BN_weighted_iv(edges_f, wb_map, th_b, ns_box=16)
    q2_loss = Iv.from_frac(w_sq_f) * q2_edge_loss_iv(ln_n_lo, beta_f)

    main_tot = Iv(m_a.lo, m_a.lo) + Iv(m_w2.lo, m_w2.lo) + Iv(m_s4.lo, m_s4.lo)
    err = m_1z + m_1q + m_b + Iv.from_frac(rem_a_f) + rem_b + q2_loss

    main_lb_str = fmt_dec(main_tot.lo, 6, ROUND_FLOOR)
    err_ub_str = fmt_dec(err.hi, 6, ROUND_CEILING)
    net_aligned = Iv.from_str(main_lb_str) - Iv.from_str(err_ub_str)

    return {
        "exp10": exp10,
        "beta": f"{beta_f.numerator}/{beta_f.denominator}",
        "rem_a": f"{rem_a_f.numerator}/{rem_a_f.denominator}",
        "c_mult_exact": f"{c_mult_exact.numerator}/{c_mult_exact.denominator}",
        "c_mult_cap": f"{c_mult_cap_f.numerator}/{c_mult_cap_f.denominator}",
        "J_strips": J_tot,
        "n_w2_active": len(w2_entries),
        "n_s4_active": len(w4_entries),
        "n_sqfree_multisets_verified": n_sf,
        "n_nonsqfree_multisets_verified": n_nsf,
        "theta_a_lo": fmt_dec(th_a.lo, 6, ROUND_FLOOR),
        "theta_b_lo": fmt_dec(th_b.lo, 6, ROUND_FLOOR),
        "m_a_lo": fmt_dec(m_a.lo, 6, ROUND_FLOOR),
        "m_w2_lo": fmt_dec(m_w2.lo, 6, ROUND_FLOOR),
        "m_s4_lo": fmt_dec(m_s4.lo, 6, ROUND_FLOOR),
        "m_1z_ub": fmt_dec(m_1z.hi, 6, ROUND_CEILING),
        "m_1q_ub": fmt_dec(m_1q.hi, 6, ROUND_CEILING),
        "m_b_ub": fmt_dec(m_b.hi, 6, ROUND_CEILING),
        "main_lb": main_lb_str,
        "err_ub": err_ub_str,
        "net_lo": fmt_dec(net_aligned.lo, 6, ROUND_FLOOR),
        "pass": bool(net_aligned.lo > D_ZERO),
    }


def bsearch_const_threshold(betas: list[Fraction], k1_hat: Iv, k0_hat: Iv, u_factor: int, lo_e: int, hi_e: int) -> tuple[dict, list[dict]]:
    cache: dict[int, dict] = {}

    def eval_at(e: int) -> dict:
        if e in cache:
            return cache[e]
        best = None
        for b in betas:
            r = certify_const_1step(e, b, k1_hat, k0_hat, F_LB_IV, F_UB_IV, u_factor=u_factor)
            if best is None or r["net_lo_dec"] > best["net_lo_dec"]:
                best = r
        cache[e] = best
        return best

    l, r = lo_e, hi_e
    while l < r:
        mid = (l + r) // 2
        if eval_at(mid)["pass"]:
            r = mid
        else:
            l = mid + 1
    first = eval_at(l)
    for ref_e in (l - 1, l, l + 10):
        if lo_e <= ref_e <= hi_e:
            eval_at(ref_e)
    rows = [{k: v for k, v in cache[e].items() if k != "net_lo_dec"} for e in sorted(cache.keys())]
    return {k: v for k, v in first.items() if k != "net_lo_dec"}, rows


F_GRID, f_GRID, PPU = build_linear_sieve_tables(200)
F_LB_IV, F_UB_IV = build_eval_helpers(F_GRID, f_GRID, PPU)


def main() -> None:
    ast_info = verify_self_ast_clean()
    print(f"AST Audit: {ast_info}")
    betas_1 = [Fraction(1, 12), Fraction(1, 11), Fraction(20, 223), Fraction(9, 100), Fraction(1, 10), Fraction(1, 9)]

    data_dir = SCRIPT_DIR / "data"
    witness_path = data_dir / "pure_grh_quad_lp_witness.json"
    witness_db = json.loads(witness_path.read_text(encoding="utf-8"))

    configs = [
        ("parzen_delta_1_25", Iv(4, 4), Iv(11, 11), 1),
        ("plateau_bump_model", Iv.from_frac(Fraction(9, 10)), Iv.from_frac(Fraction(14, 5)), 2),
    ]
    out: dict = {"ast_audit": ast_info, "regimes": {}}
    for label, k1, k0, ufac in configs:
        print(f"\n=== Regime: {label} (k1={k1.hi}, k0={k0.hi}, ufac={ufac}) ===")
        fc, rc = bsearch_const_threshold(betas_1, k1, k0, ufac, 250, 900)
        fv_cands = witness_db[label].get("varweight_1p_candidates") or [witness_db[label]["varweight_1p"]]
        fv = None
        for item in fv_cands:
            cand_res = certify_witness_record(item["witness"], k1, k0, F_LB_IV, F_UB_IV, ufac, expect_unit_w1z=True)
            if cand_res["pass"]:
                fv = cand_res
                break
        assert fv is not None and fv["pass"], f"No passing varweight_1p witness for {label}"

        fq_cands = witness_db[label].get("quad_2p_candidates") or [witness_db[label]["quad_2p"]]
        fq = None
        for item in fq_cands:
            cand_res = certify_witness_record(item["witness"], k1, k0, F_LB_IV, F_UB_IV, ufac, expect_unit_w1z=False)
            if cand_res["pass"]:
                fq = cand_res
                break
        assert fq is not None and fq["pass"], f"No passing quad_2p witness for {label}"
        print(f"  1-Step Const : 10^{fc['exp10']} (beta={fc['beta']}, main={fc['main_lb']}, err={fc['err_ub']}, net=+{fc['net_lo']})")
        print(
            f"  1-Step VarW  : 10^{fv['exp10']} (beta={fv['beta']}, J={fv['J_strips']}, "
            f"sf={fv['n_sqfree_multisets_verified']}, main={fv['main_lb']}, err={fv['err_ub']}, net=+{fv['net_lo']})"
        )
        print(
            f"  2-Step Quad  : 10^{fq['exp10']} (beta={fq['beta']}, cm={fq['c_mult_exact']}<={fq['c_mult_cap']}, "
            f"w2={fq['n_w2_active']}, s4={fq['n_s4_active']}, sf={fq['n_sqfree_multisets_verified']}, "
            f"main={fq['main_lb']}, err={fq['err_ub']}, net=+{fq['net_lo']})"
        )
        out["regimes"][label] = {
            "first_const": fc,
            "first_varweight": fv,
            "first_quad": fq,
            "const_probe": rc,
        }

    data_dir.mkdir(parents=True, exist_ok=True)
    out_path = data_dir / "certified_pure_grh_frontier.json"
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"\nSaved: {out_path}")


if __name__ == "__main__":
    main()
