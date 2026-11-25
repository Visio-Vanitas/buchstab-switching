"""
Linear sieve functions `f(s)`, `F(s)`, Lyapunov weight `h(s)`, BJS Table 1,
and finite-terminating outward-rounded Buchstab error operator `E_n(s)`.
"""

from __future__ import annotations

from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR
from fractions import Fraction

from .constants import E2, E_GAMMA, ODD_PRIMES
from .interval import D_FOUR, D_ONE, D_THREE, D_TWO, D_ZERO, Iv, directed_context, exp_iv, ln_iv, min_iv
from .primes_and_mertens import eps_large_u_two_var, eps_sup_two_var

# Explicit BJS linear sieve Table 1 pairs (k, C1, C2) for eps <= 1/k
# (Bordignon, Johnston, Starichkova, arXiv:2207.09452v2, Table 1 / Theorem 6).
BJS_TABLE: list[tuple[int, int, int]] = [
    (63, 738, 740), (65, 681, 683), (67, 636, 638), (69, 597, 599),
    (71, 565, 566), (73, 536, 537), (75, 512, 513), (77, 490, 491),
    (79, 470, 471), (81, 452, 453), (83, 437, 437), (85, 422, 422),
    (87, 408, 409), (89, 396, 396), (91, 384, 385), (93, 373, 374),
    (95, 363, 364), (97, 353, 354), (99, 345, 345), (101, 336, 337),
    (103, 328, 329), (105, 321, 322), (107, 314, 315), (109, 307, 308),
    (115, 289, 290), (121, 273, 275), (131, 251, 253), (141, 233, 235),
    (151, 218, 220), (161, 205, 207), (171, 194, 196), (181, 184, 186),
    (191, 175, 178), (200, 163, 164), (220, 154, 156), (250, 145, 147),
    (300, 135, 137), (400, 122, 124), (500, 115, 117), (1000, 103, 105),
]


def lookup_bjs(eps: Iv) -> tuple[int, int, int]:
    """Return `(k, C1, C2)` for `eps.hi * k <= 1`."""
    best = None
    with directed_context(ROUND_CEILING, 100):
        for k, c1, c2 in BJS_TABLE:
            if eps.hi * Decimal(k) <= D_ONE:
                best = (k, c1, c2)
    if best is None:
        raise AssertionError(f"eps={eps} exceeds 1/63 for BJS Table 1")
    return best


def _trap_step_error(coeff_str: str, h: Iv) -> Iv:
    return (Iv.from_str(coeff_str) * h * h * h) / Iv(12, 12)


def _i1_grid_build(n_panels: int = 2000) -> tuple[Iv, list[Iv]]:
    """Outward-rounded cumulative `I_F(u) = int_2^u ln(t-1)/t dt` on `[2, 4]`."""
    h = Iv.from_frac(Fraction(2, n_panels))
    err = _trap_step_error("1.3", h)
    grid = [Iv(0, 0)]
    acc = Iv(0, 0)
    g_prev = Iv(0, 0)
    for k in range(n_panels):
        u1 = Iv(2, 2) + Iv(k + 1, k + 1) * h
        g_cur = ln_iv(u1 - Iv(1, 1)) / u1
        trap = Iv.from_frac(Fraction(1, 2)) * (g_prev + g_cur) * h
        acc = Iv((acc + trap - err).lo, (acc + trap + err).hi)
        grid.append(acc)
        g_prev = g_cur
    return h, grid


_IF_N = 2000
_IF_H, _IF_GRID = _i1_grid_build(_IF_N)


def f_sieve_iv(s: Iv) -> Iv:
    """Outward-rounded monotone enclosure of Buchstab lower function `f(s)` on `s in [0, 6]`."""
    if s.hi <= D_TWO:
        return Iv(0, 0)
    if s.lo != s.hi:
        return Iv(f_sieve_iv(Iv(s.lo, s.lo)).lo, f_sieve_iv(Iv(s.hi, s.hi)).hi)
    if s.hi <= D_FOUR:
        return (Iv(2, 2) * E_GAMMA * ln_iv(s - Iv(1, 1))) / s
    if s.hi <= Decimal(6):
        a_out = Iv(3, 3)
        b_out = s - Iv(1, 1)
        n_out = 200
        h_out = (b_out - a_out) / Iv(n_out, n_out)
        err_i = _trap_step_error("1.3", h_out)
        err_phi = _trap_step_error("0.3", h_out)
        i_cur = Iv(0, 0)
        tot = Iv(0, 0)
        phi0 = Iv(0, 0)
        g0 = ln_iv(a_out - Iv(2, 2)) / (a_out - Iv(1, 1))
        for k in range(n_out):
            t1 = a_out + Iv(k + 1, k + 1) * h_out
            g1 = ln_iv(t1 - Iv(2, 2)) / (t1 - Iv(1, 1))
            trap_i = Iv.from_frac(Fraction(1, 2)) * (g0 + g1) * h_out
            i_next = Iv((i_cur + trap_i - err_i).lo, (i_cur + trap_i + err_i).hi)
            phi1 = i_next / t1
            trap_phi = Iv.from_frac(Fraction(1, 2)) * (phi0 + phi1) * h_out
            tot = Iv((tot + trap_phi - err_phi).lo, (tot + trap_phi + err_phi).hi)
            i_cur, phi0, g0 = i_next, phi1, g1
        return (Iv(2, 2) * E_GAMMA * (ln_iv(s - Iv(1, 1)) + tot)) / s
    raise ValueError(f"f_sieve_iv out of domain [0, 6]: {s}")


def f_lin_lb(s: Iv) -> Iv:
    """Monotone lower bound on `f(s)` for any `s >= 2` (clamped at `6` when `s > 6`)."""
    s_pt = s.lo
    if s_pt <= D_TWO:
        return Iv(0, 0)
    if s_pt <= Decimal(6):
        return f_sieve_iv(Iv(s_pt, s_pt))
    return f_sieve_iv(Iv(6, 6))


def F_sieve_iv(s: Iv) -> Iv:
    """Outward-rounded monotone enclosure of Buchstab upper function `F(s)` on `[1, 5]`."""
    if s.lo != s.hi:
        return Iv(F_sieve_iv(Iv(s.hi, s.hi)).lo, F_sieve_iv(Iv(s.lo, s.lo)).hi)
    if s.hi <= D_THREE:
        return (Iv(2, 2) * E_GAMMA) / s
    if s.hi <= Decimal(5):
        b = s - Iv(1, 1)
        with directed_context(ROUND_FLOOR, 40):
            idx = int(((b.lo - D_TWO) * Decimal(_IF_N) / D_TWO))
        idx = max(0, min(_IF_N - 1, idx))
        if_val = Iv(_IF_GRID[idx].lo, _IF_GRID[min(_IF_N, idx + 1)].hi)
        return (Iv(2, 2) * E_GAMMA * (Iv(1, 1) + if_val)) / s
    raise ValueError(f"F_sieve_iv out of domain [1, 5]: {s}")


def h_lin_ub(s: Iv) -> Iv:
    """Decreasing BJS error weight `h(s)` (`e^-2`, `e^-s`, or `3 e^-s / s`)."""
    s_pt = s.lo
    if s_pt <= D_TWO:
        return Iv(1, 1) / E2
    if s_pt <= D_THREE:
        return exp_iv(Iv(-s_pt, -s_pt))
    return (Iv(3, 3) / Iv(s_pt, s_pt)) * exp_iv(Iv(-s_pt, -s_pt))


# ---------------------------------------------------------------------------
# Finite-Terminating Buchstab Error Operator E_n(s)
# ---------------------------------------------------------------------------

_DS_STR = "0.005"
_DS_D = Decimal(_DS_STR)
_SHIFT = 200
_S_MAX_INT = 115
_N_PTS = (_S_MAX_INT - 1) * _SHIFT  # 22800
_N_GRID_MAX = 110

_F_HAT_CACHE: list[list[Decimal] | None] | None = None
_INV_S_HI: list[Decimal] = []
_E_SEQ_CACHE: dict[tuple[Decimal, int], list[list[Decimal]]] = {}


def _d_add_ceil(a: Decimal, b: Decimal) -> Decimal:
    with directed_context(ROUND_CEILING):
        return a + b


def _d_mul_ceil(a: Decimal, b: Decimal) -> Decimal:
    with directed_context(ROUND_CEILING):
        return a * b


def _d_div_ceil(a: Decimal, b: Decimal) -> Decimal:
    with directed_context(ROUND_CEILING):
        return a / b


def _ensure_f_hat() -> tuple[list[list[Decimal] | None], list[Decimal]]:
    global _F_HAT_CACHE, _INV_S_HI
    if _F_HAT_CACHE is not None:
        return _F_HAT_CACHE, _INV_S_HI
    s_d = [D_ONE + Decimal(i) * _DS_D for i in range(_N_PTS + 1)]
    inv_s_hi = [_d_div_ceil(D_ONE, s) for s in s_d]
    f_hat: list[list[Decimal] | None] = [None]
    f1 = [D_ZERO] * (_N_PTS + 1)
    for i in range(2 * _SHIFT + 1):
        f1[i] = _d_div_ceil(D_THREE - s_d[i], s_d[i])
    f_hat.append(f1)
    for n in range(2, _N_GRID_MAX + 1):
        f_prev = f_hat[-1]
        assert f_prev is not None
        tail = [D_ZERO] * (_N_PTS + 1)
        acc = D_ZERO
        for i in range(_N_PTS - 1, -1, -1):
            j = i - _SHIFT if i >= _SHIFT else 0
            acc = _d_add_ceil(acc, _d_mul_ceil(_DS_D, f_prev[j]))
            tail[i] = acc
        f_new = [D_ZERO] * (_N_PTS + 1)
        if n % 2 == 0:
            for i in range(_SHIFT, _N_PTS + 1):
                f_new[i] = _d_mul_ceil(tail[i], inv_s_hi[i])
        else:
            t_3 = tail[2 * _SHIFT]
            for i in range(_N_PTS + 1):
                tv = t_3 if i < 2 * _SHIFT else tail[i]
                f_new[i] = _d_mul_ceil(tv, inv_s_hi[i])
        f_hat.append(f_new)
    _F_HAT_CACHE = f_hat
    _INV_S_HI = inv_s_hi
    return f_hat, inv_s_hi


def _run_e_const_hi(eps_hi: Decimal, n_max: int) -> list[list[Decimal]]:
    """Outward-rounded upper envelopes `E_1 .. E_{n_max}` for constant `eps <= eps_hi`."""
    key = (eps_hi, n_max)
    if key in _E_SEQ_CACHE:
        return _E_SEQ_CACHE[key]
    f_hat, inv_s_hi = _ensure_f_hat()
    s_lim = min(_N_PTS, (n_max + 2) * _SHIFT)
    k_hi = _d_add_ceil(D_ONE, eps_hi)
    k2_hi = _d_mul_ceil(k_hi, k_hi)
    e2_hi = _d_add_ceil(_d_mul_ceil(D_TWO, eps_hi), _d_mul_ceil(eps_hi, eps_hi))
    three_k_eps = _d_mul_ceil(D_THREE, _d_mul_ceil(k_hi, eps_hi))

    e_cur = [D_ZERO] * (s_lim + 1)
    for i in range(min(s_lim + 1, 2 * _SHIFT + 1)):
        e_cur[i] = _d_mul_ceil(_d_mul_ceil(D_THREE, eps_hi), inv_s_hi[i])
    res: list[list[Decimal]] = [[], e_cur]
    for n in range(2, n_max + 1):
        f_prev = f_hat[n - 1]
        assert f_prev is not None
        tail_e = [D_ZERO] * (s_lim + 1)
        tail_f = [D_ZERO] * (s_lim + 1)
        acc_e = D_ZERO
        acc_f = D_ZERO
        for i in range(s_lim - 1, -1, -1):
            j = i - _SHIFT if i >= _SHIFT else 0
            acc_e = _d_add_ceil(acc_e, _d_mul_ceil(_DS_D, e_cur[j]))
            acc_f = _d_add_ceil(acc_f, _d_mul_ceil(_DS_D, f_prev[j]))
            tail_e[i] = acc_e
            tail_f[i] = acc_f
        e_new = [D_ZERO] * (s_lim + 1)
        if n % 2 == 0:
            for i in range(_SHIFT, s_lim + 1):
                j = i - _SHIFT
                t1 = _d_mul_ceil(eps_hi, _d_add_ceil(f_prev[j], e_cur[j]))
                t2 = _d_mul_ceil(_d_mul_ceil(k_hi, inv_s_hi[i]), tail_e[i])
                t3 = _d_mul_ceil(_d_mul_ceil(eps_hi, inv_s_hi[i]), tail_f[i])
                e_new[i] = _d_add_ceil(t1, _d_add_ceil(t2, t3))
        else:
            for i in range(2 * _SHIFT, s_lim + 1):
                j = i - _SHIFT
                t1 = _d_mul_ceil(eps_hi, _d_add_ceil(f_prev[j], e_cur[j]))
                t2 = _d_mul_ceil(_d_mul_ceil(k_hi, inv_s_hi[i]), tail_e[i])
                t3 = _d_mul_ceil(_d_mul_ceil(eps_hi, inv_s_hi[i]), tail_f[i])
                e_new[i] = _d_add_ceil(t1, _d_add_ceil(t2, t3))
            f2e2 = _d_add_ceil(f_prev[_SHIFT], e_cur[_SHIFT])
            te3, tf3 = tail_e[2 * _SHIFT], tail_f[2 * _SHIFT]
            for i in range(min(s_lim + 1, 2 * _SHIFT)):
                t1 = _d_mul_ceil(three_k_eps, _d_mul_ceil(f2e2, inv_s_hi[i]))
                t2 = _d_mul_ceil(k2_hi, _d_mul_ceil(te3, inv_s_hi[i]))
                t3 = _d_mul_ceil(e2_hi, _d_mul_ceil(tf3, inv_s_hi[i]))
                e_new[i] = _d_add_ceil(t1, _d_add_ceil(t2, t3))
        res.append(e_new)
        e_cur = e_new
    _E_SEQ_CACHE[key] = res
    return res


def compute_n_term(p_star: int, d1_hi_int: int) -> int:
    """
    Exact combinatorial Rosser-Iwaniec termination index `n_term`:
    smallest `n >= 3` such that `q_3^3 * prod_{j=4}^n q_j > d1_hi_int` where
    `q_1 < q_2 < q_3 < ...` are the primes `>= p_star`. Thus `T_n(D_1, z) = 0` for `n >= n_term`.
    """
    qs = [p for p in ODD_PRIMES if p >= p_star]
    prod = (qs[2] ** 3)
    for n in range(3, len(qs) + 1):
        if n >= 4:
            prod *= qs[n - 1]
        if prod > d1_hi_int:
            return n
    raise AssertionError(f"Prime list exhausted before reaching d1_hi={d1_hi_int}")


def finite_buchstab_even_err_hi(
    p_star: int, ln_d1_lo: Iv, ln_z_hi: Iv, n_term: int, s_lo: Decimal
) -> Iv:
    """
    Exact outward-rounded upper bound on `sum_{2 <= 2k < n_term} E_{2k}(s_A)` with
    `n <= 8` using local prime lower bounds `u_{2k} = (D/z)^{3^{-k}}` and `10 <= 2k < n_term`
    using uniform two-variable `eps_sup_two_var(p_star)`. No infinite Lyapunov tail needed.
    """
    assert n_term <= _N_GRID_MAX, f"n_term={n_term} exceeds grid cap {_N_GRID_MAX}"
    eps_glob = eps_sup_two_var(p_star)
    with directed_context(ROUND_CEILING, 20):
        eps_glob_key = eps_glob.hi.quantize(Decimal("1e-5"))

    with directed_context(ROUND_FLOOR, 30):
        idx_s = int((s_lo - D_ONE) / _DS_D)
    idx_s = max(0, idx_s)

    total = D_ZERO
    n_max_even = n_term - 1 if (n_term - 1) % 2 == 0 else n_term - 2
    if n_max_even >= 10:
        eg = _run_e_const_hi(eps_glob_key, n_max_even)
        for n in range(10, n_max_even + 1, 2):
            if idx_s < len(eg[n]):
                total = _d_add_ceil(total, eg[n][idx_s])

    for k in (1, 2, 3, 4):
        n = 2 * k
        if n >= n_term:
            break
        ln_u = (ln_d1_lo - ln_z_hi) / Iv(3 ** k, 3 ** k)
        en = min_iv(eps_glob, eps_large_u_two_var(ln_u))
        with directed_context(ROUND_CEILING, 20):
            en_key = en.hi.quantize(Decimal("1e-4"))
        e_seq = _run_e_const_hi(en_key, n)
        if idx_s < len(e_seq[n]):
            total = _d_add_ceil(total, e_seq[n][idx_s])

    return Iv(total, total)


def finite_buchstab_odd_err_hi(
    p_star: int, ln_dq_lo: Iv, n_term: int, s_lo: Decimal
) -> Iv:
    """
    Exact outward-rounded upper bound on `sum_{1 <= 2k+1 < n_term} E_{2k+1}(s_q)` with
    `n <= 7` using local prime lower bounds `u_{2k+1} = D_q^{3^{-(k+1)}}` and
    `9 <= 2k+1 < n_term` using uniform two-variable `eps_sup_two_var(p_star)`.
    """
    assert n_term <= _N_GRID_MAX, f"n_term={n_term} exceeds grid cap {_N_GRID_MAX}"
    eps_glob = eps_sup_two_var(p_star)
    with directed_context(ROUND_CEILING, 20):
        eps_glob_key = eps_glob.hi.quantize(Decimal("1e-5"))

    with directed_context(ROUND_FLOOR, 30):
        idx_s = int((s_lo - D_ONE) / _DS_D)
    idx_s = max(0, idx_s)

    total = D_ZERO
    n_max_odd = n_term - 1 if (n_term - 1) % 2 == 1 else n_term - 2
    if n_max_odd >= 9:
        eg = _run_e_const_hi(eps_glob_key, n_max_odd)
        for n in range(9, n_max_odd + 1, 2):
            if idx_s < len(eg[n]):
                total = _d_add_ceil(total, eg[n][idx_s])

    for k in (0, 1, 2, 3):
        n = 2 * k + 1
        if n >= n_term:
            break
        ln_u = ln_dq_lo / Iv(3 ** (k + 1), 3 ** (k + 1))
        en = min_iv(eps_glob, eps_large_u_two_var(ln_u))
        with directed_context(ROUND_CEILING, 20):
            en_key = en.hi.quantize(Decimal("1e-4"))
        e_seq = _run_e_const_hi(en_key, n)
        if idx_s < len(e_seq[n]):
            total = _d_add_ceil(total, e_seq[n][idx_s])

    return Iv(total, total)
