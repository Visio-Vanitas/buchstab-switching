"""Regime 2 slab certificate with the Brun block sieve (note X32 S1), built on the package's inputs.

This is the X32 script `x32_brun_blocks/brun_blocks.py` moved onto `all_even_1p4`:
  * interval arithmetic: the package's `Iv` (PREC 90, outward rounding, rounding audit on);
  * per-modulus remainder (*): `grh_remainder_coeff` (the certified c_pi(X_lo) of [JS] Lemma 5.1
    plus 1/(16 pi)) and `omega_upper` (Robin), exactly as in `regime2.certify_slab`;
    the placeholder C_PI = 10 of the X32 script is gone;
  * Mertens and pi(x): the package's `sum_inv_p_upper` / `sum_inv_p_lower` ([JS] (3.1)-(3.3),
    [BJS] Lemma 16) and `prime_count_upper` (Schoenfeld under RH), each through its own range check;
    primes <= P_CUT = 30000 are summed exactly; the Rosser-Schoenfeld inputs of the X32 script are gone;
  * z, y: `regime2.choose_z_y`; the sums over q in [z, y): `regime2.q_sums`; |A| > N/log N:
    `require_js_lemma_3_1`; the q^2 term: the same two branches as `regime2.certify_slab`.

Completeness against X26 section 3 item 6 (the decomposition of (1.1) used by `certify_slab`):
  main   = V(Q1) V_lo(P2) * b,  b = (1 - E-) - 1/2 (1 + E+) * sum_q 1/(q-1)    (X32 Corollary F)
  err_A  = #{d : lambda-_d != 0} * (*)                                         (lower sieve on A)
  err_Aq = 1/2 #{q} (*) (#{d : lambda+_d != 0} + sum_d 1/phi(d) + R+)          (upper sieves on A_q)
           with R+ <= 1 + E+ and sum_d 1/phi(d) <= prod_{Q1} p/(p-1) exp(S(P2)) (X32 Lemma E.3)
  err_q2 = 1/2 sum_q |A_{q^2}|                                                  (as in certify_slab)
These are the same three remainder families as `certify_slab`, with the Bonferroni counts replaced by
the block counts of X32 Lemma E.2 and R_odd/R_even replaced by 1 -/+ E (Lemma B.3, Lemma D).

Level: X32 Lemma E.1 gives d < M_chi = prod_i z_{i-1}^(m_i - m_{i-1}); the checks are
(prod Q1 * M_chi-)^2 <= X_lo and (y * prod Q1 * M_chi+)^2 <= X_lo, exact integers, the same form
as `certify_slab` (which uses y, not y - 1, for q < y).
Parity (Theorem A): every cap of chi- is odd and every cap of chi+ is even (stronger than needed).
"""

from __future__ import annotations

import os
import sys
from bisect import bisect_left, bisect_right
from dataclasses import dataclass
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from all_even_1p4.checks import CheckList, CertificationError  # noqa: E402
from all_even_1p4.cited import HypothesisError, require_js_lemma_3_1, schoenfeld_denominator  # noqa: E402
from all_even_1p4.constants import E5_OVER_3, LI_E5, PI  # noqa: E402
from all_even_1p4.elementary import exp_iv, ln_iv  # noqa: E402
from all_even_1p4.interval import HALF, ONE, Iv  # noqa: E402
from all_even_1p4.prime_bounds import prime_count_upper, sum_inv_p_lower, sum_inv_p_upper  # noqa: E402
from all_even_1p4.primes import P_CUT, PRIMES, binomial, factorial, isqrt_floor, product  # noqa: E402
from all_even_1p4.regime2 import choose_z_y, q_sums  # noqa: E402
from all_even_1p4.remainder import grh_remainder_coeff, omega_upper  # noqa: E402

class ParityError(ValueError):
    """A cap list violates the parity rule: a usage error, never a 'not certified' verdict."""


# Exact prefix data over the listed primes (index k = first k primes).
_PW = [Iv(0)]        # sum 1/(p-1)
_PV = [ONE]          # prod (p-2)/(p-1), factor 1 at p = 2
for _p in PRIMES:
    _PW.append(_PW[-1] + Iv.from_fraction(Fraction(1, _p - 1)))
    _PV.append(_PV[-1] * (ONE if _p == 2 else Iv.from_fraction(Fraction(_p - 2, _p - 1))))
_CUT1 = P_CUT + 1


def _idx(x: int) -> int:
    """Number of listed primes < x."""
    return bisect_left(PRIMES, x)


def _tail_inv_pm1_hi(u: int, v: int):
    """Upper bound of sum_{U <= p < v} 1/(p-1), U = max(u, P_CUT+1); (bound, U) or (0, None).

    1/(p-1) = 1/p + 1/(p(p-1)), sum_{p >= U} 1/(p(p-1)) <= 1/(U-1); sum_{U<=p<v} 1/p <=
    [upper bound of sum_{p<v}] - [lower bound of sum_{p<U}] (package Mertens bounds).
    """
    if v <= _CUT1:
        return Iv(0), None
    U = max(u, _CUT1)
    vi, Ui = Iv(v), Iv(U)
    s = sum_inv_p_upper(vi, ln_iv(vi)) - sum_inv_p_lower(Ui, ln_iv(Ui))
    return Iv(0, (s + ONE / Iv(U - 1)).hi), U


def s_hi(u: int, v: int) -> Iv:
    """[0, S] with S >= sum_{u <= p < v} 1/(p-1), 3 <= u."""
    hi = min(v, _CUT1)
    s = Iv(0)
    if u < hi:
        s = _PW[_idx(hi)] - _PW[_idx(u)]
    t, _ = _tail_inv_pm1_hi(u, v)
    return Iv(0, (s + t).hi)


def v_lo(u: int, v: int) -> Iv:
    """[V, 1] with 0 < V <= prod_{u <= p < v} (1 - 1/(p-1)), 3 <= u.

    Above P_CUT: -log(1-w) <= w + w^2 for 0 <= w <= 1/2, sum_{p >= U} 1/(p-1)^2 <= 1/(U-2).
    """
    hi = min(v, _CUT1)
    prod = ONE
    if u < hi:
        prod = _PV[_idx(hi)] / _PV[_idx(u)]
    t, U = _tail_inv_pm1_hi(u, v)
    if U is not None:
        prod = prod * exp_iv(-(t + ONE / Iv(U - 2)))
    lo = prod.lo
    if not lo > 0:
        raise CertificationError("V lower bound not positive")
    return Iv(lo, 1)


def pi_hi(x: int) -> int:
    """An integer >= pi(x) = #{p <= x}."""
    if x <= P_CUT:
        return bisect_right(PRIMES, x)
    xi = Iv(x)
    return int(prime_count_upper(xi, ln_iv(xi), x).hi) + 1


def e_bound(caps, ends) -> Iv:
    """X32 Lemma D: sum_i S(T_i)^(m_i+1)/(m_i+1)!/V(T_i), T_i = primes in [ends[i], z)."""
    assert len(caps) >= 1 and caps[0] >= 0
    z = ends[0]
    tot = Iv(0)
    for i in range(1, len(ends)):
        k = caps[i - 1] + 1
        tot = tot + (s_hi(ends[i], z) ** k) / Iv(factorial(k)) / v_lo(ends[i], z)
    return Iv(0, tot.hi)


def modbound(caps, ends) -> int:
    """X32 Lemma E.1: every d with chi(d) = 1 is < prod_i z_{i-1}^(m_i - m_{i-1})."""
    assert len(caps) >= 1 and caps[0] >= 0
    r, prev = 1, 0
    for i, m in enumerate(caps):
        r *= ends[i] ** (m - prev)
        prev = m
    return r


def adm_count(caps, sizes) -> int:
    """sum over (j_i) with j_1+..+j_i <= m_i of prod C(n_i, j_i), exact."""
    dp = {0: 1}
    for m, n in zip(caps, sizes):
        new = {}
        for c, v in dp.items():
            for j in range(0, m - c + 1):
                new[c + j] = new.get(c + j, 0) + v * binomial(n, j)
        dp = new
    return sum(dp.values())


def _iroot(n: int, k: int) -> int:
    """floor(n^(1/k)), exact."""
    if n < 2:
        return n
    x = 1 << ((n.bit_length() + k - 1) // k)
    while True:
        y = ((k - 1) * x + n // x ** (k - 1)) // k
        if y >= x:
            break
        x = y
    while x ** k > n:
        x -= 1
    while (x + 1) ** k <= n:
        x += 1
    return x


T_GRID = tuple(range(20, 86, 2))   # z_1 = z^(t/100) for three or more blocks
T_GRID_COARSE = tuple(range(10, 86, 5))   # z_2, ..., z_{r-2} for four or more blocks


def candidate_ends(caps, z, pa1, budget):
    """Block endpoints z = z_0 > z_1 > ... > z_r = p_a + 1; the last free endpoint is maximal under
    the level budget (a larger z_i shrinks T_i, which only lowers the Lemma D bound)."""
    assert len(caps) >= 1 and caps[0] >= 0
    r = len(caps)
    c = [caps[0]] + [caps[i] - caps[i - 1] for i in range(1, r)]
    if c[0] < 0 or not all(ci >= 1 for ci in c[1:]):
        return
    if r == 1:
        if z ** c[0] <= budget:
            yield [z, pa1]
        return
    if r == 2:
        rest = budget // z ** c[0]
        if rest:
            z1 = min(_iroot(rest, c[1]), z - 1)
            if z1 > pa1:
                yield [z, z1, pa1]
        return
    # r >= 3: grid on z_1, ..., z_{r-2} as fixed fractions of log z; last free endpoint maximal.
    def rec(prefix, used, depth):
        if depth == r - 1:
            rest = budget // used
            if rest:
                zl = min(_iroot(rest, c[r - 1]), prefix[-1] - 1)
                if zl > pa1:
                    yield prefix + [zl, pa1]
            return
        for t in (T_GRID if depth == 1 else T_GRID_COARSE):
            zi = _iroot(z ** t, 100)
            if zi >= prefix[-1] or zi <= pa1:
                continue
            u = used * zi ** c[depth]
            if u > budget:
                continue
            yield from rec(prefix + [zi], u, depth + 1)
    yield from rec([z], z ** c[0], 1)


def best_blocks(caps_list, z, pa1, budget, parity):
    best = None
    for caps in caps_list:
        if not all(m % 2 == parity for m in caps):
            raise ParityError(f"caps {caps} violate the parity rule")
        for ends in candidate_ends(caps, z, pa1, budget):
            e = e_bound(caps, ends)
            if best is None or e.hi < best[0].hi:
                best = (e, tuple(caps), tuple(ends))
    return best


LOW_CAPS = ((11,), (13,), (9, 13), (11, 13), (11, 15), (9, 13, 15))
UPP_CAPS = ((6,), (4, 8), (6, 8), (4, 8, 10), (4, 6, 10), (4, 8, 12), (4, 6, 10, 12))


@dataclass(frozen=True)
class BrunSlab:
    x_lo: int
    x_hi: int
    m: int
    a: int
    z: int
    y: int
    low_caps: tuple
    low_ends: tuple
    up_caps: tuple
    up_ends: tuple
    e_minus: Iv
    e_plus: Iv
    bracket: Iv
    v_lower: Iv
    main: Iv
    err_per_d: Iv
    err_a: Iv
    err_aq: Iv
    err_q2: Iv
    err_total: Iv
    net: Iv
    n_d_low: int
    n_d_up: int


def certify_brun_slab(x_lo: int, x_hi: int, m: int, a: int,
                      low_caps=LOW_CAPS, up_caps=UPP_CAPS, fixed=None) -> BrunSlab:
    """Certify net > 0 for every even N in [x_lo, x_hi); raise CertificationError otherwise.

    fixed = ((low_caps, low_ends), (up_caps, up_ends)) skips the search and uses exactly these blocks
    (parity, level and every bound are still checked); used by the replay verifier."""
    checks = CheckList(f"brun slab [{x_lo}, {x_hi})")
    checks.require("li(e^5) < e^5/3", "X26 s0.4", LI_E5, "<", E5_OVER_3)
    require_js_lemma_3_1(x_lo)
    x_lo_iv, x_hi_iv = Iv(x_lo), Iv(x_hi)
    log_x_lo, log_x_hi = ln_iv(x_lo_iv), ln_iv(x_hi_iv)

    from all_even_1p4.regime2 import SlabParams
    p = SlabParams(0, x_lo, x_hi, m, a, 1, 0)
    z, y = choose_z_y(checks, p, log_x_hi)
    z_iv, y_iv = Iv(z), Iv(y)
    log_z, log_y = ln_iv(z_iv), ln_iv(y_iv)

    assert a >= 1, f"a must be >= 1, got {a}"
    q1 = PRIMES[1:a + 1]
    assert len(q1) == a, f"a={a} exceeds listed PRIMES"
    p_a = q1[-1]
    pa1 = p_a + 1
    checks.require("p_a < z", "X26 s2", p_a, "<", z)
    q1_prod = product(q1)
    sq = isqrt_floor(x_lo)

    if fixed is None:
        lo = best_blocks(low_caps, z, pa1, sq // q1_prod, 1)
        up = best_blocks(up_caps, z, pa1, sq // (q1_prod * y), 0)
    else:
        (lc, le), (uc, ue) = fixed
        lc, le, uc, ue = tuple(lc), tuple(le), tuple(uc), tuple(ue)
        if not (all(x % 2 == 1 for x in lc) and all(x % 2 == 0 for x in uc)):
            raise ParityError(f"parity rule violated: {lc} / {uc}")
        for caps, ends in ((lc, le), (uc, ue)):
            assert len(caps) >= 1 and caps[0] >= 0
            if not (len(ends) == len(caps) + 1 and ends[0] == z and ends[-1] == pa1
                    and all(u > v for u, v in zip(ends, ends[1:])) and all(u <= v for u, v in zip(caps, caps[1:]))):
                raise CertificationError(f"bad block structure {caps} {ends}")
        lo = (e_bound(lc, le), lc, le)
        up = (e_bound(uc, ue), uc, ue)
    if lo is None or up is None:
        raise CertificationError("no admissible block structure under the level")
    e_m, cl, el = lo
    e_p, cu, eu = up
    md_low = q1_prod * modbound(cl, el)
    md_up = q1_prod * modbound(cu, eu)
    checks.require("JS-L5.1 range: (prod Q1 M_chi-)^2 <= X_lo", "X32 E.1", md_low * md_low, "<=", x_lo)
    checks.require("JS-L5.1 range: (y prod Q1 M_chi+)^2 <= X_lo", "X32 E.1", (y * md_up) ** 2, "<=", x_lo)

    v_q1, inv_phi_q1 = ONE, ONE
    for q in q1:
        v_q1 = v_q1 * Iv.from_fraction(Fraction(q - 2, q - 1))
        inv_phi_q1 = inv_phi_q1 * Iv.from_fraction(Fraction(q, q - 1))
    qs = q_sums(z, y, z_iv, y_iv, log_z, log_y)
    v_lower = v_q1 * v_lo(pa1, z)

    ratio_low = ONE - e_m               # R_chi-(P2') >= 1 - E-  (Lemma B.3, D, F)
    ratio_up = ONE + e_p                # R_chi+(P2') <= 1 + E+
    checks.require("R- > 0", "X32 F", ratio_low, ">", 0)
    bracket = ratio_low - HALF * ratio_up * qs.inv
    checks.require("bracket b > 0", "X32 F", bracket, ">", 0)
    main = v_lower * bracket

    sqrt_x_lo = x_lo_iv.sqrt()
    rc = grh_remainder_coeff(log_x_lo, x_lo)
    omega_ub = omega_upper(log_x_lo, x_lo)
    err_per_d = rc * (log_x_lo ** 2) / sqrt_x_lo + (omega_ub * log_x_lo) / x_lo_iv

    sz_l = [pi_hi(el[i] - 1) for i in range(len(cl))]   # |B_i| <= pi(z_{i-1} - 1)
    sz_u = [pi_hi(eu[i] - 1) for i in range(len(cu))]
    n_d_low = (1 << a) * adm_count(cl, sz_l)
    n_d_up = (1 << a) * adm_count(cu, sz_u)
    err_a = Iv(n_d_low) * err_per_d
    inv_phi_all = inv_phi_q1 * exp_iv(s_hi(pa1, z))      # Lemma E.3
    err_aq = HALF * qs.count * err_per_d * (Iv(n_d_up) + inv_phi_all + ratio_up)

    if y ** 4 <= x_lo:
        a_ratio = log_x_lo / (log_x_lo - Iv(2)) + (log_x_lo ** 2) / (Iv(schoenfeld_denominator(x_lo)) * PI * sqrt_x_lo)
        err_q2 = HALF * (a_ratio * qs.inv_sq + qs.count * err_per_d)
    else:
        err_q2 = HALF * log_x_hi * qs.inv_sq

    err_total = err_a + err_aq + err_q2
    net = main - err_total
    checks.require("net > 0", "X32", net, ">", 0)
    return BrunSlab(x_lo, x_hi, m, a, z, y, cl, el, cu, eu, e_m, e_p, bracket, v_lower, main, err_per_d,
                    err_a, err_aq, err_q2, err_total, net, n_d_low, n_d_up)


def try_brun(x_lo, x_hi, m, a, **kw):
    """certify_brun_slab, or None if this (M, a) does not certify. ParityError is re-raised."""
    try:
        return certify_brun_slab(x_lo, x_hi, m, a, **kw)
    except ParityError:
        raise
    except (CertificationError, HypothesisError, ValueError):
        return None
