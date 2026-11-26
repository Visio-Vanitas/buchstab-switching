"""
Brun combinatorial block lower sieve for Regime 2c (`[10^84, 10^600)`), replacing
single-order Bonferroni where m_odd <= 9 hits the O(1) switching ceiling.

All bounds derive solely from:
  - exact arithmetic over `PRIMES_PRE` (`<= P_PREFIX_MAX = 250_000`),
  - Johnston-Starichkova Lemma 3.2 Mertens bounds (`sum_inv_p_ub`, `sum_inv_p_lb`),
  - explicit `pi(x)` upper bounds (`pi_ub_iv`),
  - outward-rounded trapped-Decimal interval arithmetic (`Iv`).
"""

from __future__ import annotations

import bisect
from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction

from .bonferroni_engine import comb_int
from .constants import ODD_PRIMES, P_CUT, P_PREFIX_MAX, PRIMES, PRIMES_PRE
from .interval import D_ONE, D_ZERO, Iv, clamp_pos_iv, exp_iv, floor_root_int, ln_iv
from .primes_and_mertens import pi_ub_iv, sum_inv_p_lb, sum_inv_p_ub

# Exact prefix sums sum_{3 <= p < PRIMES_PRE[k]} 1/(p-1) and products prod (p-2)/(p-1).
_PW: list[Iv] = [Iv(0, 0)]
_PV: list[Iv] = [Iv(1, 1)]
for _p in PRIMES_PRE:
    if _p >= 3:
        _PW.append(_PW[-1] + Iv.from_frac(Fraction(1, _p - 1)))
        _PV.append(_PV[-1] * Iv.from_frac(Fraction(_p - 2, _p - 1)))
    else:
        _PW.append(_PW[-1])
        _PV.append(_PV[-1])

# P_PREFIX_MAX = 250_000 is composite, so primes < P_PREFIX_MAX equals primes <= P_PREFIX_MAX.
_CUT = P_PREFIX_MAX


def _idx_pre(x: int) -> int:
    return bisect.bisect_left(PRIMES_PRE, x)


def _tail_inv_pm1_hi(u: int, v: int) -> tuple[Iv, int | None]:
    """Upper bound on `sum_{U <= p < v} 1/(p-1)` where `U = max(u, P_PREFIX_MAX)`."""
    if v <= _CUT:
        return Iv(0, 0), None
    u_tail = max(u, _CUT)
    vi = Iv(v, v)
    ui = Iv(u_tail, u_tail)
    s_inv = clamp_pos_iv(sum_inv_p_ub(vi, ln_iv(vi)) - sum_inv_p_lb(ui, ln_iv(ui)))
    tot = s_inv + Iv(1, 1) / Iv(u_tail - 1, u_tail - 1)
    return Iv(D_ZERO, tot.hi), u_tail


def s_hi(u: int, v: int) -> Iv:
    """Interval `[0, S]` with `S >= sum_{u <= p < v} 1/(p-1)` for `3 <= u`."""
    assert u >= 3
    if v <= u:
        return Iv(0, 0)
    hi = min(v, _CUT)
    s = Iv(0, 0)
    if u < hi:
        s = _PW[_idx_pre(hi)] - _PW[_idx_pre(u)]
    t, _ = _tail_inv_pm1_hi(u, v)
    return Iv(D_ZERO, (s + t).hi)


def v_lo(u: int, v: int) -> Iv:
    """Interval `[V, 1]` with `0 < V <= prod_{u <= p < v} (1 - 1/(p-1))` for `3 <= u`."""
    assert u >= 3
    if v <= u:
        return Iv(1, 1)
    hi = min(v, _CUT)
    prod = Iv(1, 1)
    if u < hi:
        prod = _PV[_idx_pre(hi)] / _PV[_idx_pre(u)]
    t, u_tail = _tail_inv_pm1_hi(u, v)
    if u_tail is not None:
        prod = prod * exp_iv(-(t + Iv(1, 1) / Iv(u_tail - 2, u_tail - 2)))
    assert prod.lo > D_ZERO, f"Non-positive V_lo on [{u}, {v}): {prod}"
    return Iv(prod.lo, D_ONE)


def _pi_hi(x: int) -> int:
    """Integer `>= pi(x)`."""
    if x <= P_CUT:
        return bisect.bisect_right(PRIMES, x)
    xi = Iv(x, x)
    return int(pi_ub_iv(xi, ln_iv(xi)).hi) + 1


def _block_size_hi(u: int, v: int) -> int:
    """Integer `>= #{p prime : u <= p < v}`."""
    if v <= u:
        return 0
    if v <= P_CUT:
        return bisect.bisect_left(PRIMES, v) - bisect.bisect_left(PRIMES, u)
    lo_sub = bisect.bisect_left(PRIMES, u) if u <= P_CUT else 0
    return max(0, _pi_hi(v - 1) - lo_sub)


def e_bound(caps: tuple[int, ...], ends: list[int]) -> Iv:
    """
    Brun block remainder bound:
      E <= sum_{i=1}^{r} S(T_i)^(m_i + 1) / ((m_i + 1)! * V(T_i)),
    where `T_i = [ends[i], ends[0])` (`ends[0] = z > ends[1] > ... > ends[r] = p_a + 1`).
    """
    z = ends[0]
    tot = Iv(0, 0)
    fact = 1
    prev_k = 0
    for i in range(1, len(ends)):
        k = caps[i - 1] + 1
        while prev_k < k:
            prev_k += 1
            fact *= prev_k
        term = (s_hi(ends[i], z) ** k) / (Iv(fact, fact) * v_lo(ends[i], z))
        tot = tot + term
    return Iv(D_ZERO, tot.hi)


def modbound(caps: tuple[int, ...], ends: list[int]) -> int:
    """Strict upper bound `M_chi = prod_{i=0}^{r-1} ends[i]^(m_i - m_{i-1})` on support moduli."""
    bound = 1
    prev = 0
    for i, m in enumerate(caps):
        bound *= ends[i] ** (m - prev)
        prev = m
    return bound


def adm_count(caps: tuple[int, ...], sizes: list[int]) -> int:
    """Exact count `sum_{(j_i) : sum_{s<=i} j_s <= m_i} prod C(sizes[i], j_i)` via DP."""
    dp: dict[int, int] = {0: 1}
    for m, n in zip(caps, sizes):
        nxt: dict[int, int] = {}
        for c, v in dp.items():
            for j in range(0, m - c + 1):
                nxt[c + j] = nxt.get(c + j, 0) + v * comb_int(n, j)
        dp = nxt
    return sum(dp.values())


# Candidate odd-capped block structures (every cap m_i is odd by Brun parity Theorem A).
_BRUN_LOW_CAPS: tuple[tuple[int, ...], ...] = (
    (7,),
    (9,),
    (11,),
    (5, 9),
    (7, 9),
    (7, 11),
    (9, 11),
    (9, 13),
    (5, 9, 11),
    (5, 9, 13),
    (7, 9, 13),
    (7, 11, 13),
    (7, 11, 15),
    (9, 13, 15),
    (5, 9, 11, 13),
    (5, 9, 13, 15),
    (7, 11, 13, 15),
)

_T_GRID_1 = tuple(range(20, 86, 4))
_T_GRID_2 = tuple(range(10, 86, 10))


def _candidate_ends(
    caps: tuple[int, ...],
    z: int,
    pa1: int,
    budget: int,
):
    """Yield valid descending endpoint lists `[z, z_1, ..., z_{r-1}, pa1]` within `budget`."""
    r = len(caps)
    c = [caps[0]] + [caps[i] - caps[i - 1] for i in range(1, r)]
    if c[0] < 0 or not all(ci >= 1 for ci in c[1:]):
        return
    if r == 1:
        if z ** c[0] <= budget:
            yield [z, pa1]
        return
    if r == 2:
        rest = budget // (z ** c[0])
        if rest > 0:
            z1 = min(floor_root_int(rest, c[1]), z - 1)
            if z1 > pa1:
                yield [z, z1, pa1]
        return

    def _rec(prefix: list[int], used: int, depth: int):
        if depth == r - 1:
            rest = budget // used
            if rest > 0:
                zl = min(floor_root_int(rest, c[r - 1]), prefix[-1] - 1)
                if zl > pa1:
                    yield prefix + [zl, pa1]
            return
        grid = _T_GRID_1 if depth == 1 else _T_GRID_2
        for t in grid:
            zi = floor_root_int(z ** t, 100)
            if zi >= prefix[-1] or zi <= pa1:
                continue
            nxt_used = used * (zi ** c[depth])
            if nxt_used > budget:
                continue
            yield from _rec(prefix + [zi], nxt_used, depth + 1)

    z_c0 = z ** c[0]
    if z_c0 <= budget:
        yield from _rec([z], z_c0, 1)


@dataclass(frozen=True)
class BrunLowerResult:
    ratio_low: Iv
    n_moduli: int
    r_norm: Iv
    a: int
    caps: tuple[int, ...]
    ends: tuple[int, ...]
    e_minus: Iv


def eval_best_brun_lower(
    z: int,
    sqrt_x_lo: int,
    epd: Iv,
    v_full_lb: Iv,
    a_candidates: tuple[int, ...] = (0, 2, 4, 6, 8, 10, 12),
) -> BrunLowerResult | None:
    """
    Find the Brun block lower sieve `(a, caps, ends)` maximizing normalized net
    `(1 - E^-) - (2^a * adm_count * epd) / v_full_lb` subject to `(prod Q_1) * modbound <= sqrt_x_lo`.
    """
    best: tuple[Decimal, BrunLowerResult] | None = None
    best_by_e: tuple[Iv, int, int, tuple[int, ...], list[int]] | None = None

    # Stage 1: minimize E^- across admissible (a, caps, ends) since remainder is tiny in Regime 2c,
    # while checking net directly among low-E candidates per (a).
    qp = 1
    a_prev = 0
    for a in a_candidates:
        while a_prev < a:
            qp *= ODD_PRIMES[a_prev]
            a_prev += 1
        pa1 = 3 if a == 0 else (ODD_PRIMES[a - 1] + 1)
        if pa1 >= z or qp >= sqrt_x_lo:
            break
        budget = sqrt_x_lo // qp
        local_best: tuple[Iv, tuple[int, ...], list[int]] | None = None
        for caps in _BRUN_LOW_CAPS:
            assert all(m % 2 == 1 for m in caps)
            for ends in _candidate_ends(caps, z, pa1, budget):
                em = e_bound(caps, ends)
                if em.hi >= D_ONE:
                    continue
                if local_best is None or em.hi < local_best[0].hi:
                    local_best = (em, caps, ends)
        if local_best is None:
            continue
        em, caps, ends = local_best
        assert qp * modbound(caps, ends) <= sqrt_x_lo
        sizes = [_block_size_hi(ends[i + 1], ends[i]) for i in range(len(caps))]
        n_moduli = (1 << a) * adm_count(caps, sizes)
        ratio_low = Iv(clamp_pos_iv(Iv(1, 1) - em).lo, D_ONE)
        r_norm = (Iv(n_moduli, n_moduli) * epd) / v_full_lb
        score = (ratio_low - r_norm).lo
        cand = BrunLowerResult(
            ratio_low=ratio_low,
            n_moduli=n_moduli,
            r_norm=r_norm,
            a=a,
            caps=caps,
            ends=tuple(ends),
            e_minus=em,
        )
        if best is None or score > best[0]:
            best = (score, cand)
        if best_by_e is None or em.hi < best_by_e[0].hi:
            best_by_e = (em, a, qp, caps, ends)

    return None if best is None else best[1]
