"""Regime 2: thirty slabs covering 4e18 <= N < 1e170 (note X26 sections 2-3).

For each slab [X_lo, X_hi) and every even N in it, the certificate shows

    pi_4(N) / (N/log N) >= main - (err_A + err_Aq + err_q2) =: net > 0,

where, from (1.1),
  * main   = V_lb * b: lower sieve on S(A,P(z)) minus the main part of the upper
             sieves on S(A_q,P(z)), with b = R_odd(P2) - 1/2 R_even(P2) sum_{z<=q<y} 1/(q-1)
             (note section 2, Lemma 2(b)) and |A| > N/log N ([JS] Lemma 3.1);
  * err_A  = remainders of the lower sieve, (number of d) x (*);
  * err_Aq = remainders of the upper sieves for A_q (note section 3, item 6);
  * err_q2 = 1/2 sum_q |A_{q^2}|.
All error terms are divided by N/log N and evaluated at the end of the slab where
they are largest (X_lo for the GRH terms, X_hi for the elementary q^2 term).

Sieve: Q1 = the first a odd primes (exact inclusion-exclusion), P2 = odd primes in
(p_a, z) (Bonferroni of order m_odd for the lower and m_even for the upper sieve).
"Exact branch": z <= P_CUT, symmetric functions on P2 computed exactly in intervals.
"Analytic branch": z > P_CUT, bounds through S1 = sum_{P2} 1/(p-1).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from .checks import Check, CheckList
from .cited import require_js_lemma_3_1, schoenfeld_denominator
from .constants import PI
from .elementary import exp_iv, ln_iv
from .interval import HALF, ONE, TWO, Iv
from .prime_bounds import prime_count_upper, sum_inv_p_lower, sum_inv_p_upper
from .primes import P_CUT, PRIMES, binomial, product
from .remainder import grh_remainder_coeff, omega_upper
from .weights import (
    alternating_partial_sum,
    bonferroni_tail_upper,
    elementary_symmetric,
    require_weight_conditions,
    truncated_exp_sum,
)


@dataclass(frozen=True)
class SlabParams:
    """Parameters of one slab, exactly as in the original schedule.

    M: z is the least integer with z^M >= X_hi (up to the +1 below); a: size of Q1;
    m_odd / m_even: Bonferroni truncation orders of the lower / upper sieve on P2.
    """

    index: int
    x_lo: int
    x_hi: int
    m: int
    a: int
    m_odd: int
    m_even: int

    def __post_init__(self) -> None:
        if not (self.m_odd % 2 == 1 and self.m_even % 2 == 0):
            raise ValueError(f"slab {self.index}: need m_odd odd and m_even even")
        if not (0 < self.x_lo < self.x_hi and self.m > 0 and self.a >= 1):
            raise ValueError(f"slab {self.index}: invalid parameters")


_SCHEDULE = (
    (4 * 10**18, 10**20, 14, 5, 3, 0),
    (10**20, 10**22, 10, 4, 3, 0),
    (10**22, 10**24, 12, 5, 3, 0),
    (10**24, 10**26, 12, 6, 3, 0),
    (10**26, 10**28, 14, 3, 5, 2),
    (10**28, 10**30, 14, 3, 5, 2),
    (10**30, 10**33, 14, 3, 5, 2),
    (10**33, 10**36, 14, 3, 5, 2),
    (10**36, 10**40, 14, 3, 5, 2),
    (10**40, 10**45, 16, 4, 5, 2),
    (10**45, 10**50, 16, 5, 5, 2),
    (10**50, 10**56, 18, 6, 5, 2),
    (10**56, 10**62, 20, 7, 5, 2),
    (10**62, 10**70, 22, 2, 9, 4),
    (10**70, 10**78, 22, 3, 9, 4),
    (10**78, 10**86, 22, 3, 9, 4),
    (10**86, 10**94, 22, 4, 9, 4),
    (10**94, 10**102, 24, 6, 9, 4),
    (10**102, 10**110, 22, 5, 9, 4),
    (10**110, 10**118, 24, 7, 9, 4),
    (10**118, 10**126, 24, 7, 9, 4),
    (10**126, 10**134, 24, 8, 9, 4),
    (10**134, 10**138, 28, 4, 11, 6),
    (10**138, 10**142, 26, 3, 11, 6),
    (10**142, 10**146, 26, 3, 11, 6),
    (10**146, 10**150, 26, 3, 11, 6),
    (10**150, 10**154, 28, 5, 11, 6),
    (10**154, 10**158, 28, 5, 11, 6),
    (10**158, 10**164, 28, 5, 11, 6),
    (10**164, 10**170, 28, 5, 11, 6),
)
SLABS: tuple[SlabParams, ...] = tuple(SlabParams(i, *row) for i, row in enumerate(_SCHEDULE, 1))
REGIME2_START = 4 * 10**18
REGIME2_END = 10**170


def require_schedule_covers(checks: CheckList, slabs: tuple[SlabParams, ...] = SLABS) -> None:
    """The slabs are contiguous half-open intervals covering [4e18, 1e170) (exact)."""
    checks.require("schedule starts at 4e18", "X26 s3", slabs[0].x_lo, "==", REGIME2_START)
    checks.require("schedule ends at 1e170", "X26 s3", slabs[-1].x_hi, "==", REGIME2_END)
    for prev, nxt in zip(slabs, slabs[1:]):
        checks.require(f"slabs {prev.index},{nxt.index} contiguous", "X26 s3", prev.x_hi, "==", nxt.x_lo)


@dataclass(frozen=True)
class QSums:
    """Bounds for the sums over primes q in [z, y).

    count >= #{q}, inv >= sum 1/(q-1), inv_sq >= sum 1/(q(q-1)) (upper ends are the bounds).
    """

    branch: str
    count: Iv
    inv: Iv
    inv_sq: Iv


@dataclass(frozen=True)
class SieveBounds:
    """Bounds for the sieve on P2 (note section 2).

    v2_lower <= V_2(P2); ratio_odd <= R_odd(P2) (lower end); ratio_even >= R_even(P2)
    (upper end); num_d_* >= number of d with lambda_d != 0; inv_phi_p2 >= sum_{j<=m_even} e_j(P2).
    """

    branch: str
    p2_size: int | None
    v2_lower: Iv
    ratio_odd: Iv
    ratio_even: Iv
    num_d_odd: Iv
    num_d_even: Iv
    inv_phi_p2: Iv


@dataclass(frozen=True)
class SlabResult:
    """Everything certified for one slab; all real quantities normalised by N/log N."""

    params: SlabParams
    z: int
    y: int
    p_a: int
    max_d_odd: int
    max_d_even: int
    q_sums: QSums
    sieve: SieveBounds
    v_lower: Iv
    bracket: Iv
    main: Iv
    err_per_modulus: Iv
    err_a: Iv
    err_aq: Iv
    q2_branch: str
    err_q2: Iv
    err_total: Iv
    net: Iv
    checks: tuple[Check, ...]


def choose_z_y(checks: CheckList, p: SlabParams, log_x_hi: Iv) -> tuple[int, int]:
    """Integers z = floor(X_hi^(1/M)) + 1 (or so) and y with y^5 > X_hi, z y^4 >= X_hi.

    The choice uses enclosures of X_hi^(1/M), X_hi^(1/5), (X_hi/z)^(1/4); the
    properties needed are then checked with exact integers.
    """
    z = int(exp_iv(log_x_hi / Iv(p.m)).hi) + 1
    checks.require("z^M >= X_hi", "X26 s3 item 1", z ** p.m, ">=", p.x_hi, z=z, M=p.m)
    checks.require("z >= 3", "X26 s3 item 1", z, ">=", 3)
    y1 = exp_iv(log_x_hi / Iv(5))
    y2 = exp_iv((log_x_hi - ln_iv(Iv(z))) / Iv(4))
    y = int(max(y1.hi, y2.hi)) + 1
    require_weight_conditions(checks, z, y, p.x_hi)
    return z, y


def q_sums(z: int, y: int, z_iv: Iv, y_iv: Iv, log_z: Iv, log_y: Iv) -> QSums:
    """Bounds for #{q}, sum 1/(q-1), sum 1/(q(q-1)) over primes z <= q < y (note s3 item 4).

    y <= P_CUT: exact sums over the listed primes.  Otherwise pi(y) bounds the count,
    1/(q-1) = 1/q + 1/(q(q-1)), sum_{q > P} 1/(q(q-1)) <= 1/P, and
    sum_{w <= q < y} 1/q <= [upper bound for sum_{p<y}] - [lower bound for sum_{p<w}],
    where M0 enters the first with its upper and the second with its lower end, so the
    width of the M0 enclosure (about 3.3e-5) is added; this is conservative.
    """
    if y <= P_CUT:
        qs = [q for q in PRIMES if z <= q < y]
        inv = Iv(0)
        inv_sq = Iv(0)
        for q in qs:
            inv = inv + Iv.from_fraction(Fraction(1, q - 1))
            inv_sq = inv_sq + Iv.from_fraction(Fraction(1, q * (q - 1)))
        return QSums("exact (y <= P_CUT)", Iv(len(qs)), inv, inv_sq)
    count = prime_count_upper(y_iv, log_y, y)
    if z <= P_CUT:
        inv_lo = Iv(0)
        inv_sq_lo = Iv(0)
        for q in PRIMES:
            if z <= q <= P_CUT:
                inv_lo = inv_lo + Iv.from_fraction(Fraction(1, q - 1))
                inv_sq_lo = inv_sq_lo + Iv.from_fraction(Fraction(1, q * (q - 1)))
        pc = Iv(P_CUT)
        sum_p_hi = sum_inv_p_upper(y_iv, log_y) - sum_inv_p_lower(pc, ln_iv(pc))
        tail = ONE / pc
        return QSums("exact to P_CUT + Mertens", count, inv_lo + sum_p_hi + tail, inv_sq_lo + tail)
    sum_p_hi = sum_inv_p_upper(y_iv, log_y) - sum_inv_p_lower(z_iv, log_z)
    tail = ONE / Iv(z - 1)
    return QSums("Mertens", count, sum_p_hi + tail, tail)


def sieve_exact(p2: list[int], a: int, m_odd: int, m_even: int) -> SieveBounds:
    """Exact branch (z <= P_CUT): e_j(P2) in intervals, exact divisor counts."""
    w2 = [Iv.from_fraction(Fraction(1, p - 1)) for p in p2]
    v2 = ONE
    for w in w2:
        v2 = v2 * (ONE - w)
    e2 = elementary_symmetric(w2, max(m_odd, m_even))
    ratio_odd = alternating_partial_sum(e2, m_odd) / v2
    ratio_even = alternating_partial_sum(e2, m_even) / v2
    num_d_odd = Iv((1 << a) * sum(binomial(len(p2), j) for j in range(m_odd + 1)))
    num_d_even = Iv((1 << a) * sum(binomial(len(p2), j) for j in range(m_even + 1)))
    inv_phi_p2 = Iv(0)
    for j in range(m_even + 1):
        inv_phi_p2 = inv_phi_p2 + e2[j]
    return SieveBounds("exact", len(p2), v2, ratio_odd, ratio_even, num_d_odd, num_d_even, inv_phi_p2)


def sieve_analytic(z_iv: Iv, log_z: Iv, z: int, p_a: int, a: int, m_odd: int, m_even: int) -> SieveBounds:
    """Analytic branch (z > P_CUT), note section 2.

    S1 >= sum_{p_a<p<z} 1/(p-1) = [sum_{p<z} 1/p] - sum_{p<=p_a} 1/p + sum_{p>p_a} 1/(p(p-1));
    V_2 >= exp(-S1 - c sum_{p>p_a} (p-1)^-2), c = 1/(2(1 - 1/p_a)), from
    -log(1-w) <= w + w^2/(2(1-w)) (note 0.4); R_odd >= 1 - e_{m+1}/V_2, R_even <= 1 + e_{m+1}/V_2
    with e_{m+1} <= S1^(m+1)/(m+1)!; the number of d with at most m prime factors in P2 is
    <= sum_{j<=m} pi(z)^j/j!.
    """
    exact_sum_p_pa = Iv(0)
    for p in PRIMES:
        if p <= p_a:
            exact_sum_p_pa = exact_sum_p_pa + ONE / Iv(p)
    tail_pp1 = Iv(0)
    tail_pm1_sq = Iv(0)
    for p in PRIMES:
        if p > p_a:
            tail_pp1 = tail_pp1 + Iv.from_fraction(Fraction(1, p * (p - 1)))
            tail_pm1_sq = tail_pm1_sq + Iv.from_fraction(Fraction(1, (p - 1) * (p - 1)))
    tail_pp1 = tail_pp1 + ONE / Iv(P_CUT)
    tail_pm1_sq = tail_pm1_sq + ONE / Iv(P_CUT - 1)

    s1 = (sum_inv_p_upper(z_iv, log_z) - exact_sum_p_pa) + tail_pp1
    c_log = ONE / (TWO * (ONE - ONE / Iv(p_a)))
    v2_lower = exp_iv(-(s1 + c_log * tail_pm1_sq))
    ratio_odd = ONE - bonferroni_tail_upper(s1, m_odd) / v2_lower
    ratio_even = ONE + bonferroni_tail_upper(s1, m_even) / v2_lower
    pz_upper = prime_count_upper(z_iv, log_z, z)
    num_d_odd = Iv(1 << a) * truncated_exp_sum(pz_upper, m_odd)
    num_d_even = Iv(1 << a) * truncated_exp_sum(pz_upper, m_even)
    inv_phi_p2 = truncated_exp_sum(s1, m_even)
    return SieveBounds("analytic", None, v2_lower, ratio_odd, ratio_even, num_d_odd, num_d_even, inv_phi_p2)


def certify_slab(p: SlabParams) -> SlabResult:
    """Certify net > 0 for every even N in [X_lo, X_hi) (note section 3); raise otherwise."""
    checks = CheckList(f"slab {p.index}")
    require_js_lemma_3_1(p.x_lo)
    x_lo_iv = Iv(p.x_lo)
    x_hi_iv = Iv(p.x_hi)
    log_x_lo = ln_iv(x_lo_iv)
    log_x_hi = ln_iv(x_hi_iv)

    z, y = choose_z_y(checks, p, log_x_hi)
    z_iv = Iv(z)
    y_iv = Iv(y)
    log_z = ln_iv(z_iv)
    log_y = ln_iv(y_iv)

    q1 = PRIMES[1 : p.a + 1]
    if len(q1) != p.a:
        raise ValueError("not enough primes for Q1")
    p_a = q1[-1]
    checks.require("p_a < z", "X26 s2", p_a, "<", z, p_a=p_a, z=z)
    q1_prod = product(q1)

    # Moduli: every d (lower sieve) and q*d (upper sieve) is <= sqrt(X_lo) <= sqrt(N),
    # as [JS] Lemma 5.1 requires (exact integer comparisons of squares).
    if z <= P_CUT:
        p2 = [q for q in PRIMES if p_a < q < z]
        max_d_odd = q1_prod * product(p2[-p.m_odd:])
        max_d_even = q1_prod * (product(p2[-p.m_even:]) if p.m_even > 0 else 1)
    else:
        p2 = []
        max_d_odd = q1_prod * (z ** p.m_odd)
        max_d_even = q1_prod * (z ** p.m_even)
    checks.require("JS-L5.1 range: max d^2 <= X_lo", "X26 s1 (*)", max_d_odd * max_d_odd, "<=", p.x_lo,
                   max_d_odd=max_d_odd)
    checks.require("JS-L5.1 range: (y max d)^2 <= X_lo", "X26 s1 (*)", (y * max_d_even) ** 2, "<=", p.x_lo,
                   y=y, max_d_even=max_d_even)

    v_q1 = ONE
    inv_phi_q1 = ONE
    for q in q1:
        v_q1 = v_q1 * Iv.from_fraction(Fraction(q - 2, q - 1))
        inv_phi_q1 = inv_phi_q1 * Iv.from_fraction(Fraction(q, q - 1))

    qs = q_sums(z, y, z_iv, y_iv, log_z, log_y)
    if z <= P_CUT:
        sv = sieve_exact(p2, p.a, p.m_odd, p.m_even)
    else:
        sv = sieve_analytic(z_iv, log_z, z, p_a, p.a, p.m_odd, p.m_even)
    v_lower = v_q1 * sv.v2_lower

    # Main term (Lemma 2(b)): needs R_odd > 0 and b > 0.
    checks.require("R_odd > 0", "X26 s2 Lemma 2", sv.ratio_odd, ">", 0)
    bracket = sv.ratio_odd - HALF * sv.ratio_even * qs.inv
    checks.require("bracket b > 0", "X26 s2 Lemma 2(b)", bracket, ">", 0)
    main = v_lower * bracket

    # Per-modulus remainder (*) divided by N/log N, at N = X_lo (both parts decrease in N):
    # (c_pi + 1/(16 pi)) log^2 N/sqrt(N) + omega(N) log N/N.  r(1) = 0 is counted anyway.
    sqrt_x_lo = x_lo_iv.sqrt()
    rc = grh_remainder_coeff(log_x_lo, p.x_lo)
    omega_ub = omega_upper(log_x_lo, p.x_lo)
    err_per_d = rc * (log_x_lo ** 2) / sqrt_x_lo + (omega_ub * log_x_lo) / x_lo_iv

    err_a = sv.num_d_odd * err_per_d
    inv_phi_all = inv_phi_q1 * sv.inv_phi_p2
    # Switching: per q, #{d} max|r(qd)| + |r(q)| sum_d 1/phi(d) + |r(q)| R_even (V_N <= 1).
    err_aq = HALF * qs.count * err_per_d * (sv.num_d_even + inv_phi_all + sv.ratio_even)

    # q^2 term, 1/2 sum_{z<=q<y} |A_{q^2}|.
    if y ** 4 <= p.x_lo:
        # q^2 < y^2 <= sqrt(X_lo): |A_{q^2}| = |A|/(q(q-1)) + r(q^2) with (*), and
        # |A|/(N/log N) <= log N/(log N - 2) + log^2 N/(8 pi sqrt N) (Schoenfeld, note 0.4),
        # decreasing in N, so taken at X_lo.
        q2_branch = "(*) with q^2 <= sqrt(X_lo)"
        a_ratio = log_x_lo / (log_x_lo - TWO) + (log_x_lo ** 2) / (Iv(schoenfeld_denominator(p.x_lo)) * PI * sqrt_x_lo)
        err_q2 = HALF * (a_ratio * qs.inv_sq + qs.count * err_per_d)
    else:
        # |A_{q^2}| <= N/q^2 (distinct integers in [1, N-1]); normalised <= log X_hi/(q(q-1)).
        q2_branch = "elementary N/q^2"
        err_q2 = HALF * log_x_hi * qs.inv_sq

    err_total = err_a + err_aq + err_q2
    net = main - err_total
    checks.require("net > 0", "X26 s3", net, ">", 0, main=main, err=err_total)
    return SlabResult(
        params=p, z=z, y=y, p_a=p_a, max_d_odd=max_d_odd, max_d_even=max_d_even, q_sums=qs, sieve=sv,
        v_lower=v_lower, bracket=bracket, main=main, err_per_modulus=err_per_d, err_a=err_a, err_aq=err_aq,
        q2_branch=q2_branch, err_q2=err_q2, err_total=err_total, net=net, checks=checks.frozen(),
    )

