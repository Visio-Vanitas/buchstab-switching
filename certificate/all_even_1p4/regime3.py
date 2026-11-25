"""Regime 3: every even N >= X_LS = 1e170 (the note, section 4).

Sieve [BJS] Theorem 6 with the pre-sieve set Q = {3 <= p < u0, p does not divide N}:
lower bound for S(A, P(z)), upper bound for each S(A_q, P(z)), z <= q < y, with
z = N^(1/M), y = N^beta, beta = (M-1)/(4M) (so z y^4 = N), D = N^(1/2 - alpha).
Everything is normalised by M U_N N/log^2 N; the certificate shows

    pi_4(N) > net * M U_N N/log^2 N,   net = main - (R1 + R2 + rq + q2) > 0,

for every even N >= X_LS, each N-dependent piece being monotone in N and
evaluated at N = X_LS (note section 4.4).

STATUS: this regime depends on the reading of the product hypothesis of [BJS]
Theorem 6 (fixed upper endpoint z), which is under repair (see the repository README).  The code
checks arithmetic under that reading only.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import ROUND_CEILING, Context, Decimal, localcontext
from fractions import Fraction

from .checks import Check, CheckList
from .cited import (
    BJS_THEOREM_6,
    SieveTableRow,
    bjs_lemma_38_constants,
    bjs_table_row,
    buthe_constants,
    mertens_large_coeff,
    mertens_lower_coeff,
    require_js_lemma_3_1,
    robin_constant,
)
from .constants import C2_TWIN, U_C
from .elementary import exp_iv, ln_iv, pow_real_iv
from .interval import ERROR_TRAPS, HALF, ONE, TWO, Iv
from .prime_bounds import mertens_upper_error
from .primes import P_CUT, PRIMES, product
from .remainder import grh_remainder_coeff
from .sieve_functions import F_upper, f_lower, h_upper


@dataclass(frozen=True)
class TailParams:
    """X_LS, M (z = N^(1/M)), u0 (pre-sieve primes 3 <= p < u0), B (H = sqrt(N)/log^(B+1) N),
    and the number of slices of the q-sum."""

    x_ls: int = 10**170
    m: int = 22
    u0: int = 41
    b: str = "3.05"
    slices: int = 200


TAIL = TailParams()


@dataclass(frozen=True)
class EpsilonBound:
    """Note section 4.2: 1 + eps = twin_tail * exp(E_max + E_low + c sum_{p>=u0} p^-2)."""

    twin_tail: Iv
    p2_tail: Iv
    e_max: Decimal
    e_low: Decimal
    c_log: Iv
    eps: Iv
    row: SieveTableRow
    eps_used: Iv


@dataclass(frozen=True)
class TailResult:
    params: TailParams
    log_x: Iv
    beta: Iv
    q_prod: int
    alpha: Iv
    z0: Iv
    log_h0: Iv
    s: Iv
    s_min: Iv
    epsilon: EpsilonBound
    delta_v: Iv
    f_s: Iv
    h_s: Iv
    lb_a: Iv
    half_sum: Iv
    main_bracket: Iv
    main: Iv
    c4g: Iv
    phi_max: Iv
    err_r1: Iv
    err_r2: Iv
    err_rq: Iv
    err_q2: Iv
    err_total: Iv
    net: Iv
    checks: tuple[Check, ...]


def choose_alpha(checks: CheckList, log_x: Iv, b: Iv, log_q_prod: Iv) -> Iv:
    """alpha = 4-decimal ceiling of (log Q + (B+1) log log X_LS)/log X_LS (note 4.1).

    The rounding to 4 decimals only picks a parameter; the two properties used are
    then checked in intervals: alpha > (B+1)/log X (so alpha L - (B+1) log L increases
    in L = log N) and alpha log X - (B+1) log log X >= log Q (so N^alpha/log^(B+1) N >= Q).
    """
    alpha_req = (log_q_prod + (b + ONE) * ln_iv(log_x)) / log_x
    with localcontext(Context(prec=20, rounding=ROUND_CEILING, traps=ERROR_TRAPS)):
        alpha_dec = alpha_req.hi.quantize(Decimal("0.0001"))
    alpha = Iv(alpha_dec)
    checks.require("alpha > (B+1)/log X", "note s4.1", alpha, ">", (b + ONE) / log_x)
    checks.require("N^alpha/log^(B+1)N >= Q", "note s4.1", alpha * log_x - (b + ONE) * ln_iv(log_x), ">=",
                   log_q_prod, alpha=alpha)
    return alpha


def epsilon_bound(checks: CheckList, z0: Iv, u0: int) -> EpsilonBound:
    """A constant eps for the product hypothesis of [BJS] Theorem 6, uniform in u and z >= z0.

    For u0 <= u < z (smaller u reduce to u = u0, note 4.2), with g(p) = 1/(p-1):
      prod_{u<=p<z} (1 - 1/(p-1))^-1 = prod (p-1)^2/(p(p-2)) * prod (1 - 1/p)^-1,
      prod_{p>=u0} (p-1)^2/(p(p-2)) = (1/C2)/prod_{2<p<u0} (p-1)^2/(p(p-2))   (twin_tail),
      -log(1 - 1/p) <= 1/p + c/p^2, c = 1/(2(1 - 1/u0)),
      sum_{u<=p<z} 1/p <= log(log z/log u) + E_max + 2.964e-6/log u0,
    with E_max >= E_<(z) for all z >= z0 ([BJS] Lemma 16 below 1e12, [JS] (3.3) above).
    """
    p_below = ONE
    for p in PRIMES:
        if 2 < p < u0:
            p_below = p_below * Iv.from_fraction(Fraction((p - 1) ** 2, p * (p - 2)))
    twin_tail = (ONE / C2_TWIN) / p_below
    p2_tail = Iv(0)
    for p in PRIMES:
        if p >= u0:
            p2_tail = p2_tail + Iv.from_fraction(Fraction(1, p * p))
    p2_tail = p2_tail + ONE / Iv(P_CUT - 1)
    # [z0.lo, max(z0.hi, 1e40)] stands for [z0, infinity): both Mertens bounds decrease in x.
    z_all = Iv(z0.lo, max(z0.hi, Decimal(10**40)))
    e_max = mertens_upper_error(z_all, ln_iv(z_all))
    e_low = (Iv(mertens_lower_coeff(Decimal(u0))) / ln_iv(Iv(u0))).hi
    c_log = ONE / (TWO * (ONE - ONE / Iv(u0)))
    eps = twin_tail * exp_iv(Iv(e_max) + Iv(e_low) + c_log * p2_tail) - ONE
    row = bjs_table_row(eps)
    eps_used = ONE / Iv(row.inv_eps)
    checks.require("eps < eps' = 1/k (strict hypothesis)", "note s4.2", eps, "<", eps_used, k=row.inv_eps)
    checks.require("eps' <= 1/74", "note s0.1 " + BJS_THEOREM_6.key, row.inv_eps, ">=", 74)
    return EpsilonBound(twin_tail, p2_tail, e_max, e_low, c_log, eps, row, eps_used)


def v_z_delta(log_x: Iv, z0: Iv, log_z0: Iv) -> Iv:
    """delta_V with (1 - delta_V) M U_N/log N <= V(z) <= (1 + delta_V) M U_N/log N ([BJS] Lemma 38, x = z).

    t1 = 1.45 log N/(z-1) (1 + 10 log log N/log N), t2 = 1.002/(z-3), t3 = 1/(2 log^2 z);
    each decreases in N, so N = X_LS (z = z0) is the worst case.
    """
    c145, c10, c1002 = bjs_lemma_38_constants(z0.lo)
    t1 = Iv(c145) * log_x / (z0 - ONE) * (ONE + Iv(c10) * ln_iv(log_x) / log_x)
    t2 = Iv(c1002) / (z0 - Iv(3))
    t3 = ONE / (TWO * log_z0 ** 2)
    delta_lo = ONE - (ONE - t1) * (ONE - t2) * (ONE - t3)
    delta_hi = (ONE + t1) * (ONE + t2) * (ONE + t3) - ONE
    return Iv(0, max(delta_lo.hi, delta_hi.hi))


def half_q_sum(p: TailParams, m_iv: Iv, alpha: Iv, beta: Iv, log_x: Iv, z0: Iv, eps: EpsilonBound) -> Iv:
    """Upper end bounds 1/2 sum_{z<=q<y} phi(s_q)/(q-1), phi = F + eps' C1 e^2 h (note 4.3).

    s_q = M(1/2 - alpha) - M log q/log N.  [1/M, beta] is cut into ``slices`` equal pieces;
    on the slice q in [N^u_k, N^u_{k+1}), s_q >= M(1/2 - alpha - u_{k+1}) and
    sum 1/(q-1) <= z0/(z0-1) [log(u_{k+1}/u_k) + (C_up + 2.964e-6)/(u_k log N)],
    C_up = max(2/sqrt(z0), 6.836e-6) (E_<(x) <= C_up/log x for x >= z0).
    """
    e2 = exp_iv(TWO)
    c1 = Iv(eps.row.c1)
    du = (beta - ONE / m_iv) / Iv(p.slices)
    c_up = max((TWO / z0.sqrt()).hi, mertens_large_coeff(Decimal(10**12)))
    mert_coeff = Iv(c_up) + Iv(mertens_lower_coeff(z0.lo))
    q_ratio = z0 / (z0 - ONE)
    total = Iv(0)
    for k in range(p.slices):
        u_k = ONE / m_iv + Iv(k) * du
        u_k1 = ONE / m_iv + Iv(k + 1) * du
        sq_lo = m_iv * (HALF - alpha - u_k1)
        phi = F_upper(sq_lo) + eps.eps_used * c1 * e2 * h_upper(sq_lo)
        slice_sum = ln_iv(u_k1 / u_k) + mert_coeff / (u_k * log_x)
        total = total + phi * q_ratio * slice_sum
    return HALF * total


def certify_tail(p: TailParams = TAIL) -> TailResult:
    """Certify net > 0 for every even N >= X_LS (note section 4); raise otherwise."""
    checks = CheckList("tail")
    require_js_lemma_3_1(p.x_ls)
    x_iv = Iv(p.x_ls)
    log_x = ln_iv(x_iv)
    m_iv = Iv(p.m)
    beta = Iv.from_fraction(Fraction(p.m - 1, 4 * p.m))
    checks.require("M > 5", "note s4.1", p.m, ">", 5)
    checks.require("beta > 1/5", "note s1 (1.1)", beta, ">", Decimal("0.2"))
    b = Iv(Decimal(p.b))

    # 4.1 parameters
    q_primes = [q for q in PRIMES if 2 < q < p.u0]
    q_prod = product(q_primes)
    log_q_prod = ln_iv(Iv(q_prod))
    alpha = choose_alpha(checks, log_x, b, log_q_prod)

    log_z0 = log_x / m_iv
    z0 = exp_iv(log_z0)
    checks.require("log z0 > 8.9", "note s4.1", log_z0, ">", Decimal("8.9"))
    checks.require("z0 > 285", "note s4.1", z0, ">", 285)
    log_h0 = HALF * log_x - (b + ONE) * ln_iv(log_x)
    log_1e9 = ln_iv(Iv(10**9))
    checks.require("H >= 1e9", "note s4.1", log_h0, ">", log_1e9)
    checks.require("y <= H", "note s4.1", beta * log_x, "<=", log_h0)
    checks.require("1/2 - beta > (B+1)/log X", "note s4.1", HALF - beta, ">", (b + ONE) / log_x)

    s = m_iv * (HALF - alpha)
    s_min = m_iv * (HALF - alpha - beta)
    checks.require("s >= 2 (D >= z^2, lower bound)", "note s4.1 " + BJS_THEOREM_6.key, s, ">=", 2)
    checks.require("s_min >= 1 (D/q >= z, upper bound)", "note s4.1 " + BJS_THEOREM_6.key, s_min, ">=", 1)

    # 4.2 epsilon and the table row
    eps = epsilon_bound(checks, z0, p.u0)
    c1 = Iv(eps.row.c1)
    c2 = Iv(eps.row.c2)
    e2 = exp_iv(TWO)

    # 4.3 main term
    delta_v = v_z_delta(log_x, z0, log_z0)
    f_s = f_lower(s)
    h_s = h_upper(s)
    lb_a = f_s - eps.eps_used * c2 * e2 * h_s
    half_sum = half_q_sum(p, m_iv, alpha, beta, log_x, z0, eps)
    main_bracket = lb_a - half_sum
    checks.require("main bracket > 0", "note s4.3", main_bracket, ">", 0)
    main = (ONE - delta_v) * main_bracket

    # 4.4 errors, each divided by M U_N N/log^2 N, with U_N >= U_c
    sqrt_x = exp_iv(HALF * log_x)
    squarefree_density, mu2_phi_coeff = buthe_constants(log_h0.lo, log_1e9.hi)
    c4g = Iv(squarefree_density) * (grh_remainder_coeff(log_x, p.x_ls)
                                    + Iv(robin_constant(p.x_ls)) / (sqrt_x * ln_iv(log_x)))
    log_x_bm2 = pow_real_iv(log_x, b - TWO)
    log_x_bm3 = pow_real_iv(log_x, b - Iv(3))
    log_x_bm1 = pow_real_iv(log_x, b - ONE)
    checks.require("B > 3 (log powers increase in N)", "note s4.4", b - Iv(3), ">", 0)
    # R1 = R + 1/2 sum_q sum_d |r(qd)|: distinct squarefree n < QD <= H, so <= (1 + 1/2) c4G N/log^B N.
    err_r1 = (ONE + HALF) * c4g / (m_iv * U_C * log_x_bm2)
    # R2 = 1/2 sum_q |r(q)| sum_{d<QD} mu^2(d)/phi(d) <= 1/2 c4G N/log^B N * 1.1 log H, log H <= 1/2 log N.
    err_r2 = Iv(HALF.lo * mu2_phi_coeff * HALF.lo) * c4g / (m_iv * U_C * log_x_bm3)
    # rq = 1/2 V(z) phi(s_min) sum_q |r(q)| <= 1/2 (1 + delta_V) M U_N/log N phi(s_min) c4G N/log^B N.
    phi_max = F_upper(s_min) + eps.eps_used * c1 * e2 * h_upper(s_min)
    err_rq = HALF * (ONE + delta_v) * phi_max * c4g / log_x_bm1
    # q^2: |A_{q^2}| <= N/q^2, sum_{q>=z} 1/q^2 <= 1/(z-1); log^2 N/(2 M U_c (N^(1/M) - 1)) decreases
    # for log N > 2M.
    checks.require("log X > 2M", "note s4.4", log_x, ">", Iv(2 * p.m))
    err_q2 = (log_x ** 2) / (TWO * m_iv * U_C * (z0 - ONE))

    err_total = err_r1 + err_r2 + err_rq + err_q2
    net = main - err_total
    checks.require("tail net > 0", "note s4.4", net, ">", 0, main=main, err=err_total)
    return TailResult(
        params=p, log_x=log_x, beta=beta, q_prod=q_prod, alpha=alpha, z0=z0, log_h0=log_h0, s=s, s_min=s_min,
        epsilon=eps, delta_v=delta_v, f_s=f_s, h_s=h_s, lb_a=lb_a, half_sum=half_sum, main_bracket=main_bracket,
        main=main, c4g=c4g, phi_max=phi_max, err_r1=err_r1, err_r2=err_r2, err_rq=err_rq, err_q2=err_q2,
        err_total=err_total, net=net, checks=checks.frozen(),
    )
