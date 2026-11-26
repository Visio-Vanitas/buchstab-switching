"""
Asymptotic tail certification (`[X_LS, +∞)`) via certified closed-interval (H*)
linear sieve lower bound (`Q0_100`, `cn_rows_all.json`) paired with pre-sieve-free
monotone Selberg `Λ²` upper bound.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal, ROUND_CEILING

from .constants import ALPHA0, C_F0, E2, E_NEG_GAMMA, H_TILDE, PI, U_CONST
from .interval import D_ZERO, Iv, directed_context, exp_iv, ln_iv, min_iv, pow_real_iv
from .linear_sieve import f_lin_lb, h_lin_ub, load_certified_linear_sieve_row
from .primes_and_mertens import c_pi_iv, certify_closed_hstar_q0
from .schedule import AsymptoticRaySpec
from .selberg_weights import vj_monotone_lb_iv


@dataclass(frozen=True)
class RayCertificate:
    spec: AsymptoticRaySpec
    alpha_dec: Decimal
    eps_star_hi: Decimal
    k_target: int
    rec_mode: str
    c2_used_hi: Decimal
    c2_breakeven: Decimal
    s_a_lo: Decimal
    delta_v_hi: Decimal
    lb_a_lo: Decimal
    half_sum_aq_hi: Decimal
    main_lo: Decimal
    err_hi: Decimal
    net_lo: Decimal


def certify_asymptotic_ray(spec: AsymptoticRaySpec) -> RayCertificate:
    """Certify uniform positive switching density for ALL even `N >= 10^spec.exp10`."""
    x_ls = 10 ** spec.exp10
    x_iv = Iv(x_ls, x_ls)
    log_x = ln_iv(x_iv)
    m_iv = Iv(spec.m_div, spec.m_div)
    b_a = Iv.from_str(spec.b_a_str)
    b_q = Iv.from_str(spec.b_q_str)

    # beta > 1/4 and 1/M + 3*beta >= 1
    beta = (Iv(1, 1) - Iv(1, 1) / m_iv) / Iv(3, 3) + Iv.from_str("1e-9")
    assert beta.lo > Decimal("0.25")
    assert (Iv(1, 1) / m_iv + Iv(3, 3) * beta).lo >= Decimal(1)

    q0_primes, eps_frac, _, c2_frac = load_certified_linear_sieve_row(
        spec.k_target, spec.rec_mode
    )
    eps_star = certify_closed_hstar_q0(q0_primes, spec.k_target)
    eps_iv = Iv.from_frac(eps_frac)
    assert eps_star.hi <= eps_iv.lo
    c2_iv = Iv.from_frac(c2_frac)
    if spec.c2_lean_cap is not None:
        cap_dec = Decimal(spec.c2_lean_cap)
        assert c2_iv.hi <= cap_dec, f"c2_iv.hi={c2_iv.hi} exceeds Lean cap {cap_dec}"
        c2_eff = Iv(cap_dec, cap_dec)
    else:
        c2_eff = c2_iv

    q_prod = 1
    for p in q0_primes:
        q_prod *= p
    log_q = ln_iv(Iv(q_prod, q_prod))

    alpha_req = (log_q + (b_a + Iv(1, 1)) * ln_iv(log_x)) / log_x
    with directed_context(ROUND_CEILING, 20):
        alpha_dec = alpha_req.hi.quantize(Decimal("0.0001"))
    alpha = Iv(alpha_dec, alpha_dec)
    assert alpha.lo > ((b_a + Iv(1, 1)) / log_x).hi
    assert (alpha * log_x - (b_a + Iv(1, 1)) * ln_iv(log_x)).lo >= log_q.hi

    # Integer cutoff bounds: z = floor(N^(1/M)), y = ceil((N/z)^(1/3)) <= N^beta
    log_z0 = log_x / m_iv
    z0 = exp_iv(log_z0)
    assert z0.lo > Decimal("1e12")
    z_int_lb = z0 - Iv(1, 1)
    assert exp_iv(Iv.from_str("3e-9") * log_x).lo > (z0 / z_int_lb + Iv.from_str("1e-30")).hi
    assert exp_iv(Iv.from_str("1e-9") * log_x).lo > ((z0 / z_int_lb).sqrt() + Iv.from_str("1e-30")).hi

    eta_int = Iv(1, 1) / (z_int_lb * log_z0)
    log_z_lb = log_z0 * (Iv(1, 1) - eta_int)
    log_z_iv = Iv(log_z_lb.lo, log_z0.hi)

    log_h0 = Iv.from_str("0.5") * log_x - (b_a + Iv(1, 1)) * ln_iv(log_x)
    assert log_h0.lo > ln_iv(Iv(10 ** 9, 10 ** 9)).hi

    # Since z <= N^(1/M), s_A = ln(D_1)/ln(z) >= ln(D_1)/ln(N^(1/M)) = M * (0.5 - alpha)
    s_a = m_iv * (Iv.from_str("0.5") - alpha)
    assert s_a.lo > Decimal(2)

    lb_a = f_lin_lb(s_a) - eps_iv * c2_eff * E2 * h_lin_ub(s_a)

    # V_N(z) / (U_N / ln z) relative deviation using z >= z0 - 1
    sqrt_z_lb = z_int_lb.sqrt()
    f1 = (Iv(3, 3) * log_z0 + Iv(5, 5)) / (Iv(8, 8) * PI * sqrt_z_lb)
    f2 = Iv(2, 2) / z_int_lb
    f3 = (Iv(8, 8) * log_x) / z_int_lb
    f4 = Iv(1, 1) / (z_int_lb - Iv(1, 1))
    d_lo = Iv(1, 1) - (Iv(1, 1) - f1) * (Iv(1, 1) - f2) * (Iv(1, 1) - f3) * (Iv(1, 1) - f4)
    d_hi = (Iv(1, 1) + f1) * (Iv(1, 1) + f2) * (Iv(1, 1) + f3) * (Iv(1, 1) + f4) - Iv(1, 1)
    delta_v = Iv(D_ZERO, max(d_lo.hi, d_hi.hi))

    assert log_x.lo > Decimal(3)
    alpha_q = b_q * ln_iv(log_x) / log_x
    u_start = Iv(1, 1) / m_iv
    du = (beta - u_start) / Iv(spec.l_strips, spec.l_strips)
    mert_coeff = Iv.from_str("6.836e-6") + Iv.from_str("2.964e-6")
    q_ratio_ub = z_int_lb / (z_int_lb - Iv(1, 1))
    r_cap = Iv.from_str("2.95")

    sum_aq_main = Iv(0, 0)
    for k in range(spec.l_strips):
        uk = u_start + Iv(k, k) * du
        uk1 = u_start + Iv(k + 1, k + 1) * du
        r_exp = min_iv(r_cap, Iv.from_str("0.5") * m_iv * (Iv.from_str("0.5") - alpha_q - uk1))
        assert r_exp.lo > D_ZERO
        vj_lb = vj_monotone_lb_iv(log_x, m_iv, r_exp, delta_v, log_z_override=log_z_iv)
        assert vj_lb.lo > D_ZERO
        sum_q_sub = ln_iv(uk1 / uk) + mert_coeff / (uk * log_x) + Iv(1, 1) / exp_iv(uk * log_x)
        if k == 0:
            # Cover at most one prime q = z = floor(N^(1/M)) in [floor(N^(1/M)), N^(1/M))
            sum_q_sub = sum_q_sub + Iv(1, 1) / (z_int_lb - Iv(1, 1))
        sum_aq_main = sum_aq_main + (q_ratio_ub * sum_q_sub) / vj_lb

    half_aq = Iv.from_str("0.5") * sum_aq_main
    main_bracket = lb_a - half_aq
    assert main_bracket.lo > D_ZERO
    main_coeff = (Iv(1, 1) - delta_v) * E_NEG_GAMMA * main_bracket

    cp = c_pi_iv(log_x)
    sqrt_x = exp_iv(Iv.from_str("0.5") * log_x)
    c_pt = cp + Iv(1, 1) / (Iv(16, 16) * PI) + Iv.from_str("1.3841") / (sqrt_x * ln_iv(log_x))
    odd_sf = Iv(4, 4) / (PI * PI) + Iv(1, 1) / exp_iv(Iv.from_str("0.1") * log_x)
    c4g = odd_sf * c_pt

    err_r1 = c4g / (m_iv * U_CONST * pow_real_iv(log_x, b_a - Iv(2, 2)))
    sum_q_inv = ln_iv(beta * m_iv) + mert_coeff / (u_start * log_x) + Iv(1, 1) / (z_int_lb - Iv(1, 1))
    assert b_q.lo > Decimal(5)
    err_aq1 = (
        (Iv.from_str("0.0625") * c_pt * sum_q_inv / (m_iv * U_CONST))
        * ((Iv.from_str("0.5") * log_x + Iv(6, 6)) ** 2)
        / pow_real_iv(log_x, b_q - Iv(3, 3))
    )
    assert (Iv.from_str("0.5") - beta).lo > (Iv(6, 6) / log_x).hi
    y_over_n = exp_iv((beta - Iv.from_str("0.5")) * log_x)
    g_phi_n05 = H_TILDE * (Iv.from_str("0.25") * log_x + ALPHA0 + C_F0)
    err_aq2 = (
        Iv.from_str("0.5")
        * c4g
        * y_over_n
        * (log_x ** 3)
        * (Iv(1, 1) + g_phi_n05 ** 3)
        / (m_iv * U_CONST)
    )
    assert log_x.lo > Decimal(2 * spec.m_div)
    err_q2 = (log_x ** 2) / (Iv(2, 2) * m_iv * U_CONST * (z_int_lb - Iv(1, 1)))
    err_one = (log_x ** 2) / (m_iv * U_CONST * x_iv)

    tot_err = err_r1 + err_aq1 + err_aq2 + err_q2 + err_one
    net = main_coeff - tot_err
    assert net.lo > D_ZERO, f"Regime 3 failed at 10^{spec.exp10}: net={net}"

    c2_loss_per_unit = (Iv(1, 1) - delta_v) * E_NEG_GAMMA * eps_iv * E2 * h_lin_ub(s_a)
    c2_slack = c2_eff + net / c2_loss_per_unit

    return RayCertificate(
        spec=spec,
        alpha_dec=alpha_dec,
        eps_star_hi=eps_star.hi,
        k_target=spec.k_target,
        rec_mode=spec.rec_mode,
        c2_used_hi=c2_eff.hi,
        c2_breakeven=c2_slack.lo,
        s_a_lo=s_a.lo,
        delta_v_hi=delta_v.hi,
        lb_a_lo=lb_a.lo,
        half_sum_aq_hi=half_aq.hi,
        main_lo=main_coeff.lo,
        err_hi=tot_err.hi,
        net_lo=net.lo,
    )
