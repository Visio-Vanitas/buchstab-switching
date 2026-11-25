"""
Combinatorial Bonferroni `Q_1 x odd/even P_2` elementary-symmetric evaluators
and analytic large-`z` `S_1` tail bounds.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from .constants import ODD_PRIMES, P_CUT, PRIMES
from .interval import Iv, clamp_pos_iv, exp_iv, ln_iv
from .primes_and_mertens import INV_PM1_SQ_ALL, INV_PP1_ALL, PREFIX_PM1_SQ, PREFIX_PP1, pi_ub_iv, sum_inv_p_ub


def comb_int(n: int, k: int) -> int:
    if k < 0 or k > n:
        return 0
    k = min(k, n - k)
    num, den = 1, 1
    for i in range(1, k + 1):
        num *= n - k + i
        den *= i
    return num // den


def elem_sym_iv(weights: list[Iv], max_k: int) -> list[Iv]:
    """Elementary symmetric polynomials `e_0 .. e_{max_k}` in pure `Iv`."""
    e = [Iv(0, 0)] * (max_k + 1)
    e[0] = Iv(1, 1)
    for w in weights:
        for k in range(max_k, 0, -1):
            e[k] = e[k] + w * e[k - 1]
    return e


@dataclass(frozen=True)
class OddBonfEval:
    v_lb: Iv
    ratio_odd: Iv
    n_moduli: Iv
    v_full_if_exact: Iv | None


def eval_odd_bonferroni_s_a(z: int, a: int, m_odd: int, sqrt_x_lo: int) -> OddBonfEval:
    """
    Evaluate `Q_1(a) x odd Bonferroni(m_odd)` lower bound on `S(A, P_N(z))` for any `z`.
    Uses exact elementary symmetric polynomials for `z <= 1500` and analytic `S_1` tail above.
    """
    assert m_odd % 2 == 1
    z_iv = Iv(z, z)
    log_z = ln_iv(z_iv)
    q1_ps = ODD_PRIMES[:a]
    p_a = q1_ps[-1] if a > 0 else 2
    q1_prod = 1
    v_q1 = Iv(1, 1)
    for p in q1_ps:
        q1_prod *= p
        v_q1 = v_q1 * Iv.from_frac(Fraction(p - 2, p - 1))

    if z <= 2500:
        p_full = [p for p in ODD_PRIMES if p < z]
        p2_ps = p_full[a:]
        prod_max = q1_prod
        for p in p2_ps[-m_odd:]:
            prod_max *= p
        assert prod_max <= sqrt_x_lo, f"Q1*P2_max={prod_max} > sqrt(X_lo)={sqrt_x_lo}"
        w2 = [Iv.from_frac(Fraction(1, p - 1)) for p in p2_ps]
        g_full = Iv(1, 1)
        for w in w2:
            g_full = g_full * (Iv(1, 1) - w)
        v_full = v_q1 * g_full
        e2 = elem_sym_iv(w2, m_odd) if p2_ps else [Iv(1, 1)]
        b_odd = sum((e2[j] if j % 2 == 0 else -e2[j] for j in range(m_odd + 1)), Iv(0, 0)) if p2_ps else Iv(1, 1)
        ratio_odd = (b_odd / g_full) if p2_ps else Iv(1, 1)
        n_d = Iv((1 << a) * sum(comb_int(len(p2_ps), j) for j in range(m_odd + 1)))
        return OddBonfEval(v_lb=v_full, ratio_odd=ratio_odd, n_moduli=n_d, v_full_if_exact=v_full)

    assert q1_prod * (z ** m_odd) <= sqrt_x_lo, f"Q1*z^{m_odd} > sqrt(X_lo)"
    exact_sum_p_pa = sum((Iv.from_frac(Fraction(1, p)) for p in PRIMES if p <= p_a), Iv(0, 0))
    tail_pp1 = INV_PP1_ALL - PREFIX_PP1[a]
    tail_pm1_sq = INV_PM1_SQ_ALL - PREFIX_PM1_SQ[a]
    s1 = clamp_pos_iv(sum_inv_p_ub(z_iv, log_z) - exact_sum_p_pa) + tail_pp1
    c_log2 = Iv(1, 1) / (Iv(2, 2) * (Iv(1, 1) - Iv(1, 1) / Iv(max(p_a, 3), max(p_a, 3))))
    g_full_lb = exp_iv(-(s1 + c_log2 * tail_pm1_sq))
    fact = 1
    for j in range(1, m_odd + 2):
        fact *= j
    ratio_odd = Iv(1, 1) - ((s1 ** (m_odd + 1)) / Iv(fact, fact)) / g_full_lb
    pz_ub = pi_ub_iv(z_iv, log_z)
    sum_pz, fact_j = Iv(0, 0), 1
    for j in range(m_odd + 1):
        if j > 0:
            fact_j *= j
        sum_pz = sum_pz + (pz_ub ** j) / Iv(fact_j, fact_j)
    n_d = Iv(1 << a, 1 << a) * sum_pz
    return OddBonfEval(v_lb=v_q1 * g_full_lb, ratio_odd=ratio_odd, n_moduli=n_d, v_full_if_exact=None)


def build_p_sub_table(primes_lt_z: list[int]) -> list[tuple[int, Iv, Iv, int]]:
    """Precompute `(prod, V_sub, inv_phi, k)` for `P_sub` inclusion-exclusion."""
    table: list[tuple[int, Iv, Iv, int]] = [(1, Iv(1, 1), Iv(1, 1), 0)]
    prod, v_s, ip_s = 1, Iv(1, 1), Iv(1, 1)
    for k, p in enumerate(primes_lt_z, 1):
        prod *= p
        v_s = v_s * Iv.from_frac(Fraction(p - 2, p - 1))
        ip_s = ip_s * Iv.from_frac(Fraction(p, p - 1))
        table.append((prod, v_s, ip_s, k))
    return table


def build_multi_cutoff_even_tables(
    z: int, sqrt_x_lo: int, cutoffs: tuple[int, ...] = (15, 29, 53, 97, 179, 331, 600)
) -> list[tuple[int, Iv, int, Iv, Iv]]:
    """Build `(prod_max, V(z_sub)*ratio_ev, n_d, inv_phi, ratio_ev)` options for `S(A_q)`."""
    selected = sorted(set([min(z, c) for c in cutoffs if c >= 7] + ([z] if z <= 1200 else [])))
    p_pool = [p for p in ODD_PRIMES if p < min(z, 1200)]
    opts: list[tuple[int, Iv, int, Iv, Iv]] = []
    for zs in selected:
        ps = [p for p in p_pool if p < zs]
        v_s = Iv(1, 1)
        for p in ps:
            v_s = v_s * Iv.from_frac(Fraction(p - 2, p - 1))
        for aq in range(0, min(len(ps), 9), 2):
            qq_ps, p2q = ps[:aq], ps[aq:]
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
            ee = elem_sym_iv(w2q, min(10, len(p2q)))
            for mev in (2, 4, 6, 8, 10):
                if mev > len(p2q):
                    continue
                prod_ev = qq
                for p in p2q[-mev:]:
                    prod_ev *= p
                rat = sum((ee[j] if j % 2 == 0 else -ee[j] for j in range(mev + 1)), Iv(0, 0)) / g2q
                nd = (1 << aq) * sum(comb_int(len(p2q), j) for j in range(mev + 1))
                ip2 = sum((ee[j] for j in range(mev + 1)), Iv(0, 0))
                opts.append((prod_ev, v_s * rat, nd, inv_qq * ip2, rat))
    return opts
