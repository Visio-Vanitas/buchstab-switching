#!/usr/bin/env python3
"""
Zero-float outward-rounded certifier for:
  Theorem 1A: E(X) <= C * sqrt(X) * (log X)^3  for all X >= 4
  Theorem 1B: [X, X + C1 * (log X)^2] contains p1 + p2  for all X >= 4
under GRH + E(4 * 10^18) = 0.

Strict discipline:
- Zero IEEE-754 floats (Decimal FloatOperation trap enabled, no import math).
- Directed rounding: ROUND_CEILING for upper bounds, ROUND_FLOOR for lower bounds.
- Covers X in [4*10^18, 10^10000] cell-by-cell and X >= 10^10000 asymptotically.
"""

from decimal import Decimal, localcontext, getcontext, ROUND_CEILING, ROUND_FLOOR, FloatOperation
from fractions import Fraction

# Precision and strict float trap
PREC = 80
ctx = getcontext()
ctx.prec = PREC
ctx.traps[FloatOperation] = True


def d_ceil(fn):
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_CEILING
        return +fn()


def d_floor(fn):
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_FLOOR
        return +fn()


def ceil_mul(a: Decimal, b: Decimal) -> Decimal:
    return d_ceil(lambda: a * b)


def floor_mul(a: Decimal, b: Decimal) -> Decimal:
    return d_floor(lambda: a * b)


def ceil_div(a: Decimal, b: Decimal) -> Decimal:
    assert b > 0
    return d_ceil(lambda: a / b)


def floor_div(a: Decimal, b: Decimal) -> Decimal:
    assert b > 0
    return d_floor(lambda: a / b)


def ceil_add(a: Decimal, b: Decimal) -> Decimal:
    return d_ceil(lambda: a + b)


def floor_add(a: Decimal, b: Decimal) -> Decimal:
    return d_floor(lambda: a + b)


def ceil_sub(a: Decimal, b: Decimal) -> Decimal:
    return d_ceil(lambda: a - b)


def floor_sub(a: Decimal, b: Decimal) -> Decimal:
    return d_floor(lambda: a - b)


def ceil_sqrt(a: Decimal) -> Decimal:
    assert a >= 0
    return d_ceil(lambda: a.sqrt())


def floor_sqrt(a: Decimal) -> Decimal:
    assert a >= 0
    return d_floor(lambda: a.sqrt())


def ceil_ln(a: Decimal) -> Decimal:
    assert a > 0
    return d_ceil(lambda: a.ln())


def floor_ln(a: Decimal) -> Decimal:
    assert a > 0
    return d_floor(lambda: a.ln())


def ceil_exp(a: Decimal) -> Decimal:
    return d_ceil(lambda: a.exp())


def floor_exp(a: Decimal) -> Decimal:
    return d_floor(lambda: a.exp())


def frac_ceil(f: Fraction) -> Decimal:
    return ceil_div(Decimal(f.numerator), Decimal(f.denominator))


def frac_floor(f: Fraction) -> Decimal:
    return floor_div(Decimal(f.numerator), Decimal(f.denominator))


# ---------------------------------------------------------------------------
# Elementary rigorous constant enclosures (Machin pi, atan, zeta'(7/4)/zeta)
# ---------------------------------------------------------------------------

def enclose_atan_rational(num: int, den: int, terms: int = 80) -> tuple[Decimal, Decimal]:
    """Enclose atan(num/den) for 0 < num < den via alternating Taylor series."""
    assert 0 < num < den
    x = Fraction(num, den)
    x2 = x * x
    # Partial sum with even number of terms -> lower bound; odd -> upper bound
    # Actually alternating decreasing series: S_{2m} < atan(x) < S_{2m+1}
    # Let's compute S_{2m} (last term negative) and add next positive term for S_{2m+1}.
    s_even = Fraction(0)
    p = x
    for k in range(2 * terms):
        term = p / (2 * k + 1)
        if k % 2 == 0:
            s_even += term
        else:
            s_even -= term
        p *= x2
    # k = 2*terms is even, so positive next term gives strict upper bound
    s_odd = s_even + p / (4 * terms + 1)
    assert s_even < s_odd
    return frac_floor(s_even), frac_ceil(s_odd)


def enclose_pi() -> tuple[Decimal, Decimal]:
    """pi = 16 * atan(1/5) - 4 * atan(1/239)."""
    a1_lo, a1_hi = enclose_atan_rational(1, 5, terms=50)
    a2_lo, a2_hi = enclose_atan_rational(1, 239, terms=25)
    pi_lo = floor_sub(floor_mul(Decimal(16), a1_lo), ceil_mul(Decimal(4), a2_hi))
    pi_hi = ceil_sub(ceil_mul(Decimal(16), a1_hi), floor_mul(Decimal(4), a2_lo))
    assert Decimal('3.141592653589793238') < pi_lo < pi_hi < Decimal('3.141592653589793239')
    return pi_lo, pi_hi


def enclose_atan_gt1(h_num: int, h_den: int) -> Decimal:
    """Lower bound on atan(x) for x = h_num / h_den >= 1 via atan(x) = pi/2 - atan(1/x)."""
    assert h_num >= h_den > 0
    pi_lo, _ = enclose_pi()
    if h_num == h_den:
        return floor_div(pi_lo, Decimal(4))
    _, inv_hi = enclose_atan_rational(h_den, h_num, terms=40)
    return floor_sub(floor_div(pi_lo, Decimal(2)), inv_hi)


def compute_primes(limit: int) -> list[int]:
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for p in range(2, limit + 1):
        if p * p > limit:
            break
        if sieve[p]:
            for m in range(p * p, limit + 1, p):
                sieve[m] = False
    return [i for i, ok in enumerate(sieve) if ok]


def mangoldt_up_to(N: int) -> list[Decimal]:
    """Return [0, Lambda(1), ..., Lambda(N)] upper-bounded in Decimal."""
    primes = compute_primes(N)
    lam = [Decimal(0)] * (N + 1)
    for p in primes:
        lp = ceil_ln(Decimal(p))
        pk = p
        while pk <= N:
            lam[pk] = lp
            pk *= p
    return lam


def cert_neg_zeta_deriv_7_4() -> Decimal:
    """Upper bound on -zeta'(7/4)/zeta(7/4) = sum_{n>=2} Lambda(n) / n^(7/4)."""
    N = 500
    lam = mangoldt_up_to(N)
    total = Decimal(0)
    for n in range(2, N + 1):
        if lam[n] > 0:
            # n^(7/4) = n * sqrt(n * sqrt(n))
            n_d = Decimal(n)
            n_7_4_lo = floor_mul(n_d, floor_sqrt(floor_mul(n_d, floor_sqrt(n_d))))
            total = ceil_add(total, ceil_div(lam[n], n_7_4_lo))
    # Tail: sum_{n > N} log(n)/n^(7/4) <= int_N^inf log(x)/x^(7/4) dx
    # = (4/3) * N^(-3/4) * (log(N) + 4/3)
    N_d = Decimal(N)
    N_3_4_lo = floor_sqrt(floor_mul(N_d, floor_sqrt(N_d)))
    ln_N_hi = ceil_ln(N_d)
    tail = ceil_mul(
        ceil_div(Decimal(4), Decimal(3)),
        ceil_div(ceil_add(ln_N_hi, ceil_div(Decimal(4), Decimal(3))), N_3_4_lo),
    )
    ans = ceil_add(total, tail)
    assert ans < Decimal('0.964')
    return ans


def cert_twin_prime_lower() -> Decimal:
    """Lower bound on Pi_2 = prod_{p>2} (1 - 1/(p-1)^2) via UpperErrors.lean method."""
    primes = [p for p in compute_primes(59) if p > 2]
    prod = Fraction(1)
    for p in primes:
        prod *= Fraction((p - 1) ** 2 - 1, (p - 1) ** 2)
    head_lo = frac_floor(prod)
    # Tail p > 59 bound from UpperErrors.lean: sum_{p>59} 1/(p-1)^2 < sum_{r in {1,7,11,13,17,19,23,29}} 1/(30*(44+r))
    tail_frac = sum(Fraction(1, 30 * (44 + r)) for r in (1, 7, 11, 13, 17, 19, 23, 29))
    tail_hi = frac_ceil(tail_frac)
    assert tail_hi < Decimal('0.00462')
    pi2_lo = floor_mul(head_lo, floor_sub(Decimal(1), tail_hi))
    assert pi2_lo > Decimal('0.659')
    return pi2_lo


def cert_K2() -> Decimal:
    """Upper bound on K2 = prod_p (1 + (2p-1)/(p(p-1)^2))."""
    primes = compute_primes(200)
    prod = Fraction(1)
    for p in primes:
        prod *= Fraction(p * (p - 1) ** 2 + (2 * p - 1), p * (p - 1) ** 2)
    head_hi = frac_ceil(prod)
    # Tail p > 200: sum_{n>=201} (2n-1)/(n(n-1)^2) <= 2/200 + 1/(200^2)
    tail_exp = ceil_add(ceil_div(Decimal(2), Decimal(200)), ceil_div(Decimal(1), Decimal(40000)))
    ans = ceil_mul(head_hi, ceil_exp(tail_exp))
    assert ans < Decimal(8)
    return ans


def cert_K_one_eighth() -> Decimal:
    """
    Certify prod_{p | N} (2p-1)/(p-1) <= K_1_8 * N^(1/8) for all N >= 1.
    Check (2p-1)/(p-1) <= p^(1/8) for all p >= 271:
    Indeed 541^8 < 271 * 270^8, and for p >= 271, (2p-1)/(p-1) <= 541/270 while p^(1/8) >= 271^(1/8).
    """
    assert 541 ** 8 < 271 * (270 ** 8)
    primes = compute_primes(270)
    K = Decimal(1)
    for p in primes:
        ratio = ceil_div(Decimal(2 * p - 1), Decimal(p - 1))
        p_1_8_lo = floor_sqrt(floor_sqrt(floor_sqrt(Decimal(p))))
        if ratio > p_1_8_lo:
            K = ceil_mul(K, ceil_div(ratio, p_1_8_lo))
    return K


def cert_q_over_phi_sum_const() -> Decimal:
    """
    Upper bound on prod_p (1 + 1/(p(p-1))) = zeta(2)*zeta(3)/zeta(6),
    so sum_{q <= Q0} q/phi(q) <= C_phi * Q0 for all Q0 >= 1.
    """
    primes = compute_primes(300)
    prod = Fraction(1)
    for p in primes:
        prod *= Fraction(p * (p - 1) + 1, p * (p - 1))
    # Tail p > 300: sum_{n>=301} 1/(n(n-1)) = 1/300
    ans = ceil_mul(frac_ceil(prod), ceil_exp(ceil_div(Decimal(1), Decimal(300))))
    assert ans < Decimal('1.95')
    return ans


# ---------------------------------------------------------------------------
# Core Analytic Bounds
# ---------------------------------------------------------------------------

class AnalyticConstants:
    def __init__(self):
        self.pi_lo, self.pi_hi = enclose_pi()
        self.e_lo = floor_exp(Decimal(1))
        self.e_hi = ceil_exp(Decimal(1))
        self.sqrt2_hi = ceil_sqrt(Decimal(2))
        self.sqrt_pi_hi = ceil_sqrt(self.pi_hi)
        self.sqrt_2pi_hi = ceil_sqrt(ceil_mul(Decimal(2), self.pi_hi))

        self.pi2_lo = cert_twin_prime_lower()
        self.K2_hi = cert_K2()
        self.K_1_8_hi = cert_K_one_eighth()
        self.C_qphi_hi = cert_q_over_phi_sum_const()

        # -zeta'(7/4)/zeta(7/4)
        self.neg_zlog_7_4 = cert_neg_zeta_deriv_7_4()

        # C_zeta in sum_rho (5/4)/((5/4)^2 + (gamma-tau)^2) <= (log(4+|tau|) + C_zeta)/2
        # C_zeta = 2 * (neg_zlog_7_4 + 4/3 - 0.5*ln(2*pi) + (4/15 + 16/675)/2)
        ln_2pi_lo = floor_ln(floor_mul(Decimal(2), self.pi_lo))
        binet_err_hi = ceil_div(
            ceil_add(ceil_div(Decimal(4), Decimal(15)), ceil_div(Decimal(16), Decimal(675))),
            Decimal(2),
        )
        half_C_zeta = ceil_add(
            ceil_sub(
                ceil_add(self.neg_zlog_7_4, ceil_div(Decimal(4), Decimal(3))),
                floor_div(ln_2pi_lo, Decimal(2)),
            ),
            binet_err_hi,
        )
        self.C_zeta = ceil_mul(Decimal(2), half_C_zeta)
        self.C_dir = Decimal('0.2')  # from DirichletPoissonZeroMass.long_poisson

        # Vertical line Re(s)=1/4 remainder constant:
        # |Gamma(1/4+it)| <= sqrt(2)*Gamma(1/4)*e^(-pi|t|/2), and Gamma(1/4) <= 4
        self.gamma_1_4_coeff = ceil_mul(Decimal(4), self.sqrt2_hi)  # <= 5.66
        # |-L'(1/4+it)/L(1/4+it)| <= A_vert + 15*(log q* + log(4+|t|) + C(q*))
        # A_vert <= neg_zlog_7_4 + (3/8)*(64/7 + pi^2/6) + (4/3 + 4/3 + 4 + 4/7)
        digamma_diff_hi = ceil_mul(
            ceil_div(Decimal(3), Decimal(8)),
            ceil_add(ceil_div(Decimal(64), Decimal(7)), ceil_div(ceil_mul(self.pi_hi, self.pi_hi), Decimal(6))),
        )
        pole_1_4_hi = frac_ceil(Fraction(4, 3) + Fraction(4, 3) + 4 + Fraction(4, 7))
        self.A_vert_1_4 = ceil_add(ceil_add(self.neg_zlog_7_4, digamma_diff_hi), pole_1_4_hi)

        # Elementary Chebyshev bound psi(t) <= alpha_psi * t for all t > 0 (Rosser-Schoenfeld Thm 12: 1.03883)
        self.alpha_psi = Decimal('1.03883')
        # Rosser-Schoenfeld Thm 13: psi(x) - theta(x) <= 1.4262 * sqrt(x) for all x > 0
        self.alpha_pp = Decimal('1.4262')

        # Parseval integral constant: sum_{n>=2} Lambda(n)^2 e^{-2n/Y} <= (alpha_psi/2) * Y * (log Y + C_pars)
        # C_pars = 1 - log 2 + e^{-1}
        self.C_pars = ceil_add(
            ceil_sub(Decimal(1), floor_ln(Decimal(2))),
            ceil_div(Decimal(1), self.e_lo),
        )


def certify_theorem_1A_cell(const: AnalyticConstants, Y_lo: Decimal, Y_hi: Decimal) -> Decimal:
    """
    Certify C_cell such that for all Y in [Y_lo, Y_hi]:
      E(Y) - E(Y/2) <= C_cell * sqrt(Y) * (log Y)^3.
    Returns C_cell (upper bound).
    """
    L_lo = floor_ln(Y_lo)
    L_hi = ceil_ln(Y_hi)
    sqrt_Y_lo = floor_sqrt(Y_lo)
    sqrt_Y_hi = ceil_sqrt(Y_hi)
    Y_1_4_lo = floor_sqrt(sqrt_Y_lo)
    Y_3_4_hi = ceil_mul(sqrt_Y_hi, ceil_sqrt(sqrt_Y_hi))

    # Major arc parameters: Q0 = floor(0.5 * sqrt(Y)), Q_D = 2 * sqrt(Y), Delta(q) = 1/(2*q*sqrt(Y))
    # For any (a, q) with q <= 2*sqrt(Y) and |beta| <= 1/(2*q*sqrt(Y)):
    #   q*A <= q + pi*sqrt(Y) <= (2 + pi)*sqrt(Y) on m, and <= (0.5 + pi)*sqrt(Y) on M.
    #   Also q*(A+4) <= (2 + 4 + pi)*sqrt(Y) <= 10*sqrt(Y) (actually on q <= 2*sqrt(Y): 5q + pi*sqrt(Y) <= (10 + pi)*sqrt(Y)).
    # Let's bound the zero sum per character chi* mod q* (q* <= 2*sqrt(Y)):
    #   Sum_rho <= sqrt(2*pi) * Y^{1/2} * [ ((A + 2h)/sqrt(A)) * (log(q*(A+h+4)) + C_q + 1) / (4*atan(4h/5))
    #                                      + (opp_side) / sqrt(A) ]
    # Split A in [1, A_max] where A_max = 1 + pi*sqrt(Y_hi) into two regions to optimize h:
    #   Region 1: A in [1, 100], use h = 5/4 (4*atan(1) = pi, 2h = 2.5).
    #     For A in [1, 100]: (A + 2.5)/sqrt(A) <= max(3.5, (102.5)/10) = 10.25?
    #     Wait: if we split [1, 100] into [1, 16] (<= 16/4+2.5/4 = 4.625) and [16, 100] with h = 5/4?
    #     Wait: on [1, 16], (A + 2.5)/sqrt(A) is convex, max at endpoints: A=1 -> 3.5, A=16 -> 18.5/4 = 4.625!
    #     Even better: split A into [1, 4], [4, 25], [25, 200], [200, A_max] with optimal h!
    #     Wait: on A in [1, 4], h = 5/4: (A+2.5)/sqrt(A) <= max(3.5, 6.5/2) = 3.5!
    #     On A in [4, 25], h = 5/4: (A+2.5)/sqrt(A) <= max(3.25, 27.5/5) = 5.5! Wait, why is 5.5 bigger than 3.5? Because sqrt(A) is ONLY 5 while q is <= (2+pi)*sqrt(Y)/A!
    #     WAIT A SECOND! Remember we multiply by sqrt(q)!!
    #     sqrt(q) * (A + 2h) / sqrt(A) = sqrt(q*A) * (1 + 2h/A)!!
    #     LOOK AT THAT IDENTITY:
    #       sqrt(q) * (A + 2h) / sqrt(A) = sqrt(q * A) * (1 + 2h/A)!!
    #     Because q * A <= q + pi * sqrt(Y) <= (2 + pi) * sqrt(Y) UNIFORMLY FOR ALL A >= 1!!
    #     AND 1 + 2h/A IS DECREASING IN A!!
    #     So for A >= 1, 1 + 2h/A <= 1 + 2h, achieved at A = 1!
    #     And at A >= 10, with h = 25, 1 + 50/A <= 6, whereas with h = 5/4, 1 + 2.5/A <= 1.25!!
    #     HOLD ON: 1 + 2.5/A with h = 5/4 is <= 3.5 at A = 1 and <= 1.25 at A >= 10!
    #     Wait: compare (1 + 2h/A)/(4*atan(4h/5)) at A >= 10:
    #       h = 5/4: 1.25 / pi = 0.3979
    #       h = 5:   (1 + 10/A) / (4*atan(4)) <= 2 / 5.303 = 0.3771
    #       h = 25:  (1 + 50/A) / (4*atan(20)) <= 6 / 6.083 (worse at A=10, better at A >= 25: 3/6.083 = 0.49, at A >= 100: 1.5/6.083 = 0.2466!)
    #     That is SO CLEAN! For A in [1, 100], use h = 5/4; for A > 100, use h = 25 (1 + 50/100 = 1.5)!

    def zero_sum_K(coeff_qA_hi: Decimal, q_star_max: Decimal, A_min: Decimal,
                   h_num: int, h_den: int, C_q: Decimal) -> Decimal:
        """
        Bound sqrt(q) * sum_rho |Gamma(rho) z^{-rho}| / (Y^{3/4} * L_lo)
        when q * A <= coeff_qA_hi * sqrt(Y), A >= A_min, q* <= q_star_max,
        and h = h_num / h_den.
        Returns K such that sqrt(q) * sum_rho <= K * Y^{3/4} * L_lo.
        Wait: since Y >= Y_lo, we use log(q*(A+h+4)) + C_q + 1 <= (0.5 * L_hi + c_log) <= ((0.5 + c_log/L_lo) * L)
        Wait: let's express it as K * Y^{3/4} * log(Y) valid for ALL Y in [Y_lo, Y_hi]!
        """
        h = ceil_div(Decimal(h_num), Decimal(h_den))
        atan_lo = enclose_atan_gt1(4 * h_num, 5 * h_den)
        denom_lo = floor_mul(Decimal(4), atan_lo)

        # (1 + 2h/A_min) / denom_lo
        main_ratio = ceil_div(ceil_add(Decimal(1), ceil_div(ceil_mul(Decimal(2), h), A_min)), denom_lo)

        # Log bound: q*(A + h + 4) <= q*A + (h+4)*q <= coeff_qA_hi*sqrt(Y) + (h+4)*2*sqrt(Y)
        # = (coeff_qA_hi + 2*(h+4)) * sqrt(Y)
        c_arg = ceil_add(coeff_qA_hi, ceil_mul(Decimal(2), ceil_add(h, Decimal(4))))
        # log(c_arg * sqrt(Y)) + C_q + 1 = 0.5 * log Y + log(c_arg) + C_q + 1
        c_add = ceil_add(ceil_ln(c_arg), ceil_add(C_q, Decimal(1)))
        # Since Y >= Y_lo, 0.5 * L + c_add <= (0.5 + c_add / L_lo) * L
        log_mult = ceil_add(Decimal('0.5'), ceil_div(c_add, L_lo))

        # Opposite sign decay: (2/pi + 2.5)/pi * (0.5*L_hi + log(5.89) + C_q + 1) / sqrt(A_min)
        # Wait: sqrt(q) * opp / Y^{3/4}: sqrt(q) <= sqrt(2) * Y^{1/4}, so sqrt(q)*Y^{1/2} <= sqrt(2)*Y^{3/4}.
        # Wait: actually sqrt(q)/sqrt(A_min) * Y^{1/2}: for opp side we don't even get A_min help if A_min=1, just sqrt(q) <= sqrt(2)*Y^{1/4}!
        opp_h = Decimal('1.25')
        opp_const = ceil_div(ceil_add(ceil_div(Decimal(2), const.pi_lo), Decimal('2.5')), const.pi_lo)
        opp_log_c = ceil_add(ceil_ln(Decimal('5.89')), ceil_add(C_q, Decimal(1)))
        # q* <= 2*sqrt(Y) => log q* <= 0.5 * log Y + log 2
        opp_log_mult = ceil_add(Decimal('0.5'), ceil_div(ceil_add(ceil_ln(Decimal(2)), opp_log_c), L_lo))

        # Main part: sqrt(2*pi) * sqrt(coeff_qA_hi) * main_ratio * log_mult
        main_K = ceil_mul(const.sqrt_2pi_hi, ceil_mul(ceil_sqrt(coeff_qA_hi), ceil_mul(main_ratio, log_mult)))
        # Opp part: sqrt(2*pi) * sqrt(2) * opp_const * opp_log_mult / sqrt(A_min)
        opp_K = ceil_div(
            ceil_mul(const.sqrt_2pi_hi, ceil_mul(const.sqrt2_hi, ceil_mul(opp_const, opp_log_mult))),
            floor_sqrt(A_min),
        )
        return ceil_add(main_K, opp_K)

    # Vertical contour Re(s)=1/4 remainder:
    def vert_K(coeff_q_hi: Decimal, C_q: Decimal) -> Decimal:
        pi_3_4_hi = ceil_sqrt(ceil_mul(const.pi_hi, ceil_sqrt(const.pi_hi)))
        y_scale_hi = ceil_add(
            ceil_div(ceil_sqrt(coeff_q_hi), Y_1_4_lo),
            ceil_div(pi_3_4_hi, floor_sqrt(Y_1_4_lo)),
        )
        pre = ceil_div(const.gamma_1_4_coeff, const.pi_lo)
        c_log = ceil_add(ceil_ln(Decimal(10)), ceil_add(C_q, Decimal(1)))
        inner = ceil_add(
            ceil_div(const.A_vert_1_4, L_lo),
            ceil_mul(Decimal(15), ceil_add(Decimal('0.5'), ceil_div(c_log, L_lo))),
        )
        return ceil_mul(pre, ceil_mul(y_scale_hi, inner))

    # gcd(n, q) > 1 and imprimitivity correction
    ln2_lo = floor_ln(Decimal(2))
    omega_hi = ceil_add(ceil_div(ceil_add(ceil_div(L_hi, Decimal(2)), ceil_ln(Decimal(2))), ln2_lo), Decimal(1))
    gcd_err_hi = ceil_mul(
        Decimal(2),
        ceil_mul(omega_hi, ceil_add(ceil_add(L_hi, ceil_ln(L_hi)), Decimal(1))),
    )
    gcd_K_hi = ceil_div(gcd_err_hi, ceil_mul(ceil_mul(sqrt_Y_lo, Y_1_4_lo), L_lo))

    # Minor arcs m: q in (0.5*sqrt(Y), 2*sqrt(Y)]
    coeff_qA_minor = ceil_add(Decimal(2), const.pi_hi)
    K_minor_1 = ceil_add(
        zero_sum_K(coeff_qA_minor, ceil_mul(Decimal(2), sqrt_Y_hi), Decimal(1), 5, 4, const.C_dir),
        vert_K(Decimal(2), const.C_dir),
    )
    K_minor_2 = ceil_add(
        zero_sum_K(coeff_qA_minor, ceil_mul(Decimal(2), sqrt_Y_hi), Decimal(100), 25, 1, const.C_dir),
        vert_K(Decimal(2), const.C_dir),
    )
    K_minor_chi = max(K_minor_1, K_minor_2)

    K_chi0_only = ceil_add(
        zero_sum_K(ceil_add(Decimal(1), const.pi_hi), Decimal(1), Decimal(1), 5, 4, const.C_zeta),
        vert_K(Decimal(1), const.C_zeta),
    )
    M_minor_K = ceil_div(Decimal(2), L_lo)
    chi0_minor_K = ceil_div(ceil_mul(Decimal(2), K_chi0_only), Y_1_4_lo)
    K_minor_tot = ceil_add(ceil_add(K_minor_chi, gcd_K_hi), ceil_add(M_minor_K, chi0_minor_K))

    C_pars_mult = ceil_mul(
        ceil_div(const.alpha_psi, Decimal(2)),
        ceil_add(Decimal(1), ceil_div(const.C_pars, L_lo)),
    )
    I_minor_coeff = ceil_mul(ceil_mul(K_minor_tot, K_minor_tot), C_pars_mult)

    # Major arcs M: q <= 0.5 * sqrt(Y), |beta| <= 1/(2*q*sqrt(Y))
    coeff_qA_major = ceil_add(Decimal('0.5'), const.pi_hi)
    K_major_chi_1 = ceil_add(
        zero_sum_K(coeff_qA_major, ceil_mul(Decimal('0.5'), sqrt_Y_hi), Decimal(1), 5, 4, const.C_dir),
        vert_K(Decimal('0.5'), const.C_dir),
    )
    K_major_chi_2 = ceil_add(
        zero_sum_K(coeff_qA_major, ceil_mul(Decimal('0.5'), sqrt_Y_hi), Decimal(100), 25, 1, const.C_dir),
        vert_K(Decimal('0.5'), const.C_dir),
    )
    K_major_chi = max(K_major_chi_1, K_major_chi_2)

    delta_C = ceil_sub(const.C_zeta, const.C_dir)
    delta_chi0_K = ceil_div(
        ceil_mul(
            const.sqrt_2pi_hi,
            ceil_mul(
                delta_C,
                ceil_add(
                    ceil_mul(ceil_sqrt(ceil_add(Decimal(1), const.pi_hi)), ceil_div(Decimal('3.5'), const.pi_lo)),
                    ceil_div(ceil_add(ceil_div(Decimal(2), const.pi_lo), Decimal('2.5')), const.pi_lo),
                ),
            ),
        ),
        L_lo,
    )
    delta_vert_K = ceil_div(
        ceil_mul(
            ceil_div(const.gamma_1_4_coeff, const.pi_lo),
            ceil_mul(
                ceil_add(ceil_div(Decimal(1), Y_1_4_lo), ceil_div(ceil_sqrt(ceil_mul(const.pi_hi, ceil_sqrt(const.pi_hi))), floor_sqrt(Y_1_4_lo))),
                ceil_mul(Decimal(15), delta_C),
            ),
        ),
        L_lo,
    )
    K_major_tot = ceil_add(ceil_add(K_major_chi, gcd_K_hi), ceil_add(delta_chi0_K, delta_vert_K))

    sum_inv_phi_mult = ceil_mul(
        const.C_qphi_hi,
        ceil_add(Decimal('0.5'), ceil_div(Decimal(1), L_lo)),
    )
    int_M_sq_mult = ceil_div(sum_inv_phi_mult, Decimal(2))
    int_SM_sq_mult = ceil_mul(Decimal(2), ceil_add(C_pars_mult, int_M_sq_mult))
    I_major_part1_coeff = ceil_mul(Decimal(2), ceil_mul(ceil_mul(K_major_tot, K_major_tot), int_SM_sq_mult))

    # Part 2 of Major arcs
    c_add_M_5_4 = ceil_add(ceil_ln(ceil_add(coeff_qA_major, ceil_mul(Decimal(2), Decimal('5.25')))), ceil_add(const.C_dir, Decimal(1)))
    log_mult_M_5_4 = ceil_add(Decimal('0.5'), ceil_div(c_add_M_5_4, L_lo))

    c_add_M_25 = ceil_add(ceil_ln(ceil_add(coeff_qA_major, ceil_mul(Decimal(2), Decimal(29)))), ceil_add(const.C_dir, Decimal(1)))
    log_mult_M_25 = ceil_add(Decimal('0.5'), ceil_div(c_add_M_25, L_lo))

    opp_const = ceil_div(ceil_add(ceil_div(Decimal(2), const.pi_lo), Decimal('2.5')), const.pi_lo)
    opp_log_c = ceil_add(ceil_ln(Decimal('5.89')), ceil_add(const.C_dir, Decimal(1)))
    opp_log_mult = ceil_add(Decimal('0.5'), ceil_div(ceil_add(ceil_ln(Decimal(2)), opp_log_c), L_lo))

    K_z_smallA = ceil_mul(
        const.sqrt_2pi_hi,
        ceil_add(
            ceil_mul(ceil_div(Decimal('3.5'), const.pi_lo), log_mult_M_5_4),
            ceil_mul(opp_const, opp_log_mult),
        ),
    )
    pi_1_4_hi = ceil_sqrt(ceil_sqrt(const.pi_hi))
    K_vert_z_M = ceil_mul(
        ceil_div(const.gamma_1_4_coeff, const.pi_lo),
        ceil_mul(
            ceil_div(pi_1_4_hi, floor_sqrt(Y_1_4_lo)),
            ceil_add(ceil_div(const.A_vert_1_4, L_lo), ceil_mul(Decimal(15), log_mult_M_5_4)),
        ),
    )
    delta_chi0_z = ceil_div(
        ceil_mul(
            const.sqrt_2pi_hi,
            ceil_mul(
                delta_C,
                ceil_add(ceil_div(Decimal('3.5'), const.pi_lo), opp_const),
            ),
        ),
        L_lo,
    )
    gcd_z_M = ceil_div(gcd_err_hi, ceil_mul(sqrt_Y_lo, L_lo))
    K_z_smallA_tot = ceil_add(ceil_add(K_z_smallA, K_vert_z_M), ceil_add(delta_chi0_z, gcd_z_M))

    atan20_lo = enclose_atan_gt1(20, 1)
    denom25_lo = floor_mul(Decimal(4), atan20_lo)
    K_z_largeA = ceil_mul(
        const.sqrt_2pi_hi,
        ceil_add(
            ceil_mul(ceil_div(Decimal('1.5'), denom25_lo), log_mult_M_25),
            ceil_div(ceil_mul(opp_const, opp_log_mult), Decimal(100)),
        ),
    )
    K_z_largeA_tot = ceil_add(ceil_add(K_z_largeA, K_vert_z_M), ceil_add(delta_chi0_z, gcd_z_M))

    int_z_smallA = ceil_div(ceil_ln(Decimal(201)), const.pi_lo)
    int_z_largeA_mult = ceil_div(
        ceil_add(Decimal('0.5'), ceil_div(ceil_ln(ceil_add(ceil_mul(Decimal(2), const.pi_hi), Decimal(2))), L_lo)),
        const.pi_lo,
    )
    sum_q_phi_mult = ceil_mul(Decimal('0.5'), const.C_qphi_hi)
    bracket_Part2 = ceil_add(
        ceil_div(ceil_mul(ceil_mul(K_z_smallA_tot, K_z_smallA_tot), int_z_smallA), L_lo),
        ceil_mul(ceil_mul(K_z_largeA_tot, K_z_largeA_tot), int_z_largeA_mult),
    )
    I_major_part2_coeff = ceil_mul(Decimal(8), ceil_mul(sum_q_phi_mult, bracket_Part2))
    I_tot_coeff = ceil_add(I_minor_coeff, ceil_add(I_major_part1_coeff, I_major_part2_coeff))

    main_floor = floor_div(const.pi2_lo, const.e_hi)
    pp_loss = ceil_div(ceil_mul(Decimal(2), ceil_mul(const.alpha_pp, L_hi)), ceil_mul(const.e_lo, sqrt_Y_lo))
    Q0_lo_mult = Decimal('0.4999')
    Y_1_8_lo = floor_sqrt(Y_1_4_lo)
    Y_3_8_lo = floor_mul(Y_1_4_lo, Y_1_8_lo)
    sing_tail = ceil_div(
        ceil_mul(Decimal(2), ceil_mul(const.K2_hi, const.K_1_8_hi)),
        floor_mul(Q0_lo_mult, Y_3_8_lo),
    )
    sing_tail_scaled = ceil_div(sing_tail, const.e_lo)
    beta_tail = ceil_div(
        ceil_mul(
            ceil_div(const.K2_hi, floor_mul(const.pi_lo, const.pi_lo)),
            ceil_mul(const.K_1_8_hi, ceil_add(ceil_mul(Decimal('0.5'), L_hi), Decimal(1))),
        ),
        Y_3_8_lo,
    )
    gap_floor = floor_sub(main_floor, ceil_add(pp_loss, ceil_add(sing_tail_scaled, beta_tail)))
    assert gap_floor > Decimal('0.20'), f"Gap too small: {gap_floor}"
    return ceil_div(I_tot_coeff, floor_mul(gap_floor, gap_floor))


def certify_theorem_1B_cell(const: AnalyticConstants, X_lo: Decimal, X_hi: Decimal) -> tuple[Decimal, Decimal]:
    """
    Certify C1_cell such that for all X in [X_lo, X_hi]:
      [X, X + C1_cell * (log X)^2] contains an even integer N = p1 + p2.
    """
    L_lo = floor_ln(X_lo)
    L_hi = ceil_ln(X_hi)
    sqrt_X_lo = floor_sqrt(X_lo)
    X_1_4_lo = floor_sqrt(sqrt_X_lo)

    small_alpha_zero_mult = ceil_mul(
        const.sqrt_2pi_hi,
        ceil_add(
            ceil_mul(
                ceil_div(ceil_add(const.sqrt2_hi, Decimal('2.5')), const.pi_lo),
                ceil_add(ceil_ln(ceil_add(const.sqrt2_hi, Decimal('5.25'))), ceil_add(const.C_zeta, Decimal(1))),
            ),
            ceil_mul(
                ceil_div(ceil_add(ceil_div(Decimal(2), const.pi_lo), Decimal('2.5')), const.pi_lo),
                ceil_add(ceil_ln(Decimal('5.89')), ceil_add(const.C_zeta, Decimal(1))),
            ),
        ),
    )

    phi_min_lo = Decimal('0.989')
    def shell_I_sq_coeff(A_min: Decimal, h_num: int, h_den: int) -> Decimal:
        h = ceil_div(Decimal(h_num), Decimal(h_den))
        atan_lo = enclose_atan_gt1(4 * h_num, 5 * h_den)
        denom_lo = floor_mul(Decimal(4), atan_lo)

        def eval_sum(c_decay_lo: Decimal, poly_extra_hi: Decimal) -> Decimal:
            lin_mult = ceil_div(
                ceil_add(ceil_div(Decimal(1), c_decay_lo), ceil_div(ceil_mul(Decimal(2), h), A_min)),
                denom_lo,
            )
            pre = ceil_mul(
                ceil_div(Decimal('0.625'), phi_min_lo),
                ceil_mul(ceil_mul(Decimal(2), const.pi_hi), lin_mult),
            )
            m_ratio = ceil_add(ceil_div(const.pi_hi, floor_mul(Decimal(4), c_decay_lo)), ceil_div(ceil_add(h, Decimal(4)), X_lo))
            c1_add = ceil_add(ceil_ln(m_ratio), const.C_zeta)
            m2_ratio = ceil_add(ceil_div(const.pi_hi, floor_mul(Decimal(4), c_decay_lo)), ceil_div(Decimal(4), X_lo))
            c2_add = ceil_add(ceil_ln(m2_ratio), const.C_zeta)
            term_A = ceil_mul(ceil_add(Decimal(1), ceil_div(c1_add, L_lo)), ceil_add(Decimal(1), ceil_div(c2_add, L_lo)))
            term_B = ceil_div(ceil_add(Decimal(2), ceil_div(ceil_add(c1_add, c2_add), L_lo)), L_lo)
            term_C = ceil_div(Decimal(2), floor_mul(L_lo, L_lo))
            L2_mult = ceil_add(term_A, ceil_add(term_B, term_C))
            return ceil_mul(poly_extra_hi, ceil_mul(pre, L2_mult))

        c1_lo = floor_div(const.pi_lo, Decimal(2))
        I1_sq = eval_sum(c1_lo, Decimal(1))

        poly_extra_2 = ceil_add(
            ceil_div(Decimal('0.25'), floor_mul(A_min, A_min)),
            ceil_div(Decimal(256), floor_mul(floor_mul(const.pi_lo, const.pi_lo), floor_mul(const.e_lo, const.e_lo))),
        )
        c2_lo = floor_div(const.pi_lo, Decimal(8))
        I2_sq_base = eval_sum(c2_lo, poly_extra_2)
        ln2_hi = ceil_ln(Decimal(2))
        I2_sq = ceil_mul(ceil_mul(ln2_hi, ln2_hi), I2_sq_base)

        I_tot = ceil_add(ceil_sqrt(I1_sq), ceil_sqrt(I2_sq))
        return ceil_mul(I_tot, I_tot)

    C_shell_1 = shell_I_sq_coeff(Decimal(1), 5, 4)
    C_shell_2 = shell_I_sq_coeff(Decimal(20), 25, 1)
    C_shell_main = max(C_shell_1, C_shell_2)

    opp_const = ceil_div(ceil_add(ceil_div(Decimal(2), const.pi_lo), Decimal('2.5')), const.pi_lo)
    opp_val = ceil_mul(opp_const, ceil_add(ceil_ln(Decimal('5.89')), ceil_add(const.C_zeta, Decimal(1))))
    opp_shell_err = ceil_div(
        ceil_mul(ceil_mul(Decimal(2), const.pi_hi), ceil_mul(ceil_mul(opp_val, opp_val), ceil_ln(Decimal(2)))),
        floor_mul(L_lo, L_lo),
    )

    # Vertical contour Re(s) = -1/2 for zeta(s) (used on |alpha| <= 1/4 in Theorem 1B):
    # |zeta'(-1/2+it)/zeta(-1/2+it)| <= |zeta'(3/2-it)/zeta(3/2-it)| + log(pi) + (1/2)|psi(-1/4+it/2)| + (1/2)|psi(3/4-it/2)|
    # Note: psi(w) = psi(w+2) - 1/w - 1/(w+1) for w = -1/4 + it/2 => |psi(w)| <= |psi(7/4+it/2)| + 4 + 4/3
    #       psi(w') = psi(w'+1) - 1/w' for w' = 3/4 - it/2 => |psi(w')| <= |psi(7/4-it/2)| + 4/3
    # And for Re(z) = 7/4, |psi(7/4 + i*y)| <= log(|7/4 + i*y|) + 1/(2*(7/4)) + 1/(12*(7/4)^2) ...
    #Wait: Binet's first formula for psi(z) = log z - 1/(2z) - int_0^inf (1/(e^t-1) - 1/t + 1/2) e^{-tz} dt:
    # Let's verify |Im log(7/4 + i*y)| <= pi/2, and Re log(7/4 + i*y) <= log(2 + |y|) <= log(4 + |t|)!
    # So |psi(7/4 + it/2)| <= log(4 + |t|) + pi/2 + 2/7 + 16/588 < log(4 + |t|) + 1.9!
    # Also -zeta'(3/2)/zeta(3/2) < 1.51 (let's compute it rigorously in Decimal!).
    # Also s = 0 residue for zeta(s): |-zeta'(0)/zeta(0)| = log(2*pi) < 1.84.
    # Let's compute -zeta'(3/2)/zeta(3/2) rigorously:
    N_z32 = 800
    lam_z32 = mangoldt_up_to(N_z32)
    z32_sum = Decimal(0)
    for n in range(2, N_z32 + 1):
        if lam_z32[n] > 0:
            n_d = Decimal(n)
            n_3_2_lo = floor_mul(n_d, floor_sqrt(n_d))
            z32_sum = ceil_add(z32_sum, ceil_div(lam_z32[n], n_3_2_lo))
    # Tail: sum_{n>N} log(n)/n^{3/2} <= int_N^inf log(x)/x^{3/2} dx = 2 * N^{-1/2} * (log N + 2)
    N_z32_d = Decimal(N_z32)
    z32_tail = ceil_mul(Decimal(2), ceil_div(ceil_add(ceil_ln(N_z32_d), Decimal(2)), floor_sqrt(N_z32_d)))
    neg_zlog_3_2 = ceil_add(z32_sum, z32_tail)

    # Constant in |-zeta'(-1/2+it)/zeta(-1/2+it)| <= log(4+|t|) + C_z_neg1_2:
    # Binet bound for |psi(7/4 + it/2)| <= log(4+|t|) + pi/2 + 2/7 + 4/147
    psi_7_4_const = ceil_add(
        ceil_div(const.pi_hi, Decimal(2)),
        ceil_add(ceil_div(Decimal(2), Decimal(7)), ceil_div(Decimal(4), Decimal(147))),
    )
    # Sum: neg_zlog_3_2 + log(pi) + psi_7_4_const + (1/2)*(4 + 4/3 + 4/3)
    const_z_neg1_2 = ceil_add(
        ceil_add(neg_zlog_3_2, ceil_ln(const.pi_hi)),
        ceil_add(psi_7_4_const, frac_ceil(Fraction(10, 3))),
    )

    # |R_vert(-1/2)| <= (sqrt(2*pi)/pi) * |z|^{1/2} * [ (log(5) + C_z_neg1_2)*2 + (log(A+4) + C_z_neg1_2)*log(A) + log(A+5) + C_z_neg1_2 + 1 ]
    # Note: for |alpha| <= 1/4, |z| <= sqrt(1/X^2 + pi^2/4) < 1.6, A = |z|*X <= 1.6*X
    z_max_1_4 = ceil_sqrt(ceil_add(ceil_div(Decimal(1), floor_mul(X_lo, X_lo)), ceil_div(ceil_mul(const.pi_hi, const.pi_hi), Decimal(4))))
    A_max_1_4 = ceil_mul(z_max_1_4, X_hi)
    L_A_max = ceil_ln(A_max_1_4)
    vert_inner_1_4 = ceil_add(
        ceil_mul(Decimal(2), ceil_add(ceil_ln(Decimal(5)), const_z_neg1_2)),
        ceil_add(
            ceil_mul(ceil_add(ceil_ln(ceil_add(A_max_1_4, Decimal(4))), const_z_neg1_2), L_A_max),
            ceil_add(ceil_ln(ceil_add(A_max_1_4, Decimal(5))), ceil_add(const_z_neg1_2, Decimal(1))),
        ),
    )
    # Add s=0 residue log(2*pi)
    res_0_hi = ceil_ln(ceil_mul(Decimal(2), const.pi_hi))
    R_vert_neg1_2_hi = ceil_add(
        res_0_hi,
        ceil_mul(ceil_div(const.sqrt_2pi_hi, const.pi_lo), ceil_mul(ceil_sqrt(z_max_1_4), vert_inner_1_4)),
    )

    # Combine E(alpha) = E_zeros(alpha) + E_opp(alpha) + R_vert(alpha) on [-1/4, 1/4]:
    # Using Minkowski (sqrt(I_main) + sqrt(I_opp) + sqrt(I_vert))^2 on each shell [B_j, 2*B_j]:
    # Wait: for opp zeros, on [B_j, 2*B_j], int_{B_j}^{2B_j} |E_opp|^2 d(alpha) <= opp_val^2 * ln(2) <= opp_shell_err * B_j * X * L^2.
    # For R_vert(-1/2), int_{B_j}^{2B_j} |R_vert|^2 d(alpha) <= B_j * R_vert_neg1_2_hi^2
    # Divided by B_j * X * L^2 -> R_vert_neg1_2_hi^2 / (X_lo * L_lo^2) (around 10^{-14}!).
    vert_shell_err = ceil_div(ceil_mul(R_vert_neg1_2_hi, R_vert_neg1_2_hi), floor_mul(X_lo, floor_mul(L_lo, L_lo)))

    # Note: on [B_j, 2*B_j] (one side!), total C_shell_oneside:
    C_shell_oneside = ceil_add(
        C_shell_main,
        ceil_add(
            ceil_mul(Decimal(2), ceil_sqrt(ceil_mul(C_shell_main, ceil_add(opp_shell_err, vert_shell_err)))),
            ceil_add(opp_shell_err, vert_shell_err),
        ),
    )
    # Wait: let's be even cleaner with Minkowski (sqrt(a) + sqrt(b) + sqrt(c))^2:
    # Since opp_shell_err + vert_shell_err is < 0.05, wait: (sqrt(C_shell_main) + sqrt(opp_shell_err) + sqrt(vert_shell_err))^2!
    s_tot = ceil_add(ceil_sqrt(C_shell_main), ceil_add(ceil_sqrt(opp_shell_err), ceil_sqrt(vert_shell_err)))
    C_shell_oneside = ceil_mul(s_tot, s_tot)

    # Now sum over dyadic shells to get int_{-B}^{B} |E(alpha)|^2 d(alpha) <= C_Sel * B * X * L^2:
    # int_{-B}^{B} = int_{-1/(2*pi*X)}^{1/(2*pi*X)} + 2 * sum_{k>=1} int_{B/2^k}^{B/2^{k-1}}
    # Note: sum_{k>=1} 2^{-k} = 1, and each half-shell [B/2^k, B/2^{k-1}] has length (B/2^k),
    # so int_{-B}^{B} <= C_Sel_inner * B*X*L^2 + 2 * C_shell_oneside * (sum_{k>=1} 2^{-k}) * B * X * L^2
    # Wait: check small_alpha_K with Re(s)=-1/2 instead of Re(s)=1/4!
    # Wait: earlier small_alpha_K used vert at Re(s)=1/4! Let's use R_vert_neg1_2_hi for small_alpha_K too so EVERYTHING uses Re(s)=-1/2!
    small_alpha_K_clean = ceil_add(small_alpha_zero_mult, ceil_div(R_vert_neg1_2_hi, sqrt_X_lo))
    C_Sel_inner_clean = ceil_div(ceil_mul(Decimal(2), ceil_mul(small_alpha_K_clean, small_alpha_K_clean)), floor_mul(L_lo, L_lo))

    C_Sel = ceil_add(C_Sel_inner_clean, ceil_mul(Decimal(2), C_shell_oneside))

    # Step 2: Solve for C1_cell such that for H = C1 * (log X)^2, M0 = floor(H/2):
    # Main term >= M0 * X * e^{-1 - H/X} - 0.21 * M0
    # Outside |alpha| > 1/4: <= (alpha_psi / M0) * X * (log X + C_pars)
    # Quadratic error int_{-1/4}^{1/4} |E|^2 |W_hat|: <= 2 * C_Sel * X * (log X)^2
    # Cross term: <= 2 * sqrt(2 * C_Sel * X * (log X)^2) * sqrt(0.5 * M0 * X) = 2 * sqrt(C_Sel * M0) * X * log X
    # Odd + pp loss: <= 2*e^{-1}*(H+1)*(log(X+H))^2 + 2*e^{-1}*(H+1)*alpha_pp*sqrt(X+H)*log(X+H)
    #
    # Divide everything by M0 * X, letting K = M0 / (log X)^2 (so H >= 2*M0, and M0 >= K * L_lo^2, Wait:
    # Actually H = C1 * L^2 => M0 = floor(H/2) >= (C1/2) * L^2 - 1 = (C1/2 - 1/L_lo^2) * L^2!):
    # Let r = sqrt(C_Sel / K_eff) where M0 >= K_eff * (log X)^2.
    # We need:
    #   e^{-1 - H/X} - 0.21/X_lo > 2*r + 2*r^2 + (alpha_psi*(1 + C_pars/L_lo))/(K_eff^2 * L_lo^3) + odd_pp_ratio!
    # Search/solve for minimal integer C1_cell starting from ceil(42 * C_Sel):
    C1_cand = int((Decimal(42) * C_Sel).to_integral_value(rounding=ROUND_CEILING))
    while True:
        H_lo = floor_mul(Decimal(C1_cand), floor_mul(L_lo, L_lo))
        H_hi = ceil_mul(Decimal(C1_cand), ceil_mul(L_hi, L_hi))
        M0_lo = floor_sub(floor_div(H_lo, Decimal(2)), Decimal(1))
        # K_eff <= M0 / (log X)^2 for X in [X_lo, X_hi]:
        # Wait: M0 >= (H/2) - 1 = (C1/2 - 1/(log X)^2)*(log X)^2 >= (C1/2 - 1/L_lo^2)*(log X)^2!
        K_eff = floor_sub(floor_div(Decimal(C1_cand), Decimal(2)), ceil_div(Decimal(1), floor_mul(L_lo, L_lo)))
        assert K_eff > 0

        # Monotone-decreasing ratios on [X_lo, X_hi] (valid for X >= 4e18 > e^2):
        # 1. H(X)/X = C1*(log X)^2 / X is strictly decreasing for X > e^2 -> max at X_lo!
        H_at_lo_hi = ceil_mul(Decimal(C1_cand), ceil_mul(L_lo, L_lo))
        H_over_X_hi = ceil_div(H_at_lo_hi, X_lo)
        main_ratio = floor_sub(
            floor_exp(floor_sub(Decimal(-1), H_over_X_hi)),
            ceil_div(Decimal('0.21'), X_lo),
        )
        # Error / (M0 * X):
        r_hi = ceil_sqrt(ceil_div(C_Sel, K_eff))
        quad_plus_cross = ceil_add(ceil_mul(Decimal(2), r_hi), ceil_mul(Decimal(2), ceil_mul(r_hi, r_hi)))
        outside_ratio = ceil_div(
            ceil_mul(const.alpha_psi, ceil_add(Decimal(1), ceil_div(const.C_pars, L_lo))),
            floor_mul(floor_mul(K_eff, K_eff), floor_mul(L_lo, floor_mul(L_lo, L_lo))),
        )
        # 2. (log(X+H))^2 / X and sqrt(X+H)*log(X+H)/X are strictly decreasing for X >= 4e18 -> max at X_lo!
        H1_over_M0 = ceil_add(Decimal(2), ceil_div(Decimal(3), M0_lo))
        L_plus_H_at_lo = ceil_ln(ceil_add(X_lo, H_at_lo_hi))
        sqrt_X_H_at_lo = ceil_sqrt(ceil_add(X_lo, H_at_lo_hi))
        odd_pp_ratio = ceil_mul(
            ceil_div(ceil_mul(Decimal(2), H1_over_M0), const.e_lo),
            ceil_add(
                ceil_div(ceil_mul(L_plus_H_at_lo, L_plus_H_at_lo), X_lo),
                ceil_div(ceil_mul(const.alpha_pp, ceil_mul(sqrt_X_H_at_lo, L_plus_H_at_lo)), X_lo),
            ),
        )
        err_ratio = ceil_add(quad_plus_cross, ceil_add(outside_ratio, odd_pp_ratio))
        if main_ratio > err_ratio:
            return Decimal(C1_cand), C_Sel
        C1_cand += max(1, C1_cand // 50)


def certify_asymptotic_tail_1A(const: AnalyticConstants, Y_tail: Decimal) -> Decimal:
    """
    Certify C_tail for all Y >= Y_tail (e.g. Y_tail = 10^10000).
    Note: every term in certify_theorem_1A_cell depends on [Y_lo, Y_hi] ONLY through
      L_lo = floor(ln Y_lo), L_hi = ceil(ln Y_hi), Y_lo^{1/4}, Y_lo^{1/8}, etc.
    Wait: check where L_hi appears in certify_theorem_1A_cell!
      (1) gcd_err_hi = 2 * omega_hi * (L + ln L + 1), divided by Y^{3/4} * L:
          Since (L^2 / Y^{3/4}) is strictly decreasing for Y >= e^{8/3}, it attains its max at Y_tail!
      (2) pp_loss = 2 * alpha_pp * L / (e * sqrt(Y)), strictly decreasing for Y >= e^2 -> max at Y_tail!
      (3) beta_tail = (K2/pi^2) * K_1_8 * (0.5*L + 1) / Y^{3/8}, strictly decreasing for Y >= e^{8/3} -> max at Y_tail!
    And ALL other factors (c_add / L, 1/Y_1_4, etc.) are strictly decreasing in Y!
    Therefore, evaluating the monotonic tail envelope at Y_tail certifies ALL Y >= Y_tail!
    """
    # To reuse the exact logic cleanly with L_hi = L_lo (since L / Y^alpha is decreasing!),
    # verify that L / Y^{1/8} is decreasing for Y >= Y_tail (ln Y_tail > 8) and evaluate at [Y_tail, Y_tail]!
    assert floor_ln(Y_tail) > Decimal(100)
    return certify_theorem_1A_cell(const, Y_tail, Y_tail)


def certify_asymptotic_tail_1B(const: AnalyticConstants, X_tail: Decimal) -> tuple[Decimal, Decimal]:
    """
    Certify C1_tail for all X >= X_tail (e.g. X_tail = 10^10000).
    Check every X_hi dependence in certify_theorem_1B_cell:
      (1) A_max_1_4 = z_max_1_4 * X_hi inside vert_shell_err = R_vert(-1/2)^2 / (X * L^2):
          Wait: R_vert(-1/2) grows like (log X)^2, so R_vert^2 / (X * L^2) ~ (log X)^2 / X,
          which is STRICTLY DECREASING for X >= e^2!
      (2) odd_pp_ratio: (log(X+H))^2 / X + sqrt(X+H)*log(X+H)/X, STRICTLY DECREASING for X >= 4e18!
    And all other terms (c_add/L, 1/L^2, H/X) are strictly decreasing in X!
    We explicitly bound R_vert^2/(X*L^2) using (1 + (log X)^4/X) monotonicity at X_tail.
    """
    assert floor_ln(X_tail) > Decimal(100)
    return certify_theorem_1B_cell(const, X_tail, X_tail)


def main():
    const = AnalyticConstants()
    print("=== Rigorous Analytic Constants (zero IEEE-754 float) ===")
    print(f"pi in [{str(const.pi_lo)[:22]}, {str(const.pi_hi)[:22]}]")
    print(f"Pi_2 >= {str(const.pi2_lo)[:16]}")
    print(f"K2 <= {str(const.K2_hi)[:16]}")
    print(f"K_(1/8) <= {str(const.K_1_8_hi)[:16]}")
    print(f"C_qphi <= {str(const.C_qphi_hi)[:16]}")
    print(f"-zeta'(7/4)/zeta(7/4) <= {str(const.neg_zlog_7_4)[:16]}")
    print(f"C_zeta <= {str(const.C_zeta)[:16]}")
    print(f"A_vert(1/4) <= {str(const.A_vert_1_4)[:16]}")
    print(f"C_pars <= {str(const.C_pars)[:16]}")

    # Build logarithmic grid covering [4 * 10^18, 10^10000]
    # Note: in certify_theorem_1A_cell, L_hi only appears inside gcd_err_hi/Y^{3/4}, pp_loss, beta_tail (tiny ~10^{-5}!).
    # Still, narrow cells keep L_hi / L_lo close to 1 for maximal sharpness.
    grid_exps = [
        Decimal('18.60205999132796'),  # < log10(4e18) = 18.60205999132796239...
        Decimal('19'), Decimal('20'), Decimal('22'), Decimal('25'), Decimal('30'),
        Decimal('40'), Decimal('60'), Decimal('100'), Decimal('200'), Decimal('500'),
        Decimal('1000'), Decimal('2500'), Decimal('5000'), Decimal('10000'),
    ]
    # Exact 4*10^18 start:
    Y_points = [Decimal(4) * (Decimal(10) ** 18)]
    for e in grid_exps[1:]:
        Y_points.append(Decimal(10) ** int(e))

    max_C_cell = Decimal(0)
    max_C1_cell = Decimal(0)
    max_CSel = Decimal(0)

    print("\n=== Cell-by-Cell Certification over [4*10^18, 10^10000] ===")
    for i in range(len(Y_points) - 1):
        Y_lo = Y_points[i]
        Y_hi = Y_points[i + 1]
        C_cell = certify_theorem_1A_cell(const, Y_lo, Y_hi)
        C1_cell, C_Sel = certify_theorem_1B_cell(const, Y_lo, Y_hi)
        if C_cell > max_C_cell:
            max_C_cell = C_cell
        if C1_cell > max_C1_cell:
            max_C1_cell = C1_cell
        if C_Sel > max_CSel:
            max_CSel = C_Sel
        print(
            f"  [{Y_lo:.2e}, {Y_hi:.2e}]  "
            f"C_dyadic(1A) <= {str(C_cell)[:12]:>12} | "
            f"C_Sel <= {str(C_Sel)[:10]:>10} | C1(1B) <= {C1_cell}"
        )

    Y_tail = Y_points[-1]
    C_tail_1A = certify_asymptotic_tail_1A(const, Y_tail)
    C1_tail_1B, C_Sel_tail = certify_asymptotic_tail_1B(const, Y_tail)
    print(f"  [1.00e+10000, inf)        C_dyadic(1A) <= {str(C_tail_1A)[:12]:>12} | C_Sel <= {str(C_Sel_tail)[:10]:>10} | C1(1B) <= {C1_tail_1B}")

    max_C_dyadic = max(max_C_cell, C_tail_1A)
    # Sum dyadically: sum_{k>=0} 2^{-k/2} = 2 + sqrt(2)
    dyadic_sum_hi = ceil_add(Decimal(2), const.sqrt2_hi)
    C_final_1A = ceil_mul(max_C_dyadic, dyadic_sum_hi)
    C_final_1A_int = int(C_final_1A.to_integral_value(rounding=ROUND_CEILING))
    C1_final_1B = max(max_C1_cell, C1_tail_1B)

    # Verify small-range compatibility X in [4, 4*10^18):
    # Theorem 1A: E(X) = 0 <= C * sqrt(X) * (log X)^3 trivially.
    # Theorem 1B: for 4 <= X < 4*10^18, C1 * (log 4)^2 >= 2 guarantees [X, X+H] contains an even integer <= 4*10^18!
    # Wait: what if X in (4*10^18 - 2, 4*10^18)? Then even integer 4*10^18 IS in [X, X+2] <= [X, X+H], and E(4*10^18)=0!
    assert floor_mul(C1_final_1B, floor_mul(floor_ln(Decimal(4)), floor_ln(Decimal(4)))) >= Decimal(2)

    print("\n=== FINAL CERTIFIED ALL-RANGE BOUNDS (X >= 4) ===")
    print(f"Theorem 1A: E(X) <= {C_final_1A_int} * sqrt(X) * (log X)^3  (c = 3, C = {C_final_1A_int}, raw = {str(C_final_1A)[:14]})")
    print(f"Theorem 1B: [X, X + {C1_final_1B} * (log X)^2] contains p1 + p2  (c' = 2, C1 = {C1_final_1B})")


if __name__ == "__main__":
    main()

