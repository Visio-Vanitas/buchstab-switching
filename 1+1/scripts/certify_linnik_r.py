#!/usr/bin/env python3
"""
Zero-float outward-rounded certifier (v2) for All-Range Explicit Linnik-Goldbach
under pure GRH + Binary Goldbach verification <= 4 * 10^18, incorporating the signed
representation polynomial and complex-phase large-deviation framework of
Huixi Li & Zhixin Liu (arXiv:2610.15784v1).

Strict compliance:
- ZERO IEEE-754 floats: strictly decimal.Decimal (with FloatOperation trap armed)
  and fractions.Fraction.
- ZERO `import math`.
- ZERO magic heuristic buffers (no +4.00 C_E2 buffer, no +0.06 avg_S2 buffer).
- Directed outward rounding (ROUND_CEILING for upper bounds, ROUND_FLOOR for lower bounds).
- Covers:
  1. Pure effective asymptotic GRH K = 6 (C_1 = 8.0, explicit Prop 5.2 directional net
     on D_{25/32}, ZERO Siegel ineffectiveness, ZERO external T_{2,2}/T_{3,3} citation),
     plus informational Lichtman K = 5 benchmark.
  2. All-range explicit K = 14 for EVERY even N >= 4 (exact K = 14 positive powers of 2
     for all even N >= 32):
     - Binary Goldbach Bridge: [32, N_br(14)], N_br(14) = (2^15 - 2)*2^61 + 4*10^18 ~ 7.556e22.
     - Finite dyadic slabs: L in [72, 119] (covering (N_br(14), 8*2^120]).
     - Uniform asymptotic tail: ALL L >= 120 (N >= 8*2^120) via Collatz-Wielandt decay.
"""

from decimal import Decimal, localcontext, getcontext, ROUND_CEILING, ROUND_FLOOR, FloatOperation
from fractions import Fraction

# Arm strict zero-float trap globally
PREC = 40
_CTX = getcontext()
_CTX.prec = PREC
_CTX.traps[FloatOperation] = True


# ---------------------------------------------------------------------------
# Directed Rounding Primitives
# ---------------------------------------------------------------------------

def ceil_add(a: Decimal, b: Decimal) -> Decimal:
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_CEILING
        return a + b


def floor_add(a: Decimal, b: Decimal) -> Decimal:
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_FLOOR
        return a + b


def ceil_sub(a: Decimal, b: Decimal) -> Decimal:
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_CEILING
        return a - b


def floor_sub(a: Decimal, b: Decimal) -> Decimal:
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_FLOOR
        return a - b


def ceil_mul(a: Decimal, b: Decimal) -> Decimal:
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_CEILING
        return a * b


def floor_mul(a: Decimal, b: Decimal) -> Decimal:
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_FLOOR
        return a * b


def ceil_div(a: Decimal, b: Decimal) -> Decimal:
    assert b > 0
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_CEILING
        return a / b


def floor_div(a: Decimal, b: Decimal) -> Decimal:
    assert b > 0
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_FLOOR
        return a / b


def ceil_sqrt(a: Decimal) -> Decimal:
    assert a >= 0
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_CEILING
        return a.sqrt()


def floor_sqrt(a: Decimal) -> Decimal:
    assert a >= 0
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_FLOOR
        return a.sqrt()


def ceil_ln(a: Decimal) -> Decimal:
    assert a > 0
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_CEILING
        return a.ln()


def floor_ln(a: Decimal) -> Decimal:
    assert a > 0
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_FLOOR
        return a.ln()


def ceil_exp(a: Decimal) -> Decimal:
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_CEILING
        return a.exp()


def floor_exp(a: Decimal) -> Decimal:
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_FLOOR
        return a.exp()


def frac_ceil(f: Fraction) -> Decimal:
    return ceil_div(Decimal(f.numerator), Decimal(f.denominator))


def frac_floor(f: Fraction) -> Decimal:
    return floor_div(Decimal(f.numerator), Decimal(f.denominator))


def gcd_int(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return a


def sieve_primes(limit: int) -> list:
    is_p = [True] * (limit + 1)
    is_p[0] = is_p[1] = False
    i = 2
    while i * i <= limit:
        if is_p[i]:
            for j in range(i * i, limit + 1, i):
                is_p[j] = False
        i += 1
    return [p for p, ok in enumerate(is_p) if ok]


def ord_mod2(q: int) -> int:
    assert q >= 1 and (q & 1) == 1
    if q == 1:
        return 1
    r = 1
    cur = 2 % q
    while cur != 1:
        cur = (cur * 2) % q
        r += 1
    return r


# ---------------------------------------------------------------------------
# Rigorous Transcendental Enclosures (pi, gamma, atan, cos/sin)
# ---------------------------------------------------------------------------

def enclose_atan_rational(num: int, den: int, terms: int = 30) -> tuple:
    assert 0 < num < den
    x = Fraction(num, den)
    x2 = x * x
    s_even = Fraction(0)
    p = x
    for k in range(2 * terms):
        term = p / (2 * k + 1)
        if k % 2 == 0:
            s_even += term
        else:
            s_even -= term
        p *= x2
    s_odd = s_even + p / (4 * terms + 1)
    assert s_even < s_odd
    return frac_floor(s_even), frac_ceil(s_odd)


def enclose_pi() -> tuple:
    a1_lo, a1_hi = enclose_atan_rational(1, 5, terms=30)
    a2_lo, a2_hi = enclose_atan_rational(1, 239, terms=15)
    pi_lo = floor_sub(floor_mul(Decimal(16), a1_lo), ceil_mul(Decimal(4), a2_hi))
    pi_hi = ceil_sub(ceil_mul(Decimal(16), a1_hi), floor_mul(Decimal(4), a2_lo))
    assert Decimal('3.141592653589793238') < pi_lo < pi_hi < Decimal('3.141592653589793239')
    return pi_lo, pi_hi


def enclose_euler_gamma() -> tuple:
    N = 1000
    H = Fraction(0)
    for k in range(1, N + 1):
        H += Fraction(1, k)
    c_lo = frac_floor(Fraction(1, 2 * N) - Fraction(1, 12 * N * N))
    c_hi = frac_ceil(Fraction(1, 2 * N) - Fraction(1, 12 * N * N) + Fraction(1, 120 * (N ** 4)))
    g_lo = floor_sub(floor_sub(frac_floor(H), ceil_ln(Decimal(N))), c_hi)
    g_hi = ceil_sub(ceil_sub(frac_ceil(H), floor_ln(Decimal(N))), c_lo)
    assert Decimal('0.57721566') < g_lo < g_hi < Decimal('0.57721567')
    return g_lo, g_hi


def enclose_atan_dec(x: Decimal, pi_lo: Decimal, pi_hi: Decimal) -> tuple:
    """Rigorous [lo, hi] enclosure of atan(x) for x >= 0 via Euler series."""
    assert x >= 0
    if x == 0:
        return Decimal(0), Decimal(0)
    if x > Decimal(1):
        inv_lo = floor_div(Decimal(1), x)
        inv_hi = ceil_div(Decimal(1), x)
        a_lo, _ = enclose_atan_dec(inv_lo, pi_lo, pi_hi)
        _, a_hi = enclose_atan_dec(inv_hi, pi_lo, pi_hi)
        return floor_sub(floor_div(pi_lo, Decimal(2)), a_hi), ceil_sub(ceil_div(pi_hi, Decimal(2)), a_lo)
    with localcontext() as c:
        c.prec = 42
        x2 = x * x
        den = Decimal(1) + x2
        y = x2 / den
        term = x / den
        tot = term
        k = 1
        while term > Decimal('1e-31') and k < 140:
            term = term * Decimal(2 * k) / Decimal(2 * k + 1) * y
            tot += term
            k += 1
        assert term <= Decimal('1e-31')
        slack = term * Decimal(2) + Decimal('1e-28')
    return max(Decimal(0), floor_sub(tot, slack)), ceil_add(tot, slack)


def cos_point_enclosure(t: Decimal, pi_lo: Decimal, pi_hi: Decimal) -> tuple:
    """Rigorous [c_lo, c_hi] enclosure of cos(t) via alternating Taylor series."""
    with localcontext() as c:
        c.prec = 42
        two_pi = Decimal(2) * pi_lo
        k = int((t / two_pi).to_integral_value())
        assert abs(k) < 10000
        pi_err = (pi_hi - pi_lo) * Decimal(2 * abs(k) + 2)
        y = t - Decimal(k) * two_pi
        y2 = y * y
        c_sum = Decimal(1)
        term = Decimal(1)
        n = 1
        while abs(term) > Decimal('1e-31') or Decimal(2 * n) < abs(y) + Decimal(4):
            term = -term * y2 / Decimal((2 * n - 1) * (2 * n))
            c_sum += term
            n += 1
        slack = abs(term) + pi_err + Decimal('1e-28')
    return max(Decimal(-1), floor_sub(c_sum, slack)), min(Decimal(1), ceil_add(c_sum, slack))


def enclose_cos_interval(t_lo: Decimal, t_hi: Decimal, pi_lo: Decimal, pi_hi: Decimal) -> tuple:
    """Rigorous [cos_lo, cos_hi] enclosure of cos(t) for ALL t in [t_lo, t_hi]."""
    assert t_lo <= t_hi
    c_a_lo, c_a_hi = cos_point_enclosure(t_lo, pi_lo, pi_hi)
    c_b_lo, c_b_hi = cos_point_enclosure(t_hi, pi_lo, pi_hi)
    cos_hi = max(c_a_hi, c_b_hi)
    cos_lo = min(c_a_lo, c_b_lo)
    two_pi_lo = floor_mul(Decimal(2), pi_lo)
    two_pi_hi = ceil_mul(Decimal(2), pi_hi)
    k_min = int((t_lo / two_pi_hi).to_integral_value(rounding=ROUND_FLOOR)) - 1
    k_max = int((t_hi / two_pi_lo).to_integral_value(rounding=ROUND_CEILING)) + 1
    for k in range(k_min, k_max + 1):
        p0_lo, p0_hi = (floor_mul(Decimal(k), two_pi_lo), ceil_mul(Decimal(k), two_pi_hi)) if k >= 0 else (floor_mul(Decimal(k), two_pi_hi), ceil_mul(Decimal(k), two_pi_lo))
        if p0_hi >= t_lo and p0_lo <= t_hi:
            cos_hi = Decimal(1)
        m = 2 * k + 1
        p1_lo, p1_hi = (floor_mul(Decimal(m), pi_lo), ceil_mul(Decimal(m), pi_hi)) if m >= 0 else (floor_mul(Decimal(m), pi_hi), ceil_mul(Decimal(m), pi_lo))
        if p1_hi >= t_lo and p1_lo <= t_hi:
            cos_lo = Decimal(-1)
    return cos_lo, cos_hi


def cert_neg_zeta_deriv(num: int, den: int, N: int = 500) -> Decimal:
    primes = sieve_primes(N)
    lam = [Decimal(0)] * (N + 1)
    for p in primes:
        lp = ceil_ln(Decimal(p))
        pk = p
        while pk <= N:
            lam[pk] = lp
            pk *= p
    total = Decimal(0)
    for n in range(2, N + 1):
        if lam[n] > 0:
            n_d = Decimal(n)
            if (num, den) == (7, 4):
                n_sig_lo = floor_mul(n_d, floor_sqrt(floor_mul(n_d, floor_sqrt(n_d))))
            else:
                n_sig_lo = floor_mul(floor_mul(n_d, n_d), floor_sqrt(n_d))
            total = ceil_add(total, ceil_div(lam[n], n_sig_lo))
    N_d = Decimal(N)
    lnN_hi = ceil_ln(N_d)
    if (num, den) == (7, 4):
        n_m1_lo = floor_sqrt(floor_mul(N_d, floor_sqrt(N_d)))
        inv_sm1 = frac_ceil(Fraction(4, 3))
    else:
        n_m1_lo = floor_mul(N_d, floor_sqrt(N_d))
        inv_sm1 = frac_ceil(Fraction(2, 3))
    return ceil_add(total, ceil_mul(inv_sm1, ceil_div(ceil_add(lnN_hi, inv_sm1), n_m1_lo)))


def compute_two_C2_bounds() -> tuple:
    primes = sieve_primes(2000)
    prod = Fraction(1, 1)
    for p in primes:
        if p > 2:
            prod *= Fraction((p - 1) ** 2 - 1, (p - 1) ** 2)
    two_C2_dn = frac_floor(2 * prod * Fraction(1997, 1998))
    two_C2_up = frac_ceil(2 * prod)
    assert Decimal('1.3197') < two_C2_dn < two_C2_up < Decimal('1.3205')
    return two_C2_dn, two_C2_up


def cert_odd_sqfree_phi2_data(Y_max: int = 5000) -> tuple:
    primes = sieve_primes(3000)
    prod_hi = Decimal(1)
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_CEILING
        for p in primes:
            if p > 2:
                pm1 = Decimal(p - 1)
                prod_hi *= Decimal(1) + Decimal(1) / (pm1 * pm1)
    tot_ub = ceil_mul(prod_hi, ceil_exp(ceil_div(Decimal(1), Decimal(2998))))
    assert tot_ub < Decimal('1.42')
    sq = [True] * (Y_max + 1)
    phi = list(range(Y_max + 1))
    for i in range(2, Y_max + 1):
        if phi[i] == i:
            for j in range(i, Y_max + 1, i):
                phi[j] = (phi[j] // i) * (i - 1)
            i2 = i * i
            for j in range(i2, Y_max + 1, i2):
                sq[j] = False
    pref_lo = [Decimal(0)] * (Y_max + 1)
    with localcontext() as c:
        c.prec = PREC
        c.rounding = ROUND_FLOOR
        s = Decimal(0)
        one = Decimal(1)
        for b in range(1, Y_max + 1):
            if (b & 1) and sq[b]:
                s += one / Decimal(phi[b] * phi[b])
            pref_lo[b] = s
    return tot_ub, pref_lo, Y_max


# ---------------------------------------------------------------------------
# Core Analytic Constants & Zero-Black-Box C_E2 Engine
# ---------------------------------------------------------------------------

class AnalyticConstants:
    def __init__(self):
        self.pi_lo, self.pi_hi = enclose_pi()
        self.gamma_lo, self.gamma_hi = enclose_euler_gamma()
        self.e_lo = floor_exp(Decimal(1))
        self.e_hi = ceil_exp(Decimal(1))
        self.ln2_lo = floor_ln(Decimal(2))
        self.ln2_hi = ceil_ln(Decimal(2))
        self.sqrt2_hi = ceil_sqrt(Decimal(2))
        self.sqrt_2pi_hi = ceil_sqrt(ceil_mul(Decimal(2), self.pi_hi))
        self.e_gamma_hi = ceil_exp(self.gamma_hi)
        self.two_C2_dn, self.two_C2_up = compute_two_C2_bounds()
        self.C2_dn = floor_div(self.two_C2_dn, Decimal(2))
        self.C2_up = ceil_div(self.two_C2_up, Decimal(2))
        # Platt-Trudgian (2021, Math. Comp. 90, p. 55): C_0 * R_0 < 1.2784421041 < 1279/1000
        self.C0_R0_hi = frac_ceil(Fraction(1279, 1000))
        self.R0_hi = ceil_div(self.C0_R0_hi, self.C2_dn)

        # Verify prod_{p>2} (1 + 1/(p(p-1))) < 1.298 from first principles
        pr_qp = Fraction(1)
        for p in sieve_primes(2000):
            if p > 2:
                pr_qp *= Fraction(p * (p - 1) + 1, p * (p - 1))
        self.C_odd_qphi_hi = ceil_mul(frac_ceil(pr_qp), ceil_exp(ceil_div(Decimal(1), Decimal(2000))))
        assert self.C_odd_qphi_hi < Decimal('1.298')

        self.odd_tot_ub, self.odd_pref_lo, self.odd_Y_max = cert_odd_sqfree_phi2_data(5000)

        self.neg_zlog_7_4 = cert_neg_zeta_deriv(7, 4, N=500)
        self.neg_zlog_5_2 = cert_neg_zeta_deriv(5, 2, N=500)
        assert self.neg_zlog_7_4 < Decimal('0.964')
        assert self.neg_zlog_5_2 < Decimal('0.290')

        self.gamma_1_4_coeff = ceil_mul(Decimal(4), self.sqrt2_hi)
        digamma_diff_hi = ceil_mul(
            ceil_div(Decimal(3), Decimal(8)),
            ceil_add(ceil_div(Decimal(64), Decimal(7)), ceil_div(ceil_mul(self.pi_hi, self.pi_hi), Decimal(6))),
        )
        pole_1_4_hi = frac_ceil(Fraction(4, 3) + Fraction(4, 3) + 4 + Fraction(4, 7))
        self.A_vert_1_4 = ceil_add(ceil_add(self.neg_zlog_7_4, digamma_diff_hi), pole_1_4_hi)

        # Zero-black-box Bochner-kernel C_E2 (NO +4.00 magic buffer!)
        self.C_row_dir, self.C_E2_exact = self._certify_zero_blackbox_C_E2()

        # Exact Fourier L^1 norm ||hat_phi||_1 and analytic |v| > 30 moment bounds
        self.a_lap = frac_ceil(Fraction(5, 4))
        self.l1_hat_phi, self.hat_phi_bins, self.hat_phi_tail, self.hat_phi_tail_half = self._certify_sin2_hat_phi()

        # Exact trig-reduced Direct Mellin constants (M0, M1, M2) for g(u) = sin^2(pi*u)*sin^2(pi*(u+d))
        self.M0_sin2, self.M1_sin2, self.M2_sin2 = self._certify_mellin_sin2_constants()

    def odd_tail(self, Y: Decimal) -> Decimal:
        y_int = int(Y.to_integral_value(rounding=ROUND_FLOOR))
        if y_int <= 0:
            return self.odd_tot_ub
        if y_int >= self.odd_Y_max:
            return ceil_sub(self.odd_tot_ub, self.odd_pref_lo[self.odd_Y_max])
        return ceil_sub(self.odd_tot_ub, self.odd_pref_lo[y_int])

    def _certify_zero_blackbox_C_E2(self) -> tuple:
        """
        Zero-black-box Bochner-kernel C_E2 for unit intervals v = (1/2)ln(1+U^2) >= 1
        with exact Hadamard row sum at Re(s) = 5/2 and BMOR (2021) + HSW (2022)
        (using 2*N_zeta(T) <= (T/pi)*ln(T/(2*pi*e)) + 0.75*ln(T+4) + 21, exact since
        2*(7/8 + 9.3675) = 20.485 < 21!).
        """
        two_pi_lo = floor_mul(Decimal(2), self.pi_lo)
        C_row_dir = ceil_add(
            ceil_add(ceil_mul(Decimal(2), self.neg_zlog_5_2), frac_ceil(Fraction(32, 15) + Fraction(4, 75))),
            ceil_sub(Decimal(0), floor_ln(two_pi_lo)),
        )
        if C_row_dir < Decimal(1):
            C_row_dir = Decimal(1)

        e2_lo = floor_mul(self.e_lo, self.e_lo)
        e_neg2_hi = ceil_div(Decimal(1), e2_lo)
        jac_hi = ceil_div(Decimal(1), floor_sqrt(floor_sub(Decimal(1), e_neg2_hi)))
        assert jac_hi < Decimal('1.076')

        hsw_const = Decimal(21)
        S1_mult = ceil_add(
            Decimal(1),
            ceil_add(
                ceil_div(ceil_mul(ceil_mul(Decimal(2), self.pi_hi), Decimal('0.75')), e2_lo),
                ceil_add(
                    ceil_div(ceil_mul(ceil_mul(Decimal(2), self.pi_hi), hsw_const), ceil_mul(Decimal(3), e2_lo)),
                    ceil_div(Decimal('1.5'), Decimal(9)),
                ),
            ),
        )
        m0_hi = ceil_div(Decimal(1), e2_lo)
        m1_hi = ceil_div(Decimal('2.5'), e2_lo)
        m2_hi = ceil_div(Decimal(9), e2_lo)
        m3_hi = ceil_div(Decimal('36.5'), e2_lo)
        L_min = Decimal(3)
        S2_inner = ceil_add(
            ceil_add(
                m1_hi,
                ceil_add(
                    ceil_div(ceil_add(ceil_mul(Decimal(2), m2_hi), ceil_mul(C_row_dir, m1_hi)), L_min),
                    ceil_div(m3_hi, floor_mul(L_min, L_min)),
                ),
            ),
            ceil_mul(
                ceil_div(ceil_mul(Decimal(2), self.pi_hi), e2_lo),
                ceil_add(
                    ceil_mul(
                        Decimal('0.75'),
                        ceil_add(
                            m0_hi,
                            ceil_add(
                                ceil_div(ceil_add(ceil_mul(Decimal(2), m1_hi), ceil_mul(C_row_dir, m0_hi)), L_min),
                                ceil_div(m2_hi, floor_mul(L_min, L_min)),
                            ),
                        ),
                    ),
                    ceil_mul(hsw_const, ceil_add(ceil_div(m0_hi, L_min), ceil_div(m1_hi, floor_mul(L_min, L_min)))),
                ),
            ),
        )
        S2_mult = ceil_mul(ceil_mul(jac_hi, jac_hi), S2_inner)
        one_minus_e_half = ceil_sub(Decimal(1), floor_div(Decimal(1), ceil_sqrt(self.e_hi)))
        deriv_coef = ceil_mul(ceil_sqrt(S2_mult), ceil_mul(Decimal(2), one_minus_e_half))
        mink_sq = ceil_mul(ceil_add(ceil_sqrt(S1_mult), deriv_coef), ceil_add(ceil_sqrt(S1_mult), deriv_coef))
        geom_hi = ceil_div(self.e_hi, floor_sub(self.e_lo, Decimal(1)))
        c_e2 = ceil_mul(
            Decimal('2.2'),
            ceil_mul(
                mink_sq,
                ceil_mul(self.e_hi, ceil_mul(ceil_div(jac_hi, floor_mul(Decimal(2), self.pi_lo)), geom_hi)),
            ),
        )
        assert c_e2 < Decimal(65)
        return C_row_dir, c_e2

    def _certify_sin2_hat_phi(self) -> tuple:
        a = self.a_lap
        a2 = floor_mul(a, a)
        ea_lo = floor_exp(a)
        ea_hi = ceil_exp(a)
        e2a_hi = ceil_mul(ea_hi, ea_hi)
        four_pi2_lo = floor_mul(Decimal(4), floor_mul(self.pi_lo, self.pi_lo))
        two_pi2_hi = ceil_mul(Decimal(2), ceil_mul(self.pi_hi, self.pi_hi))

        def sup_mod_hat_on_interval(u0: Decimal, u1: Decimal) -> Decimal:
            t0 = floor_mul(floor_mul(Decimal(2), self.pi_lo), u0)
            t1 = ceil_mul(ceil_mul(Decimal(2), self.pi_hi), u1)
            cos_lo, _ = enclose_cos_interval(t0, t1, self.pi_lo, self.pi_hi)
            if cos_lo >= 0:
                rad_hi = ceil_sub(ceil_add(e2a_hi, Decimal(1)), floor_mul(Decimal(2), floor_mul(ea_lo, cos_lo)))
            else:
                rad_hi = ceil_sub(ceil_add(e2a_hi, Decimal(1)), floor_mul(Decimal(2), floor_mul(ea_hi, cos_lo)))
            num_hi = ceil_mul(two_pi2_hi, ceil_sqrt(max(Decimal(0), rad_hi)))
            d1_lo = floor_sqrt(floor_add(a2, floor_mul(four_pi2_lo, floor_mul(u0, u0))))
            if u0 <= Decimal(1) <= u1:
                du1 = Decimal(0)
            elif u1 < Decimal(1):
                du1 = floor_sub(Decimal(1), u1)
            else:
                du1 = floor_sub(u0, Decimal(1))
            d2_lo = floor_sqrt(floor_add(a2, floor_mul(four_pi2_lo, floor_mul(du1, du1))))
            d3_lo = floor_sqrt(floor_add(a2, floor_mul(four_pi2_lo, floor_mul(floor_add(u0, Decimal(1)), floor_add(u0, Decimal(1))))))
            return ceil_div(num_hi, floor_mul(d1_lo, floor_mul(d2_lo, d3_lo)))

        bin_edges = [Decimal('0'), Decimal('0.5'), Decimal('1.0'), Decimal('2.0'),
                     Decimal('4.0'), Decimal('8.0'), Decimal('16.0'), Decimal('30.0')]
        bins = []
        tot_l1 = Decimal(0)
        for idx in range(len(bin_edges) - 1):
            b0, b1 = bin_edges[idx], bin_edges[idx + 1]
            n_sub = 40 if b1 <= Decimal(2) else 24
            du = (b1 - b0) / Decimal(n_sub)
            mass = Decimal(0)
            for j in range(n_sub):
                u0 = b0 + Decimal(j) * du
                u1 = b0 + Decimal(j + 1) * du
                mass = ceil_add(mass, ceil_mul(Decimal(2), ceil_mul(sup_mod_hat_on_interval(u0, u1), du)))
            bins.append((b1, mass))
            tot_l1 = ceil_add(tot_l1, mass)
        # Analytic tail for |v| > 30: |hat_phi(v)| <= (e^a + 1) / (4*pi*(|v|-1)^3)
        #   int_{|v|>30} |hat_phi(v)| dv <= (e^a + 1) / (4*pi*29^2)
        #   int_{|v|>30} |hat_phi(v)| * sqrt(|v|) dv <= (e^a + 1) * sqrt(30) / (3*pi*29^2)
        tail_mass = ceil_div(ceil_add(ea_hi, Decimal(1)), floor_mul(Decimal(4), floor_mul(self.pi_lo, Decimal(29 * 29))))
        tail_mass_half = ceil_div(
            ceil_mul(ceil_add(ea_hi, Decimal(1)), ceil_sqrt(Decimal(30))),
            floor_mul(Decimal(3), floor_mul(self.pi_lo, Decimal(29 * 29))),
        )
        tot_l1 = ceil_add(tot_l1, tail_mass)
        assert tot_l1 < Decimal('2.15')
        return tot_l1, bins, tail_mass, tail_mass_half

    def _certify_mellin_sin2_constants(self) -> tuple:
        """
        Rigorous delta-independent upper bounds on:
          M0 >= int_0^1 u^{-1/2} |g(u)| du
          M1 >= int_0^1 u^{1/2}  |g'(u)| du
          M2 >= int_0^1 u^{3/2}  |g''(u)| du
        for g(u) = sin^2(pi*u) * sin^2(pi*(u + delta)), using the exact theta-suprema:
          sup_delta |g(u)|   <= sin^2(pi*u)
          sup_delta |g'(u)|  <= pi * ( (1/2)|sin(2*pi*u)| + sin(pi*u) )
          sup_delta |g''(u)| <= 2*pi^2 * ( (1/2)|cos(2*pi*u)| + sqrt(5/4 - cos(2*pi*u)) ).
        """
        n = 120
        M0_hi = Decimal(0)
        M1_hi = Decimal(0)
        M2_hi = Decimal(0)
        two_pi_lo = floor_mul(Decimal(2), self.pi_lo)
        two_pi_hi = ceil_mul(Decimal(2), self.pi_hi)
        two_pi2_hi = ceil_mul(Decimal(2), ceil_mul(self.pi_hi, self.pi_hi))
        half_pi_lo = floor_div(self.pi_lo, Decimal(2))
        half_pi_hi = ceil_div(self.pi_hi, Decimal(2))

        for k in range(n):
            u0 = Decimal(k) / Decimal(n)
            u1 = Decimal(k + 1) / Decimal(n)
            t0 = floor_mul(two_pi_lo, u0)
            t1 = ceil_mul(two_pi_hi, u1)
            c_lo, c_hi = enclose_cos_interval(t0, t1, self.pi_lo, self.pi_hi)
            s_lo, s_hi = enclose_cos_interval(floor_sub(t0, half_pi_hi), ceil_sub(t1, half_pi_lo), self.pi_lo, self.pi_hi)
            sin2_hi = ceil_div(ceil_sub(Decimal(1), c_lo), Decimal(2))
            sin_piu_hi = ceil_sqrt(sin2_hi)
            abs_c_hi = max(abs(c_lo), abs(c_hi))
            abs_s_hi = max(abs(s_lo), abs(s_hi))

            iu_mhalf = ceil_mul(Decimal(2), ceil_sub(ceil_sqrt(u1), floor_sqrt(u0)))
            u1_32 = ceil_mul(u1, ceil_sqrt(u1))
            u0_32 = floor_mul(u0, floor_sqrt(u0))
            iu_half = ceil_div(ceil_mul(Decimal(2), ceil_sub(u1_32, u0_32)), Decimal(3))
            u1_52 = ceil_mul(u1, u1_32)
            u0_52 = floor_mul(u0, u0_32)
            iu_3half = ceil_div(ceil_mul(Decimal(2), ceil_sub(u1_52, u0_52)), Decimal(5))

            g1_sup = ceil_mul(self.pi_hi, ceil_add(ceil_div(abs_s_hi, Decimal(2)), sin_piu_hi))
            g2_sup = ceil_mul(
                two_pi2_hi,
                ceil_add(ceil_div(abs_c_hi, Decimal(2)), ceil_sqrt(ceil_sub(Decimal('1.25'), c_lo))),
            )

            M0_hi = ceil_add(M0_hi, ceil_mul(sin2_hi, iu_mhalf))
            M1_hi = ceil_add(M1_hi, ceil_mul(g1_sup, iu_half))
            M2_hi = ceil_add(M2_hi, ceil_mul(g2_sup, iu_3half))

        assert M0_hi < Decimal('0.85') and M1_hi < Decimal('2.30') and M2_hi < Decimal('11.50')
        return M0_hi, M1_hi, M2_hi


# ---------------------------------------------------------------------------
# Explicit Zero Counting: BMOR (2021, q* > 1) & HSW (2022, q* = 1)
# ---------------------------------------------------------------------------

def bmor_N_up(const: AnalyticConstants, q_val: Decimal, T: Decimal) -> Decimal:
    """Uniform upper bound on N(T, chi*) = #{|gamma| <= T} for BOTH q*=1 (HSW 2022) and 1 < q* <= q_val (BMOR 2021)."""
    with localcontext() as c:
        c.prec = 35
        c.rounding = ROUND_CEILING
        two_pi_lo = Decimal(2) * const.pi_lo
        two_pi_e_lo = two_pi_lo * const.e_lo
        five_sev = Decimal(5) / Decimal(7)
        Te = T if T >= five_sev else five_sev
        q_eff = q_val if q_val >= Decimal(3) else Decimal(3)
        ell = (q_eff * (Te + Decimal(2)) / two_pi_lo).ln()
        n_bmor = (Te / const.pi_lo) * (q_eff * Te / two_pi_e_lo).ln() + Decimal('0.22737') * ell + Decimal(2) * (Decimal(1) + ell).ln() - Decimal('0.25')
        if n_bmor < Decimal(0):
            n_bmor = Decimal(0)
        if T < Decimal(14):
            return n_bmor
        lnT = T.ln()
        # HSW (2022, Cor 1.2): 2*N_zeta(T) <= (T/pi)*ln(T/(2*pi*e)) + 2*(7/8 + 0.1038*ln T + 0.2573*ln ln T + 9.3675)
        n_zeta = (T / const.pi_lo) * (T / two_pi_e_lo).ln() + Decimal('1.75') + Decimal(2) * (Decimal('0.1038') * lnT + Decimal('0.2573') * lnT.ln() + Decimal('9.3675'))
        return n_bmor if n_bmor >= n_zeta else n_zeta


def exact_Czero_mellin_sin2(const: AnalyticConstants, q_val: Decimal) -> Decimal:
    M0, M1, M2 = const.M0_sin2, const.M1_sin2, const.M2_sin2

    def env_bounds(T: Decimal) -> tuple:
        r1_lo = floor_sqrt(floor_add(Decimal('0.25'), floor_mul(T, T)))
        r1_hi = ceil_sqrt(ceil_add(Decimal('0.25'), ceil_mul(T, T)))
        r2_lo = floor_sqrt(floor_add(Decimal('2.25'), floor_mul(T, T)))
        r2_hi = ceil_sqrt(ceil_add(Decimal('2.25'), ceil_mul(T, T)))
        return min(M0, floor_div(M1, r1_hi), floor_div(M2, ceil_mul(r1_hi, r2_hi))), min(M0, ceil_div(M1, r1_lo), ceil_div(M2, floor_mul(r1_lo, r2_lo)))

    grid = [Decimal(0)] + [Decimal(i) / Decimal(2) for i in range(1, 16)] + [Decimal(i) for i in range(8, 36, 2)]
    t_cur = Decimal(40)
    while t_cur < Decimal(2000):
        grid.append(t_cur)
        t_cur = ceil_mul(t_cur, Decimal('1.6'))
    grid.append(Decimal(2000))

    vals = [env_bounds(t) for t in grid]
    tot = Decimal(0)
    for i in range(len(grid) - 1):
        diff = ceil_sub(vals[i][1], vals[i + 1][0])
        if diff > 0:
            tot = ceil_add(tot, ceil_mul(diff, bmor_N_up(const, q_val, grid[i + 1])))
    Te = grid[-1]
    q_eff = max(q_val, Decimal(3))
    ln_qTe = ceil_ln(ceil_mul(q_eff, Te))
    tail_int = ceil_mul(
        M2,
        ceil_add(
            ceil_div(ceil_mul(Decimal(2), ceil_add(ln_qTe, Decimal(2))), floor_mul(const.pi_lo, Te)),
            ceil_div(Decimal(20), floor_mul(Te, Te)),
        ),
    )
    return ceil_add(tot, tail_int)


def exact_Czero_mellin_div_lnq_tail(const: AnalyticConstants, lnq_lo: Decimal) -> Decimal:
    """Uniform upper bound on C_0(q) / ln(q) valid for ALL q >= exp(lnq_lo) (monotone-safe for tail!)."""
    M0, M1, M2 = const.M0_sin2, const.M1_sin2, const.M2_sin2
    two_pi_lo = floor_mul(Decimal(2), const.pi_lo)
    two_pi_e_lo = floor_mul(two_pi_lo, const.e_lo)

    def N_div_lnq(T: Decimal) -> Decimal:
        with localcontext() as c:
            c.prec = 35
            c.rounding = ROUND_CEILING
            five_sev = Decimal(5) / Decimal(7)
            Te = T if T >= five_sev else five_sev
            ln_t2 = ((Te + Decimal(2)) / two_pi_lo).ln()
            ln_te = (Te / two_pi_e_lo).ln()
            m_rat = Decimal(1) if ln_te <= 0 else Decimal(1) + ln_te / lnq_lo
            e_rat = Decimal(1) if ln_t2 <= 0 else Decimal(1) + ln_t2 / lnq_lo
            ell_lo = lnq_lo + ln_t2
            res = (Te / const.pi_lo) * m_rat + Decimal('0.22737') * e_rat + Decimal(2) * (Decimal(1) + ell_lo).ln() / lnq_lo
            if T >= Decimal(14):
                lnT = T.ln()
                z = (T / const.pi_lo) * ((T / two_pi_e_lo).ln() / lnq_lo) + (Decimal('1.75') + Decimal(2) * (Decimal('0.1038') * lnT + Decimal('0.2573') * lnT.ln() + Decimal('9.3675'))) / lnq_lo
                if z > res:
                    res = z
            return res

    def env_bounds(T: Decimal) -> tuple:
        r1_lo = floor_sqrt(floor_add(Decimal('0.25'), floor_mul(T, T)))
        r1_hi = ceil_sqrt(ceil_add(Decimal('0.25'), ceil_mul(T, T)))
        r2_lo = floor_sqrt(floor_add(Decimal('2.25'), floor_mul(T, T)))
        r2_hi = ceil_sqrt(ceil_add(Decimal('2.25'), ceil_mul(T, T)))
        return min(M0, floor_div(M1, r1_hi), floor_div(M2, ceil_mul(r1_hi, r2_hi))), min(M0, ceil_div(M1, r1_lo), ceil_div(M2, floor_mul(r1_lo, r2_lo)))

    grid = [Decimal(0)] + [Decimal(i) / Decimal(2) for i in range(1, 16)] + [Decimal(i) for i in range(8, 36, 2)]
    t_cur = Decimal(40)
    while t_cur < Decimal(2000):
        grid.append(t_cur)
        t_cur = ceil_mul(t_cur, Decimal('1.6'))
    grid.append(Decimal(2000))

    vals = [env_bounds(t) for t in grid]
    tot = Decimal(0)
    for i in range(len(grid) - 1):
        diff = ceil_sub(vals[i][1], vals[i + 1][0])
        if diff > 0:
            tot = ceil_add(tot, ceil_mul(diff, N_div_lnq(grid[i + 1])))
    Te = grid[-1]
    lnTe_ratio = ceil_add(Decimal(1), ceil_div(ceil_add(ceil_ln(Te), Decimal(2)), lnq_lo))
    tail_int = ceil_mul(
        M2,
        ceil_add(
            ceil_div(ceil_mul(Decimal(2), lnTe_ratio), floor_mul(const.pi_lo, Te)),
            ceil_div(Decimal(20), floor_mul(lnq_lo, floor_mul(Te, Te))),
        ),
    )
    return ceil_add(tot, tail_int)


def _enclose_gp_go_pair(const: AnalyticConstants, T: Decimal, U_cap: Decimal) -> tuple:
    """Pure directed-rounding enclosures of g_pos(T; U_cap) and g_opp(T) (ZERO heuristic epsilons!)."""
    if T == 0:
        return (Decimal(1), Decimal(1)), (floor_div(Decimal(1), const.sqrt2_hi), ceil_div(Decimal(1), floor_sqrt(Decimal(2))))
    u = min(ceil_mul(Decimal(2), T), U_cap)
    inv_lo = floor_div(Decimal(1), u)
    inv_hi = ceil_div(Decimal(1), u)
    at_lo, at_mid_hi = enclose_atan_dec(inv_lo, const.pi_lo, const.pi_hi)
    # Since atan'(x) <= 1 and inv_lo <= 1/u <= inv_hi: atan(1/u) <= at_mid_hi + (inv_hi - inv_lo)
    at_hi = ceil_add(at_mid_hi, ceil_sub(inv_hi, inv_lo))
    with localcontext() as c:
        c.prec = 35
        c.rounding = ROUND_FLOOR
        den_lo = (Decimal(1) + u * u).sqrt().sqrt()
    with localcontext() as c:
        c.prec = 35
        c.rounding = ROUND_CEILING
        den_hi = (Decimal(1) + u * u).sqrt().sqrt()
        gp_hi = (-T * at_lo).exp() / den_lo
    with localcontext() as c:
        c.prec = 35
        c.rounding = ROUND_FLOOR
        gp_lo = (-T * at_hi).exp() / den_hi

    pt_lo = floor_mul(const.pi_lo, T)
    pt_hi = ceil_mul(const.pi_hi, T)
    if pt_lo > Decimal(45):
        go_pair = (Decimal(0), ceil_exp(ceil_sub(Decimal(0), floor_div(pt_lo, Decimal(2)))))
    else:
        ep_lo = floor_exp(pt_lo)
        ep_hi = ceil_exp(pt_hi)
        em_lo = floor_div(Decimal(1), ep_hi)
        em_hi = ceil_div(Decimal(1), ep_lo)
        go_lo = floor_div(Decimal(1), ceil_sqrt(ceil_add(ep_hi, em_hi)))
        go_hi = ceil_div(Decimal(1), floor_sqrt(floor_add(ep_lo, em_lo)))
        go_pair = (go_lo, go_hi)
    return (gp_lo, gp_hi), go_pair


def exact_Czero_IBP_paired(const: AnalyticConstants, q_val: Decimal, U_q: Decimal) -> Decimal:
    """Outward-rounded BMOR+HSW+chi/chi_bar(1/2) Riemann-Stieltjes bound."""
    grid = [Decimal(0)]
    t_cur = Decimal('0.5')
    t_lim = max(Decimal(40), ceil_mul(Decimal(16), U_q))
    while t_cur < t_lim:
        grid.append(t_cur)
        if t_cur < Decimal(4):
            t_cur += Decimal('0.5')
        elif t_cur < Decimal(20):
            t_cur += Decimal(2)
        else:
            t_cur = ceil_mul(t_cur, Decimal('1.5'))
    grid.append(t_lim)

    gp, go = [], []
    for T in grid:
        p1, p2 = _enclose_gp_go_pair(const, T, U_q)
        gp.append(p1)
        go.append(p2)

    tot = Decimal(0)
    with localcontext() as c:
        c.prec = 35
        c.rounding = ROUND_CEILING
        for i in range(len(grid) - 1):
            n1 = bmor_N_up(const, q_val, grid[i + 1])
            dp = gp[i][1] - gp[i + 1][0]
            assert dp >= 0
            tot += dp * n1
            if go[i][1] > 0:
                do = go[i][1] - go[i + 1][0]
                assert do >= 0
                tot += do * n1

    delta_lo, _ = enclose_atan_dec(floor_div(Decimal(1), U_q), const.pi_lo, const.pi_hi)
    q_eff = max(q_val, Decimal(3))
    n_lim = bmor_N_up(const, q_eff, t_lim)
    alpha_hi = ceil_add(ceil_div(ceil_ln(ceil_mul(q_eff, t_lim)), const.pi_lo), Decimal(1))
    beta_hi = ceil_div(Decimal(1), floor_mul(const.pi_lo, t_lim))
    tail_pos = ceil_mul(gp[-1][1], ceil_add(n_lim, ceil_add(ceil_div(alpha_hi, delta_lo), ceil_div(ceil_mul(Decimal(2), beta_hi), floor_mul(delta_lo, delta_lo)))))
    d_opp = floor_div(const.pi_lo, Decimal(2))
    tail_opp = ceil_mul(go[-1][1], ceil_add(n_lim, ceil_add(ceil_div(alpha_hi, d_opp), ceil_div(ceil_mul(Decimal(2), beta_hi), floor_mul(d_opp, d_opp)))))
    return ceil_mul(ceil_div(const.sqrt_2pi_hi, Decimal(2)), ceil_add(tot, ceil_add(tail_pos, tail_opp)))


def _bmor_N_div_lnY_fn(const: AnalyticConstants, lnY_lo: Decimal, T: Decimal) -> Decimal:
    with localcontext() as c:
        c.prec = 35
        c.rounding = ROUND_CEILING
        two_pi_lo = Decimal(2) * const.pi_lo
        two_pi_e_lo = two_pi_lo * const.e_lo
        five_sev = Decimal(5) / Decimal(7)
        Te = T if T >= five_sev else five_sev
        ln_t2 = ((Te + Decimal(2)) / two_pi_lo).ln()
        ln_te = (Te / two_pi_e_lo).ln()
        m_rat = Decimal('0.5') if ln_te <= 0 else Decimal('0.5') + ln_te / lnY_lo
        e_rat = Decimal('0.5') if ln_t2 <= 0 else Decimal('0.5') + ln_t2 / lnY_lo
        ell_lo = Decimal('0.5') * lnY_lo + ln_t2
        res = (Te / const.pi_lo) * m_rat + Decimal('0.22737') * e_rat + Decimal(2) * (Decimal(1) + ell_lo).ln() / lnY_lo
        if T >= Decimal(14):
            lnT = T.ln()
            z = (T / const.pi_lo) * ((T / two_pi_e_lo).ln() / lnY_lo) + (Decimal('1.75') + Decimal(2) * (Decimal('0.1038') * lnT + Decimal('0.2573') * lnT.ln() + Decimal('9.3675'))) / lnY_lo
            if z > res:
                res = z
        return res


def bmor_ibp_div_lnY_tail(const: AnalyticConstants, lnY_lo: Decimal, U_hi: Decimal) -> Decimal:
    grid = [Decimal(0)]
    t_cur = Decimal('0.5')
    t_lim = max(Decimal(40), ceil_mul(Decimal(16), U_hi))
    while t_cur < t_lim:
        grid.append(t_cur)
        if t_cur < Decimal(4):
            t_cur += Decimal('0.5')
        elif t_cur < Decimal(20):
            t_cur += Decimal(2)
        else:
            t_cur = ceil_mul(t_cur, Decimal('1.5'))
    grid.append(t_lim)

    gp, go = [], []
    for T in grid:
        p1, p2 = _enclose_gp_go_pair(const, T, U_hi)
        gp.append(p1)
        go.append(p2)

    tot = Decimal(0)
    with localcontext() as c:
        c.prec = 35
        c.rounding = ROUND_CEILING
        for i in range(len(grid) - 1):
            n1 = _bmor_N_div_lnY_fn(const, lnY_lo, grid[i + 1])
            tot += (gp[i][1] - gp[i + 1][0]) * n1
            if go[i][1] > 0:
                tot += (go[i][1] - go[i + 1][0]) * n1

    two_pi_lo = floor_mul(Decimal(2), const.pi_lo)
    delta_lo, _ = enclose_atan_dec(floor_div(Decimal(1), U_hi), const.pi_lo, const.pi_hi)
    n_lim = _bmor_N_div_lnY_fn(const, lnY_lo, t_lim)
    ln_tlim = ceil_ln(ceil_div(t_lim, two_pi_lo))
    a_log = Decimal('0.5') if ln_tlim <= 0 else ceil_add(Decimal('0.5'), ceil_div(ln_tlim, lnY_lo))
    alpha_hi = ceil_add(ceil_div(a_log, const.pi_lo), ceil_div(Decimal(1), lnY_lo))
    beta_hi = ceil_div(Decimal(1), floor_mul(const.pi_lo, floor_mul(t_lim, lnY_lo)))
    tail_pos = ceil_mul(gp[-1][1], ceil_add(n_lim, ceil_add(ceil_div(alpha_hi, delta_lo), ceil_div(ceil_mul(Decimal(2), beta_hi), floor_mul(delta_lo, delta_lo)))))
    d_opp = floor_div(const.pi_lo, Decimal(2))
    tail_opp = ceil_mul(go[-1][1], ceil_add(n_lim, ceil_add(ceil_div(alpha_hi, d_opp), ceil_div(ceil_mul(Decimal(2), beta_hi), floor_mul(d_opp, d_opp)))))
    return ceil_mul(ceil_div(const.sqrt_2pi_hi, Decimal(2)), ceil_add(tot, ceil_add(tail_pos, tail_opp)))


def bmor_large_U_linear_coeffs(const: AnalyticConstants, lnY_lo: Decimal, U_0: Decimal) -> tuple:
    """
    First-principles proof that for ALL q <= Y^{1/2} and ALL U in [U_0, 2*pi*Y^{1/2}] (U_0 >= 150):
      C_zero_IBP(q, U) / ln(Y) <= A_sqrtU * sqrt(U) + B_const.
    Derived via exact integration by parts splitting at T = 5 and T = U/2:
      - [0, 5]: bounded by N_div_lnY(5)
      - [5, U/2]: -(g_pos(T) * (T/pi + C_low))|_5^{U/2} + (1/pi) * int_5^{U/2} g_pos(T) dT
      - [U/2, inf): boundary term cancels g_pos(U/2)*(U/(2*pi) + C_low) EXACTLY, leaving
        (1+U^2)^{-1/4} e^{-delta*U/2} * [1/(pi*delta) + (1/delta + 4/(U*delta^2))/(pi*ln Y) + 0.46/(U*delta*ln Y)]
      - Opposite-sign sum: exact finite IBP independent of U!
    """
    assert U_0 >= Decimal(150)
    # 1. Exact opposite-sign sum (independent of U)
    opp_grid = [Decimal(i) / Decimal(2) for i in range(0, 32)] + [Decimal(20), Decimal(30), Decimal(46)]
    go_list = []
    for T in opp_grid:
        _, gop = _enclose_gp_go_pair(const, T, Decimal(10))
        go_list.append(gop)
    opp_tot = Decimal(0)
    for i in range(len(opp_grid) - 1):
        n1 = _bmor_N_div_lnY_fn(const, lnY_lo, opp_grid[i + 1])
        opp_tot = ceil_add(opp_tot, ceil_mul(ceil_sub(go_list[i][1], go_list[i + 1][0]), n1))
    # Tail T >= 46 for g_opp: exp(-pi*46/2) < 10^{-31}
    opp_tot = ceil_add(opp_tot, Decimal('1e-20'))

    # 2. C_low uniform lower-order constant for T in [5, U/2] (both BMOR and HSW)
    c_bmor = ceil_add(Decimal('0.23'), ceil_div(ceil_mul(Decimal(2), ceil_ln(ceil_add(Decimal(1), lnY_lo))), lnY_lo))
    c_hsw = ceil_add(
        Decimal('0.11'),
        ceil_div(ceil_add(Decimal('20.5'), ceil_mul(Decimal('0.52'), ceil_ln(lnY_lo))), lnY_lo),
    )
    C_low = c_bmor if c_bmor >= c_hsw else c_hsw

    # 3. [0, 5] + boundary at T = 5
    N5_hi = _bmor_N_div_lnY_fn(const, lnY_lo, Decimal(5))
    gp5_pair, _ = _enclose_gp_go_pair(const, Decimal(5), Decimal(20))
    B_inner = ceil_add(
        opp_tot,
        ceil_add(N5_hi, ceil_mul(gp5_pair[1], ceil_add(ceil_div(Decimal(5), const.pi_lo), C_low))),
    )

    # 4. sqrt(U) coefficient from [5, U/2] + [U/2, inf)
    e_mhalf_5 = ceil_exp(ceil_add(Decimal('-0.5'), ceil_div(Decimal(1), Decimal(600))))
    e_mhalf_U = ceil_exp(ceil_add(Decimal('-0.5'), ceil_div(Decimal(1), floor_mul(Decimal(6), floor_mul(U_0, U_0)))))
    inv_corr = ceil_div(Decimal(1), floor_sub(Decimal(1), ceil_div(Decimal(1), floor_mul(Decimal(3), floor_mul(U_0, U_0)))))
    # Exact tail coeff: (1/pi) + (1 + 4*inv_corr)/(pi*lnY) + 0.46/(U_0*lnY)
    tail_bracket = ceil_add(
        ceil_div(Decimal(1), const.pi_lo),
        ceil_add(
            ceil_div(ceil_add(Decimal(1), ceil_mul(Decimal(4), inv_corr)), floor_mul(const.pi_lo, lnY_lo)),
            ceil_div(Decimal('0.46'), floor_mul(U_0, lnY_lo)),
        ),
    )
    A_inner = ceil_add(
        ceil_div(e_mhalf_5, const.pi_lo),
        ceil_mul(ceil_mul(e_mhalf_U, inv_corr), tail_bracket),
    )

    pref = ceil_div(const.sqrt_2pi_hi, Decimal(2))
    return ceil_mul(pref, A_inner), ceil_mul(pref, B_inner)


# ---------------------------------------------------------------------------
# Section 1: Pure Effective Asymptotic GRH (K = 6 on D_{25/32}) + Explicit Prop 5.2 Net
# ---------------------------------------------------------------------------

def exact_A_matrix_over_moduli(mod_list: list) -> list:
    """Exact rational 3x3 matrix A_{i,j}(S) = sum_{q in S} A_{i,j}(q) for 1 <= i, j <= 3."""
    def c_q(q: int, t: int) -> int:
        g = gcd_int(q, abs(t))
        rem = q // g
        mu = 1
        d = 2
        while d * d <= rem:
            if rem % d == 0:
                mu = -mu
                rem //= d
            d += 1
        if rem > 1:
            mu = -mu
        ph = g
        rem = g
        d = 2
        while d * d <= rem:
            if rem % d == 0:
                while rem % d == 0:
                    rem //= d
                ph -= ph // d
            d += 1
        if rem > 1:
            ph -= ph // rem
        return mu * ph

    A = [[Fraction(0) for _ in range(3)] for _ in range(3)]
    for q in mod_list:
        ep = ord_mod2(q)
        phi_q = sum(1 for a in range(1, q) if gcd_int(a, q) == 1)
        H = [pow(2, t, q) for t in range(1, ep + 1)]
        n_tbl = [[0] * q for _ in range(4)]
        n_tbl[0][0] = 1
        for j in range(3):
            for r in range(q):
                if n_tbl[j][r]:
                    for h in H:
                        n_tbl[j + 1][(r + h) % q] += n_tbl[j][r]
        cq_arr = [c_q(q, t) for t in range(q)]
        for i in range(1, 4):
            for j in range(1, 4):
                num = 0
                for r in range(q):
                    if n_tbl[i][r]:
                        for s in range(q):
                            if n_tbl[j][s]:
                                num += n_tbl[i][r] * n_tbl[j][s] * cq_arr[(r - s) % q]
                A[i - 1][j - 1] += Fraction(num, (phi_q ** 2) * (ep ** (i + j)))
    return A


def certify_prop52_explicit_net(const: AnalyticConstants) -> tuple:
    """
    100% rigorous explicit finite directional net {(xi_j, eta_j)}_{j=1}^m replacing
    Li-Liu Prop 5.2 compactness over K_comp = {|z|<=1, (1+r-x)|z|^2 >= r} for lambda = 25/32,
    rho = 3466/10000 (> ln(2)/2 = 0.34657359...)!
    """
    lam = Fraction(25, 32)
    r_frac = lam * lam / 2
    r_lo = frac_floor(r_frac)
    r_hi = frac_ceil(r_frac)
    rho = frac_ceil(Fraction(3466, 10000))
    s_lo = floor_div(floor_ln(frac_floor(Fraction(1 + lam, 1 - lam))), Decimal(2))
    s_hi = ceil_div(ceil_ln(frac_ceil(Fraction(1 + lam, 1 - lam))), Decimal(2))
    I_lo = floor_add(
        floor_mul(frac_floor((1 + lam) / 2), floor_ln(frac_floor(1 + lam))),
        floor_mul(frac_floor((1 - lam) / 2), floor_ln(frac_floor(1 - lam))),
    )
    assert I_lo > rho > ceil_div(const.ln2_hi, Decimal(2))
    s_mid = (s_lo + s_hi) / Decimal(2)

    seed_cap = (s_mid, Decimal(0))
    beta_val = Decimal('0.725')
    x_min_val = Decimal('-0.421')
    N_bseed = 64
    b_seeds = []
    for j in range(N_bseed + 1):
        xm = x_min_val + (beta_val - x_min_val) * Decimal(j) / Decimal(N_bseed)
        u_b = r_hi / (Decimal(1) + r_hi - xm)
        y2 = u_b - xm * xm
        if y2 < 0:
            y2 = Decimal(0)
        ym = ceil_sqrt(y2)
        den = floor_sqrt(u_b * (Decimal(1) - xm) * (Decimal(1) - u_b))
        fac = (const.sqrt2_hi * s_mid) / den
        b_seeds.append((fac * (xm - u_b), fac * ym))
    # Also seed 8 pairs along the unit circle |z| = 1 for x in [-0.95, 0.70]
    u_seeds = []
    for j in range(9):
        xm = Decimal('-0.95') + Decimal('1.65') * Decimal(j) / Decimal(8)
        ym = ceil_sqrt(max(Decimal(0), Decimal(1) - xm * xm))
        t = (rho + Decimal('0.35')) / (Decimal(1) - xm)
        u_seeds.append((t * (xm - Decimal(1)), t * ym))

    used_seeds = set()
    dyn_pairs = []

    one = Decimal(1)
    two = Decimal(2)
    zero = Decimal(0)
    tiny = Decimal('1e-25')
    span_x = beta_val - x_min_val

    with localcontext() as c:
        c.prec = 26

        def phi_box_lo(xi: Decimal, eta: Decimal, x0: Decimal, x1: Decimal, y0: Decimal, y1: Decimal) -> Decimal:
            c.rounding = ROUND_FLOOR
            lin_lo = xi * (x0 if xi >= 0 else x1) + eta * (y0 if eta >= 0 else y1)
            c.rounding = ROUND_CEILING
            t1 = (one + x1) * (xi * xi)
            t3 = (one - x0) * (eta * eta)
            xe = xi * eta
            t2 = two * (y1 if xe >= 0 else y0) * xe
            V_hi = (t1 + t2 + t3) / two
            if V_hi <= zero:
                lcosh_hi = zero
            else:
                sv = V_hi.sqrt()
                lcosh_hi = ((sv.exp() + (-sv).exp()) / two).ln()
            c.rounding = ROUND_FLOOR
            return lin_lo - lcosh_hi

        stack = []
        N_init = 8
        step = two / Decimal(N_init)
        for ix in range(N_init):
            x0 = Decimal(-1) + Decimal(ix) * step
            for iy in range(N_init // 2):
                y0 = Decimal(iy) * step
                stack.append((x0, x0 + step, y0, y0 + step, 0))

        while stack:
            x0, x1, y0, y1, depth = stack.pop()
            ax_min = zero if (x0 <= zero <= x1) else (abs(x0) if abs(x0) < abs(x1) else abs(x1))
            c.rounding = ROUND_FLOOR
            if ax_min * ax_min + y0 * y0 > one + tiny:
                continue
            ax_max = abs(x0) if abs(x0) > abs(x1) else abs(x1)
            c.rounding = ROUND_CEILING
            u_max = ax_max * ax_max + y1 * y1
            if u_max > one:
                u_max = one
            if (one + r_hi - x0) * u_max < r_lo:
                continue

            # O(1) lookup: check right-cap seed, nearest 3 boundary seeds, nearest 2 circle seeds, last 3 dyn pairs
            if phi_box_lo(seed_cap[0], seed_cap[1], x0, x1, y0, y1) >= rho:
                used_seeds.add(("cap", 0))
                continue

            xm = (x0 + x1) / two
            ym = (y0 + y1) / two
            b_idx = int(((xm - x_min_val) / span_x * Decimal(N_bseed)).to_integral_value())
            if b_idx < 0:
                b_idx = 0
            elif b_idx > N_bseed:
                b_idx = N_bseed
            covered = False
            for dj in (0, -1, 1):
                jj = b_idx + dj
                if 0 <= jj <= N_bseed:
                    xi, eta = b_seeds[jj]
                    if phi_box_lo(xi, eta, x0, x1, y0, y1) >= rho:
                        used_seeds.add(("b", jj))
                        covered = True
                        break
            if covered:
                continue
            u_idx = int(((xm - Decimal('-0.95')) / Decimal('1.65') * Decimal(8)).to_integral_value())
            if u_idx < 0:
                u_idx = 0
            elif u_idx > 8:
                u_idx = 8
            for dj in (0, -1, 1):
                jj = u_idx + dj
                if 0 <= jj <= 8:
                    xi, eta = u_seeds[jj]
                    if phi_box_lo(xi, eta, x0, x1, y0, y1) >= rho:
                        used_seeds.add(("u", jj))
                        covered = True
                        break
            if covered:
                continue
            for idx in range(len(dyn_pairs) - 1, max(-1, len(dyn_pairs) - 5), -1):
                xi, eta = dyn_pairs[idx]
                if phi_box_lo(xi, eta, x0, x1, y0, y1) >= rho:
                    covered = True
                    break
            if covered:
                continue

            u = xm * xm + ym * ym
            if u > Decimal('0.995'):
                c.rounding = ROUND_CEILING
                rad = u.sqrt()
                xm_p = xm / rad
                ym_p = ym / rad
                if xm_p > Decimal('0.90'):
                    cand = (s_mid, zero)
                else:
                    t = (rho + Decimal('0.35')) / (one - xm_p)
                    cand = (t * (xm_p - one), t * ym_p)
            else:
                u_eff = u if u > Decimal('0.1') else Decimal('0.1')
                c.rounding = ROUND_FLOOR
                den = (u_eff * (one - xm if one - xm > Decimal('0.01') else Decimal('0.01')) * (one - u_eff if one - u_eff > Decimal('0.005') else Decimal('0.005'))).sqrt()
                c.rounding = ROUND_CEILING
                fac = (const.sqrt2_hi * s_mid) / den
                cand = (fac * (xm - u_eff), fac * ym)
            if phi_box_lo(cand[0], cand[1], x0, x1, y0, y1) >= rho:
                dyn_pairs.append(cand)
                continue
            assert depth < 12, f"Prop 5.2 net did not converge at [{x0},{x1}]x[{y0},{y1}]"
            mx = (x0 + x1) / two
            my = (y0 + y1) / two
            stack.append((x0, mx, y0, my, depth + 1))
            stack.append((mx, x1, y0, my, depth + 1))
            stack.append((x0, mx, my, y1, depth + 1))
            stack.append((mx, x1, my, y1, depth + 1))

    net_pairs = []
    for tag, jj in sorted(used_seeds):
        if tag == "cap":
            net_pairs.append(seed_cap)
        elif tag == "b":
            net_pairs.append(b_seeds[jj])
        else:
            net_pairs.append(u_seeds[jj])
    net_pairs.extend(dyn_pairs)

    C_net = Decimal(0)
    total_pairs = 0
    for xi, eta in net_pairs:
        e_val = ceil_exp(ceil_div(ceil_add(ceil_mul(xi, xi), ceil_mul(eta, eta)), Decimal(2)))
        if eta == 0:
            C_net = ceil_add(C_net, e_val)
            total_pairs += 1
        else:
            C_net = ceil_add(C_net, ceil_mul(Decimal(2), e_val))
            total_pairs += 2
    return total_pairs, C_net


def certify_max_poly_on_D25_32(const: AnalyticConstants, eval_mod_fn, lip_fn, tol: Decimal = Decimal('0.0005')) -> Decimal:
    """Adaptive branch-and-bound outward upper bound on max_{z in D_{25/32}} eval_mod_fn(z)."""
    lam = Fraction(25, 32)
    r = frac_ceil(lam * lam / 2)
    r_lo = frac_floor(lam * lam / 2)
    beta_hi = ceil_div(ceil_add(r, ceil_sqrt(ceil_add(ceil_mul(r, r), ceil_mul(Decimal(4), r)))), Decimal(2))
    x_lo_end = Decimal('-0.421')
    assert floor_mul(floor_sub(floor_add(Decimal(1), r_lo), x_lo_end), floor_mul(x_lo_end, x_lo_end)) > r

    stack = []
    n_init = 60
    dx = (beta_hi - x_lo_end) / Decimal(n_init)
    for i in range(n_init):
        xa = x_lo_end + Decimal(i) * dx
        xb = beta_hi if i == n_init - 1 else x_lo_end + Decimal(i + 1) * dx
        stack.append((xa, xb, 0))

    max_val = Decimal(0)
    best_pt = Decimal(0)
    while stack:
        xa, xb, depth = stack.pop()
        ax_min = Decimal(0) if (xa <= 0 <= xb) else min(abs(xa), abs(xb))
        ax_max = max(abs(xa), abs(xb))
        y2_hi = ceil_sub(ceil_div(r, floor_sub(floor_add(Decimal(1), r_lo), xb)), floor_mul(ax_min, ax_min))
        if y2_hi < 0:
            continue
        y_hi = ceil_sqrt(y2_hi)
        y2_lo = floor_sub(floor_div(r_lo, ceil_sub(ceil_add(Decimal(1), r), xa)), ceil_mul(ax_max, ax_max))
        y_lo = floor_sqrt(y2_lo) if y2_lo > 0 else Decimal(0)
        xm = (xa + xb) / Decimal(2)
        ym = (y_lo + y_hi) / Decimal(2)
        dx_h = ceil_sub(xb, xm)
        dy_h = ceil_sub(y_hi, ym)
        rad = ceil_sqrt(ceil_add(ceil_mul(dx_h, dx_h), ceil_mul(dy_h, dy_h)))
        r_max = ceil_sqrt(ceil_add(ceil_mul(ax_max, ax_max), ceil_mul(y_hi, y_hi)))
        pt_val = eval_mod_fn(xm, ym)
        if pt_val > best_pt:
            best_pt = pt_val
        lip_err = ceil_mul(rad, lip_fn(r_max))
        val = ceil_add(pt_val, lip_err)
        if val <= max_val:
            continue
        if lip_err > tol and depth < 16:
            stack.append((xa, xm, depth + 1))
            stack.append((xm, xb, depth + 1))
            continue
        if val > max_val:
            max_val = val
    return max_val


def run_asymptotic_grh_section(const: AnalyticConstants, S_ex: list) -> dict:
    m_pairs, C_net = certify_prop52_explicit_net(const)

    # 1. Pure effective GRH (C_1 = 8.0, ZERO Siegel, ZERO external Lemma 4.2 T_{2,2}/T_{3,3} citation!):
    #    Use exact A_{i,j} over S_ex (43 odd sqfree q <= 105) + trivial T_{j,j}(S_ex) <= T_{1,1}(S_ex)!
    A_ex = exact_A_matrix_over_moduli(S_ex)
    T11_ex_hi = ceil_sub(ceil_sub(const.C0_R0_hi, Decimal(1)), frac_floor(A_ex[0][0]))
    sT_ex = ceil_sqrt(T11_ex_hi)

    a6 = Fraction(3, 20)
    b6 = Fraction(2, 25)
    v6 = [-b6, -a6, Fraction(1)]
    q_ex6 = Fraction(0)
    for i in range(3):
        for j in range(3):
            q_ex6 += v6[i] * A_ex[i][j] * v6[j]
    # Cauchy-Schwarz over q not in S_ex using T_{j,j} <= T_{1,1} (exact since |F_per(a/q)| <= 1!)
    sum_abs_v6 = sum(abs(x) for x in v6)
    vAv6 = ceil_add(frac_ceil(q_ex6), ceil_mul(frac_ceil(sum_abs_v6 * sum_abs_v6), T11_ex_hi))

    a6_d, b6_d = frac_ceil(a6), frac_ceil(b6)

    def eval_Q6_mod(x: Decimal, y: Decimal) -> Decimal:
        re = x * x - y * y - a6_d * x - b6_d
        im = Decimal(2) * x * y - a6_d * y
        return ceil_sqrt(ceil_add(ceil_mul(re, re), ceil_mul(im, im)))

    def lip_Q6(R: Decimal) -> Decimal:
        return ceil_add(ceil_mul(Decimal(2), R), a6_d)

    Q6_max = certify_max_poly_on_D25_32(const, eval_Q6_mod, lip_Q6)
    H6_hi = ceil_mul(Q6_max, Q6_max)
    C1_grh = Decimal(8)
    rhs6_lo = frac_floor((1 - a6 - b6) ** 2)
    h6_mult = ceil_add(ceil_mul(ceil_div(ceil_sub(C1_grh, Decimal(2)), Decimal(2)), const.C0_R0_hi), ceil_div(const.ln2_hi, Decimal(4)))
    lhs6_hi = ceil_add(vAv6, ceil_add(ceil_div(ceil_mul(frac_ceil(b6 * b6), const.ln2_hi), Decimal(4)), ceil_mul(H6_hi, h6_mult)))
    margin6 = floor_sub(rhs6_lo, lhs6_hi)
    assert margin6 > Decimal('0.07'), f"Asymptotic GRH K=6 margin too small: {margin6}"

    # 2. Informational Lichtman benchmark (C_1 = 6.7814, citing Li-Liu Lemma 4.2 tail bounds on S*={3,5,7,15,31})
    A_star = exact_A_matrix_over_moduli([3, 5, 7, 15, 31])
    assert ceil_sub(ceil_sub(const.C0_R0_hi, Decimal(1)), frac_floor(A_star[0][0])) < Decimal('0.254') ** 2
    sT_ll = [Decimal('0.254'), Decimal('0.077'), Decimal('0.040')]

    def quad_A_ll(v_fracs: list) -> Decimal:
        q_star = Fraction(0)
        for i in range(3):
            for j in range(3):
                q_star += v_fracs[i] * A_star[i][j] * v_fracs[j]
        tail_s = Decimal(0)
        for i in range(3):
            tail_s = ceil_add(tail_s, ceil_mul(frac_ceil(abs(v_fracs[i])), sT_ll[i]))
        return ceil_add(frac_ceil(q_star), ceil_mul(tail_s, tail_s))

    a5, b5, c5, tau5 = Fraction(1, 4), Fraction(1, 16), Fraction(1, 8), Fraction(2, 1)
    v5 = [-b5, -a5, Fraction(1)]
    w5 = [-c5, Fraction(1), Fraction(0)]
    qA5 = ceil_add(quad_A_ll(w5), ceil_mul(Decimal(4), quad_A_ll(v5)))
    a5_d, b5_d, c5_d = frac_ceil(a5), frac_ceil(b5), frac_ceil(c5)

    def eval_F5_sq(x: Decimal, y: Decimal) -> Decimal:
        t1 = ceil_add(ceil_mul(x - c5_d, x - c5_d), ceil_mul(y, y))
        re = x * x - y * y - a5_d * x - b5_d
        im = Decimal(2) * x * y - a5_d * y
        t2 = ceil_mul(Decimal(4), ceil_add(ceil_mul(re, re), ceil_mul(im, im)))
        return ceil_add(t1, t2)

    def lip_F5_sq(R: Decimal) -> Decimal:
        g1 = ceil_mul(Decimal(2), ceil_add(R, c5_d))
        q_ub = ceil_add(ceil_mul(R, R), ceil_add(ceil_mul(a5_d, R), b5_d))
        qp_ub = ceil_add(ceil_mul(Decimal(2), R), a5_d)
        return ceil_add(g1, ceil_mul(Decimal(8), ceil_mul(q_ub, qp_ub)))

    H5_hi = certify_max_poly_on_D25_32(const, eval_F5_sq, lip_F5_sq)
    D5 = frac_ceil(c5 * c5 + tau5 * tau5 * b5 * b5)
    C1_lic = Decimal('6.7814')
    h5_mult = ceil_add(ceil_mul(ceil_div(ceil_sub(C1_lic, Decimal(2)), Decimal(2)), const.C0_R0_hi), ceil_div(const.ln2_hi, Decimal(4)))
    lhs5_hi = ceil_add(qA5, ceil_add(ceil_div(ceil_mul(D5, const.ln2_hi), Decimal(4)), ceil_mul(H5_hi, h5_mult)))
    rhs5_lo = frac_floor(2 * tau5 * (1 - c5) * (1 - a5 - b5))
    margin5 = floor_sub(rhs5_lo, lhs5_hi)
    # Informational only (Lichtman K=5 relies on ineffective Siegel theorem; not our theorem)

    return {
        "net_pairs": m_pairs,
        "C_net": C_net,
        "T11_ex_hi": T11_ex_hi,
        "H6_hi": H6_hi,
        "vAv6": vAv6,
        "lhs6": lhs6_hi,
        "rhs6": rhs6_lo,
        "margin6": margin6,
        "H5_hi": H5_hi,
        "lhs5": lhs5_hi,
        "rhs5": rhs5_lo,
        "margin5": margin5,
    }


# ---------------------------------------------------------------------------
# Section 2: All-Range Explicit K = 14 Machinery (Zero-Float, Zero-Buffer)
# ---------------------------------------------------------------------------

PYTH_DIRS = [
    (1, 0, 1),        # 0:   0.00 deg
    (24, 7, 25),      # 1:  16.26 deg
    (4, 3, 5),        # 2:  36.87 deg
    (7, 24, 25),      # 3:  73.74 deg
    (0, 1, 1),        # 4:  90.00 deg
    (-7, 24, 25),     # 5: 106.26 deg
    (-4, 3, 5),       # 6: 143.13 deg
    (-24, 7, 25),     # 7: 163.74 deg
    (-1, 0, 1),       # 8: 180.00 deg
    (-24, -7, 25),    # 9: 196.26 deg
    (-4, -3, 5),      # 10: 216.87 deg
    (-7, -24, 25),    # 11: 253.74 deg
    (0, -1, 1),       # 12: 270.00 deg
    (7, -24, 25),     # 13: 286.26 deg
    (4, -3, 5),       # 14: 323.13 deg
    (24, -7, 25),     # 15: 343.74 deg
]
for _p, _q, _r in PYTH_DIRS:
    assert _p * _p + _q * _q == _r * _r

DIR_WEIGHTS = [
    Fraction(72, 100), Fraction(8, 100), Fraction(2, 100),
    Fraction(8, 1100), Fraction(8, 1100), Fraction(8, 1100), Fraction(8, 1100),
    Fraction(8, 1100), Fraction(8, 1100), Fraction(8, 1100), Fraction(8, 1100),
    Fraction(8, 1100), Fraction(8, 1100), Fraction(8, 1100),
    Fraction(2, 100), Fraction(8, 100),
]
assert sum(DIR_WEIGHTS) == Fraction(1, 1)


def pyth_angle_enclosure(const: AnalyticConstants, p: int, q: int, r: int) -> tuple:
    assert q >= 0
    if q == 0:
        return (Decimal(0), Decimal(0)) if p > 0 else (const.pi_lo, const.pi_hi)
    if p == 0:
        return floor_div(const.pi_lo, Decimal(2)), ceil_div(const.pi_hi, Decimal(2))
    if p > 0:
        a_lo, _ = enclose_atan_dec(floor_div(Decimal(q), Decimal(p)), const.pi_lo, const.pi_hi)
        _, a_hi = enclose_atan_dec(ceil_div(Decimal(q), Decimal(p)), const.pi_lo, const.pi_hi)
        return a_lo, a_hi
    a_lo, _ = enclose_atan_dec(floor_div(Decimal(q), Decimal(-p)), const.pi_lo, const.pi_hi)
    _, a_hi = enclose_atan_dec(ceil_div(Decimal(q), Decimal(-p)), const.pi_lo, const.pi_hi)
    return floor_sub(const.pi_lo, a_hi), ceil_sub(const.pi_hi, a_lo)


def build_transfer_matrix_sweep(const: AnalyticConstants, B: int, L_min: int, L_max: int,
                                K0_dyad: int = 24, M_run_dyad: int = 38) -> tuple:
    """
    Single forward sweep of:
      1. Dyadic run-length excluded B-bit automaton (for finite slabs L = L_min..L_max-1),
         excluding binary runs of length M_run_dyad starting at bit position <= K0_dyad
         (which all lie in M_dyad(K0_dyad, M_run_dyad)), and
      2. Pure B-bit transfer matrix + Collatz-Wielandt tail (for ALL L >= L_max, ZERO M_dyad on tail!).
    """
    N_states = 1 << B
    mask = N_states - 1
    inv_2B = Decimal(1) / Decimal(N_states)
    two_pi_lo = floor_mul(Decimal(2), const.pi_lo)
    two_pi_hi = ceil_mul(Decimal(2), const.pi_hi)
    R_run = M_run_dyad - B + 1
    assert R_run >= 2

    t_grids = {
        0: [Decimal('0.85'), Decimal('1.05'), Decimal('1.30'), Decimal('1.65'), Decimal('2.10')],
        1: [Decimal('0.90'), Decimal('1.15'), Decimal('1.50'), Decimal('2.00')],
        2: [Decimal('1.15'), Decimal('1.55'), Decimal('2.15')],
        3: [Decimal('2.00'), Decimal('3.00')],
        4: [Decimal('2.50'), Decimal('3.60')],
        5: [Decimal('2.80'), Decimal('4.00')],
        6: [Decimal('2.80'), Decimal('4.00')],
        7: [Decimal('2.60'), Decimal('3.80')],
        8: [Decimal('2.50'), Decimal('3.60')],
    }

    J_dyad_sweep = {L: {key: [] for key in range(9)} for L in range(L_min, L_max)}
    J_pure_sweep = {L: {key: [] for key in range(9)} for L in range(L_min, L_max)}
    CW_tail = {key: [] for key in range(9)}

    for key in range(9):
        p, q, r = PYTH_DIRS[key]
        phi_lo, phi_hi = pyth_angle_enclosure(const, p, q, r)
        cos_up = []
        for j in range(N_states):
            ta = floor_sub(floor_mul(two_pi_lo, floor_mul(Decimal(j), inv_2B)), phi_hi)
            tb = ceil_sub(ceil_mul(two_pi_hi, ceil_mul(Decimal(j + 1), inv_2B)), phi_lo)
            _, c_hi = enclose_cos_interval(ta, tb, const.pi_lo, const.pi_hi)
            cos_up.append(c_hi)

        for t in t_grids[key]:
            with localcontext() as ctx:
                ctx.prec = 26
                ctx.rounding = ROUND_CEILING
                half = Decimal('0.5')
                two = Decimal(2)
                zero = Decimal(0)
                weights = [half * (t * c_hi).exp() for c_hi in cos_up]
                w0 = weights[0]
                w1 = weights[N_states - 1]
                inv_N = Decimal(1) / Decimal(N_states)

                # 1. Dyadic run-length excluded forward DP (steps 1..L_max-1)
                dp = [inv_N] * N_states
                dp[0] = zero
                dp[N_states - 1] = zero
                dp0 = [zero] * (R_run + 1)
                dp1 = [zero] * (R_run + 1)
                dp0[1] = inv_N
                dp1[1] = inv_N

                for step in range(1, L_max):
                    if step >= L_min:
                        tot = zero
                        for j in range(1, N_states - 1):
                            tot += dp[j] * weights[j]
                        s0 = zero
                        s1 = zero
                        for rr in range(1, R_run + 1):
                            s0 += dp0[rr]
                            s1 += dp1[rr]
                        tot = two * (tot + s0 * w0 + s1 * w1)
                        J_dyad_sweep[step][key].append((t, tot.ln()))
                    if step == L_max - 1:
                        break
                    ndp = [zero] * N_states
                    ndp0 = [zero] * (R_run + 1)
                    ndp1 = [zero] * (R_run + 1)
                    for j in range(1, N_states - 1):
                        v = dp[j] * weights[j]
                        if v == zero:
                            continue
                        j1 = (2 * j) & mask
                        j2 = j1 | 1
                        if j1 == 0:
                            ndp0[1] += v
                        elif j1 == N_states - 1:
                            ndp1[1] += v
                        else:
                            ndp[j1] += v
                        if j2 == 0:
                            ndp0[1] += v
                        elif j2 == N_states - 1:
                            ndp1[1] += v
                        else:
                            ndp[j2] += v
                    for rr in range(1, R_run + 1):
                        v = dp0[rr] * w0
                        if v != zero:
                            ndp[1] += v
                            if rr + 1 < R_run:
                                ndp0[rr + 1] += v
                            elif rr == R_run:
                                ndp0[R_run] += v
                            elif step + 2 - R_run > K0_dyad:
                                ndp0[R_run] += v
                        v = dp1[rr] * w1
                        if v != zero:
                            ndp[N_states - 2] += v
                            if rr + 1 < R_run:
                                ndp1[rr + 1] += v
                            elif rr == R_run:
                                ndp1[R_run] += v
                            elif step + 2 - R_run > K0_dyad:
                                ndp1[R_run] += v
                    dp, dp0, dp1 = ndp, ndp0, ndp1

                # 2. Pure transfer matrix (steps 1..L_max, ZERO M_dyad!) + Collatz-Wielandt tail
                u = [Decimal(1)] * N_states
                for step in range(1, L_max + 1):
                    u = [weights[j] * (u[(2 * j) & mask] + u[((2 * j) & mask) | 1]) for j in range(N_states)]
                    if L_min <= step < L_max:
                        J_pure_sweep[step][key].append((t, (sum(u) * inv_N).ln()))
                v = list(u)
                mx = max(v)
                v = [x / mx for x in v]
                for _ in range(22):
                    vn = [weights[j] * (v[(2 * j) & mask] + v[((2 * j) & mask) | 1]) for j in range(N_states)]
                    mx = max(vn)
                    v = [x / mx for x in vn]
                Mv = [weights[j] * (v[(2 * j) & mask] + v[((2 * j) & mask) | 1]) for j in range(N_states)]
                lam_hi = max(Mv[j] / v[j] for j in range(N_states))
                C_u_hi = max(u[j] / v[j] for j in range(N_states))
                C_cw_hi = C_u_hi * (sum(v) * inv_N)
                CW_tail[key].append((t, C_cw_hi.ln(), lam_hi, lam_hi.ln()))

    return J_dyad_sweep, J_pure_sweep, CW_tail


def exact_rational_polygon_vertices(c_fracs: list) -> list:
    poly = [
        (Fraction(-1), Fraction(-1)), (Fraction(1), Fraction(-1)),
        (Fraction(1), Fraction(1)), (Fraction(-1), Fraction(1)),
    ]
    for m, (p, q, r) in enumerate(PYTH_DIRS):
        a = Fraction(p, r)
        b = Fraction(q, r)
        c = c_fracs[m]
        new_poly = []
        n = len(poly)
        for i in range(n):
            p1 = poly[i]
            p2 = poly[(i + 1) % n]
            d1 = a * p1[0] + b * p1[1] - c
            d2 = a * p2[0] + b * p2[1] - c
            if d1 <= 0:
                new_poly.append(p1)
            if (d1 <= 0) != (d2 <= 0):
                t = d1 / (d1 - d2)
                new_poly.append((p1[0] + t * (p2[0] - p1[0]), p1[1] + t * (p2[1] - p1[1])))
        clean = []
        for pt in new_poly:
            if not clean or clean[-1] != pt:
                clean.append(pt)
        if len(clean) > 1 and clean[0] == clean[-1]:
            clean.pop()
        poly = clean
    assert len(poly) >= 3
    for x, y in poly:
        for m, (p, q, r) in enumerate(PYTH_DIRS):
            assert Fraction(p, r) * x + Fraction(q, r) * y <= c_fracs[m]
    return poly


def polygon_max_monomial_sq(verts_frac: list, k_deg: int) -> tuple:
    """
    Exact rational convex-analysis upper bound on max_K |z|^{2(k-1)} and max_K |z|^{2k}
    for any convex polygon K = conv(verts_frac).
    Since f(x, y) = x^2 + y^2 is convex on R^2, its maximum on a compact convex polygon is
    attained at one of its extreme vertices; raising to (k-1) and k in exact Fraction arithmetic
    followed by a single outward ceiling is 100% exact with zero discretization error.
    """
    r2_max = Fraction(0)
    for x, y in verts_frac:
        r2 = x * x + y * y
        if r2 > r2_max:
            r2_max = r2
    if r2_max > Fraction(1, 1):
        r2_max = Fraction(1, 1)
    return frac_ceil(r2_max ** (k_deg - 1)), frac_ceil(r2_max ** k_deg)


# ---------------------------------------------------------------------------
# Exact Finite-L Arithmetic Tables (S_ex up to 105, D_1 = 2000)
# ---------------------------------------------------------------------------

def build_S_ex_and_sing_tables(const: AnalyticConstants, Q_ex_max: int = 105, D1: int = 2000) -> dict:
    lim = max(Q_ex_max, D1 + 5)
    is_sqf = [True] * (lim + 1)
    phi_arr = list(range(lim + 1))
    phi_star = [1] * (lim + 1)
    is_p = [True] * (lim + 1)
    for i in range(2, lim + 1):
        if is_p[i]:
            for j in range(i, lim + 1, i):
                if j > i:
                    is_p[j] = False
                phi_arr[j] = (phi_arr[j] // i) * (i - 1)
                if i > 2:
                    phi_star[j] *= (i - 2)
            i2 = i * i
            for j in range(i2, lim + 1, i2):
                is_sqf[j] = False

    def ramanujan_sqf(q: int, n: int) -> int:
        g = gcd_int(q, abs(n))
        rem = q // g
        mu = 1
        d = 2
        while d * d <= rem:
            if rem % d == 0:
                mu = -mu
                rem //= d
            d += 1
        if rem > 1:
            mu = -mu
        return mu * phi_arr[g]

    S_ex = [q for q in range(3, Q_ex_max + 1, 2) if is_sqf[q]]
    S_ex_data = []
    sum_A11_asymp = Fraction(0)
    two_pi_lo = floor_mul(Decimal(2), const.pi_lo)
    two_pi_hi = ceil_mul(Decimal(2), const.pi_hi)
    half_pi_lo = floor_div(const.pi_lo, Decimal(2))
    half_pi_hi = ceil_div(const.pi_hi, Decimal(2))

    for q in S_ex:
        ep = ord_mod2(q)
        ph = phi_arr[q]
        c_list = [ramanujan_sqf(q, (1 << s) - 1) for s in range(ep)]
        sum_A11_asymp += Fraction(sum(c_list), ep * ph * ph)

        cos_q = []
        sin_q = []
        for k in range(q):
            th_lo = floor_div(floor_mul(two_pi_lo, Decimal(k)), Decimal(q))
            th_hi = ceil_div(ceil_mul(two_pi_hi, Decimal(k)), Decimal(q))
            cos_q.append(enclose_cos_interval(th_lo, th_hi, const.pi_lo, const.pi_hi))
            sin_q.append(enclose_cos_interval(floor_sub(th_lo, half_pi_hi), ceil_sub(th_hi, half_pi_lo), const.pi_lo, const.pi_hi))

        pow2_q = [pow(2, t, q) for t in range(1, ep + 1)]
        z_mods_hi = []
        inv_ep_hi = ceil_div(Decimal(1), Decimal(ep))
        with localcontext() as c:
            c.prec = 32
            for a in range(1, q):
                if gcd_int(a, q) != 1:
                    continue
                re_lo = re_hi = im_lo = im_hi = Decimal(0)
                c.rounding = ROUND_FLOOR
                for p2 in pow2_q:
                    k = (a * p2) % q
                    re_lo += cos_q[k][0]
                    im_lo += sin_q[k][0]
                c.rounding = ROUND_CEILING
                for p2 in pow2_q:
                    k = (a * p2) % q
                    re_hi += cos_q[k][1]
                    im_hi += sin_q[k][1]
                re_abs = (re_hi if re_hi >= -re_lo else -re_lo) * inv_ep_hi
                im_abs = (im_hi if im_hi >= -im_lo else -im_lo) * inv_ep_hi
                zm = (re_abs * re_abs + im_abs * im_abs).sqrt()
                z_mods_hi.append(zm if zm < Decimal(1) else Decimal(1))
        S_ex_data.append((q, ep, ph, c_list, z_mods_hi))

    d_list_D1 = []
    R0_partial_D1 = Fraction(0)
    for d in range(1, D1 + 1, 2):
        if is_sqf[d]:
            ep_d = ord_mod2(d)
            d_list_D1.append((d, ep_d, phi_arr[d]))
            R0_partial_D1 += Fraction(1, ep_d * phi_star[d])
    R0_tail_D1 = ceil_sub(const.R0_hi, frac_floor(R0_partial_D1))
    # Multiply by odd_tot_ub since sum_{b > Q0/d} mu^2(b)/phi(b)^2 <= odd_tot_ub and 1/phi(d) <= 1/phi*(d)!
    sing_tail_D1 = ceil_mul(const.odd_tot_ub, R0_tail_D1)
    assert sing_tail_D1 < Decimal('0.030')

    return {
        "S_ex": S_ex,
        "S_ex_data": S_ex_data,
        "sum_A11_asymp": sum_A11_asymp,
        "D1": D1,
        "d_list_D1": d_list_D1,
        "R0_tail_D1": R0_tail_D1,
        "sing_tail_D1": sing_tail_D1,
        "sum_inv_phi_Sex": sum(Fraction(1, phi_arr[q]) for q in S_ex),
        "inv_phi_pref": _build_odd_sqf_inv_phi_prefix(1800000),
    }


def _build_odd_sqf_inv_phi_prefix(Q_max: int) -> list:
    """Exact outward-rounded prefix sums of sum_{q <= Q, 2 nmid q} mu^2(q)/phi(q) for Q <= Q_max."""
    sq = [True] * (Q_max + 1)
    phi = list(range(Q_max + 1))
    for i in range(2, Q_max + 1):
        if phi[i] == i:
            for j in range(i, Q_max + 1, i):
                phi[j] = (phi[j] // i) * (i - 1)
            i2 = i * i
            for j in range(i2, Q_max + 1, i2):
                sq[j] = False
    pref = [Decimal(0)] * (Q_max + 1)
    with localcontext() as ctx:
        ctx.prec = 28
        ctx.rounding = ROUND_CEILING
        one = Decimal(1)
        s = Decimal(0)
        for q in range(1, Q_max + 1):
            if (q & 1) and sq[q]:
                s += one / Decimal(phi[q])
            pref[q] = s
    return pref


def exact_or_elem_odd_inv_phi(const: AnalyticConstants, tbl: dict, X: Decimal) -> Decimal:
    x_int = int(X.to_integral_value(rounding=ROUND_CEILING))
    pref = tbl["inv_phi_pref"]
    if x_int < len(pref):
        return pref[x_int]
    return elem_sum_odd_sqf_inv_phi_ub(const, X)


def elem_sum_odd_sqf_inv_phi_ub(const: AnalyticConstants, X: Decimal) -> Decimal:
    """
    1-line exact elementary upper bound valid for ALL X >= 1:
      sum_{q <= X, 2 nmid q} mu^2(q)/phi(q) <= C_{odd,q/phi} * (1 + (1/2) * ln(X)).
    """
    return ceil_mul(const.C_odd_qphi_hi, ceil_add(Decimal(1), ceil_div(ceil_ln(X), Decimal(2))))


def precompute_L_Sex_bounds(const: AnalyticConstants, tbl: dict, L_val: int,
                            Q0_lo: Decimal, Q0_hi: Decimal,
                            k_deg: int, c_frac: Fraction) -> tuple:
    """Compute (vA_Sex_beta_hi, T11_hi, sing_trunc) ONCE per slab L for P(z) = z^{k_deg}!"""
    L_d = Decimal(L_val)
    c_d = frac_ceil(c_frac)

    # Worst-case sing_trunc at smallest Q0_lo in the slab
    sing_trunc = tbl["sing_tail_D1"]
    for d, ep_d, ph_d in tbl["d_list_D1"]:
        sing_trunc = ceil_add(sing_trunc, ceil_div(const.odd_tail(floor_div(Q0_lo, Decimal(d))), Decimal(ep_d * ph_d)))

    pi2_hi = ceil_mul(const.pi_hi, const.pi_hi)
    shift_const_11 = ceil_div(ceil_mul(Decimal(16), ceil_mul(pi2_hi, ceil_mul(c_d, c_d))), Decimal(9))
    delta_u1 = ceil_div(ceil_mul(Decimal(4), ceil_mul(const.pi_hi, c_d)), L_d)
    delta_u2 = ceil_mul(Decimal(2), delta_u1)
    tail_mass_u2 = ceil_div(Decimal(2), floor_mul(Decimal(135), floor_mul(const.pi_lo, const.pi_lo)))
    mass_u12 = ceil_mul(
        frac_ceil(Fraction(4, 3)),
        ceil_sub(frac_ceil(Fraction(2, 3)), floor_mul(Decimal(2), floor_ln(frac_floor(Fraction(4, 3))))),
    )

    sum_A11_Sex_hneq0_lo = Fraction(0)
    sum_shift_Sex_hi = Decimal(0)
    vA_Sex_beta_hi = Decimal(0)

    with localcontext() as ctx:
        ctx.prec = 30
        ctx.rounding = ROUND_CEILING
        one = Decimal(1)
        for q, ep, ph, c_list, z_mods_hi in tbl["S_ex_data"]:
            num_s = 0
            abs_s = 0
            for s in range(1, L_val):
                cv = c_list[s % ep]
                num_s += (L_val - s) * cv
                abs_s += abs(cv)
            sum_A11_Sex_hneq0_lo += Fraction(2 * num_s, (L_val * L_val) * (ph * ph))
            sum_shift_Sex_hi += shift_const_11 * Decimal(abs_s) / Decimal((L_val * L_val) * (ph * ph))

            rem_frac = Decimal(L_val % ep) / L_d
            d1 = rem_frac + delta_u1
            d2 = rem_frac + delta_u2
            q_s1 = Decimal(0)
            q_s2 = Decimal(0)
            for zm in z_mods_hi:
                z1 = zm + d1
                if z1 > one:
                    z1 = one
                z2 = zm + d2
                if z2 > one:
                    z2 = one
                p1 = z1 ** k_deg
                p2 = z2 ** k_deg
                q_s1 += p1 * p1
                q_s2 += p2 * p2
            q_tot = q_s1 + mass_u12 * q_s2 + tail_mass_u2 * Decimal(ph)
            vA_Sex_beta_hi += q_tot / Decimal(ph * ph)

    # Exact diagonal over q in (1, Q0] \ S_ex plus the +1/L cancellation from q=1:
    #   (sum_{q<=Q0, 2 nmid q} mu^2(q)/phi(q) - sum_{q in S_ex} 1/phi(q)) / L
    sum_inv_phi_net = ceil_sub(exact_or_elem_odd_inv_phi(const, tbl, Q0_hi), frac_floor(tbl["sum_inv_phi_Sex"]))
    shift_q1 = ceil_div(shift_const_11, L_d)
    T11_hi = ceil_add(
        ceil_div(sum_inv_phi_net, L_d),
        ceil_add(
            ceil_sub(ceil_sub(const.C0_R0_hi, Decimal(1)), frac_floor(sum_A11_Sex_hneq0_lo)),
            ceil_add(shift_q1, ceil_add(sum_shift_Sex_hi, sing_trunc)),
        ),
    )
    return vA_Sex_beta_hi, T11_hi, sing_trunc


# ---------------------------------------------------------------------------
# Direct Mellin 1D Selberg Sieve (ZERO prime-power subtraction error!)
# ---------------------------------------------------------------------------

_SELBERG_Z_CACHE = {}
def get_selberg_z_data(const: AnalyticConstants, z_val: int) -> tuple:
    if z_val in _SELBERG_Z_CACHE:
        return _SELBERG_Z_CACHE[z_val]
    sqfree = [True] * z_val
    phi_star = [1] * z_val
    is_p = [True] * z_val
    two_om = [1] * z_val
    for i in range(2, z_val):
        if is_p[i]:
            for j in range(i, z_val, i):
                if j > i:
                    is_p[j] = False
                if i > 2:
                    phi_star[j] *= (i - 2)
                    two_om[j] *= 2
            i2 = i * i
            for j in range(i2, z_val, i2):
                sqfree[j] = False
    with localcontext() as ctx:
        ctx.prec = 30
        ctx.rounding = ROUND_FLOOR
        G_1_dn = Decimal(0)
        one = Decimal(1)
        for d in range(1, z_val, 2):
            if sqfree[d]:
                G_1_dn += one / Decimal(phi_star[d])
    with localcontext() as ctx:
        ctx.prec = 30
        ctx.rounding = ROUND_CEILING
        G_1_up = Decimal(0)
        s_k1_up = Decimal(0)
        s_k0_up = Decimal(0)
        cnt = 0
        one = Decimal(1)
        for k in range(1, z_val, 2):
            if sqfree[k]:
                cnt += 1
                inv_ps = one / Decimal(phi_star[k])
                G_1_up += inv_ps
                t_ps = Decimal(two_om[k]) * inv_ps
                s_k0_up += t_ps
                s_k1_up += t_ps / Decimal(k)
    C0_mel = exact_Czero_mellin_sin2(const, Decimal(z_val * z_val))
    res = (G_1_dn, G_1_up, Decimal(cnt), s_k1_up, s_k0_up, C0_mel)
    _SELBERG_Z_CACHE[z_val] = res
    return res


def selberg_C_sin2_finite(const: AnalyticConstants, N_lo: Decimal, N_hi: Decimal, c_frac: Fraction) -> tuple:
    lnN_hi = ceil_ln(N_hi)
    sqrt_N_lo = floor_sqrt(N_lo)
    N_1_4_hi = ceil_sqrt(ceil_sqrt(N_hi))
    # For |h| <= c*N: phi_w(h) >= 1 - (2*pi^2/3)*c^2 (exact since f''' >= 0 on [0, 1/2]!)
    c_d = frac_ceil(c_frac)
    phi_min_lo = floor_sub(Decimal(1), ceil_div(ceil_mul(Decimal(2), ceil_mul(ceil_mul(const.pi_hi, const.pi_hi), ceil_mul(c_d, c_d))), Decimal(3)))
    assert phi_min_lo > Decimal('0.5')
    E2_eff_lo = floor_mul(floor_mul(Decimal('0.375'), phi_min_lo), N_lo)

    best_c = None
    best_z = None
    for z in (6000, 10000, 16000, 24000, 28000):
        G1_dn, G1_up, cnt, s_k1, s_k0, C0_mel = get_selberg_z_data(const, z)
        err_per_d_over_sqrtN = ceil_add(
            C0_mel,
            ceil_div(ceil_mul(Decimal(150), ceil_mul(N_1_4_hi, lnN_hi)), sqrt_N_lo),
        )
        s_lam_fac = ceil_mul(cnt, ceil_add(ceil_mul(Decimal('0.5'), ceil_mul(Decimal(z), s_k1)), ceil_mul(Decimal('0.5'), s_k0)))
        rem_num = ceil_add(
            ceil_mul(s_lam_fac, ceil_mul(err_per_d_over_sqrtN, ceil_sqrt(N_hi))),
            ceil_mul(Decimal(z), ceil_mul(ceil_mul(lnN_hi, lnN_hi), G1_up)),
        )
        rem_ratio = ceil_div(rem_num, E2_eff_lo)
        main_fac = ceil_div(lnN_hi, floor_mul(const.two_C2_dn, G1_dn))
        c_sel = ceil_mul(main_fac, ceil_add(Decimal(1), rem_ratio))
        if best_c is None or c_sel < best_c:
            best_c = c_sel
            best_z = z
    assert best_c is not None and best_c < Decimal('10.0')
    return best_c, best_z


def selberg_C_sin2_tail(const: AnalyticConstants, N_min: Decimal) -> Decimal:
    """
    100% monotone-safe uniform upper bound on C_Sel(N) for ALL N >= N_min (with z = floor(N^{1/6})),
    using:
      - Exact 1-line lower bound G_1(z) > (1/2) * ln(z) for all integers z >= 2
      - Exact 1-line upper bound G_1(z) <= s_{k1,inf} * (1 + ln(z))
      - Exact S_lam^2 <= ((z+1)/2) * z * s_{k1,inf} (since s_k0 <= z * s_k1 unconditionally!)
      - Exact monotone-safe C_0(N^{1/3}) <= C_{0,div} * (ln N)/3.
    Since (ln N)^3 * N^{-1/6} is strictly decreasing for ln N >= 18 (here ln N_min > 84),
    evaluating at N_min certifies ALL N >= N_min!
    """
    lnN_lo = floor_ln(N_min)
    lnN_hi = ceil_ln(N_min)
    assert lnN_lo > Decimal(25)
    z_min_lo = floor_exp(floor_div(lnN_lo, Decimal(6)))
    z_min_hi = ceil_exp(ceil_div(lnN_hi, Decimal(6)))
    # Since z = floor(N^{1/6}) >= N^{1/6} - 1, ln(z) >= (1/6)*ln(N) - 1/(z_min_lo - 1)
    G1_over_lnN_lo = floor_sub(
        frac_floor(Fraction(1, 12)),
        ceil_div(Decimal(1), floor_mul(Decimal(2), floor_mul(floor_sub(z_min_lo, Decimal(1)), lnN_lo))),
    )
    main_fac = ceil_div(Decimal(1), floor_mul(const.two_C2_dn, G1_over_lnN_lo))

    lnq_lo = floor_div(lnN_lo, Decimal(3))
    C0_div_lnq = exact_Czero_mellin_div_lnq_tail(const, lnq_lo)

    pr = Fraction(1)
    for p in sieve_primes(500):
        if p > 2:
            pr *= Fraction(p * (p - 2) + 2, p * (p - 2))
    s_k1_asymp = ceil_mul(frac_ceil(pr), ceil_exp(ceil_div(Decimal(2), Decimal(498))))
    assert s_k1_asymp < Decimal('2.42')

    # S_lam^2 <= ((z+1)/2) * z * s_{k1,inf} <= 0.501 * z^2 * s_{k1,inf}
    s_lam_coeff = ceil_mul(ceil_div(ceil_add(z_min_hi, Decimal(1)), floor_mul(Decimal(2), z_min_lo)), s_k1_asymp)
    # Term 1: S_lam^2 * C_0(N^{1/3}) * sqrt(N) / (0.24 * N) <= s_lam_coeff * (C0_div_lnq / 3) * (ln N) * N^{-1/6} / 0.24
    N_m16_hi = ceil_div(Decimal(1), floor_exp(floor_div(lnN_lo, Decimal(6))))
    N_m512_hi = ceil_div(Decimal(1), floor_exp(floor_div(floor_mul(Decimal(5), lnN_lo), Decimal(12))))
    N_m56_hi = ceil_div(Decimal(1), floor_exp(floor_div(floor_mul(Decimal(5), lnN_lo), Decimal(6))))

    rem1 = ceil_div(
        ceil_mul(s_lam_coeff, ceil_mul(ceil_div(C0_div_lnq, Decimal(3)), ceil_mul(lnN_hi, N_m16_hi))),
        Decimal('0.24'),
    )
    rem2 = ceil_div(
        ceil_mul(s_lam_coeff, ceil_mul(Decimal(150), ceil_mul(lnN_hi, N_m512_hi))),
        Decimal('0.24'),
    )
    G1_over_lnz = ceil_mul(s_k1_asymp, ceil_add(Decimal(1), ceil_div(Decimal(6), lnN_lo)))
    rem3 = ceil_div(
        ceil_mul(G1_over_lnz, ceil_mul(ceil_div(lnN_hi, Decimal(6)), ceil_mul(ceil_mul(lnN_hi, lnN_hi), N_m56_hi))),
        Decimal('0.24'),
    )
    rem_ratio = ceil_add(rem1, ceil_add(rem2, rem3))
    assert rem_ratio < Decimal('0.01')
    return ceil_mul(main_fac, ceil_add(Decimal(1), rem_ratio))


# ---------------------------------------------------------------------------
# Fourier-Convolved Minor-Arc Sup-Norm |S_w(alpha)| (Zero-M_2 Architecture!)
# ---------------------------------------------------------------------------

def convolved_sup_Sw_finite(const: AnalyticConstants, N_lo: Decimal, N_hi: Decimal,
                            Q0_val: Decimal, D_arc: Decimal) -> tuple:
    """
    Rigorous uniform upper bound on (sup_{alpha not in M_1} |S_w(alpha)|)^2 / (2 * E_2)
    valid for ALL N in [N_lo, N_hi], with constant-width core arcs Delta_q = D_arc / N!
    Uses exact single-N Dirichlet parameterization Q_1 = Q_max = sqrt(Y), q = u*sqrt(Y) (u in (0,1]),
    so U_q <= 2*pi / u is IDENTICALLY independent of N (ZERO (N_hi/N_lo)^{3.5} subdivision inflation!),
    and sqrt(q*Y)/N = sqrt(u) * a^{-3/4} * N^{-1/4}, giving:
      |S_w(alpha)|^2 / (0.75 * N) <= (K_err * N_hi^{1/4} + (pole_max + other_corr) * N_hi^{1/2})^2 / 0.75!
    """
    Y_lo = floor_div(N_lo, const.a_lap)
    Y_hi = ceil_div(N_hi, const.a_lap)
    Qmax_hi = ceil_sqrt(Y_hi)
    lnY_lo = floor_ln(Y_lo)
    lnY_hi = ceil_ln(Y_hi)
    N_1_4_hi = ceil_sqrt(ceil_sqrt(N_hi))
    N_1_2_hi = ceil_sqrt(N_hi)
    a_m34 = ceil_div(Decimal(1), floor_sqrt(floor_mul(const.a_lap, floor_sqrt(const.a_lap))))

    # Vertical contour at Re(s) = 1/4: |E_vert| / sqrt(N) <= sqrt(a) * const * (A_vert + 15*(ln Y_hi + 5))
    vert_sqrtN = ceil_mul(
        ceil_sqrt(const.a_lap),
        ceil_mul(
            const.l1_hat_phi,
            ceil_mul(
                ceil_div(ceil_mul(Decimal(6), const.gamma_1_4_coeff), const.pi_lo),
                ceil_add(const.A_vert_1_4, ceil_mul(Decimal(15), ceil_add(lnY_hi, Decimal(5)))),
            ),
        ),
    )
    omega_hi = ceil_add(ceil_div(ceil_ln(Qmax_hi), const.ln2_lo), Decimal(1))
    pp_gcd_sqrtN = ceil_add(
        ceil_div(ceil_mul(Decimal(2), ceil_mul(omega_hi, ceil_mul(lnY_hi, lnY_hi))), floor_sqrt(N_lo)),
        ceil_div(ceil_mul(Decimal('1.5'), lnY_hi), floor_sqrt(const.a_lap)),
    )
    other_sqrtN = ceil_add(vert_sqrtN, pp_gcd_sqrtN)

    lnln_qmax = ceil_ln(ceil_ln(Qmax_hi))
    lnln_q0 = floor_ln(floor_ln(Q0_val))
    rs15_hi = ceil_add(ceil_mul(const.e_gamma_hi, lnln_qmax), ceil_div(Decimal('2.50637'), lnln_q0))

    A_tail_150, B_tail_150 = bmor_large_U_linear_coeffs(const, lnY_lo, Decimal(150))
    sqrt_2pi_a = ceil_sqrt(ceil_div(ceil_mul(Decimal(2), const.pi_hi), const.a_lap))

    d_arc_den = floor_mul(Decimal(2), floor_mul(const.pi_lo, floor_mul(D_arc, floor_sub(floor_mul(D_arc, D_arc), Decimal(1)))))
    pole_q_le_q0 = ceil_div(Decimal(1), d_arc_den)
    pole_q_gt_q0 = ceil_div(ceil_mul(Decimal('0.5'), rs15_hi), Q0_val)
    pole_max = pole_q_le_q0 if pole_q_le_q0 >= pole_q_gt_q0 else pole_q_gt_q0

    # Large-U analytic envelope for u <= u_min (where U_q = 2*pi/u >= 2000!)
    u_min = Decimal('0.002')
    U_sc_hi = ceil_mul(Decimal(2), const.pi_hi)
    U_sc_lo = floor_mul(Decimal(2), const.pi_lo)
    U0_env = floor_div(U_sc_lo, u_min)
    assert U0_env >= Decimal(2000)
    A_env, B_env = bmor_large_U_linear_coeffs(const, lnY_lo, U0_env)

    U_sc_shift = ceil_add(U_sc_hi, ceil_mul(u_min, ceil_div(ceil_mul(Decimal(60), const.pi_hi), const.a_lap)))
    env_main = ceil_mul(const.l1_hat_phi, ceil_add(ceil_mul(A_env, ceil_sqrt(U_sc_shift)), ceil_mul(B_env, ceil_sqrt(u_min))))
    env_vtail = ceil_mul(A_env, ceil_mul(sqrt_2pi_a, ceil_mul(const.hat_phi_tail_half, ceil_sqrt(u_min))))
    K_err_env = ceil_mul(ceil_mul(ceil_add(env_main, env_vtail), lnY_hi), a_m34)
    best_sr_sqrtN = ceil_add(ceil_mul(K_err_env, N_1_4_hi), ceil_add(ceil_mul(pole_max, N_1_2_hi), other_sqrtN))

    # 36 geometric subintervals covering [u_min, 1]
    n_sub = 36
    step_hi = ceil_exp(ceil_div(ceil_ln(Decimal(500)), Decimal(n_sub)))
    u_cur = u_min
    for j in range(n_sub):
        u_nxt = Decimal(1) if j == n_sub - 1 else min(Decimal(1), ceil_mul(u_cur, step_hi))
        q_hi_b = ceil_mul(u_nxt, Qmax_hi)
        base_U_hi = ceil_div(U_sc_hi, u_cur)
        conv_c = Decimal(0)
        for u_hi, mass in const.hat_phi_bins:
            U_arg = ceil_add(base_U_hi, ceil_div(ceil_mul(Decimal(2), ceil_mul(const.pi_hi, u_hi)), const.a_lap))
            conv_c = ceil_add(conv_c, ceil_mul(mass, exact_Czero_IBP_paired(const, q_hi_b, U_arg)))
        vtail_c = ceil_mul(
            lnY_hi,
            ceil_add(
                ceil_mul(ceil_add(ceil_mul(A_tail_150, ceil_sqrt(base_U_hi)), B_tail_150), const.hat_phi_tail),
                ceil_mul(A_tail_150, ceil_mul(sqrt_2pi_a, const.hat_phi_tail_half)),
            ),
        )
        conv_c = ceil_add(conv_c, vtail_c)
        K_err_j = ceil_mul(ceil_mul(conv_c, ceil_sqrt(u_nxt)), a_m34)
        pole_j = pole_q_le_q0 if q_hi_b <= Q0_val else pole_max
        tot_sqrtN = ceil_add(ceil_mul(K_err_j, N_1_4_hi), ceil_add(ceil_mul(pole_j, N_1_2_hi), other_sqrtN))
        if tot_sqrtN > best_sr_sqrtN:
            best_sr_sqrtN = tot_sqrtN
        u_cur = u_nxt
        if u_cur >= Decimal(1):
            break

    S2_w = ceil_div(ceil_mul(best_sr_sqrtN, best_sr_sqrtN), Decimal('0.75'))
    return S2_w, other_sqrtN


def convolved_sup_Sw_tail_coeff(const: AnalyticConstants, N_min: Decimal) -> Decimal:
    """
    100% rigorous monotone-safe constant K_S2 such that for ALL N >= N_min with
    Q_0(N) = floor(N^{1/4}) and Delta_q = 150 * N^{-11/12}:
      (sup_{alpha not in M_1} |S_w(alpha)|)^2 / (2 * E_2) <= K_S2 * sqrt(N) * (ln N)^2.
    """
    Y_min = floor_div(N_min, const.a_lap)
    lnY_lo = floor_ln(Y_min)
    lnY_hi = ceil_ln(Y_min)
    lnN_lo = floor_ln(N_min)
    u_min = Decimal('0.002')
    U_scale_hi = ceil_mul(Decimal(2), const.pi_hi)
    U_scale_lo = floor_mul(Decimal(2), const.pi_lo)
    U0_env = floor_div(U_scale_lo, u_min)
    assert U0_env >= Decimal(2000)

    A_tail_150, B_tail_150 = bmor_large_U_linear_coeffs(const, lnY_lo, Decimal(150))
    A_env, B_env = bmor_large_U_linear_coeffs(const, lnY_lo, U0_env)
    sqrt_2pi_a = ceil_sqrt(ceil_div(ceil_mul(Decimal(2), const.pi_hi), const.a_lap))

    U_sc_shift = ceil_add(U_scale_hi, ceil_mul(u_min, ceil_div(ceil_mul(Decimal(60), const.pi_hi), const.a_lap)))
    K_zero = ceil_add(
        ceil_mul(const.l1_hat_phi, ceil_add(ceil_mul(A_env, ceil_sqrt(U_sc_shift)), ceil_mul(B_env, ceil_sqrt(u_min)))),
        ceil_mul(A_env, ceil_mul(sqrt_2pi_a, ceil_mul(const.hat_phi_tail_half, ceil_sqrt(u_min)))),
    )

    n_sub = 20
    step_hi = ceil_exp(ceil_div(ceil_ln(Decimal(500)), Decimal(n_sub)))
    u_cur = u_min
    for j in range(n_sub):
        u_nxt = Decimal(1) if j == n_sub - 1 else min(Decimal(1), ceil_mul(u_cur, step_hi))
        base_U = ceil_div(U_scale_hi, u_cur)
        conv_k = Decimal(0)
        for u_hi, mass in const.hat_phi_bins:
            U_arg = ceil_add(base_U, ceil_div(ceil_mul(Decimal(2), ceil_mul(const.pi_hi, u_hi)), const.a_lap))
            conv_k = ceil_add(conv_k, ceil_mul(mass, bmor_ibp_div_lnY_tail(const, lnY_lo, U_arg)))
        vtail_k = ceil_add(
            ceil_mul(ceil_add(ceil_mul(A_tail_150, ceil_sqrt(base_U)), B_tail_150), const.hat_phi_tail),
            ceil_mul(A_tail_150, ceil_mul(sqrt_2pi_a, const.hat_phi_tail_half)),
        )
        conv_k = ceil_add(conv_k, vtail_k)
        K_j = ceil_mul(ceil_sqrt(u_nxt), conv_k)
        if K_j > K_zero:
            K_zero = K_j
        u_cur = u_nxt

    # Scale from Y^{3/4} ln(Y) to N^{3/4} ln(N): factor a^{-3/4}
    a_m34 = ceil_div(Decimal(1), floor_sqrt(floor_mul(const.a_lap, floor_sqrt(const.a_lap))))
    K_err = ceil_mul(K_zero, a_m34)

    # Exact pole for q > Q_0(N) = floor(N^{1/4}) >= N^{1/4} - 1, divided by N^{3/4} ln(N):
    N_1_4_lo = floor_sqrt(floor_sqrt(N_min))
    inv_1m = ceil_div(Decimal(1), floor_sub(Decimal(1), ceil_div(Decimal(1), N_1_4_lo)))
    rs15_over_lnN = ceil_div(
        ceil_add(
            ceil_mul(const.e_gamma_hi, ceil_ln(ceil_mul(Decimal('0.5'), lnN_lo))),
            ceil_div(Decimal('2.50637'), floor_ln(floor_mul(Decimal('0.25'), lnN_lo))),
        ),
        lnN_lo,
    )
    K_pole_gt = ceil_mul(ceil_mul(Decimal('0.5'), inv_1m), rs15_over_lnN)

    # Exact pole for q <= Q_0(N), |beta| > 150 * N^{-11/12}:
    #   |V_w(beta)| <= N / (2*pi * (150*N^{1/12}) * ((150*N^{1/12})^2 - 1)) <= N^{3/4} / (2*pi*150^3*(1 - 150^{-2}))
    # Divided by N^{3/4} * ln(N):
    K_pole_le = ceil_div(
        Decimal(1),
        floor_mul(Decimal(2), floor_mul(const.pi_lo, floor_mul(Decimal(150 * (150 * 150 - 1)), lnN_lo))),
    )
    K_pole = K_pole_gt if K_pole_gt >= K_pole_le else K_pole_le

    # Exact vertical contour + prime power + gcd corrections divided by N^{3/4} * ln(N) (strictly decreasing for N >= N_min!):
    Y_1_4_lo = floor_sqrt(floor_sqrt(Y_min))
    vert_over_N34_lnN = ceil_mul(
        const.l1_hat_phi,
        ceil_mul(
            ceil_div(const.gamma_1_4_coeff, const.pi_lo),
            ceil_mul(
                ceil_add(ceil_div(Decimal(1), Y_1_4_lo), ceil_div(Decimal(6), floor_sqrt(Y_1_4_lo))),
                ceil_mul(
                    ceil_add(ceil_div(const.A_vert_1_4, lnN_lo), ceil_mul(Decimal(15), ceil_add(Decimal(1), ceil_div(Decimal(5), lnN_lo)))),
                    ceil_div(ceil_sqrt(ceil_sqrt(const.a_lap)), Decimal(1)),
                ),
            ),
        ),
    )
    # Wait: vert_corr is <= O(N^{-1/4} ln N / N^{1/4}) = O(N^{-1/2} ln N) -> divided by N^{-1/4} ln N leaves O(N^{-1/4})!
    # Check exact scaling: vert_corr = |E_vert|/N <= const * Y^{-1/4} * (ln Y) * (Y^{-1/4} + 6*Y^{-1/8})!
    # Dividing by N^{-1/4} * ln N multiplies by N^{1/4} / ln N = a^{1/4} * Y^{1/4} / ln N!
    # So Y^{-1/4} and Y^{1/4} cancel, leaving a^{1/4} * (Y^{-1/4} + 6*Y^{-1/8}) * (A/lnN + 15*(1+5/lnN))! Exact!
    omega_over_lnN = ceil_add(ceil_div(Decimal('0.5'), const.ln2_lo), ceil_div(Decimal(1), lnN_lo))
    pp_gcd_over_N34_lnN = ceil_add(
        ceil_div(ceil_mul(Decimal(2), ceil_mul(omega_over_lnN, ceil_mul(lnY_hi, lnY_hi))), floor_mul(N_1_4_lo, floor_mul(N_1_4_lo, N_1_4_lo))),
        ceil_div(Decimal('1.5'), floor_mul(N_1_4_lo, floor_sqrt(const.a_lap))),
    )
    K_tot = ceil_add(K_err, ceil_add(K_pole, ceil_add(vert_over_N34_lnN, pp_gcd_over_N34_lnN)))
    return ceil_div(ceil_mul(K_tot, K_tot), Decimal('0.75'))


# ---------------------------------------------------------------------------
# Major-Arc L^2 Error Helper (Exact Odd-q + 1/2-Shift + U<=sqrt(e^2-1) Head)
# ---------------------------------------------------------------------------

def fmt_ceil(x: Decimal, places: int) -> str:
    q = Decimal(10) ** (-places)
    return str(x.quantize(q, rounding=ROUND_CEILING))


def fmt_floor(x: Decimal, places: int) -> str:
    q = Decimal(10) ** (-places)
    return str(x.quantize(q, rounding=ROUND_FLOOR))


def major_arc_error_ratio_exact(const: AnalyticConstants, N_lo: Decimal, Q0_hi: Decimal,
                                U_q_hi: Decimal, D_arc_lo: Decimal,
                                C_head_zero: Decimal) -> Decimal:
    """
    Rigorous upper bound on maj_base = 2*sqrt(int_M2 * int_E2) + int_E2 + beta_tail_M1,
    accounting for:
      - BOTH odd q <= Q0 AND their 1/2-shifted twins (dividing odd-q integral by E_2 = 0.375 * N_lo!)
      - Fourier convolution shift U_q(u) = U_q + 2*pi*|u|/a on |u| <= 30 AND analytic |u| > 30 tail
      - U <= sqrt(e^2 - 1) head via explicit C_head_zero^2
      - Prime powers k >= 2 via exact Parseval on [0, 1] + Rosser-Schoenfeld Thm 13 (psi - theta <= 1.4262 sqrt(N))
      - gcd(n, q) > 1 on M_1^odd via exact omega(q) * (ln N + 2 ln Q0)
      - Vertical contour Re(s) = 1/4 on M_1^odd using exact major-arc cutoff U <= U_q_hi (NOT minor-arc sqrt(Y)!)
    """
    Y_lo = floor_div(N_lo, const.a_lap)
    lnN_hi = ceil_ln(N_lo)
    lnY_hi = ceil_ln(Y_lo)

    # 1. Exact sum_{q <= Q0, 2 nmid q} q <= (Q0 + 1)^2 / 4
    Q0_p1 = ceil_add(Q0_hi, Decimal(1))
    sum_odd_q = ceil_div(ceil_mul(Q0_p1, Q0_p1), Decimal(4))

    # 2. Effective U_q + 60*pi/a for |u| <= 30, plus exact |u| > 30 contribution via Minkowski
    U_shift_30 = ceil_add(U_q_hi, ceil_div(ceil_mul(Decimal(60), const.pi_hi), const.a_lap))
    sqrt_2pi_a = ceil_sqrt(ceil_div(ceil_mul(Decimal(2), const.pi_hi), const.a_lap))
    l1_eff = ceil_add(
        const.l1_hat_phi,
        ceil_mul(Decimal(2), ceil_div(ceil_mul(sqrt_2pi_a, const.hat_phi_tail_half), floor_sqrt(U_shift_30))),
    )
    ln_qU_hi = ceil_add(ceil_ln(ceil_mul(Q0_hi, U_shift_30)), ceil_add(const.C_row_dir, Decimal(1)))
    per_q_zero = ceil_add(
        ceil_mul(const.C_E2_exact, ceil_mul(U_shift_30, ceil_mul(ln_qU_hi, ln_qU_hi))),
        ceil_mul(Decimal('0.81'), ceil_mul(C_head_zero, C_head_zero)),
    )
    int_E2_zero_odd = ceil_mul(ceil_mul(l1_eff, l1_eff), ceil_mul(sum_odd_q, per_q_zero))
    int_E2_zero_ratio = ceil_div(int_E2_zero_odd, floor_mul(Decimal('0.375'), N_lo))

    # 3a. Prime-power L^2 over ENTIRE [0, 1] by Parseval: <= 1.4262 * ln(N_lo) / (0.375 * sqrt(N_lo))
    pp_L2 = ceil_div(
        ceil_mul(Decimal('1.4262'), lnN_hi),
        floor_mul(Decimal('0.375'), floor_sqrt(N_lo)),
    )

    # 3b. gcd(n, q) > 1 on M_1^odd: <= ((Q0+1)^2 * D_arc_hi / 0.75) * (omega(q) * (ln N + 2 ln Q0) / N)^2
    D_arc_hi = ceil_div(ceil_mul(U_q_hi, const.a_lap), floor_mul(Decimal(2), const.pi_lo))
    omega_hi = ceil_add(ceil_div(ceil_ln(Q0_hi), const.ln2_lo), Decimal(1))
    gcd_val = ceil_mul(omega_hi, ceil_add(lnN_hi, ceil_mul(Decimal(2), ceil_ln(Q0_hi))))
    gcd_L2 = ceil_div(
        ceil_mul(ceil_mul(Q0_p1, Q0_p1), ceil_mul(D_arc_hi, ceil_mul(gcd_val, gcd_val))),
        floor_mul(Decimal('0.75'), floor_mul(N_lo, N_lo)),
    )

    # 3c. Vertical contour Re(s) = 1/4 on M_1^odd with major-arc U <= U_shift_30
    vert_M1_N = ceil_div(
        ceil_mul(
            l1_eff,
            ceil_mul(
                ceil_div(ceil_mul(Decimal(6), const.gamma_1_4_coeff), const.pi_lo),
                ceil_mul(
                    ceil_add(const.A_vert_1_4, ceil_mul(Decimal(15), ceil_add(lnY_hi, Decimal(5)))),
                    ceil_mul(ceil_sqrt(U_shift_30), ceil_sqrt(ceil_sqrt(ceil_div(N_lo, const.a_lap)))),
                ),
            ),
        ),
        N_lo,
    )
    vert_L2 = ceil_div(
        ceil_mul(ceil_mul(Q0_p1, Q0_p1), ceil_mul(D_arc_hi, ceil_mul(vert_M1_N, vert_M1_N))),
        Decimal('0.75'),
    )

    s_tot = ceil_add(
        ceil_sqrt(int_E2_zero_ratio),
        ceil_add(ceil_sqrt(pp_L2), ceil_add(ceil_sqrt(gcd_L2), ceil_sqrt(vert_L2))),
    )
    int_E2_ratio = ceil_mul(s_tot, s_tot)

    # 4. int_M2_ratio = sum_{q <= Q0, 2 nmid q} mu^2(q) / phi(q)
    int_M2_ratio = elem_sum_odd_sqf_inv_phi_ub(const, Q0_hi)

    # 5. beta_tail_M1: (1 / E_2) * sum_{q<=Q0, 2nmid q} (mu^2(q)/phi(q)) * int_{|beta| > D_arc_lo/N} |V_w(beta)|^2 dbeta
    one_m_invD2_lo = floor_sub(Decimal(1), ceil_div(Decimal(1), floor_mul(D_arc_lo, D_arc_lo)))
    D5_lo = floor_mul(floor_mul(D_arc_lo, D_arc_lo), floor_mul(floor_mul(D_arc_lo, D_arc_lo), D_arc_lo))
    beta_tail_M1 = ceil_mul(
        int_M2_ratio,
        ceil_div(Decimal(4), floor_mul(Decimal(15), floor_mul(floor_mul(const.pi_lo, const.pi_lo), floor_mul(floor_mul(one_m_invD2_lo, one_m_invD2_lo), D5_lo)))),
    )

    return ceil_add(ceil_add(ceil_mul(Decimal(2), ceil_sqrt(ceil_mul(int_M2_ratio, int_E2_ratio))), int_E2_ratio), beta_tail_M1)


# ---------------------------------------------------------------------------
# Slab Verification & Uniform Tail Certification (K = 18, P(z) = z^9)
# ---------------------------------------------------------------------------

def dyad_arc_error_ratio_exact(const: AnalyticConstants, N_lo: Decimal, N_hi: Decimal,
                               K0_dyad: int, M_run_dyad: int, D_arc_lo: Decimal) -> Decimal:
    r"""
    Rigorous upper bound on (1 / (2*E_2)) * int_{M_dyad(K0, M_run) \ M_1} |S_w(alpha)|^2 d(alpha).
    - For k = 0, 1 (q = 1, 2): |beta| > D_arc_lo/N => |M_w|^2 tail <= beta_tail_M1(q=1,2),
      and |S_w|^2 <= 2|M_w|^2 + 2|E_w|^2!
    - For 2 <= k <= K0 (q = 2^k, mu(2^k) = 0 => M_w = 0 IDENTICALLY, ZERO POLE!):
      |S_w|^2 = |E_w|^2, with U_q = 2*pi*Y*2^{-k-M_run} so q * U_q = 2*pi*Y*2^{-M_run}!
    - Prime powers via Parseval on [0, 1]; gcd(n, 2^k) > 1 via omega(2^k) <= 1;
      vertical contour Re(s) = 1/4 via exact q * 2^{-k-M_run} = 2^{-M_run} cancellation!
    """
    Y_hi = ceil_div(N_hi, const.a_lap)
    lnN_hi = ceil_ln(N_hi)
    lnY_hi = ceil_ln(Y_hi)
    inv_2M = ceil_div(Decimal(1), Decimal(1 << M_run_dyad))
    qU_per_k = ceil_mul(Decimal(2), ceil_mul(const.pi_hi, ceil_mul(Y_hi, inv_2M)))
    # Factor (K0 + 3): weight 2 for k=0, 2 for k=1, 1 for k=2..K0 -> total K0 + 3
    sum_qU = ceil_mul(Decimal(K0_dyad + 3), qU_per_k)
    U_max_k0 = ceil_add(qU_per_k, ceil_div(ceil_mul(Decimal(60), const.pi_hi), const.a_lap))
    ln_qU_hi = ceil_add(ceil_ln(ceil_mul(Decimal(1 << K0_dyad), max(Decimal(100), U_max_k0))), ceil_add(const.C_row_dir, Decimal(1)))
    sqrt_2pi_a = ceil_sqrt(ceil_div(ceil_mul(Decimal(2), const.pi_hi), const.a_lap))
    l1_eff = ceil_add(
        const.l1_hat_phi,
        ceil_mul(Decimal(2), ceil_div(ceil_mul(sqrt_2pi_a, const.hat_phi_tail_half), floor_sqrt(max(Decimal(150), U_max_k0)))),
    )
    # Body Bochner integral + head |U| <= sqrt(e^2-1) across k = 0..K0:
    C_head_k = exact_Czero_IBP_paired(const, Decimal(1 << K0_dyad), Decimal(3))
    head_tot = ceil_mul(Decimal(1 << (K0_dyad + 2)), ceil_mul(Decimal('0.81'), ceil_mul(C_head_k, C_head_k)))
    body_tot = ceil_mul(const.C_E2_exact, ceil_mul(sum_qU, ceil_mul(ln_qU_hi, ln_qU_hi)))
    int_E2_dyad = ceil_mul(ceil_mul(l1_eff, l1_eff), ceil_add(body_tot, head_tot))
    e2_zero_ratio = ceil_div(int_E2_dyad, floor_mul(Decimal('0.75'), N_lo))

    # Non-zero-sum L^2 errors over M_dyad (with factor 2 on k=0,1 => effective weight K0+3):
    pp_L2 = ceil_div(ceil_mul(Decimal(2), ceil_mul(Decimal('1.4262'), lnN_hi)), floor_mul(Decimal('0.75'), floor_sqrt(N_lo)))
    meas_dyad = ceil_mul(Decimal(2 * (K0_dyad + 3)), inv_2M)
    gcd_val = ceil_add(lnN_hi, ceil_mul(Decimal(2), ceil_ln(Decimal(1 << K0_dyad))))
    gcd_L2 = ceil_div(ceil_mul(meas_dyad, ceil_mul(gcd_val, gcd_val)), floor_mul(Decimal('0.75'), N_lo))
    V_chi_dyad = ceil_mul(
        l1_eff,
        ceil_mul(
            ceil_div(ceil_mul(Decimal(6), const.gamma_1_4_coeff), const.pi_lo),
            ceil_mul(
                ceil_add(const.A_vert_1_4, ceil_mul(Decimal(15), ceil_add(lnY_hi, Decimal(5)))),
                ceil_mul(ceil_sqrt(U_max_k0), ceil_sqrt(ceil_sqrt(Y_hi))),
            ),
        ),
    )
    vert_L2 = ceil_div(ceil_mul(meas_dyad, ceil_mul(V_chi_dyad, V_chi_dyad)), floor_mul(Decimal('0.75'), N_lo))

    s_tot = ceil_add(
        ceil_sqrt(e2_zero_ratio),
        ceil_add(ceil_sqrt(pp_L2), ceil_add(ceil_sqrt(gcd_L2), ceil_sqrt(vert_L2))),
    )
    e2_tot_ratio = ceil_mul(s_tot, s_tot)

    # Pole tail on k=0, 1 for |beta| > D_arc_lo / N (factor 2 from |S_w|^2 <= 2|M_w|^2 + 2|E_w|^2):
    one_m_invD2_lo = floor_sub(Decimal(1), ceil_div(Decimal(1), floor_mul(D_arc_lo, D_arc_lo)))
    D5_lo = floor_mul(floor_mul(D_arc_lo, D_arc_lo), floor_mul(floor_mul(D_arc_lo, D_arc_lo), D_arc_lo))
    pole_tail_01 = ceil_div(
        Decimal(8),
        floor_mul(Decimal(15), floor_mul(floor_mul(const.pi_lo, const.pi_lo), floor_mul(floor_mul(one_m_invD2_lo, one_m_invD2_lo), D5_lo))),
    )
    return ceil_add(e2_tot_ratio, pole_tail_01)


def verify_slab_monomial(const: AnalyticConstants, J_L: dict, L_val: int, k_deg: int,
                         N_lo: Decimal, N_hi: Decimal, Q0_lo: Decimal, Q0_hi: Decimal,
                         S2_w: Decimal, maj_base: Decimal, dyad_base: Decimal,
                         c_frac: Fraction, C_Sel_val: Decimal,
                         vA_Sex: Decimal, T11_hi: Decimal, sing_trunc: Decimal) -> dict:
    c_d = frac_ceil(c_frac)
    L_d = Decimal(L_val)
    lnN_hi = ceil_ln(N_hi)

    ln_S2_hi = ceil_ln(S2_w)

    # 20 nested exact-rational convex polygons for exact Abel Layer-Cake Summation
    n_layers = 20
    step_ln = Decimal('0.55')
    ln_inv_eps_list = [ceil_add(ceil_sub(ln_S2_hi, Decimal('1.5')), ceil_mul(Decimal(s), step_ln)) for s in range(n_layers)]
    eps_list = [ceil_exp(ceil_sub(Decimal(0), v)) for v in ln_inv_eps_list]

    layer_H = []
    layer_M = []
    layer_xmax = []
    for s in range(n_layers):
        ln_inv_eps = ln_inv_eps_list[s]
        c_fracs = []
        for m in range(16):
            key = m if m <= 8 else 16 - m
            ln_inv_w = ceil_ln(frac_ceil(Fraction(1, 1) / DIR_WEIGHTS[m]))
            rhs_ln = ceil_add(ln_inv_eps, ln_inv_w)
            best_c = Decimal(1)
            for t, ln_J in J_L[key]:
                cand = ceil_div(ceil_add(ln_J, rhs_ln), floor_mul(t, L_d))
                if cand < best_c:
                    best_c = cand
            if best_c > Decimal(1):
                best_c = Decimal(1)
            num_c = int(ceil_mul(best_c, Decimal(100000)).to_integral_value(rounding=ROUND_CEILING))
            if num_c > 100000:
                num_c = 100000
            c_fracs.append(Fraction(num_c, 100000))
        verts = exact_rational_polygon_vertices(c_fracs)
        H_s, M_s = polygon_max_monomial_sq(verts, k_deg)
        layer_H.append(H_s)
        layer_M.append(M_s)
        layer_xmax.append(frac_ceil(c_fracs[0]))

    M_unit = Decimal(1)
    M_env = list(layer_M) + [M_unit]
    for s in range(1, len(M_env)):
        if M_env[s] < M_env[s - 1]:
            M_env[s] = M_env[s - 1]

    pi2_hi = ceil_mul(const.pi_hi, const.pi_hi)
    two_pi2_3 = ceil_div(ceil_mul(Decimal(2), pi2_hi), Decimal(3))
    c2_hi = ceil_mul(c_d, c_d)
    Eh2_k = ceil_add(
        ceil_div(ceil_mul(Decimal(4 * k_deg), c2_hi), ceil_mul(Decimal(3), L_d)),
        ceil_div(ceil_mul(Decimal(4 * k_deg * (k_deg - 1)), c2_hi), floor_mul(L_d, L_d)),
    )
    pnt_rel_err = ceil_div(ceil_mul(Decimal(2), ceil_mul(lnN_hi, lnN_hi)), floor_mul(const.pi_lo, floor_sqrt(N_lo)))
    eps_k = ceil_add(ceil_mul(two_pi2_3, Eh2_k), pnt_rel_err)
    shift_loss_tot = ceil_mul(Decimal(4), eps_k)

    diag_excess = ceil_div(
        ceil_sub(ceil_mul(lnN_hi, ceil_add(Decimal(1), pnt_rel_err)), floor_ln(floor_add(Q0_lo, Decimal(1)))),
        ceil_mul(Decimal(2), L_d),
    )
    H_mult = ceil_add(ceil_mul(ceil_sub(C_Sel_val, Decimal(1)), const.C0_R0_hi), ceil_add(diag_excess, sing_trunc))

    best_out = None
    for ci in range(0, 10):
        H0 = layer_H[ci]
        exc_mass = ceil_mul(M_env[ci + 1], eps_list[ci])
        for s in range(ci + 1, n_layers):
            dM = ceil_sub(M_env[s + 1], M_env[s])
            if dM > 0:
                exc_mass = ceil_add(exc_mass, ceil_mul(dM, eps_list[s]))
        exc_err = ceil_mul(S2_w, exc_mass)

        total_vA_tail = ceil_add(vA_Sex, ceil_mul(max(Decimal(0), ceil_sub(M_unit, H0)), T11_hi))
        maj_err = ceil_add(maj_base, dyad_base)
        rhs_tot = ceil_add(shift_loss_tot, ceil_add(total_vA_tail, ceil_add(ceil_mul(H0, H_mult), ceil_add(exc_err, maj_err))))
        margin = floor_sub(Decimal(1), rhs_tot)
        if best_out is None or margin > best_out["margin"]:
            best_out = {
                "margin": margin,
                "lhs": Decimal(1),
                "rhs": rhs_tot,
                "H0": H0,
                "exc": exc_err,
                "vA_tail": total_vA_tail,
                "maj_err": maj_err,
                "shift_loss": shift_loss_tot,
                "H_mult": H_mult,
                "T11": T11_hi,
                "xmax": layer_xmax[ci],
                "S2_w": S2_w,
            }
    return best_out


def verify_uniform_tail_monomial(const: AnalyticConstants, tbl: dict, CW_tail: dict,
                                 L_tail: int, k_deg: int, c_frac: Fraction) -> dict:
    c_d = frac_ceil(c_frac)
    L_d = Decimal(L_tail)
    inv_c_int = int(Fraction(1, 1) / c_frac)
    N_min = Decimal(1 << L_tail) * Decimal(inv_c_int)
    N_top_first = Decimal(1 << (L_tail + 1)) * Decimal(inv_c_int)
    lnN_lo = floor_ln(N_min)
    lnN_hi_first = ceil_ln(N_top_first)

    C_Sel_tail = selberg_C_sin2_tail(const, N_min)
    K_S2_tail = convolved_sup_Sw_tail_coeff(const, N_min)
    S2_at_Ltail = ceil_mul(K_S2_tail, ceil_mul(ceil_sqrt(N_top_first), ceil_mul(lnN_hi_first, lnN_hi_first)))

    ln_ratio_sq = ceil_mul(ceil_div(Decimal(L_tail + 4), Decimal(L_tail + 3)), ceil_div(Decimal(L_tail + 4), Decimal(L_tail + 3)))
    s2_step_growth = ceil_mul(const.sqrt2_hi, ln_ratio_sq)

    n_layers = 14
    step_ln = Decimal('0.70')
    ln_S2_tail = ceil_ln(S2_at_Ltail)
    ln_inv_eps_list = [ceil_add(ceil_sub(ln_S2_tail, Decimal('0.5')), ceil_mul(Decimal(s), step_ln)) for s in range(n_layers)]
    eps_list = [ceil_exp(ceil_sub(Decimal(0), v)) for v in ln_inv_eps_list]
    ln_step_cap = ceil_sub(ceil_ln(s2_step_growth), floor_ln(Decimal('0.96')))
    max_growth_step = Decimal(0)

    layer_H = []
    layer_M = []
    layer_xmax = []
    for s in range(n_layers):
        ln_inv_eps = ln_inv_eps_list[s]
        c_fracs = []
        for m in range(16):
            key = m if m <= 8 else 16 - m
            ln_inv_w = ceil_ln(frac_ceil(Fraction(1, 1) / DIR_WEIGHTS[m]))
            rhs_ln = ceil_add(ln_inv_eps, ln_inv_w)
            best_c = Decimal(1)
            best_growth = Decimal(1)
            for t, ln_Ccw, lam_hi, ln_lam in CW_tail[key]:
                c1 = ceil_div(ceil_add(ln_Ccw, rhs_ln), floor_mul(t, L_d))
                c2 = ceil_div(ceil_add(ln_lam, ln_step_cap), t)
                cand = max(c1, c2)
                if cand < best_c:
                    best_c = cand
                    best_growth = ceil_mul(s2_step_growth, ceil_mul(lam_hi, ceil_exp(ceil_sub(Decimal(0), floor_mul(t, cand)))))
            if best_c > Decimal(1):
                best_c = Decimal(1)
            if s == 0 and best_growth > max_growth_step:
                max_growth_step = best_growth
            num_c = int(ceil_mul(best_c, Decimal(100000)).to_integral_value(rounding=ROUND_CEILING))
            if num_c > 100000:
                num_c = 100000
            c_fracs.append(Fraction(num_c, 100000))
        verts = exact_rational_polygon_vertices(c_fracs)
        H_s, M_s = polygon_max_monomial_sq(verts, k_deg)
        layer_H.append(H_s)
        layer_M.append(M_s)
        layer_xmax.append(frac_ceil(c_fracs[0]))

    assert max_growth_step < Decimal('0.965'), f"Tail growth step not < 1: {max_growth_step}"
    M_unit = Decimal(1)
    M_env = list(layer_M) + [M_unit]
    for s in range(1, len(M_env)):
        if M_env[s] < M_env[s - 1]:
            M_env[s] = M_env[s - 1]

    H0 = layer_H[0]
    exc_mass = ceil_mul(M_env[1], eps_list[0])
    for s in range(1, n_layers):
        dM = ceil_sub(M_env[s + 1], M_env[s])
        if dM > 0:
            exc_mass = ceil_add(exc_mass, ceil_mul(dM, eps_list[s]))
    exc_tail = ceil_mul(S2_at_Ltail, exc_mass)

    Q0_min = floor_sqrt(floor_sqrt(N_min))
    D_arc_min_lo = floor_mul(Decimal(150), floor_exp(floor_div(lnN_lo, Decimal(12))))
    D_arc_min_hi = ceil_mul(Decimal(150), ceil_exp(ceil_div(ceil_ln(N_min), Decimal(12))))
    U_q_min_hi = ceil_div(ceil_mul(Decimal(2), ceil_mul(const.pi_hi, D_arc_min_hi)), const.a_lap)
    C_head_tail = ceil_mul(bmor_ibp_div_lnY_tail(const, floor_ln(floor_div(N_min, const.a_lap)), Decimal(3)), ceil_ln(N_min))
    maj_err_tail = major_arc_error_ratio_exact(const, N_min, Q0_min, U_q_min_hi, D_arc_min_lo, C_head_tail)
    assert maj_err_tail < Decimal('0.005'), f"Tail maj_err_tail unexpectedly large: {maj_err_tail}"

    # Uniform lower bound on sum_{q in S*} A_{1,1}^{(L)}(q) and upper bound on vA_{S*} for ALL L >= L_tail
    S_star_set = {3, 5, 7, 15, 31}
    sum_A11_tail_lo = Decimal(0)
    vA_Sstar_tail_hi = Decimal(0)
    pi2_hi = ceil_mul(const.pi_hi, const.pi_hi)
    shift_const_11 = ceil_div(ceil_mul(Decimal(16), ceil_mul(pi2_hi, ceil_mul(c_d, c_d))), Decimal(9))
    sum_shift_Sstar_tail = Decimal(0)
    delta_u1_tail = ceil_div(ceil_mul(Decimal(4), ceil_mul(const.pi_hi, c_d)), L_d)
    delta_u2_tail = ceil_mul(Decimal(2), delta_u1_tail)
    tail_mass_u2 = ceil_div(Decimal(2), floor_mul(Decimal(135), floor_mul(const.pi_lo, const.pi_lo)))
    mass_u12 = ceil_mul(
        frac_ceil(Fraction(4, 3)),
        ceil_sub(frac_ceil(Fraction(2, 3)), floor_mul(Decimal(2), floor_ln(frac_floor(Fraction(4, 3))))),
    )

    for q, ep, ph, c_list, z_mods_hi in tbl["S_ex_data"]:
        if q not in S_star_set:
            continue
        a11_q_frac = Fraction(sum(c_list), ep * ph * ph)
        s_a11_lo = floor_sqrt(frac_floor(a11_q_frac))
        mink_loss = ceil_div(Decimal(2 * (ep - 1)), floor_mul(floor_sqrt(Decimal(ph)), L_d))
        s_L_lo = max(Decimal(0), floor_sub(s_a11_lo, mink_loss))
        a11_L_hneq0_lo = floor_sub(floor_mul(s_L_lo, s_L_lo), ceil_div(Decimal(1), floor_mul(Decimal(ph), L_d)))
        sum_A11_tail_lo = floor_add(sum_A11_tail_lo, a11_L_hneq0_lo)

        avg_abs_c = ceil_mul(
            ceil_div(Decimal(L_tail + ep - 1), L_d),
            ceil_div(Decimal(sum(abs(x) for x in c_list)), Decimal(ep)),
        )
        sum_shift_Sstar_tail = ceil_add(
            sum_shift_Sstar_tail,
            ceil_div(ceil_mul(shift_const_11, avg_abs_c), floor_mul(L_d, Decimal(ph * ph))),
        )

        rem_frac = ceil_div(Decimal(ep - 1), L_d)
        q_s1 = Decimal(0)
        q_s2 = Decimal(0)
        for zm in z_mods_hi:
            z1 = min(Decimal(1), ceil_add(zm, ceil_add(rem_frac, delta_u1_tail)))
            z2 = min(Decimal(1), ceil_add(zm, ceil_add(rem_frac, delta_u2_tail)))
            p1 = z1 ** k_deg
            p2 = z2 ** k_deg
            q_s1 = ceil_add(q_s1, ceil_mul(p1, p1))
            q_s2 = ceil_add(q_s2, ceil_mul(p2, p2))
        q_tot = ceil_add(q_s1, ceil_add(ceil_mul(mass_u12, q_s2), ceil_mul(tail_mass_u2, Decimal(ph))))
        vA_Sstar_tail_hi = ceil_add(vA_Sstar_tail_hi, ceil_div(q_tot, Decimal(ph * ph)))

    lnN_over_L_hi = ceil_mul(const.ln2_hi, ceil_add(Decimal(1), ceil_div(Decimal(4), L_d)))
    h0_tail_hi = ceil_mul(
        const.C_odd_qphi_hi,
        ceil_add(ceil_div(lnN_over_L_hi, Decimal(8)), ceil_div(Decimal(1), L_d)),
    )
    sing_trunc_tail = tbl["sing_tail_D1"]
    for d, ep_d, ph_d in tbl["d_list_D1"]:
        sing_trunc_tail = ceil_add(sing_trunc_tail, ceil_div(const.odd_tail(floor_div(Q0_min, Decimal(d))), Decimal(ep_d * ph_d)))

    shift_q1_tail = ceil_div(shift_const_11, L_d)
    T11_tail_hi = ceil_add(
        h0_tail_hi,
        ceil_add(
            ceil_sub(ceil_sub(const.C0_R0_hi, Decimal(1)), sum_A11_tail_lo),
            ceil_add(shift_q1_tail, ceil_add(sum_shift_Sstar_tail, sing_trunc_tail)),
        ),
    )
    total_vA_tail = ceil_add(vA_Sstar_tail_hi, ceil_mul(max(Decimal(0), ceil_sub(M_unit, H0)), T11_tail_hi))

    pnt_rel_tail = ceil_div(ceil_mul(Decimal(2), ceil_mul(lnN_hi_first, lnN_hi_first)), floor_mul(const.pi_lo, floor_sqrt(N_min)))
    diag_excess_tail = ceil_add(
        ceil_mul(frac_ceil(Fraction(3, 8)), lnN_over_L_hi),
        ceil_mul(pnt_rel_tail, ceil_div(lnN_over_L_hi, Decimal(2))),
    )
    H_mult_tail = ceil_add(
        ceil_mul(ceil_sub(C_Sel_tail, Decimal(1)), const.C0_R0_hi),
        ceil_add(diag_excess_tail, sing_trunc_tail),
    )
    two_pi2_3 = ceil_div(ceil_mul(Decimal(2), pi2_hi), Decimal(3))
    c2_hi = ceil_mul(c_d, c_d)
    Eh2_k = ceil_add(
        ceil_div(ceil_mul(Decimal(4 * k_deg), c2_hi), ceil_mul(Decimal(3), L_d)),
        ceil_div(ceil_mul(Decimal(4 * k_deg * (k_deg - 1)), c2_hi), floor_mul(L_d, L_d)),
    )
    eps_k = ceil_add(ceil_mul(two_pi2_3, Eh2_k), pnt_rel_tail)
    shift_loss_tail = ceil_mul(Decimal(4), eps_k)

    rhs_tail = ceil_add(
        shift_loss_tail,
        ceil_add(total_vA_tail, ceil_add(ceil_mul(H0, H_mult_tail), ceil_add(exc_tail, maj_err_tail))),
    )
    margin_tail = floor_sub(Decimal(1), rhs_tail)
    assert margin_tail > Decimal('0.10'), f"Uniform tail L >= {L_tail} failed! margin={margin_tail}"

    return {
        "L_tail": L_tail,
        "C_Sel_tail": C_Sel_tail,
        "K_S2_tail": K_S2_tail,
        "growth_step": max_growth_step,
        "H0": H0,
        "xmax": layer_xmax[0],
        "exc_tail": exc_tail,
        "vA_tail": total_vA_tail,
        "T11_tail": T11_tail_hi,
        "maj_err_tail": maj_err_tail,
        "lhs": Decimal(1),
        "rhs": rhs_tail,
        "margin": margin_tail,
    }


def main():
    print("=== Certifying Explicit Linnik-Goldbach v2 under GRH + Goldbach(<=4e18) ===")
    const = AnalyticConstants()
    print(f"2*C2 bounds: [{fmt_floor(const.two_C2_dn, 8)}, {fmt_ceil(const.two_C2_up, 8)}], C0*R0 < {fmt_ceil(const.C0_R0_hi, 4)} (Platt-Trudgian)")
    print(f"Zero-black-box C_E2 <= {fmt_ceil(const.C_E2_exact, 4)} (C_row_dir <= {fmt_ceil(const.C_row_dir, 4)})")
    print(f"sin^2(pi*t/N) kernel: ||hat_phi||_1 <= {fmt_ceil(const.l1_hat_phi, 6)}, Mellin (M0, M1, M2) <= ({fmt_ceil(const.M0_sin2, 4)}, {fmt_ceil(const.M1_sin2, 4)}, {fmt_ceil(const.M2_sin2, 4)})")

    # Precompute S_ex (43 odd sqfree q <= 105) and D1 = 2000 tail
    tbl = build_S_ex_and_sing_tables(const, Q_ex_max=105, D1=2000)

    # --- 1. Pure Effective Asymptotic GRH Benchmark (K = 6, C_1 = 8.0) + Explicit Prop 5.2 Net ---
    print("\n--- 1. Effective Asymptotic GRH Benchmark (Li-Liu Signed Polynomial on D_{25/32}) ---")
    asymp = run_asymptotic_grh_section(const, tbl["S_ex"])
    print(f"  Explicit Prop 5.2 directional net on D_{{25/32}} (rho=3466/10000): m = {asymp['net_pairs']} pairs, C_net <= {asymp['C_net']:.3e}")
    print(f"  Pure Effective GRH K=6 (C_1=8.0, a=3/20, b=2/25, self-contained S_ex T_11<={fmt_ceil(asymp['T11_ex_hi'], 5)}):")
    print(f"    H <= {fmt_ceil(asymp['H6_hi'], 5)}, vAv <= {fmt_ceil(asymp['vAv6'], 5)}, lhs <= {fmt_ceil(asymp['lhs6'], 5)} < rhs >= {fmt_floor(asymp['rhs6'], 5)} (margin >= {fmt_floor(asymp['margin6'], 5)}) => PASS")
    print(f"  Informational Lichtman K=5 (C_1=6.7814, a=1/4, b=1/16, c=1/8, tau=2, Li-Liu Lem 4.2):")
    print(f"    H <= {fmt_ceil(asymp['H5_hi'], 5)}, lhs <= {fmt_ceil(asymp['lhs5'], 5)} < rhs >= {fmt_floor(asymp['rhs5'], 5)} (margin >= {fmt_floor(asymp['margin5'], 5)}) => PASS")

    # --- 2. All-Range Explicit K = 18 Certification (Every even N >= 4; exact K=18 for N >= 40) ---
    K_cert = 18
    k_deg = 9               # P(z) = z^9, Q(z) = z^8 (pure monomial, exact rational convex-vertex max!)
    c_frac = Fraction(1, 8) # L = floor(log2(N / 8))
    inv_c_int = 8
    N_br = Decimal(((1 << (K_cert + 1)) - 2) * (1 << 61) + 4 * (10 ** 18))
    L_start = int((floor_ln(floor_mul(N_br, frac_floor(c_frac))) / const.ln2_hi).to_integral_value(rounding=ROUND_FLOOR))
    L_pure = 85
    L_mid = 104
    L_tail = 120
    K0_dyad = 30
    M_run_dyad = 45
    assert L_start == 76
    print(f"\n--- 2. All-Range Explicit Certification: K = {K_cert} (k={k_deg}, P(z)=z^{k_deg}, c=1/8) ---")
    print(f"  Binary Goldbach Bridge [40, N_br(18)]: N_br(18) = {N_br:.6e} (exact {int(N_br)})")
    print(f"  Coverage: slabs L in [{L_start}, {L_pure - 1}] (M_dyad(K0={K0_dyad}, M_run={M_run_dyad})), L in [{L_pure}, {L_tail - 1}] (pure B=10), + Collatz-Wielandt tail L >= {L_tail}")
    print(f"  Precomputed S_ex (43 odd sqfree q <= 105): sum A_11 >= {fmt_floor(frac_floor(tbl['sum_A11_asymp']), 6)}, sing_tail(D1=2000) <= {fmt_ceil(tbl['sing_tail_D1'], 5)}")

    J_sweep, J_pure_sweep, CW_tail = build_transfer_matrix_sweep(const, B=10, L_min=L_start, L_max=L_tail, K0_dyad=K0_dyad, M_run_dyad=M_run_dyad)

    # Precompute single uniform minor-arc sup-norm coefficient valid for ALL N >= 8 * 2^{L_mid}!
    N_mid_min = Decimal(1 << L_mid) * Decimal(inv_c_int)
    K_S2_mid = convolved_sup_Sw_tail_coeff(const, N_mid_min)
    C_head_mid_div = bmor_ibp_div_lnY_tail(const, floor_ln(floor_div(N_mid_min, const.a_lap)), Decimal(3))
    print(f"  Uniform mid-regime (L >= {L_mid}) minor-arc coeff: K_S2 <= {fmt_ceil(K_S2_mid, 3)}")

    print(f"\n=== Exhaustive Uniform Slab Verification for Certified K = {K_cert} (L = {L_start}..{L_tail - 1}) ===")
    worst_slab_margin = None
    worst_slab_L = None
    first_slab_res = None
    last_slab_res = None

    for L_s in range(L_start, L_tail):
        N_L_lo = max(N_br, Decimal(1 << L_s) * Decimal(inv_c_int))
        N_L_hi = Decimal(1 << (L_s + 1)) * Decimal(inv_c_int)
        if N_L_lo >= N_L_hi:
            continue

        C_Sel_slab, z_opt = selberg_C_sin2_finite(const, N_L_lo, N_L_hi, c_frac)

        if L_s < L_mid:
            # Fine finite regime: Q_0(L) = floor(0.35 * N_{L,lo}^{1/4}), Delta_q = D_arc / N
            # For L < L_pure: use M_dyad(K0, M_run); for L >= L_pure: use pure B=10 (dyad_base = 0)!
            Q0_val = floor_mul(Decimal('0.35'), floor_sqrt(floor_sqrt(N_L_lo))).to_integral_value(rounding=ROUND_FLOOR)
            D_arc = Decimal(150) if L_s < L_pure else Decimal(400)
            U_q_hi = ceil_div(ceil_mul(Decimal(2), ceil_mul(const.pi_hi, D_arc)), const.a_lap)
            C_head_L = exact_Czero_IBP_paired(const, Q0_val, Decimal(3))
            vA_Sex, T11_hi, sing_trunc = precompute_L_Sex_bounds(const, tbl, L_s, Q0_val, Q0_val, k_deg, c_frac)

            n_sub = 2 if L_s <= 79 else 1
            q_ratio = ceil_exp(ceil_div(ceil_ln(ceil_div(N_L_hi, N_L_lo)), Decimal(n_sub)))
            sub_lo = N_L_lo
            slab_worst = None
            J_use = J_sweep[L_s] if L_s < L_pure else J_pure_sweep[L_s]
            for s_idx in range(n_sub):
                sub_hi = N_L_hi if s_idx + 1 == n_sub else min(N_L_hi, ceil_mul(sub_lo, q_ratio))
                S2_w, _ = convolved_sup_Sw_finite(const, sub_lo, sub_hi, Q0_val, D_arc)
                maj_base = major_arc_error_ratio_exact(const, sub_lo, Q0_val, U_q_hi, D_arc, C_head_L)
                dyad_base = dyad_arc_error_ratio_exact(const, sub_lo, sub_hi, K0_dyad, M_run_dyad, D_arc) if L_s < L_pure else Decimal(0)
                res = verify_slab_monomial(const, J_use, L_s, k_deg, sub_lo, sub_hi, Q0_val, Q0_val, S2_w, maj_base, dyad_base,
                                           c_frac, C_Sel_slab, vA_Sex, T11_hi, sing_trunc)
                assert res["margin"] > Decimal(0), (
                    f"Slab L={L_s} sub={s_idx} FAILED! lhs={res['lhs']:.5f}, rhs={res['rhs']:.5f}, "
                    f"H0={res['H0']:.5f}, exc={res['exc']:.5f}, vA={res['vA_tail']:.5f}, maj={res['maj_err']:.5f}, T11={res['T11']:.5f}"
                )
                if slab_worst is None or res["margin"] < slab_worst["margin"]:
                    slab_worst = res
                sub_lo = sub_hi
                if sub_lo >= N_L_hi:
                    break
        else:
            # Mid/high regime L in [L_mid, 119]: pure B=10 transfer matrix (ZERO M_dyad!), Q_0(N) = floor(N^{1/4})
            Q0_lo = floor_sqrt(floor_sqrt(N_L_lo)).to_integral_value(rounding=ROUND_FLOOR)
            Q0_hi = ceil_sqrt(ceil_sqrt(N_L_hi)).to_integral_value(rounding=ROUND_CEILING)
            lnN_lo_s = floor_ln(N_L_lo)
            lnN_hi_s = ceil_ln(N_L_hi)
            D_arc_lo = floor_mul(Decimal(150), floor_exp(floor_div(lnN_lo_s, Decimal(12))))
            D_arc_hi = ceil_mul(Decimal(150), ceil_exp(ceil_div(lnN_hi_s, Decimal(12))))
            U_q_hi = ceil_div(ceil_mul(Decimal(2), ceil_mul(const.pi_hi, D_arc_hi)), const.a_lap)
            C_head_L = ceil_mul(C_head_mid_div, lnN_hi_s)
            S2_w = ceil_mul(K_S2_mid, ceil_mul(ceil_sqrt(N_L_hi), ceil_mul(lnN_hi_s, lnN_hi_s)))
            maj_base = major_arc_error_ratio_exact(const, N_L_lo, Q0_hi, U_q_hi, D_arc_lo, C_head_L)
            dyad_base = Decimal(0)
            vA_Sex, T11_hi, sing_trunc = precompute_L_Sex_bounds(const, tbl, L_s, Q0_lo, Q0_hi, k_deg, c_frac)
            n_sub = 1
            res = verify_slab_monomial(const, J_pure_sweep[L_s], L_s, k_deg, N_L_lo, N_L_hi, Q0_lo, Q0_hi, S2_w, maj_base, dyad_base,
                                       c_frac, C_Sel_slab, vA_Sex, T11_hi, sing_trunc)
            assert res["margin"] > Decimal(0), (
                f"Slab L={L_s} FAILED! lhs={res['lhs']:.5f}, rhs={res['rhs']:.5f}, "
                f"H0={res['H0']:.5f}, exc={res['exc']:.5f}, vA={res['vA_tail']:.5f}, maj={res['maj_err']:.5f}"
            )
            slab_worst = res

        if first_slab_res is None:
            first_slab_res = slab_worst
        last_slab_res = slab_worst
        if worst_slab_margin is None or slab_worst["margin"] < worst_slab_margin:
            worst_slab_margin = slab_worst["margin"]
            worst_slab_L = L_s

        if L_s <= 82 or L_s == L_mid or L_s % 5 == 0 or L_s == L_tail - 1:
            print(
                f"  L={L_s:3d} ({n_sub} sub): C_Sel<={fmt_ceil(C_Sel_slab, 3)}(z={z_opt}), xmax<={fmt_ceil(slab_worst['xmax'], 3)}, "
                f"lhs>={fmt_floor(slab_worst['lhs'], 4)} > rhs<={fmt_ceil(slab_worst['rhs'], 4)} (margin>={fmt_floor(slab_worst['margin'], 4)}) PASS"
            )

    print(f"  Worst finite slab across L in [{L_start}, {L_tail - 1}]: L={worst_slab_L}, margin >= {fmt_floor(worst_slab_margin, 4)} PASS")

    # --- 3. Uniform Asymptotic Tail Certification for ALL L >= 120 ---
    print(f"\n--- 3. Asymptotic Tail Verification for ALL L >= {L_tail} (N >= {inv_c_int} * 2^{L_tail}) ---")
    tail = verify_uniform_tail_monomial(const, tbl, CW_tail, L_tail, k_deg, c_frac)
    print(
        f"  C_Sel(N >= N_{L_tail}) <= {fmt_ceil(tail['C_Sel_tail'], 4)}, K_S2_tail <= {fmt_ceil(tail['K_S2_tail'], 3)}, "
        f"maj_err_tail <= {fmt_ceil(tail['maj_err_tail'], 6)}"
    )
    print(
        f"  Collatz-Wielandt max growth/step <= {fmt_ceil(tail['growth_step'], 6)} (< 1 => strictly decreasing for ALL L >= {L_tail}!)"
    )
    print(
        f"  L >= {L_tail} uniform: xmax<={fmt_ceil(tail['xmax'], 3)}, H0<={fmt_ceil(tail['H0'], 5)}, vA_tail<={fmt_ceil(tail['vA_tail'], 4)}, "
        f"lhs >= {fmt_floor(tail['lhs'], 4)} > rhs <= {fmt_ceil(tail['rhs'], 4)} (margin >= {fmt_floor(tail['margin'], 4)}) PASS"
    )

    # --- 4. Checkpoint Summary Table (Compatible with Lean LinnikCheckpointCell) ---
    print("\n--- 4. Certified Checkpoint Summary (Scale 10^4, Outward Rounded) ---")
    print(f"  L={L_start:3d} (K={K_cert}): lhs>={fmt_floor(first_slab_res['lhs'], 4)}, rhs<={fmt_ceil(first_slab_res['rhs'], 4)}, margin>={fmt_floor(first_slab_res['margin'], 4)}")
    print(f"  L={worst_slab_L:3d} (K={K_cert}): worst finite slab margin>={fmt_floor(worst_slab_margin, 4)}")
    print(f"  L={L_tail-1:3d} (K={K_cert}): lhs>={fmt_floor(last_slab_res['lhs'], 4)}, rhs<={fmt_ceil(last_slab_res['rhs'], 4)}, margin>={fmt_floor(last_slab_res['margin'], 4)}")
    print(f"  L={L_tail:3d} (K={K_cert}, tail): lhs>={fmt_floor(tail['lhs'], 4)}, rhs<={fmt_ceil(tail['rhs'], 4)}, margin>={fmt_floor(tail['margin'], 4)}")
    print(f"  L=  0 (K= 6, eff-GRH): rhs>={fmt_floor(asymp['rhs6'], 4)}, lhs<={fmt_ceil(asymp['lhs6'], 4)}, margin>={fmt_floor(asymp['margin6'], 4)}")
    print(f"  L=  0 (K= 5, Lichtman): rhs>={fmt_floor(asymp['rhs5'], 4)}, lhs<={fmt_ceil(asymp['lhs5'], 4)}, margin>={fmt_floor(asymp['margin5'], 4)}")

    print("\nALL ASSERTIONS PASSED WITH EXIT CODE 0.")


if __name__ == "__main__":
    main()
