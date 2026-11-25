#!/usr/bin/env python3
"""
Checker for note X26 (research/goldbach/notes/X26-all-even-1p4-under-grh.md).

Claim checked: under GRH, every even N >= 4 is p + eta with p prime and
Omega(eta) <= 4.  Regime 1 (N <= 4e18) is the Goldbach verification; this
script checks Regime 2 (30 slabs on [4e18, 1e170)) and Regime 3 (N >= 1e170),
plus a benchmark that reproduces a published number with the same sieve table.

Arithmetic guarantee:
  No float and no math module.  Real quantities are enclosed in intervals
  Iv(lo, hi) of decimal.Decimal at PREC = 90 digits; every operation that can
  round is done inside a localcontext with ROUND_FLOOR (lo) or ROUND_CEILING
  (hi).  Negation uses copy_negate (exact).  Integer quantities are Python
  ints and are compared exactly.  As a mechanical audit, main() sets the
  traps Inexact and Rounded in the default Decimal context: any Decimal
  operation that rounds outside a directed context raises and the run fails.

Sources (all quoted in the note, section 0):
  [BJS]  Bordignon-Johnston-Starichkova, arXiv:2207.09452v6: Theorem 6 (linear
         sieve) + Table 1; Lemma 16, Lemma 17 (Mertens); Lemma 19 (f, F);
         Lemma 23 (squarefree count); Lemma 38 (V(x)).
  [JS]   Johnston-Starichkova, arXiv:2208.01229v3 (numbering of the v3 PDF):
         Lemma 3.1 (|A| > N/log N), Lemma 3.2 (Mertens), Lemma 5.1 (GRH bound
         for pi(x;q,a)), Lemma 5.7, Lemma 5.8, Theorem 5.9 (benchmark only).
  [BS]   Bordignon-Starichkova, arXiv:2211.08844v1: Lemma 1 (Schoenfeld under
         RH, as quoted there), Lemma 4 (Robin omega bound), Lemma 5 (Buthe
         squarefree sums).
"""

from decimal import (Decimal, localcontext, getcontext, ROUND_FLOOR, ROUND_CEILING,
                     Inexact, Rounded)
from fractions import Fraction

PREC = 90

# Audit (set before any computation, so it also covers the module-level constants):
# any Decimal operation that rounds in the default context raises decimal.Inexact /
# decimal.Rounded.  Directed helpers below switch these traps off inside their own
# localcontext; the two heuristic contexts (choice of a scaling exponent, whose result
# is re-verified in interval arithmetic) do the same and are marked HEURISTIC.
getcontext().traps[Inexact] = True
getcontext().traps[Rounded] = True

# ---------------------------------------------------------------------------
# Outward-rounded Decimal primitives & Interval Arithmetic Iv(lo, hi)
# ---------------------------------------------------------------------------

def _round_floor(a: Decimal) -> Decimal:
    with localcontext() as ctx:
        ctx.prec = PREC
        ctx.rounding = ROUND_FLOOR
        ctx.traps[Inexact] = False
        ctx.traps[Rounded] = False
        return +a

def _round_ceil(a: Decimal) -> Decimal:
    with localcontext() as ctx:
        ctx.prec = PREC
        ctx.rounding = ROUND_CEILING
        ctx.traps[Inexact] = False
        ctx.traps[Rounded] = False
        return +a

def _add(a: Decimal, b: Decimal, r) -> Decimal:
    with localcontext() as ctx:
        ctx.prec = PREC
        ctx.rounding = r
        ctx.traps[Inexact] = False
        ctx.traps[Rounded] = False
        return a + b

def _sub(a: Decimal, b: Decimal, r) -> Decimal:
    with localcontext() as ctx:
        ctx.prec = PREC
        ctx.rounding = r
        ctx.traps[Inexact] = False
        ctx.traps[Rounded] = False
        return a - b

def _mul(a: Decimal, b: Decimal, r) -> Decimal:
    with localcontext() as ctx:
        ctx.prec = PREC
        ctx.rounding = r
        ctx.traps[Inexact] = False
        ctx.traps[Rounded] = False
        return a * b

def _div(a: Decimal, b: Decimal, r) -> Decimal:
    with localcontext() as ctx:
        ctx.prec = PREC
        ctx.rounding = r
        ctx.traps[Inexact] = False
        ctx.traps[Rounded] = False
        return a / b

def _sqrt(a: Decimal, r) -> Decimal:
    with localcontext() as ctx:
        ctx.prec = PREC
        ctx.rounding = r
        ctx.traps[Inexact] = False
        ctx.traps[Rounded] = False
        return a.sqrt()

def _neg(a: Decimal) -> Decimal:
    # exact: copy_negate does not consult the context (unary minus does round)
    return a.copy_negate()

class Iv:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        if not isinstance(lo, Decimal):
            lo = Decimal(lo)
        if not isinstance(hi, Decimal):
            hi = Decimal(hi)
        lo = _round_floor(lo)
        hi = _round_ceil(hi)
        if lo > hi:
            raise ValueError(f"Invalid interval: [{lo}, {hi}]")
        self.lo = lo
        self.hi = hi

    @classmethod
    def from_frac(cls, f: Fraction):
        return cls(Decimal(f.numerator)) / cls(Decimal(f.denominator))

    def __repr__(self):
        return f"Iv({self.lo}, {self.hi})"

    def __neg__(self):
        return Iv(_neg(self.hi), _neg(self.lo))

    def __add__(self, other):
        o = other if isinstance(other, Iv) else Iv(other)
        return Iv(_add(self.lo, o.lo, ROUND_FLOOR), _add(self.hi, o.hi, ROUND_CEILING))

    def __radd__(self, other):
        return Iv(other) + self

    def __sub__(self, other):
        o = other if isinstance(other, Iv) else Iv(other)
        return Iv(_sub(self.lo, o.hi, ROUND_FLOOR), _sub(self.hi, o.lo, ROUND_CEILING))

    def __rsub__(self, other):
        return Iv(other) - self

    def __mul__(self, other):
        o = other if isinstance(other, Iv) else Iv(other)
        p_lo = (
            _mul(self.lo, o.lo, ROUND_FLOOR),
            _mul(self.lo, o.hi, ROUND_FLOOR),
            _mul(self.hi, o.lo, ROUND_FLOOR),
            _mul(self.hi, o.hi, ROUND_FLOOR),
        )
        p_hi = (
            _mul(self.lo, o.lo, ROUND_CEILING),
            _mul(self.lo, o.hi, ROUND_CEILING),
            _mul(self.hi, o.lo, ROUND_CEILING),
            _mul(self.hi, o.hi, ROUND_CEILING),
        )
        return Iv(min(p_lo), max(p_hi))

    def __rmul__(self, other):
        return Iv(other) * self

    def __truediv__(self, other):
        o = other if isinstance(other, Iv) else Iv(other)
        if o.lo <= 0 <= o.hi:
            raise ZeroDivisionError(f"Interval division straddles zero: {o}")
        q_lo = (
            _div(self.lo, o.lo, ROUND_FLOOR),
            _div(self.lo, o.hi, ROUND_FLOOR),
            _div(self.hi, o.lo, ROUND_FLOOR),
            _div(self.hi, o.hi, ROUND_FLOOR),
        )
        q_hi = (
            _div(self.lo, o.lo, ROUND_CEILING),
            _div(self.lo, o.hi, ROUND_CEILING),
            _div(self.hi, o.lo, ROUND_CEILING),
            _div(self.hi, o.hi, ROUND_CEILING),
        )
        return Iv(min(q_lo), max(q_hi))

    def __rtruediv__(self, other):
        return Iv(other) / self

    def __pow__(self, n: int):
        if not isinstance(n, int) or n < 0:
            raise ValueError("Only non-negative integer powers supported directly")
        if n == 0:
            return Iv(1, 1)
        if n == 1:
            return self
        res = Iv(1, 1)
        base = self
        e = n
        while e > 0:
            if e & 1:
                res = res * base
            e >>= 1
            if e > 0:
                base = base * base
        return res

    def sqrt(self):
        if self.lo < 0:
            raise ValueError(f"sqrt of negative interval {self}")
        return Iv(_sqrt(self.lo, ROUND_FLOOR), _sqrt(self.hi, ROUND_CEILING))

    def abs_hi(self) -> Decimal:
        return max(_neg(self.lo), self.hi)

# ---------------------------------------------------------------------------
# Transcendental functions ln, exp, pi, gamma via elementary Iv series
# ---------------------------------------------------------------------------

def _ln2_iv() -> Iv:
    # ln(2) = 2 * sum_{k=0}^\infty 1 / ((2k+1) * 3^(2k+1))
    # Tail after N=100 terms: < 2 / (201 * 3^201) / (1 - 1/9) < 10^-97
    N = 100
    s = Iv(0, 0)
    pow3 = 3
    for k in range(N):
        denom = (2 * k + 1) * pow3
        s = s + Iv.from_frac(Fraction(1, denom))
        pow3 *= 9
    tail = Iv(Decimal(0), Decimal("1e-95"))
    return Iv(2, 2) * (s + tail)

LN2 = _ln2_iv()

def _ln_point_iv(x: Decimal) -> Iv:
    if x <= 0:
        raise ValueError(f"ln of non-positive {x}")
    if x == 1:
        return Iv(0, 0)
    # Scale x by 2^k into [0.75, 1.5]
    k = 0
    m = Iv(x, x)
    half = Iv(Decimal("0.5"), Decimal("0.5"))
    two = Iv(2, 2)
    # Fast coarse power-of-2 scaling via string exponent estimate
    with localcontext() as ctx:  # HEURISTIC: only picks the scaling exponent k_est
        ctx.prec = 30
        ctx.traps[Inexact] = False
        ctx.traps[Rounded] = False
        adj = x.adjusted()
    k_est = int(adj * 3321928 // 1000000)
    if k_est > 0:
        scale = Iv(Decimal(1 << k_est), Decimal(1 << k_est))
        m = m / scale
        k += k_est
    elif k_est < 0:
        scale = Iv(Decimal(1 << (-k_est)), Decimal(1 << (-k_est)))
        m = m * scale
        k += k_est
    while m.hi > Decimal("1.5"):
        m = m * half
        k += 1
    while m.lo < Decimal("0.75"):
        m = m * two
        k -= 1
    # Now m in [0.75, 1.5] -> u = (m - 1)/(m + 1) has |u| <= 0.2
    u = (m - Iv(1, 1)) / (m + Iv(1, 1))
    if u.abs_hi() > Decimal("0.21"):
        raise AssertionError(f"ln reduction failed: m={m}, u={u}")
    u2 = u * u
    # ln(m) = 2 * sum_{j=0}^{N-1} u^(2j+1)/(2j+1) + R_N
    # |R_N| <= 2 * 0.21^(2N+1) / ((2N+1) * (1 - 0.21^2))
    # For N = 70: 0.21^141 < 10^-95
    N = 70
    term = u
    s = Iv(0, 0)
    for j in range(N):
        s = s + term / Iv(2 * j + 1, 2 * j + 1)
        term = term * u2
    err = Decimal("1e-90")
    ln_m = Iv(2, 2) * s + Iv(_neg(err), err)
    return ln_m + Iv(k, k) * LN2

def ln_iv(x: Iv) -> Iv:
    lo_iv = _ln_point_iv(x.lo)
    hi_iv = _ln_point_iv(x.hi)
    return Iv(lo_iv.lo, hi_iv.hi)

def _exp_point_iv(x: Decimal) -> Iv:
    if x == 0:
        return Iv(1, 1)
    # x = k * ln(2) + r with |r| <= 0.4
    with localcontext() as ctx:  # HEURISTIC: only picks k; |r| <= 0.4 is re-checked in Iv below
        ctx.prec = 30
        ctx.traps[Inexact] = False
        ctx.traps[Rounded] = False
        k = int((x / LN2.lo).to_integral_value())
    r = Iv(x, x) - Iv(k, k) * LN2
    while r.hi > Decimal("0.4"):
        k += 1
        r = Iv(x, x) - Iv(k, k) * LN2
    while r.lo < Decimal("-0.4"):
        k -= 1
        r = Iv(x, x) - Iv(k, k) * LN2
    # Taylor sum_{j=0}^{N-1} r^j / j! + R_N
    # |R_N| <= 0.4^N / (N! * (1 - 0.4/(N+1)))
    # For N = 60: 0.4^60 / 60! < 2e-106
    N = 60
    s = Iv(1, 1)
    term = Iv(1, 1)
    for j in range(1, N):
        term = term * r / Iv(j, j)
        s = s + term
    err = Decimal("1e-90")
    exp_r = s + Iv(_neg(err), err)
    if k >= 0:
        pow2 = Iv(Decimal(1 << k), Decimal(1 << k))
        return exp_r * pow2
    else:
        pow2 = Iv(Decimal(1 << (-k)), Decimal(1 << (-k)))
        return exp_r / pow2

def exp_iv(x: Iv) -> Iv:
    lo_iv = _exp_point_iv(x.lo)
    hi_iv = _exp_point_iv(x.hi)
    return Iv(lo_iv.lo, hi_iv.hi)

def pow_real_iv(base: Iv, exponent: Iv) -> Iv:
    return exp_iv(exponent * ln_iv(base))

# ---------------------------------------------------------------------------
# Fundamental Mathematical Constants (computed from first principles in Iv)
# ---------------------------------------------------------------------------

def _atan_inv_iv(m: int, terms: int) -> Iv:
    # Alternating series atan(1/m) = sum_k (-1)^k / ((2k+1) m^(2k+1)).
    # Partial sums with an even number n_lo of terms are lower bounds, with
    # n_hi = n_lo + 1 terms upper bounds (terms decrease to 0).
    # Denominators are exact Python ints; Decimal(int) is exact; the only
    # rounding is the directed division below.
    s_lo = Decimal(0)
    s_hi = Decimal(0)
    n_lo = 2 * (terms // 2)
    n_hi = n_lo + 1
    pow_m = m          # exact int m^(2k+1)
    m2 = m * m
    for k in range(n_hi):
        denom = Decimal(pow_m * (2 * k + 1))
        if k % 2 == 0:
            t_lo = _div(Decimal(1), denom, ROUND_FLOOR)
            t_hi = _div(Decimal(1), denom, ROUND_CEILING)
            if k < n_lo:
                s_lo = _add(s_lo, t_lo, ROUND_FLOOR)
            s_hi = _add(s_hi, t_hi, ROUND_CEILING)
        else:
            t_lo = _div(Decimal(1), denom, ROUND_CEILING)
            t_hi = _div(Decimal(1), denom, ROUND_FLOOR)
            if k < n_lo:
                s_lo = _sub(s_lo, t_lo, ROUND_FLOOR)
            s_hi = _sub(s_hi, t_hi, ROUND_CEILING)
        pow_m = pow_m * m2
    return Iv(s_lo, s_hi)

PI = Iv(4, 4) * (Iv(4, 4) * _atan_inv_iv(5, 80) - _atan_inv_iv(239, 40))

def _compute_gamma_iv() -> Iv:
    # Euler-Maclaurin on sum_{k=1}^M 1/k - ln(M) with M = 1000, B_2..B_16
    M = 1000
    harmonic = Iv(0, 0)
    for k in range(1, M + 1):
        harmonic = harmonic + Iv(1, 1) / Iv(k, k)
    ln_M = ln_iv(Iv(M, M))
    # Even Bernoulli numbers B_2, B_4, ..., B_18
    bern = [
        Fraction(1, 6),          # B_2
        Fraction(-1, 30),        # B_4
        Fraction(1, 42),         # B_6
        Fraction(-1, 30),        # B_8
        Fraction(5, 66),         # B_10
        Fraction(-691, 2730),    # B_12
        Fraction(7, 6),          # B_14
        Fraction(-3617, 510),    # B_16
    ]
    b18_abs = Fraction(43867, 798)
    corr = Iv(0, 0)
    M2 = M * M
    pow_M = M2
    for idx, b in enumerate(bern):
        two_j = 2 * (idx + 1)
        term = Iv.from_frac(b / (two_j * pow_M))
        corr = corr + term
        pow_M *= M2
    rem_bound = Iv.from_frac(b18_abs / (18 * pow_M))
    rem = Iv(_neg(rem_bound.hi), rem_bound.hi)
    return harmonic - ln_M - Iv.from_frac(Fraction(1, 2 * M)) + corr + rem

GAMMA = _compute_gamma_iv()
E_GAMMA = exp_iv(GAMMA)
E_NEG_GAMMA = exp_iv(-GAMMA)

def sieve_primes(limit: int):
    is_p = bytearray([1]) * (limit + 1)
    is_p[0] = 0
    is_p[1] = 0
    r = int(Iv(limit, limit).sqrt().hi)
    for i in range(2, r + 1):
        if is_p[i]:
            is_p[i * i : limit + 1 : i] = bytearray(len(range(i * i, limit + 1, i)))
    return [i for i, v in enumerate(is_p) if v]

P_CUT = 30000
PRIMES = sieve_primes(P_CUT)

def _compute_twin_and_M0():
    # Twin prime constant C_2 = prod_{p>2} (1 - 1/(p-1)^2)
    # Tail error: sum_{p > P_CUT} 1/(p-1)^2 < sum_{n >= P_CUT} 1/n^2 < 1/(P_CUT - 1)
    c2_fin = Iv(1, 1)
    m0_corr = Iv(0, 0)
    for p in PRIMES:
        if p > 2:
            c2_fin = c2_fin * Iv.from_frac(Fraction((p - 1) * (p - 1) - 1, (p - 1) * (p - 1)))
        # M0 = gamma + sum_p (ln(1 - 1/p) + 1/p)
        inv_p = Iv(1, 1) / Iv(p, p)
        ln_1mp = ln_iv(Iv(1, 1) - inv_p)
        m0_corr = m0_corr + ln_1mp + inv_p
    tail_c2 = Iv(1, 1) - Iv(1, 1) / Iv(P_CUT - 1, P_CUT - 1)
    c2_iv = Iv((c2_fin * tail_c2).lo, c2_fin.hi)
    # Tail for M0: -sum_{p>P_CUT} sum_{k>=2} 1/(k p^k) in [-1/(P_CUT - 1), 0]
    tail_m0 = Iv((-Iv(1, 1) / Iv(P_CUT - 1, P_CUT - 1)).lo, 0)
    m0_iv = GAMMA + m0_corr + tail_m0
    return c2_iv, m0_iv

C2_TWIN, M0_CONST = _compute_twin_and_M0()
U_CONST = Iv(2, 2) * E_NEG_GAMMA * C2_TWIN

def li_exp_iv(u: Iv) -> Iv:
    # li(e^u) = gamma + ln(u) + sum_{k=1}^\infty u^k / (k * k!) for u > 0
    # Valid for all u > 0; for u <= 5, 60 terms suffices with negligible tail
    s = GAMMA + ln_iv(u)
    N = 60
    term = u
    for k in range(1, N):
        s = s + term / Iv(k, k)
        term = term * u / Iv(k + 1, k + 1)
    # Tail bound: term_N / (N * (1 - u / (N * (N+1))))
    u_hi = u.hi
    # Ensure u_hi < 10 so (N+1) >> u_hi
    if u_hi >= 10:
        raise ValueError("Use more terms for large u in li_exp_iv")
    tail = term / (Iv(N, N) * (Iv(1, 1) - u / Iv(N + 1, N + 1)))
    return s + Iv(0, tail.hi)

LI2 = li_exp_iv(LN2)
LI_E5 = li_exp_iv(Iv(5, 5))

# ---------------------------------------------------------------------------
# Number-theoretic helper bounds (100% outward-rounded Iv)
# ---------------------------------------------------------------------------

def c_pi_iv(log_X: Iv, X2_int=None) -> Iv:
    # [JS] Lemma 5.1 (v3 PDF; TeX label epilem), assuming GRH:
    #   for x >= X2 >= 4e18, 3 <= q <= sqrt(x), (a,q) = 1:
    #   |pi(x;q,a) - li(x)/phi(q)| <= c_pi(X2) sqrt(x) log x,
    #   c_pi(X2) = 3/(8 pi) + (6 + 1/pi)/(4 log X2) + 6/log^2 X2 + li(2)/(sqrt(X2) log X2).
    # Callers pass log X2 with X2 >= 4e18 (asserted) and use it only for moduli
    # 3 <= q <= sqrt(X2) <= sqrt(x) coprime to the residue N.
    if X2_int is not None:
        assert X2_int >= 4 * 10**18, "Lemma 5.1 needs X2 >= 4e18"
    else:
        assert log_X.lo >= ln_iv(Iv(4 * 10**18, 4 * 10**18)).hi, "Lemma 5.1 needs X2 >= 4e18"
    sqrt_X = exp_iv(Iv(Decimal("0.5"), Decimal("0.5")) * log_X)
    t1 = Iv(3, 3) / (Iv(8, 8) * PI)
    t2 = (Iv(6, 6) + Iv(1, 1) / PI) / (Iv(4, 4) * log_X)
    t3 = Iv(6, 6) / (log_X ** 2)
    t4 = LI2 / (sqrt_X * log_X)
    return t1 + t2 + t3 + t4

def r_coeff_iv(log_X: Iv, X2_int=None) -> Iv:
    # Coefficient of sqrt(N) log N in |pi(N;d,N) - pi(N)/phi(d)| for 3 <= d <= sqrt(N),
    # (d,N) = 1:  c_pi(X2) + 1/(16 pi).  The 1/(16 pi) is |pi(N) - li(N)|/phi(d) with
    # |pi(N) - li(N)| <= sqrt(N) log N/(8 pi) (Schoenfeld under RH, [BS] Lemma 1,
    # stated there for x >= 3) and phi(d) >= 2 for d >= 3.  This is the argument of
    # [JS] Lemma 5.7.  The total remainder bound is then
    #   |r(d)| <= (c_pi + 1/(16 pi)) sqrt(N) log N + omega(N)          (*)
    # with r(d) = |A_d| - |A|/phi(d), A = {N - p : p <= N, p nmid N}, because
    # |A| = pi(N) - omega(N), |A_d| = pi(N;d,N) - omega(N;d,N)  ([JS] Lemma 5.8 proof).
    return c_pi_iv(log_X, X2_int) + Iv(1, 1) / (Iv(16, 16) * PI)

def omega_ub_iv(log_X: Iv) -> Iv:
    # [BS] Lemma 4 (Robin): omega(N) < 1.3841 log N / log log N for N >= 3.
    # log N / log log N is increasing for log N > e, so callers pass the slab's upper end
    # when an upper bound uniform in the slab is needed.
    return Iv(Decimal("1.3841")) * log_X / ln_iv(log_X)

# Mertens-type bounds. Notation: E_<(x) := sum_{p<x} 1/p - log log x - M0.
#  [JS] Lemma 3.2 (3.1): sum_{p<x} 1/p >= loglog x + M0 - 2.964e-6/log x,  x >= 2
#  [JS] Lemma 3.2 (3.2): sum_{p<x} 1/p <= loglog x + M0 + 1.614e-3,        x > exp(8.9)
#  [JS] Lemma 3.2 (3.3): sum_{p<x} 1/p <= loglog x + M0 + 6.836e-6/log x,  x > 1e12
#  [BJS] Lemma 16: loglog x + M < sum_{p<=x} 1/p < loglog x + M + 2/(sqrt(x) log x),
#                  2 <= x <= 1e12   (and sum_{p<x} <= sum_{p<=x}).
TEN12 = Iv(10**12, 10**12)

def mertens_ub_err(z: Iv, log_z: Iv) -> Decimal:
    # Upper bound for E_<(x), uniform for every real x in the interval z (z.lo > exp(8.9)).
    assert log_z.lo > Decimal("8.9"), f"z too small for [JS] (3.2): {z}"
    bounds = []
    if z.lo <= TEN12.lo:
        # x in [z.lo, min(z.hi, 1e12)]: [BJS] Lemma 16 (2/(sqrt(x) log x), decreasing) or (3.2)
        x0 = Iv(z.lo, z.lo)
        b16 = (Iv(2, 2) / (x0.sqrt() * ln_iv(x0))).hi
        bounds.append(min(b16, Decimal("1.614e-3")))
    if z.hi > TEN12.lo:
        # x in (max(z.lo, 1e12), z.hi]: (3.3), 6.836e-6/log x decreasing in x
        x0 = Iv(max(z.lo, TEN12.lo), max(z.lo, TEN12.lo))
        bounds.append((Iv(Decimal("6.836e-6")) / ln_iv(x0)).hi)
    return max(bounds)

def sum_inv_p_ub(z: Iv, log_z: Iv) -> Iv:
    # upper bound on sum_{p < x} 1/p, uniform for x in z
    e = mertens_ub_err(z, log_z)
    return ln_iv(log_z) + M0_CONST + Iv(e, e)

def sum_inv_p_lb(z: Iv, log_z: Iv) -> Iv:
    # [JS] Lemma 3.2 (3.1): lower bound on sum_{p < x} 1/p, x >= 2
    assert z.lo >= 2
    err = Iv(Decimal("2.964e-6")) / log_z
    return ln_iv(log_z) + M0_CONST - err

def pi_ub_iv(z: Iv, log_z: Iv) -> Iv:
    # pi(x) <= li(x) + sqrt(x) log x/(8 pi) ([BS] Lemma 1, RH, x >= 3) and
    # li(x) < x/(log x - 2) for x >= e^5 (proved in the note; li(e^5) < e^5/3 asserted in main).
    if z.hi <= P_CUT:
        cnt = sum(1 for p in PRIMES if Decimal(p) <= z.hi)
        return Iv(cnt, cnt)
    assert log_z.lo >= 5
    return z / (log_z - Iv(2, 2)) + z.sqrt() * log_z / (Iv(8, 8) * PI)

# ---------------------------------------------------------------------------
# [BJS] Theorem 6 and Table 1 (arXiv:2207.09452v6), transcribed from the v6 source.
# Hypothesis of Theorem 6: 0 < eps <= 1/74 and, for all n and all 1 < u < z,
#     prod_{p in P \ Q, u <= p < z} (1 - g_n(p))^{-1} < (1 + eps) log z / log u.
# Columns: eps^{-1}, C_1(eps) (upper bound), C_2(eps) (lower bound).
# Use (see note, section 0.1): if the hypothesis holds with eps, it holds with every
# eps' in [eps, 1/74]; we apply the theorem with eps' = 1/k for the largest table row
# k <= 1/eps and use the tabulated C_i(1/k).  No interpolation, no monotonicity in eps.
# ---------------------------------------------------------------------------

BJS_TABLE = [
    (74, 631, 630), (76, 559, 559), (78, 504, 504), (80, 461, 461),
    (85, 386, 386), (90, 336, 337), (95, 302, 302), (100, 276, 277),
    (120, 218, 219), (140, 189, 190), (160, 172, 173), (180, 161, 162),
    (200, 153, 154), (300, 133, 134), (400, 125, 126), (500, 121, 122),
    (600, 118, 119), (700, 116, 117), (800, 115, 116), (900, 114, 115),
    (1000, 113, 114), (2000, 109, 110), (10000, 106, 108), (100000, 106, 107),
]

def lookup_BJS(eps_iv: Iv):
    """Return (k, C1, C2, eps_used = 1/k) with k the largest row such that eps <= 1/k
    (eps_iv.hi is used, so the hypothesis with eps implies it with 1/k)."""
    inv_lo = (Iv(1, 1) / Iv(eps_iv.hi, eps_iv.hi)).lo
    chosen = None
    for k, c1, c2 in BJS_TABLE:
        if Decimal(k) <= inv_lo:
            chosen = (k, c1, c2)
    assert chosen is not None, f"1/eps = {inv_lo} < 74: [BJS] Theorem 6 does not apply"
    k, c1, c2 = chosen
    return k, c1, c2, Iv(1, 1) / Iv(k, k)

# ---------------------------------------------------------------------------
# Benchmark 0: reproduce [JS] v3 Theorem 1.4 ranges and Theorem 5.9 at their parameters
# with the SAME table lookup that Regime 3 uses.
# ---------------------------------------------------------------------------

def verify_benchmark_0():
    print("=== BENCHMARK 0: Johnston-Starichkova (2208.01229v3), Thm 1.4 ranges and Thm 5.9 ===")
    # 1. Ranges in the proof of [JS] Theorem 1.4 (Lemma 3.5 / Proposition 5.6):
    #    K = largest integer with theta(p_{K+L+1}) - theta(p_{L+1}) < log X.
    def max_K_for_logX(L_plus_1: int, logX_val: Iv) -> int:
        s = Iv(0, 0)
        K = 0
        for p in PRIMES[L_plus_1:]:
            s = s + ln_iv(Iv(p, p))
            if s.hi < logX_val.lo:
                K += 1
            else:
                break
        return K

    log_X2 = exp_iv(Iv(Decimal("5.077")))
    k1 = max_K_for_logX(6, Iv(104, 104))
    k2 = max_K_for_logX(13, Iv(149, 149))
    k3 = max_K_for_logX(21, log_X2)
    print(f"  N < exp(104) (L+1=6):  K = {k1}")
    print(f"  N < exp(149) (L+1=13): K = {k2}")
    print(f"  N < exp(exp(5.077))={log_X2.lo:.4f} (L+1=21): K = {k3}")
    assert k1 <= 25 and k2 == 31 and k3 == 31

    # 2. [JS] Theorem 5.9 at X2 = exp(exp(5.077)), M = 18, alpha = 0.285, B = 2.01,
    #    eps = 1.312e-2 ([JS] Lemma 3.3), xi = 1244 ([JS] Lemma 3.4).  [JS] report
    #    S(A,P(z)) > 1.48 U_N N/log^2 N using C = 559.
    M = Iv(18, 18)
    alpha = Iv(Decimal("0.285"))
    B = Iv(Decimal("2.01"))
    eps_js = Iv(Decimal("1.312e-2"))
    k_tab, c1_int, c2_int, eps_used = lookup_BJS(eps_js)
    assert k_tab == 76 and c1_int == 559 and c2_int == 559
    C2 = Iv(c2_int, c2_int)
    xi = Iv(1244, 1244)
    s = M * (Iv(Decimal("0.5")) - alpha)  # 3.87, in [2, 4] where f(s) = 2e^gamma log(s-1)/s
    f_s = Iv(2, 2) * E_GAMMA * ln_iv(s - Iv(1, 1)) / s
    h_s = (Iv(3, 3) / s) * exp_iv(-s)
    pG = Iv(Decimal("0.65")) * r_coeff_iv(log_X2)         # [JS] Lemma 5.7
    sqrt_X2 = exp_iv(Iv(Decimal("0.5")) * log_X2)
    c4G = pG + Iv(Decimal("0.9")) / (sqrt_X2 * ln_iv(log_X2))  # [JS] Lemma 5.8
    e2 = exp_iv(Iv(2, 2))
    xi_fac = Iv(1, 1) - xi / (log_X2 ** 2)
    logX2_Bm2 = pow_real_iv(log_X2, B - Iv(2, 2))
    tail = (Iv(1, 1) / M) * (Iv(1, 1) / xi_fac) * (Iv(1, 1) / U_CONST) * (c4G / logX2_Bm2)
    for label, eC in [("JS: eps=1.312e-2 times C=559", eps_js * C2),
                      ("as Regime 3: eps'=1/76 times C2(1/76)=559", eps_used * C2)]:
        coeff = M * xi_fac * (f_s - eC * e2 * h_s - tail)
        print(f"  Theorem 5.9 ({label}): coeff in [{coeff.lo:.4f}, {coeff.hi:.4f}]")
        assert coeff.lo > Decimal("1.4"), "benchmark does not reproduce [JS] Theorem 5.9 (1.48)"

# ---------------------------------------------------------------------------
# Regime 2: Finite Slab Ladder [4*10^18, 10^170) for K = 4
# ---------------------------------------------------------------------------

def _comb(n: int, k: int) -> int:
    if k < 0 or k > n:
        return 0
    k = min(k, n - k)
    num = 1
    den = 1
    for i in range(1, k + 1):
        num *= n - k + i
        den *= i
    return num // den

def elem_sym_iv(weights, max_k):
    e = [Iv(0, 0)] * (max_k + 1)
    e[0] = Iv(1, 1)
    for w in weights:
        for k in range(max_k, 0, -1):
            e[k] = e[k] + w * e[k - 1]
    return e

def certify_slab_K4(X_lo: int, X_hi: int, M: int, a: int, m_odd: int, m_even: int):
    """
    Checks pi_4(N) > 0 for all even N in [X_lo, X_hi) (note, section 3):
      - A = {N - p : p <= N, p nmid N}; every element is coprime to N, so no
        correction term for N - p with p | N is needed (note, section 1)
      - integers z, y with z^M >= X_hi, y^5 > X_hi, z*y^4 >= X_hi
      - Q_1 = the first a odd primes (exact inclusion-exclusion on Q_1 minus primes | N)
      - P_2 = odd primes p_a < p < z (Bonferroni on P_2 minus primes | N)
      - lower sieve on S(A, P(z)): order m_odd on P_2   (Lemma 1)
      - upper sieve on S(A_q, P(z)), z <= q < y: order m_even on P_2 (m_even = 0:
        A_q is sieved by Q_1 only)
      - worst case over N in the slab by Lemma 2 (main term) and monotonicity (errors)
    Returns a dict with lower bound on pi_4(N) / (N / log N).
    """
    assert m_odd % 2 == 1 and m_even % 2 == 0
    X_lo_iv = Iv(X_lo, X_lo)
    X_hi_iv = Iv(X_hi, X_hi)
    logX_lo = ln_iv(X_lo_iv)
    logX_hi = ln_iv(X_hi_iv)

    # Integer z, y with rigorous verification that y^5 > X_hi and z * y^4 >= X_hi
    z_real = exp_iv(logX_hi / Iv(M, M))
    z = int(z_real.hi) + 1
    assert z ** M >= X_hi and z >= 3

    y1 = exp_iv(logX_hi / Iv(5, 5))
    y2 = exp_iv((logX_hi - ln_iv(Iv(z, z))) / Iv(4, 4))
    y = int(max(y1.hi, y2.hi)) + 1
    assert y ** 5 > X_hi and z * (y ** 4) >= X_hi and y > z

    z_iv = Iv(z, z)
    y_iv = Iv(y, y)
    log_z = ln_iv(z_iv)
    log_y = ln_iv(y_iv)

    # Q_1 primes: PRIMES[1 : a+1] (a odd primes starting at 3)
    Q1 = PRIMES[1 : a + 1]
    assert len(Q1) == a
    p_a = Q1[-1]
    assert p_a < z
    Q1_prod = 1
    for p in Q1:
        Q1_prod *= p

    # Max modulus checks (exact integers): d <= sqrt(X_lo) and y * d <= sqrt(X_lo),
    # so every modulus used lies in [3, sqrt(N)] as [JS] Lemma 5.1 requires.
    sqrt_X_lo = X_lo_iv.sqrt()
    if z <= P_CUT:
        P2 = [p for p in PRIMES if p_a < p < z]
        max_d_odd = Q1_prod
        for p in P2[-m_odd:]:
            max_d_odd *= p
        max_d_even = Q1_prod
        if m_even > 0:
            for p in P2[-m_even:]:
                max_d_even *= p
    else:
        max_d_odd = Q1_prod * (z ** m_odd)
        max_d_even = Q1_prod * (z ** m_even)
    assert max_d_odd * max_d_odd <= X_lo, f"max_d_odd={max_d_odd} > sqrt(X_lo)"
    assert (y * max_d_even) ** 2 <= X_lo, "y*max_d_even > sqrt(X_lo)"

    # V(Q1) and sum_{q1 | Q1} 1/phi(q1)
    V_Q1 = Iv(1, 1)
    inv_phi_Q1 = Iv(1, 1)
    for p in Q1:
        V_Q1 = V_Q1 * Iv.from_frac(Fraction(p - 2, p - 1))
        inv_phi_Q1 = inv_phi_Q1 * Iv.from_frac(Fraction(p, p - 1))

    # Switching sums over z <= q < y
    if y <= P_CUT:
        Q_sw = [q for q in PRIMES if z <= q < y]
        num_q = Iv(len(Q_sw), len(Q_sw))
        sum_q_inv = Iv(0, 0)
        sum_q2_inv = Iv(0, 0)
        for q in Q_sw:
            sum_q_inv = sum_q_inv + Iv.from_frac(Fraction(1, q - 1))
            sum_q2_inv = sum_q2_inv + Iv.from_frac(Fraction(1, q * (q - 1)))
    else:
        num_q = pi_ub_iv(y_iv, log_y)
        if z <= P_CUT:
            # Split at P_CUT (P_CUT = 30000 > e^10 and composite)
            sum_q_inv_lo = Iv(0, 0)
            sum_q2_inv_lo = Iv(0, 0)
            for q in PRIMES:
                if z <= q <= P_CUT:
                    sum_q_inv_lo = sum_q_inv_lo + Iv.from_frac(Fraction(1, q - 1))
                    sum_q2_inv_lo = sum_q2_inv_lo + Iv.from_frac(Fraction(1, q * (q - 1)))
            pc_iv = Iv(P_CUT, P_CUT)
            log_pc = ln_iv(pc_iv)
            # M0 cancels identically: sum_{P_CUT < q < y} 1/q <= sum_{q<y}1/q - sum_{q<P_CUT}1/q
            sum_p_hi = sum_inv_p_ub(y_iv, log_y) - sum_inv_p_lb(pc_iv, log_pc)
            tail_q = Iv(1, 1) / pc_iv
            sum_q_inv = sum_q_inv_lo + sum_p_hi + tail_q
            sum_q2_inv = sum_q2_inv_lo + tail_q
        else:
            sum_p_hi = sum_inv_p_ub(y_iv, log_y) - sum_inv_p_lb(z_iv, log_z)
            tail_q = Iv(1, 1) / Iv(z - 1, z - 1)
            sum_q_inv = sum_p_hi + tail_q
            sum_q2_inv = tail_q

    # Bonferroni ratios on P_2
    if z <= P_CUT:
        w2 = [Iv.from_frac(Fraction(1, p - 1)) for p in P2]
        g_full = Iv(1, 1)
        for w in w2:
            g_full = g_full * (Iv(1, 1) - w)
        e2 = elem_sym_iv(w2, max(m_odd, m_even))
        B_odd = Iv(0, 0)
        for j in range(m_odd + 1):
            B_odd = B_odd + (e2[j] if j % 2 == 0 else -e2[j])
        B_even = Iv(0, 0)
        for j in range(m_even + 1):
            B_even = B_even + (e2[j] if j % 2 == 0 else -e2[j])
        ratio_odd = B_odd / g_full
        ratio_even = B_even / g_full
        V_lb = V_Q1 * g_full
        # Exact divisor counts
        num_d_odd = Iv((1 << a) * sum(_comb(len(P2), j) for j in range(m_odd + 1)))
        num_d_even = Iv((1 << a) * sum(_comb(len(P2), j) for j in range(m_even + 1)))
        inv_phi_P2 = Iv(0, 0)
        for j in range(m_even + 1):
            inv_phi_P2 = inv_phi_P2 + e2[j]
    else:
        # Analytic bounds using S1 = sum_{p_a < p < z} 1/(p-1)
        exact_sum_p_pa = Iv(0, 0)
        for p in PRIMES:
            if p <= p_a:
                exact_sum_p_pa = exact_sum_p_pa + Iv(1, 1) / Iv(p, p)
        tail_pp1 = Iv(0, 0)
        tail_pm1_sq = Iv(0, 0)
        for p in PRIMES:
            if p > p_a:
                tail_pp1 = tail_pp1 + Iv.from_frac(Fraction(1, p * (p - 1)))
                tail_pm1_sq = tail_pm1_sq + Iv.from_frac(Fraction(1, (p - 1) * (p - 1)))
        tail_pp1 = tail_pp1 + Iv(1, 1) / Iv(P_CUT, P_CUT)
        tail_pm1_sq = tail_pm1_sq + Iv(1, 1) / Iv(P_CUT - 1, P_CUT - 1)

        S1 = (sum_inv_p_ub(z_iv, log_z) - exact_sum_p_pa) + tail_pp1
        c_log2 = Iv(1, 1) / (Iv(2, 2) * (Iv(1, 1) - Iv(1, 1) / Iv(p_a, p_a)))
        g_full_lb = exp_iv(-(S1 + c_log2 * tail_pm1_sq))
        V_lb = V_Q1 * g_full_lb

        # Odd-order Bonferroni: ratio_odd >= 1 - e_{m_odd+1}/g >= 1 - (S1^(m_odd+1)/(m_odd+1)!)/g_lb
        fact = 1
        for j in range(1, m_odd + 2):
            fact *= j
        e_2r_ub = (S1 ** (m_odd + 1)) / Iv(fact, fact)
        ratio_odd = Iv(1, 1) - e_2r_ub / g_full_lb

        # Even-order Bonferroni: ratio_even <= 1 + (S1^(m_even+1)/(m_even+1)!)/g_lb
        fact_e = 1
        for j in range(1, m_even + 2):
            fact_e *= j
        e_2s1_ub = (S1 ** (m_even + 1)) / Iv(fact_e, fact_e)
        ratio_even = Iv(1, 1) + e_2s1_ub / g_full_lb

        pz_ub = pi_ub_iv(z_iv, log_z)
        sum_pz_odd = Iv(0, 0)
        fact_j = 1
        for j in range(m_odd + 1):
            if j > 0:
                fact_j *= j
            sum_pz_odd = sum_pz_odd + (pz_ub ** j) / Iv(fact_j, fact_j)
        num_d_odd = Iv(1 << a, 1 << a) * sum_pz_odd

        sum_pz_even = Iv(0, 0)
        inv_phi_P2 = Iv(0, 0)
        fact_j = 1
        for j in range(m_even + 1):
            if j > 0:
                fact_j *= j
            sum_pz_even = sum_pz_even + (pz_ub ** j) / Iv(fact_j, fact_j)
            inv_phi_P2 = inv_phi_P2 + (S1 ** j) / Iv(fact_j, fact_j)
        num_d_even = Iv(1 << a, 1 << a) * sum_pz_even

    assert ratio_odd.lo > 0
    bracket = ratio_odd - Iv(Decimal("0.5")) * ratio_even * sum_q_inv
    assert bracket.lo > 0, f"Main bracket non-positive: {bracket}"
    main_norm = V_lb * bracket  # normalized by |A| > N / log N

    # Error terms normalized by N / log N.  Per modulus d (3 <= d <= sqrt(N), (d,N)=1),
    # by (*) in r_coeff_iv:  |r(d)| <= (c_pi(X_lo) + 1/(16 pi)) sqrt(N) log N + omega(N).
    # Divided by N/log N:  (c_pi + 1/(16 pi)) log^2 N / sqrt(N) + omega(N) log N / N, both
    # decreasing in N (omega(N) log N/N <= 1.3841 log^2 N/(N log log N)), so X_lo is the
    # worst case.  The omega(N) summand is the whole effect of the elements N - p, p | N,
    # that A excludes (|A| = pi(N) - omega(N)).  r(1) = 0 but d = 1 is counted anyway.
    rc = r_coeff_iv(logX_lo, X_lo)
    omega_ub = omega_ub_iv(logX_lo)
    err_per_d_norm = rc * (logX_lo ** 2) / sqrt_X_lo + (omega_ub * logX_lo) / X_lo_iv

    err_A_norm = num_d_odd * err_per_d_norm
    inv_phi_all = inv_phi_Q1 * inv_phi_P2
    # In switching: 0.5 * sum R_q + 0.5 * sum |r(q)| * V(z) * ratio_even (using V(z) <= 1)
    err_Aq_norm = Iv(Decimal("0.5")) * num_q * err_per_d_norm * (num_d_even + inv_phi_all + ratio_even)

    # q^2 term: (1/2) sum_{z <= q < y} |A_{q^2}|.
    if y ** 4 <= X_lo:
        # q^2 < y^2 <= sqrt(X_lo): |A_{q^2}| = |A|/phi(q^2) + r(q^2) with (*) for d = q^2, and
        # |A| <= pi(N) <= li(N) + sqrt(N) log N/(8 pi), li(N) < N/(log N - 2) (N >= e^5).
        # Normalized: |A|/(N/log N) <= logX/(logX-2) + log^2 X/(8 pi sqrt X), decreasing in N.
        A_ratio = logX_lo / (logX_lo - Iv(2, 2)) + (logX_lo ** 2) / (Iv(8, 8) * PI * sqrt_X_lo)
        err_q2_norm = Iv(Decimal("0.5")) * (A_ratio * sum_q2_inv + num_q * err_per_d_norm)
    else:
        # elementary: A_{q^2} consists of distinct integers in [1, N-1] divisible by q^2,
        # so |A_{q^2}| <= (N-1)/q^2 < N/q^2; normalized <= log N / q^2 <= logX_hi/(q(q-1)).
        err_q2_norm = Iv(Decimal("0.5")) * logX_hi * sum_q2_inv

    tot_err_norm = err_A_norm + err_Aq_norm + err_q2_norm
    net_norm = main_norm - tot_err_norm
    assert net_norm.lo > 0, f"Slab [{X_lo}, {X_hi}) FAILED: net={net_norm}"
    return {
        "z": z, "y": y,
        "main_lo": main_norm.lo,
        "err_hi": tot_err_norm.hi,
        "net_lo": net_norm.lo,
    }

# Slab schedule covering [4 * 10^18, 10^170) with exact integer boundaries
SLABS = [
    (4 * 10**18, 10**20, 14, 5, 3, 0),
    (10**20,     10**22, 10, 4, 3, 0),
    (10**22,     10**24, 12, 5, 3, 0),
    (10**24,     10**26, 12, 6, 3, 0),
    (10**26,     10**28, 14, 3, 5, 2),
    (10**28,     10**30, 14, 3, 5, 2),
    (10**30,     10**33, 14, 3, 5, 2),
    (10**33,     10**36, 14, 3, 5, 2),
    (10**36,     10**40, 14, 3, 5, 2),
    (10**40,     10**45, 16, 4, 5, 2),
    (10**45,     10**50, 16, 5, 5, 2),
    (10**50,     10**56, 18, 6, 5, 2),
    (10**56,     10**62, 20, 7, 5, 2),
    (10**62,     10**70, 22, 2, 9, 4),
    (10**70,     10**78, 22, 3, 9, 4),
    (10**78,     10**86, 22, 3, 9, 4),
    (10**86,     10**94, 22, 4, 9, 4),
    (10**94,     10**102, 24, 6, 9, 4),
    (10**102,    10**110, 22, 5, 9, 4),
    (10**110,    10**118, 24, 7, 9, 4),
    (10**118,    10**126, 24, 7, 9, 4),
    (10**126,    10**134, 24, 8, 9, 4),
    (10**134,    10**138, 28, 4, 11, 6),
    (10**138,    10**142, 26, 3, 11, 6),
    (10**142,    10**146, 26, 3, 11, 6),
    (10**146,    10**150, 26, 3, 11, 6),
    (10**150,    10**154, 28, 5, 11, 6),
    (10**154,    10**158, 28, 5, 11, 6),
    (10**158,    10**164, 28, 5, 11, 6),
    (10**164,    10**170, 28, 5, 11, 6),
]

def verify_regime_2():
    print("\n=== REGIME 2: Finite Slab Ladder [4*10^18, 10^170) for K = 4 ===")
    assert SLABS[0][0] == 4 * 10**18
    assert SLABS[-1][1] == 10**170
    for i in range(len(SLABS) - 1):
        assert SLABS[i][1] == SLABS[i + 1][0], f"Gap at slab {i}"
    min_net = None
    for idx, (X_lo, X_hi, M, a, m_odd, m_even) in enumerate(SLABS, 1):
        res = certify_slab_K4(X_lo, X_hi, M, a, m_odd, m_even)
        if min_net is None or res["net_lo"] < min_net:
            min_net = res["net_lo"]
        print(
            f"  Slab {idx:2d}: [{X_lo:.0e}, {X_hi:.0e}) M={M:2d} a={a:2d} "
            f"odd={m_odd:2d} even={m_even:2d} z={res['z']} y={res['y']} "
            f"| main>={res['main_lo']:.6f} err<={res['err_hi']:.6f} net>={res['net_lo']:.6f}"
        )
    print(f"  Regime 2 PASSED across all {len(SLABS)} contiguous slabs (min net_lo = {min_net:.6f})")

# ---------------------------------------------------------------------------
# Regime 3: N >= X_LS = 10^170.  [BJS] Theorem 6 (lower bound for S(A,P(z)), upper
# bound for each S(A_q,P(z))) with pre-sieve set Q = {3 <= p < u0, p nmid N}.
# ---------------------------------------------------------------------------

def F_lin_ub(s_iv: Iv, n_quad: int = 200) -> Iv:
    # Upper bound for F(s') for every s' >= s_iv.lo (F is decreasing, [JS] section 2).
    # F(s) = 2e^gamma/s for 0 < s <= 3 ([BJS] Theorem 6 / Lemma 19).  For 3 <= s <= 5,
    # sF(s) = 3F(3) + int_3^s f(t-1) dt with f(t) = 2e^gamma log(t-1)/t on [2,4]
    # ([BJS] Lemma 19), i.e. F(s) = (2e^gamma/s)(1 + int_2^{s-1} log(t-1)/t dt).
    # log(t-1)/t is increasing on [2,4] (t/(t-1) > log(t-1) there), so the
    # right-endpoint Riemann sum is an upper bound.  For s > 5 we use F(s) <= F(5).
    s = s_iv.lo
    if s <= 1:
        raise ValueError(f"F(s) needs s > 1, got {s}")
    if s <= 3:
        return Iv(2, 2) * E_GAMMA / Iv(s, s)
    s_cap = min(s, Decimal(5))
    a = Iv(2, 2)
    b = Iv(s_cap, s_cap) - Iv(1, 1)
    h = (b - a) / Iv(n_quad, n_quad)
    tot = Iv(0, 0)
    for i in range(1, n_quad + 1):
        t = a + Iv(i, i) * h
        tot = tot + ln_iv(t - Iv(1, 1)) / t
    return (Iv(2, 2) * E_GAMMA / Iv(s_cap, s_cap)) * (Iv(1, 1) + tot * h)

def f_lin_lb(s_iv: Iv) -> Iv:
    # Lower bound for f(s') for every s' >= s_iv.lo (f is increasing, [JS] section 2);
    # f(s) = 2e^gamma log(s-1)/s on [2,4] ([BJS] Lemma 19); for s > 4 use f(s) >= f(4).
    s = s_iv.lo
    if s <= 2:
        return Iv(0, 0)
    s_cap = min(s, Decimal(4))
    s_cap_iv = Iv(s_cap, s_cap)
    return Iv(2, 2) * E_GAMMA * ln_iv(s_cap_iv - Iv(1, 1)) / s_cap_iv

def h_lin_ub(s_iv: Iv) -> Iv:
    # h from [BJS] Theorem 6: e^-2 on [1,2], e^-s on [2,3], 3 s^-1 e^-s for s >= 3;
    # continuous and non-increasing, so h(s_iv.lo) bounds h(s') for s' >= s_iv.lo.
    s = s_iv.lo
    if s <= 2:
        return exp_iv(Iv(-2, -2))
    if s <= 3:
        return exp_iv(Iv(_neg(s), _neg(s)))
    return (Iv(3, 3) / Iv(s, s)) * exp_iv(Iv(_neg(s), _neg(s)))

def regime3(X_LS: int, M: int, u0: int, B_str: str, L_sub: int = 200, verbose: bool = True):
    X_iv = Iv(X_LS, X_LS)
    logX = ln_iv(X_iv)
    M_iv = Iv(M, M)
    # z = N^(1/M), y = N^beta with beta = (1 - 1/M)/4, so z y^4 = N and y^5 > N.
    beta = Iv.from_frac(Fraction(M - 1, 4 * M))
    assert M > 5 and beta.lo > Decimal("0.2")
    B = Iv(Decimal(B_str))

    # Pre-sieve primes Q = {3 <= p < u0, p nmid N} (a subset of P), Q <= Q_prod.
    Q_primes = [p for p in PRIMES if 2 < p < u0]
    Q_prod = 1
    for p in Q_primes:
        Q_prod *= p
    log_Q_prod = ln_iv(Iv(Q_prod, Q_prod))
    # alpha with N^alpha / log^(B+1) N >= Q_prod for all N >= X_LS; D = N^(1/2 - alpha),
    # so Q D <= H := sqrt(N)/log^(B+1) N.
    alpha_req = (log_Q_prod + (B + Iv(1, 1)) * ln_iv(logX)) / logX
    with localcontext() as ctx:
        ctx.prec = 20
        ctx.rounding = ROUND_CEILING
        ctx.traps[Inexact] = False
        ctx.traps[Rounded] = False
        alpha_dec = alpha_req.hi.quantize(Decimal("0.0001"))
    alpha = Iv(alpha_dec, alpha_dec)
    # monotone: d/dL [alpha L - (B+1) log L] = alpha - (B+1)/L > 0 for L >= log X_LS
    assert alpha.lo > ((B + Iv(1, 1)) / logX).hi
    assert (alpha * logX - (B + Iv(1, 1)) * ln_iv(logX)).lo >= log_Q_prod.hi

    log_z0 = logX / M_iv
    z0 = exp_iv(log_z0)
    assert log_z0.lo > Decimal("8.9") and z0.lo > 285
    log_H0 = Iv(Decimal("0.5")) * logX - (B + Iv(1, 1)) * ln_iv(logX)
    # H >= 10^9 (needed for [BS] Lemma 5), y <= H (needed for the r(q) sums);
    # both differences are increasing in log N for log N >= log X_LS.
    assert log_H0.lo > ln_iv(Iv(10**9, 10**9)).hi
    assert (beta * logX).hi <= log_H0.lo
    assert (Iv(Decimal("0.5")) - beta).lo > ((B + Iv(1, 1)) / logX).hi

    # [BJS] Theorem 6 needs D >= z^2 (lower bound) and D/q >= z for q < y (upper bound).
    s = M_iv * (Iv(Decimal("0.5")) - alpha)
    s_min = M_iv * (Iv(Decimal("0.5")) - alpha - beta)
    assert s.lo >= 2 and s_min.lo >= 1

    # ---- epsilon in the hypothesis of [BJS] Theorem 6 (note, section 4.2) ----
    # For every z >= z0 and every 1 < u < z, with g(p) = 1/(p-1):
    #   prod_{p in P\Q, u <= p < z} (1 - 1/(p-1))^{-1} <= prod_{p >= max(u,u0), p < z} (...)
    # and for u <= u0 the right side does not depend on u while log z/log u only grows,
    # so it suffices to treat u0 <= u < z.  There:
    #   prod (1-1/(p-1))^{-1} = prod (p-1)^2/(p(p-2)) * prod (1-1/p)^{-1}
    #   prod_{p >= u0} (p-1)^2/(p(p-2)) = (1/C2) / prod_{2<p<u0} (p-1)^2/(p(p-2))   [twin_tail]
    #   -log(1-1/p) <= 1/p + c/p^2,  c = 1/(2(1 - 1/u0))
    #   sum_{u<=p<z} 1/p <= loglog z - loglog u + E_max + 2.964e-6/log u0
    # with E_max >= E_<(z) for all z >= z0 ([BJS] Lemma 16 up to 1e12, [JS] (3.3) above).
    p_below = Iv(1, 1)
    for p in PRIMES:
        if 2 < p < u0:
            p_below = p_below * Iv.from_frac(Fraction((p - 1) ** 2, p * (p - 2)))
    twin_tail = (Iv(1, 1) / C2_TWIN) / p_below
    p2_tail = Iv(0, 0)
    for p in PRIMES:
        if p >= u0:
            p2_tail = p2_tail + Iv.from_frac(Fraction(1, p * p))
    p2_tail = p2_tail + Iv(1, 1) / Iv(P_CUT - 1, P_CUT - 1)
    z_all = Iv(z0.lo, max(z0.hi, Decimal(10**40)))  # stands for [z0, infinity): both
    E_max = mertens_ub_err(z_all, ln_iv(z_all))         # bounds are decreasing in x
    E_low = (Iv(Decimal("2.964e-6")) / ln_iv(Iv(u0, u0))).hi
    c_log = Iv(1, 1) / (Iv(2, 2) * (Iv(1, 1) - Iv(1, 1) / Iv(u0, u0)))
    eps = twin_tail * exp_iv(Iv(E_max, E_max) + Iv(E_low, E_low) + c_log * p2_tail) - Iv(1, 1)
    k_tab, c1_int, c2_int, eps_used = lookup_BJS(eps)
    # strictness in the hypothesis: our bound is <= (1+eps) log z/log u with eps < 1/k
    assert eps.hi < eps_used.lo
    C1 = Iv(c1_int, c1_int)
    C2 = Iv(c2_int, c2_int)
    e2 = exp_iv(Iv(2, 2))

    # ---- V(z): [BJS] Lemma 38 with j = 0, x = z = N^(1/M) >= 285 ----
    # V(z) = U_N/log z [1 + 1.45 th1 log N/(z-1) (1 + 10 loglog N/log N)] (1 + 1.002 th2/(z-3))
    #        (1 + th3/(2 log^2 z)),  |th_i| <= 1.  Each correction decreases in N for N >= X_LS.
    t1 = Iv(Decimal("1.45")) * logX / (z0 - Iv(1, 1)) * (Iv(1, 1) + Iv(10, 10) * ln_iv(logX) / logX)
    t2 = Iv(Decimal("1.002")) / (z0 - Iv(3, 3))
    t3 = Iv(1, 1) / (Iv(2, 2) * log_z0 ** 2)
    delta_V_lo = Iv(1, 1) - (Iv(1, 1) - t1) * (Iv(1, 1) - t2) * (Iv(1, 1) - t3)
    delta_V_hi = (Iv(1, 1) + t1) * (Iv(1, 1) + t2) * (Iv(1, 1) + t3) - Iv(1, 1)
    delta_V = Iv(0, max(delta_V_lo.hi, delta_V_hi.hi))
    # so (1 - delta_V) M U_N/log N <= V(z) <= (1 + delta_V) M U_N/log N

    # ---- main bracket ----
    lb_A = f_lin_lb(s) - eps_used * C2 * e2 * h_lin_ub(s)
    # (1/2) sum_{z<=q<y} phi(s_q)/(q-1), phi = F + eps' C1 e^2 h, s_q = M(1/2-alpha) - M log q/log N.
    # Slices q in [N^{u_k}, N^{u_{k+1}}), u from 1/M to beta.  On a slice s_q >= M(1/2-alpha-u_{k+1})
    # and sum 1/(q-1) <= z0/(z0-1) * sum 1/q, with
    # sum_{slice} 1/q <= log(u_{k+1}/u_k) + (C_up + 2.964e-6)/(u_k log N),
    # C_up = max(2/sqrt(z0), 6.836e-6): for x >= z0, E_<(x) <= C_up/log x ([BJS] Lemma 16 if
    # x <= 1e12 since 2/(sqrt(x) log x) <= (2/sqrt(z0))/log x; [JS] (3.3) if x > 1e12).
    du = (beta - Iv(1, 1) / M_iv) / Iv(L_sub, L_sub)
    C_up = max((Iv(2, 2) / z0.sqrt()).hi, Decimal("6.836e-6"))
    mert_coeff = Iv(C_up, C_up) + Iv(Decimal("2.964e-6"))
    q_ratio_ub = z0 / (z0 - Iv(1, 1))
    sum_Aq_main = Iv(0, 0)
    for k in range(L_sub):
        u_k = Iv(1, 1) / M_iv + Iv(k, k) * du
        u_k1 = Iv(1, 1) / M_iv + Iv(k + 1, k + 1) * du
        sq_lo = M_iv * (Iv(Decimal("0.5")) - alpha - u_k1)
        phi_ub = F_lin_ub(sq_lo) + eps_used * C1 * e2 * h_lin_ub(sq_lo)
        sum_q_sub = ln_iv(u_k1 / u_k) + mert_coeff / (u_k * logX)
        sum_Aq_main = sum_Aq_main + phi_ub * q_ratio_ub * sum_q_sub
    main_bracket = lb_A - Iv(Decimal("0.5")) * sum_Aq_main
    assert main_bracket.lo > 0
    # pi_4(N) >= V(z)|A| main_bracket - errors, |A| > N/log N ([JS] Lemma 3.1);
    # normalizing by M U_N N/log^2 N:
    main_coeff = (Iv(1, 1) - delta_V) * main_bracket

    # ---- errors, each divided by M U_N N/log^2 N and bounded using U_N >= U_c ----
    # Sum over squarefree n <= H, (n,N) = 1 of |r(n)|:  by (*) and [BS] Lemma 5 (sum mu^2 <= 0.608 H,
    # H >= 1e9) and [BS] Lemma 4:  <= 0.608 H [(c_pi + 1/(16 pi)) sqrt(N) log N + 1.3841 log N/loglog N]
    #                              = c4G N / log^B N,  c4G = 0.608 (c_pi + 1/(16pi) + 1.3841/(sqrt(N) loglog N)).
    sqrt_X = exp_iv(Iv(Decimal("0.5")) * logX)
    c4G = Iv(Decimal("0.608")) * (r_coeff_iv(logX, X_LS) + Iv(Decimal("1.3841")) / (sqrt_X * ln_iv(logX)))
    logX_Bm2 = pow_real_iv(logX, B - Iv(2, 2))
    logX_Bm3 = pow_real_iv(logX, B - Iv(3, 3))
    logX_Bm1 = pow_real_iv(logX, B - Iv(1, 1))
    assert (B - Iv(3, 3)).lo > 0   # all three powers of log N in the denominators grow with N
    # R1: R = sum_{d|P(z), d<QD}|r(d)| plus (1/2) sum_q sum_{d|P(z), d<QD/q} |r(qd)|; the n = qd are
    #     distinct (q is the largest prime factor) and < QD <= H: total <= 1.5 c4G N/log^B N.
    err_R1 = Iv(Decimal("1.5")) * c4G / (M_iv * U_CONST * logX_Bm2)
    # R2: r_q(d) = r(qd) - r(q)/phi(d) gives (1/2) sum_q |r(q)| sum_{d<QD} mu^2(d)/phi(d)
    #     <= (1/2) c4G N/log^B N * 1.1 log H <= 0.275 c4G N/log^(B-1) N   (y <= H; [BS] Lemma 5).
    err_R2 = Iv(Decimal("0.275")) * c4G / (M_iv * U_CONST * logX_Bm3)
    # rq: |A_q| <= |A|/(q-1) + |r(q)| in the main term of the upper bound for S(A_q):
    #     (1/2) V(z) phi(s_min) sum_q |r(q)| <= (1/2)(1+delta_V) M U_N/log N phi(s_min) c4G N/log^B N.
    phi_max = F_lin_ub(s_min) + eps_used * C1 * e2 * h_lin_ub(s_min)
    err_rq = Iv(Decimal("0.5")) * (Iv(1, 1) + delta_V) * phi_max * c4G / logX_Bm1
    # q^2: |A_{q^2}| <= N/q^2 (distinct integers in [1, N-1]); sum_{q >= z} 1/q^2 <= 1/(z-1).
    #     Normalized: log^2 N/(2 M U_N (N^(1/M) - 1)), decreasing for log N > 2M.
    assert logX.lo > Iv(2 * M, 2 * M).hi
    err_q2 = (logX ** 2) / (Iv(2, 2) * M_iv * U_CONST * (z0 - Iv(1, 1)))

    tot_err = err_R1 + err_R2 + err_rq + err_q2
    net_coeff = main_coeff - tot_err
    res = dict(alpha=alpha, z0=z0, eps=eps, k=k_tab, c1=c1_int, c2=c2_int, s=s, s_min=s_min,
               delta_V=delta_V, c4G=c4G, lb_A=lb_A, half_sum=Iv(Decimal("0.5")) * sum_Aq_main,
               main=main_coeff, err=tot_err, R1=err_R1, R2=err_R2, rq=err_rq, q2=err_q2,
               net=net_coeff, logX=logX, beta=beta)
    return res

def verify_regime_3():
    print("\n=== REGIME 3: N >= 10^170, [BJS] Theorem 6 with pre-sieve, K = 4 ===")
    M, u0, B_str = R3_PARAMS
    r = regime3(10 ** 170, M, u0, B_str)
    print(f"  X_LS = 10^170 (log X_LS in [{r['logX'].lo:.4f}, {r['logX'].hi:.4f}])")
    print(f"  M = {M}, beta = {r['beta'].lo:.6f}, u0 = {u0}, B = {B_str}, alpha = {r['alpha'].lo}")
    print(f"  z0 >= {r['z0'].lo:.4e}, eps <= {r['eps'].hi:.6e}, 1/eps >= {(Iv(1,1)/r['eps']).lo:.2f}")
    print(f"  [BJS] Table 1 row eps^-1 = {r['k']}: applied with eps' = 1/{r['k']}, C1 = {r['c1']}, C2 = {r['c2']}")
    print(f"  s in [{r['s'].lo:.4f}, {r['s'].hi:.4f}], s_min in [{r['s_min'].lo:.4f}, {r['s_min'].hi:.4f}]")
    print(f"  delta_V <= {r['delta_V'].hi:.6e}, c_4G <= {r['c4G'].hi:.6f}")
    print(f"  f(s) - eps'*C2*e^2*h(s) >= {r['lb_A'].lo:.6f}")
    print(f"  0.5 * sum_q phi(s_q)/(q-1) <= {r['half_sum'].hi:.6f}")
    print(f"  main_coeff >= {r['main'].lo:.6f}")
    print(f"  tot_err    <= {r['err'].hi:.6f} (R1={r['R1'].hi:.6f}, R2={r['R2'].hi:.6f}, rq={r['rq'].hi:.6f}, q2={r['q2'].hi:.2e})")
    assert r['net'].lo > 0, f"Regime 3 FAILED: net_coeff={r['net']}"
    print(f"  NET COEFF  >= {r['net'].lo:.6f} (pi_4(N) > NET * {M} * U_N * N / log^2 N for all even N >= 10^170)")

R3_PARAMS = (22, 41, "3.05")

def main():
    print("Outward-rounded Decimal/Fraction/int verification (PREC = 90); default context traps Inexact, Rounded")
    print(f"  pi     in [{PI.lo:.25f}, {PI.hi:.25f}]")
    print(f"  ln(2)  in [{LN2.lo:.25f}, {LN2.hi:.25f}]")
    print(f"  gamma  in [{GAMMA.lo:.25f}, {GAMMA.hi:.25f}]")
    print(f"  C2     in [{C2_TWIN.lo:.12f}, {C2_TWIN.hi:.12f}]")
    print(f"  M0     in [{M0_CONST.lo:.12f}, {M0_CONST.hi:.12f}]")
    print(f"  U_c    in [{U_CONST.lo:.12f}, {U_CONST.hi:.12f}]")
    print(f"  li(2)  in [{LI2.lo:.12f}, {LI2.hi:.12f}]")
    print(f"  li(e^5) in [{LI_E5.lo:.12f}, {LI_E5.hi:.12f}] < e^5/3 = {(exp_iv(Iv(5,5))/Iv(3,3)).lo:.12f}")
    assert LI_E5.hi < (exp_iv(Iv(5, 5)) / Iv(3, 3)).lo

    verify_benchmark_0()
    print("\n=== REGIME 1: 4 <= N <= 4 * 10^18 ===")
    print("  Covered unconditionally by Oliveira e Silva, Herzog & Pardi (2014) with K = 1 <= 4.")
    verify_regime_2()
    verify_regime_3()
    print("\n=== RESULT ===")
    print("  All asserted inequalities hold: Regimes 2 and 3 checked; Regime 1 is the cited Goldbach verification.")
    print("  Together with the quoted lemmas (note X26, section 0), this gives K = 4 for all even N >= 4 under GRH.")

if __name__ == "__main__":
    main()
