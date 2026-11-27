"""
Pure-integer binary proof-by-reflection mirror matching Lean `Dyadic`,
`LogWitness`, Q64 `log`/`exp`/`J_full`, and static `OddPrimeTree`. Zero `float`, zero `math`.
"""

from __future__ import annotations

from decimal import Decimal
from pathlib import Path

P_EXACT = 27000
DYADIC_BIAS = 8192
Q64_SCALE = 1 << 64
BIAS_SUB_64 = DYADIC_BIAS - 64


def _sieve_primes(limit: int) -> list[int]:
    flags = bytearray([1]) * (limit + 1)
    flags[0] = flags[1] = 0
    i = 2
    while i * i <= limit:
        if flags[i]:
            flags[i * i :: i] = bytearray(len(flags[i * i :: i]))
        i += 1
    return [n for n in range(limit + 1) if flags[n]]


def _sieve_odd_sqf_1024() -> list[tuple[int, list[int]]]:
    ps = [p for p in _sieve_primes(1024) if p >= 3]
    out: list[tuple[int, list[int]]] = []
    for d in range(1, 1025, 2):
        rem, fac, sqf = d, [], True
        for p in ps:
            if p * p > rem:
                break
            if rem % p == 0:
                rem //= p
                if rem % p == 0:
                    sqf = False
                    break
                fac.append(p)
        if sqf:
            if rem > 1:
                fac.append(rem)
            out.append((d, fac))
    return out


PRIMES_EXACT: list[int] = _sieve_primes(P_EXACT - 1)
ODD_PRIMES_EXACT: list[int] = [p for p in PRIMES_EXACT if p >= 3]
ODD_SQF_1024: list[tuple[int, list[int]]] = _sieve_odd_sqf_1024()

LN2_LO64 = 12786308645202649952
LN2_HI64 = 12786308645202668399
LOG_TAIL64 = 256
RATIO13_12_UB = 19983972746518680918

INV2_ODD_PAIRS64: list[tuple[int, int]] = [
    ((2 * Q64_SCALE) // (2 * j + 1), (2 * Q64_SCALE + 2 * j) // (2 * j + 1))
    for j in range(16)
]
INV_SUCC64_UB: list[int] = [(Q64_SCALE + j) // (j + 1) for j in range(12)]
INV32_SUCC64_LB: list[int] = [Q64_SCALE // (32 * (j + 1)) for j in range(8)]


def _build_inv_fact64() -> list[int]:
    out, fact = [], 1
    for j in range(16):
        if j > 0:
            fact *= j
        out.append((Q64_SCALE + fact - 1) // fact)
    return out


INV_FACT64_UB: list[int] = _build_inv_fact64()


def msb_pos(n: int) -> int:
    return 0 if n == 0 else n.bit_length() - 1


def ceil_shr(n: int, k: int) -> int:
    q = n >> k
    return q if (q << k) == n else q + 1


def trim_shift(m: int, keep: int = 80) -> int:
    b = msb_pos(m)
    return (b + 1 - keep) if keep <= b + 1 else 0


class Dyadic:
    __slots__ = ("m", "e")

    def __init__(self, m: int, e: int) -> None:
        self.m, self.e = m, e

    def __eq__(self, o: object) -> bool:
        return isinstance(o, Dyadic) and self.m == o.m and self.e == o.e

    @staticmethod
    def zero() -> Dyadic:
        return Dyadic(0, DYADIC_BIAS)

    @staticmethod
    def one() -> Dyadic:
        return Dyadic(1, DYADIC_BIAS)

    @staticmethod
    def of_nat(n: int) -> Dyadic:
        return Dyadic(n, DYADIC_BIAS)

    @staticmethod
    def of_q64(m: int) -> Dyadic:
        return Dyadic(m, BIAS_SUB_64)

    @staticmethod
    def of_q48(m: int) -> Dyadic:
        return Dyadic(m, DYADIC_BIAS - 48)

    def shr_lb(self, k: int) -> Dyadic:
        return Dyadic(self.m >> k, self.e + k)

    def shr_ub(self, k: int) -> Dyadic:
        return Dyadic(ceil_shr(self.m, k), self.e + k)

    def mul_pow2(self, k: int) -> Dyadic:
        return Dyadic(self.m, self.e + k)

    def div_pow2_lb(self, k: int) -> Dyadic:
        return Dyadic(self.m, self.e - k) if k <= self.e else Dyadic(self.m >> (k - self.e), 0)

    def div_pow2_ub(self, k: int) -> Dyadic:
        return Dyadic(self.m, self.e - k) if k <= self.e else Dyadic(ceil_shr(self.m, k - self.e), 0)

    def trim_lb(self, keep: int = 80) -> Dyadic:
        return Dyadic.zero() if self.m == 0 else self.shr_lb(trim_shift(self.m, keep))

    def trim_ub(self, keep: int = 80) -> Dyadic:
        return Dyadic.zero() if self.m == 0 else self.shr_ub(trim_shift(self.m, keep))

    def ble(self, o: Dyadic) -> bool:
        if self.m == 0:
            return True
        if o.m == 0:
            return False
        if self.e <= o.e:
            return self.m <= (o.m << (o.e - self.e))
        return (self.m << (self.e - o.e)) <= o.m

    def blt(self, o: Dyadic) -> bool:
        if o.m == 0:
            return False
        if self.m == 0:
            return True
        if self.e <= o.e:
            return self.m < (o.m << (o.e - self.e))
        return (self.m << (self.e - o.e)) < o.m

    def add(self, o: Dyadic) -> Dyadic:
        if self.m == 0:
            return o
        if o.m == 0:
            return self
        if self.e <= o.e:
            return Dyadic(self.m + (o.m << (o.e - self.e)), self.e)
        return Dyadic((self.m << (self.e - o.e)) + o.m, o.e)

    def sub_lb(self, o: Dyadic) -> Dyadic:
        if o.m == 0:
            return self
        if self.m == 0:
            return Dyadic.zero()
        if self.e <= o.e:
            return Dyadic(max(0, self.m - (o.m << (o.e - self.e))), self.e)
        return Dyadic(max(0, (self.m << (self.e - o.e)) - o.m), o.e)

    def mul_raw_lb(self, o: Dyadic) -> Dyadic:
        if self.m == 0 or o.m == 0:
            return Dyadic.zero()
        if DYADIC_BIAS <= self.e + o.e:
            return Dyadic(self.m * o.m, self.e + o.e - DYADIC_BIAS)
        return Dyadic((self.m * o.m) >> (DYADIC_BIAS - (self.e + o.e)), 0)

    def mul_raw_ub(self, o: Dyadic) -> Dyadic:
        if self.m == 0 or o.m == 0:
            return Dyadic.zero()
        if DYADIC_BIAS <= self.e + o.e:
            return Dyadic(self.m * o.m, self.e + o.e - DYADIC_BIAS)
        return Dyadic(ceil_shr(self.m * o.m, DYADIC_BIAS - (self.e + o.e)), 0)

    def mul_lb(self, o: Dyadic) -> Dyadic:
        return self.mul_raw_lb(o).trim_lb(80)

    def mul_ub(self, o: Dyadic) -> Dyadic:
        return self.mul_raw_ub(o).trim_ub(80)

    def pow_ub(self, k: int) -> Dyadic:
        res = Dyadic.one()
        for _ in range(k):
            res = res.mul_ub(self)
        return res

    def to_q64_lb(self) -> int:
        if BIAS_SUB_64 <= self.e:
            return self.m << (self.e - BIAS_SUB_64)
        return self.m >> (BIAS_SUB_64 - self.e)

    def to_q64_ub(self) -> int:
        if BIAS_SUB_64 <= self.e:
            return self.m << (self.e - BIAS_SUB_64)
        return ceil_shr(self.m, BIAS_SUB_64 - self.e)

    def div_lb(self, o: Dyadic, keep: int = 80) -> Dyadic:
        assert o.m > 0
        if self.m == 0:
            return Dyadic.zero()
        sh = max(0, (o.m.bit_length() - self.m.bit_length()) + keep + 4)
        q_m = (self.m << sh) // o.m
        q_e = DYADIC_BIAS + self.e - o.e - sh
        if q_e < 0:
            return Dyadic(q_m >> (-q_e), 0).trim_lb(keep)
        return Dyadic(q_m, q_e).trim_lb(keep)

    def div_ub(self, o: Dyadic, keep: int = 80) -> Dyadic:
        assert o.m > 0
        if self.m == 0:
            return Dyadic.zero()
        sh = max(0, (o.m.bit_length() - self.m.bit_length()) + keep + 4)
        q_m = ((self.m << sh) + o.m - 1) // o.m
        q_e = DYADIC_BIAS + self.e - o.e - sh
        if q_e < 0:
            return Dyadic(ceil_shr(q_m, -q_e), 0).trim_ub(keep)
        return Dyadic(q_m, q_e).trim_ub(keep)

    def ceil_nat(self) -> int:
        if self.m == 0:
            return 0
        if DYADIC_BIAS <= self.e:
            return self.m << (self.e - DYADIC_BIAS)
        return ceil_shr(self.m, DYADIC_BIAS - self.e)

    def to_dec_floor(self, p: int = 18) -> Decimal:
        sh = DYADIC_BIAS - self.e
        val = ((self.m << (-sh)) * (10**p)) if sh <= 0 else ((self.m * (10**p)) >> sh)
        return Decimal(val) / Decimal(10**p)

    def to_dec_ceil(self, p: int = 18) -> Decimal:
        sh = DYADIC_BIAS - self.e
        val = ((self.m << (-sh)) * (10**p)) if sh <= 0 else ceil_shr(self.m * (10**p), sh)
        return Decimal(val) / Decimal(10**p)

    def to_lean(self) -> str:
        return f"⟨{self.m}, {self.e}⟩"


def solve_ble_mul_lb(num: Dyadic, den: Dyadic, keep: int = 80) -> Dyadic:
    """Return 80-bit `q` satisfying `num.ble(q.mul_lb(den))`."""
    if num.m == 0:
        return Dyadic.zero()
    q = num.div_ub(den, keep)
    while not num.ble(q.mul_lb(den)):
        q = Dyadic(q.m + 1, q.e).trim_ub(keep)
    return q


def solve_mul_ub_ble(num: Dyadic, den: Dyadic, keep: int = 80) -> Dyadic:
    """Return 80-bit `q` satisfying `q.mul_ub(den).ble(num)`."""
    if num.m == 0:
        return Dyadic.zero()
    q = num.div_lb(den, keep)
    while q.m > 0 and not q.mul_ub(den).ble(num):
        q = Dyadic(q.m - 1, q.e)
    return q


def div_dyadic_lb(a: Dyadic, b: Dyadic) -> Dyadic:
    if b.m == 0 or a.m == 0:
        return Dyadic.zero()
    sh = 80 + msb_pos(b.m)
    qm = (a.m << sh) // b.m
    if b.e + sh <= a.e + DYADIC_BIAS:
        return Dyadic(qm, a.e + DYADIC_BIAS - (b.e + sh)).trim_lb(80)
    return Dyadic(qm >> ((b.e + sh) - (a.e + DYADIC_BIAS)), 0)


def div_dyadic_ub(a: Dyadic, b: Dyadic) -> Dyadic:
    if b.m == 0 or a.m == 0:
        return Dyadic.zero()
    sh = 80 + msb_pos(b.m)
    qm = ((a.m << sh) + b.m - 1) // b.m
    if b.e + sh <= a.e + DYADIC_BIAS:
        return Dyadic(qm, a.e + DYADIC_BIAS - (b.e + sh)).trim_ub(80)
    return Dyadic(ceil_shr(qm, (b.e + sh) - (a.e + DYADIC_BIAS)), 0)


DY_ZERO = Dyadic.zero()
DY_ONE = Dyadic.one()
DY_TWO = Dyadic.of_nat(2)
DY_THREE = Dyadic.of_nat(3)
DY_FOUR = Dyadic.of_nat(4)
DY_SIX = Dyadic.of_nat(6)
DY_SEVEN = Dyadic.of_nat(7)
DY_TEN = Dyadic.of_nat(10)

DY_LOG27000_LO = Dyadic.of_q64(188223052931078346056)
DY_LOG27000_HI = Dyadic.of_q64(188223052931078604594)
DY_PI_LO4 = Dyadic.of_q64(57950446507558556401)
DY_8PI_LO4 = Dyadic.of_q64(463603572060468451213)
DY_16PI_LO4 = Dyadic.of_q64(927207144120936902426)
DY_13841_UB = Dyadic.of_q64(25532138472421390392)
DY_LI2_UB = Dyadic.of_q64(19279868766938236891)
DY_2964_UB = Dyadic.of_q64(54676149434476)
DY_6836_UB = Dyadic.of_q64(126101942487879)
DY_78E2_UB = Dyadic.of_q64(14388460377493450261)
DY_13E1_UB = Dyadic.of_q64(23980767295822417101)

H0_LO_DY = Dyadic.of_q64(27932727089960614046)
H0_HI_DY = Dyadic.of_q64(27967774427758222114)
CJ_UB_DY = Dyadic.of_q64(148137153875374043203)
A0_LB_DY = Dyadic.of_q64(11717002900738832995)
A0_UB_DY = Dyadic.of_q64(11732129230879274828)
LOG_10E12_HI_DY = Dyadic.of_q64(509702391329038242312)
LOG_W_DUMMY = {"b": 0, "mU": 0}


def sqrt_floor_dyadic(n: int) -> Dyadic:
    if n == 0:
        return DY_ZERO
    sh2 = max(0, 84 - (n.bit_length() + 1) // 2)
    scaled = n << (2 * sh2)
    g = 1 << (msb_pos(scaled) // 2 + 1)
    while True:
        gn = (g + scaled // g) >> 1
        if gn >= g:
            break
        g = gn
    res = Dyadic(g, DYADIC_BIAS - sh2).trim_lb(80)
    target = Dyadic.of_nat(n)
    while res.m > 0 and not res.mul_ub(res).ble(target):
        res = Dyadic(res.m - 1, res.e)
    assert res.mul_ub(res).ble(target)
    return res


def sqrt_ceil_dyadic(n: int) -> Dyadic:
    if n == 0:
        return DY_ZERO
    sh2 = max(0, 84 - (n.bit_length() + 1) // 2)
    scaled = n << (2 * sh2)
    g = 1 << (msb_pos(scaled) // 2 + 1)
    while True:
        gn = (g + scaled // g) >> 1
        if gn >= g:
            break
        g = gn
    s = g if g * g == scaled else g + 1
    res = Dyadic(s, DYADIC_BIAS - sh2).trim_ub(80)
    target = Dyadic.of_nat(n)
    while not target.ble(res.mul_lb(res)):
        res = Dyadic(res.m + 1, res.e).trim_ub(80)
    assert target.ble(res.mul_lb(res))
    return res


def log_witness_and_bounds(x: Dyadic) -> tuple[dict, Dyadic, Dyadic]:
    assert x.m > 0
    b = msb_pos(x.m)
    assert DYADIC_BIAS <= b + x.e
    p2 = 1 << b
    a, den = x.m - p2, x.m + p2
    m_u = (a << 64) // den
    assert m_u * den <= (a << 64) <= (m_u + 1) * den
    k = b + x.e - DYADIC_BIAS
    u2_lo = (m_u * m_u) >> 64
    u2_hi = ceil_shr((m_u + 1) * (m_u + 1), 64)
    t_lo, t_hi, s_lo, s_hi = m_u, m_u + 1, 0, 0
    for c_lo, c_hi in INV2_ODD_PAIRS64:
        s_lo += (t_lo * c_lo) >> 64
        s_hi += ceil_shr(t_hi * c_hi, 64)
        t_lo = (t_lo * u2_lo) >> 64
        t_hi = ceil_shr(t_hi * u2_hi, 64)
    return (
        {"b": b, "mU": m_u},
        Dyadic.of_q64(k * LN2_LO64 + s_lo),
        Dyadic.of_q64(k * LN2_HI64 + s_hi + LOG_TAIL64),
    )


def check_log_dyadic(x: Dyadic, w: dict, lo: Dyadic, hi: Dyadic) -> bool:
    p2 = 1 << w["b"]
    a, b = x.m - p2, x.m + p2
    if not (0 < x.m and DYADIC_BIAS <= w["b"] + x.e and p2 <= x.m < 2 * p2
            and w["mU"] * b <= (a << 64) <= (w["mU"] + 1) * b):
        return False
    k = w["b"] + x.e - DYADIC_BIAS
    u2_lo = (w["mU"] * w["mU"]) >> 64
    u2_hi = ceil_shr((w["mU"] + 1) * (w["mU"] + 1), 64)
    t_lo, t_hi, s_lo, s_hi = w["mU"], w["mU"] + 1, 0, 0
    for c_lo, c_hi in INV2_ODD_PAIRS64:
        s_lo += (t_lo * c_lo) >> 64
        s_hi += ceil_shr(t_hi * c_hi, 64)
        t_lo = (t_lo * u2_lo) >> 64
        t_hi = ceil_shr(t_hi * u2_hi, 64)
    return lo.ble(Dyadic.of_q64(k * LN2_LO64 + s_lo)) and Dyadic.of_q64(k * LN2_HI64 + s_hi + LOG_TAIL64).ble(hi)


def dy_log_bounds(x: Dyadic) -> tuple[bool, Dyadic, Dyadic]:
    if x.m == 0:
        return False, DY_ZERO, DY_ZERO
    b = msb_pos(x.m)
    if not (DYADIC_BIAS <= b + x.e):
        return False, DY_ZERO, DY_ZERO
    w, lo, hi = log_witness_and_bounds(x)
    return check_log_dyadic(x, w, lo, hi), lo, hi


def exp_ub_dyadic(t: Dyadic) -> tuple[bool, Dyadic]:
    if t.m == 0:
        return True, DY_ONE
    b = msb_pos(4 * t.m)
    s = (b + 1 + t.e - DYADIC_BIAS) if DYADIC_BIAS <= b + 1 + t.e else 0
    y = t.div_pow2_ub(s)
    y64 = y.to_q64_ub()
    if 4 * y64 > Q64_SCALE:
        return False, DY_ZERO
    t_c, s_c = Q64_SCALE, 0
    for c in INV_SUCC64_UB:
        s_c += t_c
        t_c = ceil_shr(ceil_shr(t_c * y64, 64) * c, 64)
    r = Dyadic.of_q64(s_c + ceil_shr(t_c * RATIO13_12_UB, 64))
    for _ in range(s):
        r = r.mul_ub(r)
    return True, r


def exp_ge_q64(x64: int) -> int:
    t, r = Q64_SCALE, Q64_SCALE
    for c in INV32_SUCC64_LB:
        t = ((t * x64) >> 64) * c >> 64
        r += t
    for _ in range(5):
        r = (r * r) >> 64
    return max(Q64_SCALE, r)


def exp_ge_dyadic(t: Dyadic) -> Dyadic:
    return Dyadic.of_q64(exp_ge_q64(t.to_q64_lb()))


def exp_neg_ub_dyadic(t: Dyadic) -> Dyadic:
    e64 = exp_ge_q64(t.to_q64_lb())
    return Dyadic.of_q64((Q64_SCALE * Q64_SCALE + e64 - 1) // e64)


def sum_pow_div_fact_ub(x: Dyadic, k: int) -> Dyadic:
    assert k < 16
    acc = DY_ONE
    for j in range(1, k + 1):
        acc = acc.add(x.pow_ub(j).mul_ub(Dyadic.of_q64(INV_FACT64_UB[j])))
    return acc


def _build_jodd_step_table() -> list[tuple[int, Dyadic, Dyadic]]:
    out = []
    for k in range(11):
        m = 1 << k
        s64 = 0
        for d, ps in ODD_SQF_1024:
            if d <= m:
                den = 1
                for p in ps:
                    den *= p - 2
                s64 += (Q64_SCALE + den - 1) // den
        out.append((m, Dyadic.of_q64(k * LN2_LO64), Dyadic.of_q64(s64)))
    return out


JODD_STEP_TABLE_DY: list[tuple[int, Dyadic, Dyadic]] = _build_jodd_step_table()


def j_odd_lb_dyadic(log_lo: Dyadic) -> Dyadic:
    main_lb = H0_LO_DY.mul_lb(log_lo.div_pow2_lb(1).add(A0_LB_DY))
    err_ub = CJ_UB_DY.mul_ub(exp_neg_ub_dyadic(log_lo.div_pow2_lb(2)))
    return main_lb.sub_lb(err_ub) if err_ub.ble(main_lb) else DY_ZERO


def j_odd_hybrid_ub_dyadic(log_lo: Dyadic, log_hi: Dyadic) -> Dyadic:
    asym = H0_HI_DY.mul_ub(log_hi.div_pow2_ub(1).add(A0_UB_DY)).add(
        CJ_UB_DY.mul_ub(exp_neg_ub_dyadic(log_lo.div_pow2_lb(2)))
    )
    for _, lm_lo, step_ub in JODD_STEP_TABLE_DY:
        if log_hi.ble(lm_lo):
            return step_ub if step_ub.ble(asym) else asym
    return asym


def js_mert_lo_ub_dyadic(log_lo: Dyadic) -> Dyadic:
    return div_dyadic_ub(DY_2964_UB, log_lo)


def js_mert_hi_ub_dyadic(log_lo: Dyadic) -> Dyadic:
    t1 = div_dyadic_ub(DY_6836_UB, log_lo)
    if LOG_10E12_HI_DY.ble(log_lo):
        return t1
    sq_lb = exp_ge_dyadic(log_lo.div_pow2_lb(1))
    t2 = div_dyadic_ub(div_dyadic_ub(DY_TWO, sq_lb), log_lo)
    return t2 if t1.ble(t2) else t1


def _lin_comb_log(a: int, b: int, d: int, s_lo: Dyadic, s_hi: Dyadic, t_lo: Dyadic, t_hi: Dyadic) -> tuple[Dyadic, Dyadic]:
    den = Dyadic.of_nat(d)
    return (
        div_dyadic_lb(Dyadic.of_nat(a).mul_lb(s_lo).add(Dyadic.of_nat(b).mul_lb(t_lo)), den),
        div_dyadic_ub(Dyadic.of_nat(a).mul_ub(s_hi).add(Dyadic.of_nat(b).mul_ub(t_hi)), den),
    )


def _log_ratio_lb_dy(log1_lo: Dyadic, log0_hi: Dyadic) -> Dyadic:
    if log0_hi.m == 0:
        return DY_ZERO
    r = div_dyadic_lb(log1_lo, log0_hi)
    if DY_ONE.ble(r):
        ok, lo, _ = dy_log_bounds(r)
        return lo if ok else DY_ZERO
    return DY_ZERO


def calc_j_full_lb_2c_dy(z: int, z_lo: Dyadic, z_hi: Dyadic, xi_lb: Dyadic, xi_lo: Dyadic, xi_hi: Dyadic) -> Dyadic:
    if xi_lb.blt(Dyadic.of_nat(z)):
        return j_odd_lb_dyadic(xi_lo)
    if not Dyadic.of_nat(z).blt(xi_lb):
        return j_odd_lb_dyadic(z_lo.sub_lb(DY_ONE))
    if not (DY_TEN.blt(z_lo) and xi_lb.blt(Dyadic.of_nat(z**3))):
        return DY_ZERO
    s1 = DY_ZERO
    for k in range(12):
        w0_lo, w0_hi = _lin_comb_log(12 - k, k, 12, z_lo, z_hi, xi_lo, xi_hi)
        w1_lo, w1_hi = _lin_comb_log(11 - k, k + 1, 12, z_lo, z_hi, xi_lo, xi_hi)
        w1p_hi = w1_hi.add(div_dyadic_ub(DY_ONE, xi_lb)) if k + 1 == 12 else w1_hi
        r_ub = div_dyadic_ub(w1p_hi, w0_lo)
        ok_l, _, r_log_hi = dy_log_bounds(r_ub)
        w0_lb = exp_ge_dyadic(w0_lo)
        den2 = w0_lb.sub_lb(DY_TWO)
        if not (DY_TEN.blt(w0_lo) and DY_TEN.blt(w1_lo) and DY_TWO.ble(w0_lb) and DY_ONE.ble(den2) and ok_l):
            return DY_ZERO
        mert = r_log_hi.add(js_mert_hi_ub_dyadic(w1_lo)).add(js_mert_lo_ub_dyadic(w0_lo)).add(div_dyadic_ub(DY_TWO, den2))
        s1 = s1.add(j_odd_hybrid_ub_dyadic(xi_lo.sub_lb(w0_hi), xi_hi.sub_lb(w0_lo)).mul_ub(mert))
    s2 = DY_ZERO
    if z_hi.add(z_hi).blt(xi_lo):
        td_lo = xi_lo.sub_lb(z_hi.add(z_hi))
        td_hi = xi_hi.sub_lb(z_lo.add(z_lo))
        for i in range(3):
            a0_lo = z_lo.add(Dyadic.of_nat(i).mul_lb(td_lo).div_pow2_lb(3))
            a0_hi = z_hi.add(Dyadic.of_nat(i).mul_ub(td_hi).div_pow2_ub(3))
            a1_lo = z_lo.add(Dyadic.of_nat(i + 1).mul_lb(td_lo).div_pow2_lb(3))
            outer = _log_ratio_lb_dy(a1_lo, a0_hi).sub_lb(js_mert_lo_ub_dyadic(a1_lo).add(js_mert_hi_ub_dyadic(a0_lo)))
            inner_sum = DY_ZERO
            for j in range(4):
                c0 = 2 * (i + 1) + j * (3 - i)
                c1 = 2 * (i + 1) + (j + 1) * (3 - i)
                b0_lo = z_lo.add(Dyadic.of_nat(c0).mul_lb(td_lo).div_pow2_lb(4))
                b0_hi = z_hi.add(Dyadic.of_nat(c0).mul_ub(td_hi).div_pow2_ub(4))
                b1_lo = z_lo.add(Dyadic.of_nat(c1).mul_lb(td_lo).div_pow2_lb(4))
                rem_lo = Dyadic.of_nat((3 - i) * (3 - j)).mul_lb(td_lo).div_pow2_lb(4)
                s2_ij = _log_ratio_lb_dy(b1_lo, b0_hi).sub_lb(js_mert_lo_ub_dyadic(b1_lo).add(js_mert_hi_ub_dyadic(b0_lo)))
                inner_sum = inner_sum.add(s2_ij.mul_lb(j_odd_lb_dyadic(rem_lo)))
            s2 = s2.add(outer.mul_lb(inner_sum))
    rhs = j_odd_lb_dyadic(xi_lo).add(s2)
    if not s1.ble(rhs):
        return DY_ZERO
    jf = rhs.sub_lb(s1).trim_lb(80)
    assert jf.add(s1).ble(rhs)
    return jf


def make_prime_entry(p: int) -> dict:
    return {
        "p": p,
        "gLb64": Q64_SCALE // (p - 1),
        "gUb64": (Q64_SCALE + p - 2) // (p - 1),
        "mulUb64": (Q64_SCALE + p * (p - 1) - 1) // (p * (p - 1)),
        "sqUb64": (Q64_SCALE + (p - 1) ** 2 - 1) // ((p - 1) ** 2),
        "vLb64": ((p - 2) * Q64_SCALE) // (p - 1),
        "vUb64": ((p - 2) * Q64_SCALE + p - 2) // (p - 1),
        "phiUb64": (p * Q64_SCALE + p - 2) // (p - 1),
    }


ODD_PRIME_ENTRIES: list[dict] = [make_prime_entry(p) for p in ODD_PRIMES_EXACT]


def build_prime_tree() -> dict:
    entries = ODD_PRIME_ENTRIES
    n, k = len(entries), 64
    base, rem = divmod(n, k)
    leaves, idx = [], 0
    for i in range(k):
        sz = base + (1 if i < rem else 0)
        es = entries[idx : idx + sz]
        idx += sz
        s1 = s_mul = s_sq = DY_ZERO
        v_lb = v_ub = DY_ONE
        for e in es:
            s1 = s1.add(Dyadic.of_q64(e["gUb64"]))
            s_mul = s_mul.add(Dyadic.of_q64(e["mulUb64"]))
            s_sq = s_sq.add(Dyadic.of_q64(e["sqUb64"]))
            v_lb = v_lb.mul_lb(Dyadic.of_q64(e["vLb64"]))
            v_ub = v_ub.mul_ub(Dyadic.of_q64(e["vUb64"]))
        leaves.append({
            "kind": "leaf",
            "sum": {"lo": es[0]["p"], "hi": es[-1]["p"], "cnt": len(es),
                    "s1Ub": s1, "sMulUb": s_mul, "sSqUb": s_sq, "vLb": v_lb, "vUb": v_ub},
            "entries": es,
        })

    def merge(nodes: list[dict]) -> dict:
        if len(nodes) == 1:
            return nodes[0]
        mid = len(nodes) // 2
        l, r = merge(nodes[:mid]), merge(nodes[mid:])
        sl, sr = l["sum"], r["sum"]
        return {
            "kind": "node",
            "sum": {
                "lo": sl["lo"], "hi": sr["hi"], "cnt": sl["cnt"] + sr["cnt"],
                "s1Ub": sl["s1Ub"].add(sr["s1Ub"]),
                "sMulUb": sl["sMulUb"].add(sr["sMulUb"]),
                "sSqUb": sl["sSqUb"].add(sr["sSqUb"]),
                "vLb": sl["vLb"].mul_lb(sr["vLb"]),
                "vUb": sl["vUb"].mul_ub(sr["vUb"]),
            },
            "left": l,
            "right": r,
        }

    return merge(leaves)


PRIME_TREE = build_prime_tree()


def tree_filter_range(q0: int, q1: int, node: dict = PRIME_TREE) -> list[dict]:
    s = node["sum"]
    if q1 <= s["lo"] or s["hi"] < q0:
        return []
    if node["kind"] == "leaf":
        if q0 <= s["lo"] and s["hi"] < q1:
            return list(node["entries"])
        return [e for e in node["entries"] if q0 <= e["p"] < q1]
    return tree_filter_range(q0, q1, node["left"]) + tree_filter_range(q0, q1, node["right"])


def tree_query_count(q0: int, q1: int, node: dict = PRIME_TREE) -> int:
    s = node["sum"]
    if q1 <= s["lo"] or s["hi"] < q0:
        return 0
    if q0 <= s["lo"] and s["hi"] < q1:
        return s["cnt"]
    if node["kind"] == "leaf":
        return sum(1 for e in node["entries"] if q0 <= e["p"] < q1)
    return tree_query_count(q0, q1, node["left"]) + tree_query_count(q0, q1, node["right"])


def _tree_query_sum(ekey: str, skey: str, q0: int, q1: int, node: dict = PRIME_TREE) -> Dyadic:
    s = node["sum"]
    if q1 <= s["lo"] or s["hi"] < q0:
        return DY_ZERO
    if q0 <= s["lo"] and s["hi"] < q1:
        return s[skey]
    if node["kind"] == "leaf":
        acc = DY_ZERO
        for e in node["entries"]:
            if q0 <= e["p"] < q1:
                acc = acc.add(Dyadic.of_q64(e[ekey]))
        return acc
    return _tree_query_sum(ekey, skey, q0, q1, node["left"]).add(_tree_query_sum(ekey, skey, q0, q1, node["right"]))


def _tree_query_prod(is_lb: bool, q0: int, q1: int, node: dict = PRIME_TREE) -> Dyadic:
    s = node["sum"]
    if q1 <= s["lo"] or s["hi"] < q0:
        return DY_ONE
    if q0 <= s["lo"] and s["hi"] < q1:
        return s["vLb" if is_lb else "vUb"]
    if node["kind"] == "leaf":
        acc = DY_ONE
        for e in node["entries"]:
            if q0 <= e["p"] < q1:
                v = Dyadic.of_q64(e["vLb64" if is_lb else "vUb64"])
                acc = acc.mul_lb(v) if is_lb else acc.mul_ub(v)
        return acc
    l = _tree_query_prod(is_lb, q0, q1, node["left"])
    r = _tree_query_prod(is_lb, q0, q1, node["right"])
    return l.mul_lb(r) if is_lb else l.mul_ub(r)


def exact_prime_count(q0: int, q1: int) -> int:
    return (1 if q0 <= 2 < q1 else 0) + tree_query_count(q0, q1)


def exact_inv_sub_one_sum_ub(q0: int, q1: int) -> Dyadic:
    b = _tree_query_sum("gUb64", "s1Ub", q0, q1)
    return DY_ONE.add(b) if q0 <= 2 < q1 else b


def exact_inv_mul_pred_sum_ub(q0: int, q1: int) -> Dyadic:
    b = _tree_query_sum("mulUb64", "sMulUb", q0, q1)
    return Dyadic.of_q64(Q64_SCALE // 2).add(b) if q0 <= 2 < q1 else b


def exact_inv_pred_sq_sum_ub(q0: int, q1: int) -> Dyadic:
    b = _tree_query_sum("sqUb64", "sSqUb", q0, q1)
    return DY_ONE.add(b) if q0 <= 2 < q1 else b


def exact_prod_one_sub_inv_pred_lb(q0: int, q1: int) -> Dyadic:
    return _tree_query_prod(True, q0, q1)


def exact_prod_one_sub_inv_pred_ub(q0: int, q1: int) -> Dyadic:
    return _tree_query_prod(False, q0, q1)


V_PREFIX_27000_LB = exact_prod_one_sub_inv_pred_lb(3, P_EXACT)


def v2_entries_lb(es: list[dict]) -> Dyadic:
    acc = Q64_SCALE
    for e in es:
        acc = (acc * e["vLb64"]) >> 64
    return Dyadic.of_q64(acc)


def v2_entries_ub(es: list[dict]) -> Dyadic:
    acc = Q64_SCALE
    for e in es:
        acc = ceil_shr(acc * e["vUb64"], 64)
    return Dyadic.of_q64(acc)


def inv_phi_entries_ub(es: list[dict]) -> Dyadic:
    acc = Q64_SCALE
    for e in es:
        acc = ceil_shr(acc * e["phiUb64"], 64)
    return Dyadic.of_q64(acc)


def sum_g1_entries_ub(es: list[dict]) -> Dyadic:
    return Dyadic.of_q64(sum(e["gUb64"] for e in es))


def sum_g2_entries_ub(es: list[dict]) -> Dyadic:
    return Dyadic.of_q64(sum(e["sqUb64"] for e in es))


def elem_sym_interval64(es: list[dict], m: int) -> list[tuple[Dyadic, Dyadic]]:
    dp = [(Q64_SCALE, Q64_SCALE)] + [(0, 0)] * m
    for e in es:
        gl, gu = e["gLb64"], e["gUb64"]
        dp = [(Q64_SCALE, Q64_SCALE)] + [
            (cur[0] + ((gl * prev[0]) >> 64), cur[1] + ceil_shr(gu * prev[1], 64))
            for cur, prev in zip(dp[1:], dp)
        ]
    return [(Dyadic.of_q64(lo), Dyadic.of_q64(hi)) for lo, hi in dp]


def elem_sym_sums_dy(dp: list[tuple[Dyadic, Dyadic]]) -> tuple[Dyadic, Dyadic, Dyadic, Dyadic]:
    acc = [DY_ZERO, DY_ZERO, DY_ZERO, DY_ZERO]
    for j, (lo, hi) in enumerate(dp):
        idx = 0 if j % 2 == 0 else 2
        acc[idx], acc[idx + 1] = acc[idx].add(lo), acc[idx + 1].add(hi)
    return acc[0], acc[1], acc[2], acc[3]


def _fmt_summary(s: dict) -> str:
    return (f"⟨{s['lo']}, {s['hi']}, {s['cnt']}, {s['s1Ub'].to_lean()}, "
            f"{s['sMulUb'].to_lean()}, {s['sSqUb'].to_lean()}, {s['vLb'].to_lean()}, {s['vUb'].to_lean()}⟩")


def _fmt_entry(e: dict) -> str:
    return f"⟨{e['p']}, {e['gLb64']}, {e['gUb64']}, {e['mulUb64']}, {e['sqUb64']}, {e['vLb64']}, {e['vUb64']}, {e['phiUb64']}⟩"


def write_prime_tree_data_lean(out_path: Path) -> None:
    lines = [
        "import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstDefs",
        "",
        "set_option maxRecDepth 200000",
        "",
        "/-!",
        "# Machine-Generated Static Odd-Prime Segment Tree (`3 ≤ p < 27000`)",
        "Auto-generated by `scripts/sieve_cert/dyadic_mirror.py`. Do not edit by hand.",
        "-/",
        "",
        "namespace BuchstabSwitching.SieveInst",
        "",
    ]
    leaf_defs: list[str] = []

    def emit_node(node: dict, indent: str, lines_out: list[str]) -> None:
        if node["kind"] == "leaf":
            idx = len(leaf_defs)
            name = f"oddPrimeLeaf{idx:02d}"
            es = node["entries"]
            leaf_lines = [f"private def {name} : OddPrimeTree := .leaf {_fmt_summary(node['sum'])} ["]
            for j in range(0, len(es), 18):
                chunk = ", ".join(_fmt_entry(x) for x in es[j : j + 18])
                leaf_lines.append("  " + chunk + ("," if j + 18 < len(es) else ""))
            leaf_lines.append("]")
            leaf_defs.extend(leaf_lines)
            lines_out.append(f"{indent}{name}")
            return
        l_line: list[str] = []
        r_line: list[str] = []
        emit_node(node["left"], indent + "  ", l_line)
        emit_node(node["right"], indent + "  ", r_line)
        if len(l_line) == 1 and len(r_line) == 1:
            lines_out.append(f"{indent}.node {_fmt_summary(node['sum'])} ({l_line[0].strip()}) ({r_line[0].strip()})")
        else:
            lines_out.append(f"{indent}.node {_fmt_summary(node['sum'])}")
            lines_out.append(f"{indent}  ("); lines_out.extend(l_line); lines_out.append(f"{indent}  )")
            lines_out.append(f"{indent}  ("); lines_out.extend(r_line); lines_out.append(f"{indent}  )")

    tree_lines: list[str] = []
    emit_node(PRIME_TREE, "  ", tree_lines)
    lines.extend(leaf_defs)
    lines.append("")
    lines.append("def oddPrimeTree : OddPrimeTree :=")
    lines.extend(tree_lines)
    lines.extend(["", "end BuchstabSwitching.SieveInst", ""])
    out_path.write_text("\n".join(lines), encoding="utf-8")


if __name__ == "__main__":
    p = Path(__file__).resolve().parents[2] / "BuchstabSwitching/Sieve/Regime2SlabBridge/SlabCertInstPrimeTreeData.lean"
    write_prime_tree_data_lean(p)
    print(f"Wrote {p.name}: {len(p.read_text().splitlines())} lines")
