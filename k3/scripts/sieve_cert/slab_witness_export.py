"""
Pure-integer / outward-rounded Lean 4 witness exporter & Bool-verifier mirror for
all 127 Regime 2 slabs (`2a`: 21, `2b`: 40, `2c`: 66). Zero `float`, zero `math`.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
import re

from .bonferroni_engine import comb_int
from .brun_block_sieve import _BRUN_LOW_CAPS, _candidate_ends, adm_count
from .constants import PRIMES
from .interval import Iv, ceil_root_int, floor_root_int, pow_real_iv
from .schedule import SLABS_2A, SLABS_2B, SLABS_2C, Slab2ASpec, Slab2BSpec, Slab2CSpec

P_EXACT = 27000
PRIMES_EXACT: list[int] = [p for p in PRIMES if p < P_EXACT]
ODD_PRIMES_EXACT: list[int] = [p for p in PRIMES_EXACT if p >= 3]
SCI_SCALE, LOG_SCALE16, EXP_SCALE16, SCALE_S = 10**24, 10**16, 10**16, 10**12
LN2_LO16, LN2_HI16, LOG_TAIL16 = 6931471805599450, 6931471805599460, 12

def _fact(n: int) -> int:
    r = 1
    for j in range(2, n + 1): r *= j
    return r

def _prod(ps: list[int]) -> int:
    r = 1
    for p in ps: r *= p
    return r

def num_digits10(n: int) -> int:
    c = 0
    for _ in range(1000):
        if n == 0: return c
        c, n = c + 1, n // 10
    return c

class SciNat:
    __slots__ = ("m", "e")
    def __init__(self, m: int, e: int) -> None: self.m, self.e = m, e
    @staticmethod
    def of_nat(n: int) -> SciNat: return SciNat(n, 0)
    @staticmethod
    def ceil_div(n: int, d: int) -> int: return 0 if d == 0 else (n + d - 1) // d
    def ble(self, o: SciNat) -> bool: return self.m * (10 ** (o.e - self.e)) <= o.m if self.e <= o.e else self.m <= o.m * (10 ** (self.e - o.e))
    def blt(self, o: SciNat) -> bool: return self.m * (10 ** (o.e - self.e)) < o.m if self.e <= o.e else self.m < o.m * (10 ** (self.e - o.e))
    def mul(self, o: SciNat) -> SciNat: return SciNat(self.m * o.m, self.e + o.e)
    def add(self, o: SciNat) -> SciNat: return SciNat(self.m * (10 ** (o.e - self.e)) + o.m, o.e) if self.e <= o.e else SciNat(self.m + o.m * (10 ** (self.e - o.e)), self.e)
    def sub_lb(self, o: SciNat) -> SciNat: return SciNat(max(0, self.m * (10 ** (o.e - self.e)) - o.m), o.e) if self.e <= o.e else SciNat(max(0, self.m - o.m * (10 ** (self.e - o.e))), self.e)
    def div_ub(self, o: SciNat, prec: int = 24) -> SciNat: return SciNat(0, 0) if o.m == 0 else SciNat(SciNat.ceil_div(self.m * (10 ** (o.e + prec)), o.m), self.e + prec)
    def div_lb(self, o: SciNat, prec: int = 24) -> SciNat: return SciNat(0, 0) if o.m == 0 else SciNat((self.m * (10 ** (o.e + prec))) // o.m, self.e + prec)
    def trim_ub(self, mx: int = 30) -> SciNat: return self if self.e <= mx else SciNat(SciNat.ceil_div(self.m, 10 ** (self.e - mx)), mx)
    def trim_lb(self, mx: int = 30) -> SciNat: return self if self.e <= mx else SciNat(self.m // (10 ** (self.e - mx)), mx)
    def _trim_sig(self, sig: int, ub: bool) -> SciNat:
        d = min(max(0, num_digits10(self.m) - sig), self.e)
        return self if d == 0 else SciNat(SciNat.ceil_div(self.m, 10**d) if ub else self.m // (10**d), self.e - d)
    def trim_ub_sig(self, sig: int = 26) -> SciNat: return self._trim_sig(sig, True)
    def trim_lb_sig(self, sig: int = 26) -> SciNat: return self._trim_sig(sig, False)
    def ceil_nat(self) -> int: return SciNat.ceil_div(self.m, 10**self.e)
    def to_dec_floor(self, p: int = 18) -> Decimal:
        x = self.trim_lb_sig(30)
        return Decimal((x.m * (10**p)) // (10**x.e)) / Decimal(10**p)
    def to_dec_ceil(self, p: int = 18) -> Decimal:
        x = self.trim_ub_sig(30)
        return Decimal(SciNat.ceil_div(x.m * (10**p), 10**x.e)) / Decimal(10**p)
    def to_lean(self) -> str: return f"⟨{self.m}, {self.e}⟩"

_Z0, _ONE = SciNat(0, 0), SciNat(1, 0)
PI_LO4, LOG27000_LO, LOG27000_HI = SciNat(31415, 4), SciNat(102035921449864610, 16), SciNat(102035921449864778, 16)
V_PREFIX_27000_LB = SciNat(72601774652157303544786, 24)
H0_LO, H0_HI, CJ_UB, A0_LB, A0_UB = SciNat(1514236169719, 12), SciNat(1516136089708, 12), SciNat(8030531202875, 12), SciNat(63518, 5), SciNat(636, 3)

def div_sig_prec(b: SciNat, sig: int = 24) -> int: return max(0, num_digits10(b.m) - b.e) + sig
def div_ub_sig(a: SciNat, b: SciNat, sig: int = 24) -> SciNat: return a.div_ub(b, div_sig_prec(b, sig))
def div_lb_sig(a: SciNat, b: SciNat, sig: int = 24) -> SciNat: return a.div_lb(b, div_sig_prec(b, sig))

def _find_pow2_aux(num: int, den: int, fuel: int = 12, k: int = 0) -> int:
    for b in range(fuel - 1, -1, -1):
        if den * (1 << (k + (1 << b))) <= num: k += 1 << b
    return k

def sqrt_sci_bounds(n: int, prec: int = 18) -> tuple[bool, SciNat, SciNat]:
    scaled, s = n * (10 ** (2 * prec)), 0
    if scaled:
        g = 1 << (_find_pow2_aux(scaled, 1, 12, 0) // 2 + 1)
        for _ in range(16):
            if g == 0 or (gn := (g + scaled // g) // 2) >= g: break
            g = gn
        s = g
    return (s * s <= scaled < (s + 1) ** 2), SciNat(s, prec), SciNat(s + 1, prec)

def rat_log_bounds(num: int, den: int) -> tuple[bool, SciNat, SciNat]:
    k = _find_pow2_aux(num, den, 12, 0)
    p2 = den * (1 << k)
    if not (0 < den and p2 <= num < 2 * p2): return False, _Z0, _Z0
    a, b = num - p2, num + p2
    a2, b2, t_lo, t_hi, s_lo, s_hi = a * a, b * b, (LOG_SCALE16 * a) // b, SciNat.ceil_div(LOG_SCALE16 * a, b), 0, 0
    for j in range(14):
        d = 2 * j + 1
        s_lo, s_hi = s_lo + (2 * t_lo) // d, s_hi + SciNat.ceil_div(2 * t_hi, d)
        t_lo, t_hi = (t_lo * a2) // b2, SciNat.ceil_div(t_hi * a2, b2)
    return True, SciNat(k * LN2_LO16 + s_lo, 16), SciNat(k * LN2_HI16 + s_hi + LOG_TAIL16, 16)

def sci_log_bounds(a: SciNat) -> tuple[bool, SciNat, SciNat]: return rat_log_bounds(a.m, 10**a.e)

def exp_ub_bounds(t: SciNat) -> tuple[bool, SciNat]:
    s, p10 = 0, 10**t.e
    for _ in range(20):
        if 4 * t.m <= p10 * (1 << s): break
        s += 1
    den = p10 * (1 << s)
    if 4 * t.m > den: return False, _Z0
    t_cur, s_cur = EXP_SCALE16, 0
    for j in range(12): s_cur, t_cur = s_cur + t_cur, SciNat.ceil_div(t_cur * t.m, den * (j + 1))
    r = SciNat(s_cur + SciNat.ceil_div(13 * t_cur, 12), 16)
    for _ in range(s): r = r.mul(r).trim_ub(24)
    return True, r

def exp_ge(num: int, den: int) -> int:
    y_den, t, r = 32 * den, SCALE_S, SCALE_S
    for j in range(8):
        t = (t * num) // (y_den * (j + 1))
        r += t
    for _ in range(5): r = (r * r) // SCALE_S
    return r

def exp_neg_ub12(t: SciNat) -> SciNat:
    r = t.trim_lb(8); den = 10**r.e
    return SciNat(SCALE_S if r.m == 0 else (1 if 40 * den <= r.m else SciNat.ceil_div(SCALE_S * SCALE_S, exp_ge(r.m, den))), 12)

def exp_ge12(t: SciNat) -> SciNat:
    r = t.trim_lb(8)
    return SciNat(max(SCALE_S, exp_ge(r.m, 10**r.e)), 12)

_JODD_EXACT_SUMS = {
    1: 1000000000000, 2: 1000000000000, 4: 2000000000000, 8: 2533333333334,
    16: 3068686868690, 32: 3513315908048, 64: 4099455785525, 128: 4628412984809,
    256: 5171408917027, 512: 5691482868826, 1024: 6209544437640,
}
JODD_STEP_TABLE = [(m, rat_log_bounds(m, 1)[1], SciNat(_JODD_EXACT_SUMS[m], 12)) for m in _JODD_EXACT_SUMS]

def elem_sym_interval(ps: list[int], m: int) -> list[tuple[SciNat, SciNat]]:
    dp = [(_ONE, _ONE)] + [(_Z0, _Z0)] * m
    for p in ps:
        w_lo, w_ub = _ONE.div_lb(SciNat.of_nat(p - 1), 24), _ONE.div_ub(SciNat.of_nat(p - 1), 24)
        dp = [(_ONE, _ONE)] + [(c[0].add(w_lo.mul(pr[0])).trim_lb(24), c[1].add(w_ub.mul(pr[1])).trim_ub(24)) for c, pr in zip(dp[1:], dp)]
    return dp

def elem_sym_sums(dp: list[tuple[SciNat, SciNat]]) -> tuple[SciNat, SciNat, SciNat, SciNat]:
    acc = [_Z0, _Z0, _Z0, _Z0]
    for j, (lo, hi) in enumerate(dp):
        idx = 0 if j % 2 == 0 else 2
        acc[idx], acc[idx + 1] = acc[idx].add(lo), acc[idx + 1].add(hi)
    return acc[0], acc[1], acc[2], acc[3]

def v2_list(ps: list[int], is_lb: bool) -> SciNat:
    acc = SCI_SCALE
    for p in ps: acc = (acc * (p - 2)) // (p - 1) if is_lb else SciNat.ceil_div(acc * (p - 2), p - 1)
    return SciNat(acc, 24)

def inv_phi_list_ub(ps: list[int]) -> SciNat:
    acc = SCI_SCALE
    for p in ps: acc = SciNat.ceil_div(acc * p, p - 1)
    return SciNat(acc, 24)

def sum_g_list_ub(ps: list[int], sq: bool = False) -> SciNat:
    return SciNat(sum(SciNat.ceil_div(SCI_SCALE, (p - 1) ** 2 if sq else (p - 1)) for p in ps), 24)

def sci_pow_ub(a: SciNat, k: int) -> SciNat:
    res = _ONE
    for _ in range(k): res = res.mul(a).trim_ub(30)
    return res

def exact_inv_sum_ub(q0: int, q1: int, mode: str) -> SciNat:
    acc = SciNat(0, 24)
    for q in PRIMES_EXACT:
        if q0 <= q < q1:
            den = (q - 1) if mode == "sub1" else (q * (q - 1) if mode == "mul" else (q - 1) ** 2)
            acc = acc.add(_ONE.div_ub(SciNat.of_nat(den), 24))
    return acc

def exact_prime_count(q0: int, q1: int) -> int: return sum(1 for q in PRIMES_EXACT if q0 <= q < q1)

def exact_prod_one_sub_inv_pred(q0: int, q1: int, is_lb: bool) -> SciNat:
    acc = _ONE
    for p in PRIMES_EXACT:
        if q0 <= p < q1:
            r = SciNat.of_nat(p - 2).div_lb(SciNat.of_nat(p - 1), 24) if is_lb else SciNat.of_nat(p - 2).div_ub(SciNat.of_nat(p - 1), 24)
            acc = acc.mul(r).trim_lb(24) if is_lb else acc.mul(r).trim_ub(24)
    return acc

def calc_epd_ub(x_lo: int, log_lo: SciNat, log_hi: SciNat) -> SciNat:
    sqrt_lb, llx_lb = sqrt_sci_bounds(x_lo, 18)[1], sci_log_bounds(log_lo)[1]
    c_sum = div_ub_sig(SciNat(7, 0), SciNat(16, 0).mul(PI_LO4), 24).add(
        div_ub_sig(SciNat(6, 0).add(div_ub_sig(_ONE, PI_LO4, 24)), SciNat(4, 0).mul(log_lo), 24).add(
            div_ub_sig(SciNat(6, 0), log_lo.mul(log_lo), 24).add(div_ub_sig(SciNat(1045163780117493, 15), sqrt_lb.mul(log_lo), 24))))
    return div_ub_sig(c_sum.mul(log_hi.mul(log_hi)), sqrt_lb, 24).add(
        div_ub_sig(SciNat(13841, 4).mul(log_hi.mul(log_hi)), SciNat.of_nat(x_lo).mul(llx_lb), 24)).trim_ub_sig(26)

def calc_li_ratio_ub(x_lo: int, log_lo: SciNat, log_hi: SciNat) -> SciNat:
    sqrt_ub, llx_lb = sqrt_sci_bounds(x_lo, 18)[2], sci_log_bounds(log_lo)[1]
    loss = div_ub_sig(sqrt_ub.mul(log_hi.mul(log_hi)), SciNat(8, 0).mul(PI_LO4), 24).add(div_ub_sig(SciNat(13841, 4).mul(log_hi.mul(log_hi)), llx_lb, 24))
    return div_ub_sig(_ONE, _ONE.sub_lb(div_ub_sig(loss, SciNat.of_nat(x_lo), 24)), 24).trim_ub_sig(26)

def analytic_slice_aux(a: int, b: int, a_lo: SciNat, a_hi: SciNat, b_lo: SciNat, b_hi: SciNat) -> tuple[bool, SciNat, SciNat]:
    ok_ll, _, ll_ratio = sci_log_bounds(div_ub_sig(b_hi, a_lo, 24))
    ok_sa, _, a_sq_ub = sqrt_sci_bounds(a, 18)
    ok_sb2, _, b_sq_ub = sqrt_sci_bounds(b, 18)
    ok_sb, b_sq_lb, _ = sqrt_sci_bounds(b, 12)
    if not (P_EXACT <= a < b and SciNat(3, 0).blt(a_lo) and SciNat(3, 0).blt(b_lo) and ok_ll and ok_sa and ok_sb2 and (b > 10**12 or (ok_sb and b_sq_lb.m > 0))):
        return False, _Z0, _Z0
    hi_err = div_ub_sig(SciNat(6836, 9), b_lo, 24) if b > 10**12 else div_ub_sig(SciNat(2, 0), b_sq_lb.mul(b_lo), 24)
    sq_ub = ll_ratio.add(hi_err.add(div_ub_sig(SciNat(2964, 9), a_lo, 24).add(div_ub_sig(_ONE, SciNat.of_nat(a - 1), 24))))
    pi_diff = div_ub_sig(SciNat.of_nat(b - a), a_lo, 24).add(div_ub_sig(b_sq_ub.mul(b_hi).add(a_sq_ub.mul(a_hi)), SciNat(8, 0).mul(PI_LO4), 24).add(_ONE))
    pi_single = div_ub_sig(SciNat.of_nat(b), b_lo.sub_lb(SciNat(2, 0)), 24).add(SciNat(1045163780117493, 15).add(div_ub_sig(b_sq_ub.mul(b_hi), SciNat(8, 0).mul(PI_LO4), 24)))
    return True, sq_ub.trim_ub_sig(26), (pi_diff if pi_diff.ble(pi_single) else pi_single).trim_ub_sig(26)

def slice_bounds_lean(q0: int, q1: int, l0_lo: SciNat, l0_hi: SciNat, l1_lo: SciNat, l1_hi: SciNat) -> tuple[SciNat, SciNat]:
    if q1 <= q0: return _Z0, _Z0
    if q1 <= P_EXACT: return exact_inv_sum_ub(q0, q1, "sub1"), SciNat.of_nat(exact_prime_count(q0, q1))
    if P_EXACT <= q0:
        ok, sq, cnt = analytic_slice_aux(q0, q1, l0_lo, l0_hi, l1_lo, l1_hi); assert ok; return sq, cnt
    ok, sq_an, cnt_an = analytic_slice_aux(P_EXACT, q1, LOG27000_LO, LOG27000_HI, l1_lo, l1_hi); assert ok
    return exact_inv_sum_ub(q0, P_EXACT, "sub1").add(sq_an), SciNat.of_nat(exact_prime_count(q0, P_EXACT)).add(cnt_an)

def sum_pow_div_fact_ub(x: SciNat, k: int) -> SciNat:
    acc, fact = _ONE, 1
    for j in range(1, k + 1): fact *= j; acc = acc.add(div_ub_sig(sci_pow_ub(x, j), SciNat.of_nat(fact), 24))
    return acc

def compute_mertens_tail_2c(u: int, v: int, u_lo: SciNat, u_hi: SciNat, v_lo: SciNat, v_hi: SciNat) -> tuple[SciNat, SciNat, int]:
    if v <= u: return _Z0, _Z0, 0
    if v <= P_EXACT: return exact_inv_sum_ub(u, v, "sub1"), exact_inv_sum_ub(u, v, "sq"), exact_prime_count(u, v)
    if P_EXACT <= u:
        ok, s1, cnt = analytic_slice_aux(u, v, u_lo, u_hi, v_lo, v_hi); assert ok
        return s1, div_ub_sig(_ONE, SciNat.of_nat(u - 2), 24), cnt.ceil_nat()
    ok, s1_an, cnt_an = analytic_slice_aux(P_EXACT, v, LOG27000_LO, LOG27000_HI, v_lo, v_hi); assert ok
    return exact_inv_sum_ub(u, P_EXACT, "sub1").add(s1_an), exact_inv_sum_ub(u, P_EXACT, "sq").add(div_ub_sig(_ONE, SciNat.of_nat(26998), 24)), exact_prime_count(u, P_EXACT) + cnt_an.ceil_nat()

def v2_tail_lb_2c(u: int, v: int, u_lo: SciNat, u_hi: SciNat, v_lo: SciNat, v_hi: SciNat) -> SciNat:
    if v <= u: return _ONE
    if v <= P_EXACT: return exact_prod_one_sub_inv_pred(u, v, True)
    u0, (l0_lo, l0_hi) = (u, (u_lo, u_hi)) if P_EXACT <= u else (P_EXACT, (LOG27000_LO, LOG27000_HI))
    s1, s2, _ = compute_mertens_tail_2c(u0, v, l0_lo, l0_hi, v_lo, v_hi)
    tail_lb = div_lb_sig(_ONE, exp_ub_bounds(s1.add(div_ub_sig(SciNat.of_nat(u0 - 1), SciNat.of_nat(2 * (u0 - 2)), 24).mul(s2)))[1], 24)
    return tail_lb if P_EXACT <= u else exact_prod_one_sub_inv_pred(u, P_EXACT, True).mul(tail_lb).trim_lb(24)

def j_odd_lb_sci(log_lo: SciNat) -> SciNat:
    m, e = H0_LO.mul(log_lo.mul(SciNat(5, 1)).add(A0_LB)), CJ_UB.mul(exp_neg_ub12(div_lb_sig(log_lo, SciNat(4, 0), 8)))
    return m.sub_lb(e).trim_lb(12) if e.ble(m) else _Z0

def j_odd_ub_hybrid_sci(log_lo: SciNat, log_hi: SciNat) -> SciNat:
    asym = H0_HI.mul(log_hi.mul(SciNat(5, 1)).add(A0_UB)).add(CJ_UB.mul(exp_neg_ub12(div_lb_sig(log_lo, SciNat(4, 0), 8)))).trim_ub(12)
    for _, lm_lo, step_ub in JODD_STEP_TABLE:
        if log_hi.ble(lm_lo): return step_ub if step_ub.ble(asym) else asym
    return asym

def js_mert_hi_ub_sci(log_lo: SciNat) -> SciNat:
    t1 = div_ub_sig(SciNat(6836, 9), log_lo, 12)
    if SciNat(27631022, 6).ble(log_lo): return t1
    t2 = div_ub_sig(SciNat(2, 0), exp_ge12(log_lo.mul(SciNat(5, 1)).trim_lb(8)).mul(log_lo), 12)
    return t2 if t1.ble(t2) else t1

def _log_ratio_lb(log1_lo: SciNat, log0_hi: SciNat) -> SciNat:
    if log0_hi.m == 0: return _Z0
    r = div_lb_sig(log1_lo, log0_hi, 12)
    return rat_log_bounds(r.m, 10**r.e)[1] if _ONE.ble(r) else _Z0

def _lin_comb(z_v: SciNat, xi_v: SciNat, n1: int, n2: int, d: int, is_ub: bool) -> SciNat:
    return (div_ub_sig if is_ub else div_lb_sig)(SciNat.of_nat(n1).mul(z_v).add(SciNat.of_nat(n2).mul(xi_v)), SciNat.of_nat(d), 12)

def calc_j_full_lb_2c(z: int, z_lo: SciNat, z_hi: SciNat, xi_lb: SciNat, xi_lo: SciNat, xi_hi: SciNat) -> SciNat:
    if xi_lb.blt(SciNat.of_nat(z)): return j_odd_lb_sci(xi_lo)
    if not SciNat.of_nat(z).blt(xi_lb): return j_odd_lb_sci(z_lo.sub_lb(_ONE))
    s1 = s2 = _Z0
    for k in range(12):
        w0_lo, w0_hi = _lin_comb(z_lo, xi_lo, 12 - k, k, 12, False), _lin_comb(z_hi, xi_hi, 12 - k, k, 12, True)
        w1_lo, w1_hi = _lin_comb(z_lo, xi_lo, 11 - k, k + 1, 12, False), _lin_comb(z_hi, xi_hi, 11 - k, k + 1, 12, True)
        r_ub = div_ub_sig(w1_hi.add(div_ub_sig(_ONE, xi_lb, 12)) if k == 11 else w1_hi, w0_lo, 12)
        ok_l, _, r_log = rat_log_bounds(r_ub.m, 10**r_ub.e)
        w0_lb = exp_ge12(w0_lo); den2 = w0_lb.sub_lb(SciNat(2, 0))
        if not (SciNat(10, 0).blt(w0_lo) and SciNat(10, 0).blt(w1_lo) and SciNat(2, 0).ble(w0_lb) and _ONE.ble(den2) and ok_l): return _Z0
        mert = r_log.add(js_mert_hi_ub_sci(w1_lo)).add(div_ub_sig(SciNat(2964, 9), w0_lo, 12)).add(div_ub_sig(SciNat(2, 0), den2, 12))
        s1 = s1.add(j_odd_ub_hybrid_sci(xi_lo.sub_lb(w0_hi), xi_hi.sub_lb(w0_lo)).mul(mert))
    if z_hi.mul(SciNat(2, 0)).blt(xi_lo):
        td_lo, td_hi = xi_lo.sub_lb(z_hi.mul(SciNat(2, 0))), xi_hi.sub_lb(z_lo.mul(SciNat(2, 0)))
        for i in range(3):
            a0_lo = z_lo.add(div_lb_sig(SciNat.of_nat(i).mul(td_lo), SciNat(8, 0), 12))
            a0_hi = z_hi.add(div_ub_sig(SciNat.of_nat(i).mul(td_hi), SciNat(8, 0), 12))
            a1_lo = z_lo.add(div_lb_sig(SciNat.of_nat(i + 1).mul(td_lo), SciNat(8, 0), 12))
            t1 = _log_ratio_lb(a1_lo, a0_hi).sub_lb(div_ub_sig(SciNat(2964, 9), a1_lo, 12).add(js_mert_hi_ub_sci(a0_lo)))
            for j in range(4):
                c0, c1 = 2 * (i + 1) + j * (3 - i), 2 * (i + 1) + (j + 1) * (3 - i)
                b0_lo = z_lo.add(div_lb_sig(SciNat.of_nat(c0).mul(td_lo), SciNat(16, 0), 12))
                b0_hi = z_hi.add(div_ub_sig(SciNat.of_nat(c0).mul(td_hi), SciNat(16, 0), 12))
                b1_lo = z_lo.add(div_lb_sig(SciNat.of_nat(c1).mul(td_lo), SciNat(16, 0), 12))
                t2 = _log_ratio_lb(b1_lo, b0_hi).sub_lb(div_ub_sig(SciNat(2964, 9), b1_lo, 12).add(js_mert_hi_ub_sci(b0_lo)))
                s2 = s2.add(t1.mul(t2).mul(j_odd_lb_sci(div_lb_sig(SciNat.of_nat((3 - i) * (3 - j)).mul(td_lo), SciNat(16, 0), 12))))
    base = j_odd_lb_sci(xi_lo).add(s2)
    return base.sub_lb(s1).trim_lb_sig(14) if s1.ble(base) else _Z0

def _build_slices_geom(z: int, y: int, k_sl: int) -> list[int]:
    r_sl = pow_real_iv(Iv(y, y) / Iv(z, z), Iv.from_frac(Fraction(1, k_sl)))
    bpts, cur = [z], Iv(z, z)
    for _ in range(k_sl - 1):
        cur = cur * r_sl; v = int(cur.hi)
        if bpts[-1] < v < y: bpts.append(v)
    if z < P_EXACT < y and P_EXACT not in bpts: bpts.append(P_EXACT); bpts.sort()
    bpts.append(y)
    return bpts

@dataclass(frozen=True)
class Witness2abResult:
    slab: dict; main_lo_dec: Decimal; err_hi_dec: Decimal; sieve_net_lo_dec: Decimal

@dataclass(frozen=True)
class Witness2cResult:
    slab: dict; main_lo_dec: Decimal; err_hi_dec: Decimal; note: str

_CUTOFF_2AB_CACHE: dict[int, list[tuple]] = {}

def _g_lb_analytic(p2: list[int], s1_ub: SciNat, s2_ub: SciNat) -> SciNat:
    return _ONE if not p2 else div_lb_sig(_ONE, exp_ub_bounds(s1_ub.add(SciNat.of_nat(p2[0] - 1).div_ub(SciNat.of_nat(2 * (p2[0] - 2)), 24).mul(s2_ub)))[1], 24)

def _get_exact_ev_opts(cutoffs: tuple[int, ...]) -> list[tuple]:
    out = []
    for zs in cutoffs:
        if zs not in _CUTOFF_2AB_CACHE:
            ps, v_sub_ub, opts = [p for p in ODD_PRIMES_EXACT if p < zs], exact_prod_one_sub_inv_pred(3, zs, False), []
            for aq in range(0, min(len(ps), 11), 2):
                q1, p2 = ps[:aq], ps[aq:]
                qq, inv_qq, dp, g_p2_lb = _prod(q1), inv_phi_list_ub(q1), elem_sym_interval(p2, min(8, len(p2))), v2_list(p2, True)
                g_sub_lb = _g_lb_analytic(p2, sum_g_list_ub(p2), sum_g_list_ub(p2, True))
                for mev in (1, 2, 3, 4):
                    k = 2 * mev
                    if k > len(p2): continue
                    prod_ev = qq * _prod(p2[-k:])
                    if not p2: rat_ub, ip2_ub = _ONE, inv_qq
                    else:
                        sums = elem_sym_sums(dp[: k + 1]); em = max(sums[1].e, sums[2].e)
                        dm = sums[1].m * (10 ** (em - sums[1].e)) - sums[2].m * (10 ** (em - sums[2].e))
                        rat_ub = _Z0 if dm <= 0 else SciNat(dm, em).div_ub(g_p2_lb, 24).trim_ub_sig(26)
                        ip2_ub = inv_qq.mul(sums[1].add(sums[3])).trim_ub_sig(26)
                    opts.append((prod_ev, v_sub_ub, rat_ub, ip2_ub, (1 << aq) * sum(comb_int(len(p2), j) for j in range(k + 1)), zs, aq, mev, 1, g_sub_lb))
            _CUTOFF_2AB_CACHE[zs] = opts
        out.extend(_CUTOFF_2AB_CACHE[zs])
    return out

def _p_sub_opts(p_full: list[int], sqrt_x_lo: int) -> list[tuple]:
    opts, prod = [], 1
    for k_sub, p in enumerate(p_full, 1):
        prod *= p
        if prod > sqrt_x_lo: break
        opts.append((prod, exact_prod_one_sub_inv_pred(3, p + 1, False), _ONE, inv_phi_list_ub(p_full[:k_sub]), 1 << k_sub, p + 1, k_sub, 0, 1, _ONE))
    return opts

def _analytic_ev_opts_2ab(z: int, sqrt_x_lo: int) -> list[tuple]:
    ps, v_sub_ub, opts = [p for p in ODD_PRIMES_EXACT if p < z], exact_prod_one_sub_inv_pred(3, z, False), []
    for aq in (0, 2, 4, 6, 8, 10):
        if aq >= len(ps): break
        q1, p2 = ps[:aq], ps[aq:]; qq = _prod(q1)
        if qq > sqrt_x_lo: break
        s1_ub, s2_ub = sum_g_list_ub(p2), sum_g_list_ub(p2, True)
        g_sub_lb, ip2_ub = _g_lb_analytic(p2, s1_ub, s2_ub), inv_phi_list_ub(q1).mul(exp_ub_bounds(s1_ub)[1]).trim_ub_sig(26)
        for mev in (1, 2, 3, 4):
            k = 2 * mev
            if k > len(p2) or (prod_ev := qq * _prod(p2[-k:])) > sqrt_x_lo: continue
            rat_ub = _ONE.add(sci_pow_ub(s1_ub, k + 1).div_ub(SciNat.of_nat(_fact(k + 1)).mul(g_sub_lb), 24)).trim_ub_sig(26)
            opts.append((prod_ev, v_sub_ub, rat_ub, ip2_ub, (1 << aq) * sum(comb_int(len(p2), j) for j in range(k + 1)), z, aq, mev, 2, g_sub_lb))
    return opts

def _mk_sl2ab(q0, q1, kind, zs, aq, mev, nd, dm, sq, cnt, l0, l1, ip2, vsub, gsub, rat, msl, esl) -> dict:
    return {"q0": q0, "q1": q1, "kind": kind, "zSub": zs, "aQ": aq, "mEv": mev, "nD": nd, "dMax": dm, "sqUb": sq, "cntUb": cnt,
            "logQ0Lb": l0[0], "logQ0Ub": l0[1], "logQ1Lb": l1[0], "logQ1Ub": l1[1], "ip2": ip2, "vSubUb": vsub, "gSubLb": gsub, "ratUb": rat, "mSl": msl, "eSl": esl}

def _mk_sl2c(q0, q1, is_sel, zs, aq, mev, nd, dm, hq, xi, xilo, xihi, jf, sq, cnt, l0, l1, ip2, vsub, gsub, rat, mrat, s3c, es1, f0, msl, esl) -> dict:
    return {"q0": q0, "q1": q1, "isSelberg": is_sel, "zSub": zs, "aQ": aq, "mEv": mev, "nD": nd, "dMax": dm, "hQ": hq, "xiQLb": xi, "xiQUb": xi,
            "xiQLogLb": xilo, "xiQLogUb": xihi, "jfLb": jf, "sqUb": sq, "cntUb": cnt, "logQ0Lb": l0[0], "logQ0Ub": l0[1], "logQ1Lb": l1[0],
            "logQ1Ub": l1[1], "ip2": ip2, "vSubUb": vsub, "gSubLb": gsub, "ratUb": rat, "mRatUb": mrat, "s3cUb": s3c, "es1Ub": es1, "f0Ub": f0, "mSl": msl, "eSl": esl}

def build_slab_2ab_witness(reg: str, spec: Slab2ASpec | Slab2BSpec) -> Witness2abResult:
    z = spec.z if isinstance(spec, Slab2ASpec) else ceil_root_int(spec.x_hi, spec.m_div)
    y = max(ceil_root_int(spec.x_hi + 1, 4), ceil_root_int((spec.x_hi + z - 1) // z, 3))
    sqrt_x_lo, q_sq = floor_root_int(spec.x_lo, 2), floor_root_int(spec.x_lo, 4)
    _, x_lo_lb, x_lo_ub = rat_log_bounds(spec.x_lo, 1)
    x_hi_ub, epd_ub = rat_log_bounds(spec.x_hi, 1)[2], calc_epd_ub(spec.x_lo, x_lo_lb, x_lo_ub)
    ps = [p for p in ODD_PRIMES_EXACT if p < z]
    q1, p2, k_odd = ps[: spec.a], ps[spec.a :], spec.m_odd
    d_max, n_d = _prod(q1) * _prod(p2[-k_odd:] if k_odd > 0 else []), (1 << spec.a) * sum(comb_int(len(p2), j) for j in range(k_odd + 1))
    v_full_lb, v_full_ub = exact_prod_one_sub_inv_pred(3, z, True), exact_prod_one_sub_inv_pred(3, z, False)
    if not p2: rat_lb, use_ana, g_lb = _ONE, False, _Z0
    elif z <= 1500:
        sums, g_p2_ub = elem_sym_sums(elem_sym_interval(p2, k_odd)), v2_list(p2, False); em = max(sums[0].e, sums[3].e)
        rat_lb, use_ana, g_lb = SciNat(sums[0].m * (10 ** (em - sums[0].e)) - sums[3].m * (10 ** (em - sums[3].e)), em).div_lb(g_p2_ub, 24).trim_lb_sig(26), False, _Z0
    else:
        s1_ub, s2_ub = sum_g_list_ub(p2), sum_g_list_ub(p2, True); g_lb = _g_lb_analytic(p2, s1_ub, s2_ub)
        rat_lb, use_ana = _ONE.sub_lb(sci_pow_ub(s1_ub, k_odd + 1).div_ub(SciNat.of_nat(_fact(k_odd + 1)).mul(g_lb), 24)).trim_lb_sig(26), True
    if reg == "2a":
        cutoffs = tuple(sorted(set([c for c in (11, 17, 23, 29, 37) if c <= z] + [z])))
        bpts = (_build_slices_geom(z, P_EXACT, 48)[:-1] + _build_slices_geom(P_EXACT, y, 4)) if z < P_EXACT < y else _build_slices_geom(z, y, 64)
        ev_opts = _p_sub_opts(ps, sqrt_x_lo) + _get_exact_ev_opts(cutoffs)
    else:
        cutoffs = tuple(sorted(set([c for c in (29, 89, 251, 600, 1500) if c < z] + ([z] if z <= 1500 else []))))
        bpts = _build_slices_geom(z, y, 56)
        ev_opts = _p_sub_opts(ps[:18], sqrt_x_lo) + _get_exact_ev_opts(cutoffs) + (_analytic_ev_opts_2ab(z, sqrt_x_lo) if z > 1500 else [])
    slices_w, sum_m, sum_e = [], _Z0, _Z0
    for q0, q1s in zip(bpts[:-1], bpts[1:]):
        l0, l1 = rat_log_bounds(q0, 1)[1:] if q0 >= P_EXACT else (_Z0, _Z0), rat_log_bounds(q1s, 1)[1:] if q1s > P_EXACT else (_Z0, _Z0)
        sq_ub, cnt_ub = slice_bounds_lean(q0, q1s, l0[0], l0[1], l1[0], l1[1]); q_max, best = q1s - 1, None
        if q_max * q_max <= spec.x_lo:
            m0, e0 = sq_ub, cnt_ub.mul(epd_ub).trim_ub_sig(26)
            best = (m0.add(e0), _mk_sl2ab(q0, q1s, 0, 0, 0, 0, 0, 0, sq_ub, cnt_ub, l0, l1, _Z0, _Z0, _Z0, _Z0, m0, e0))
        for pe, v_sub_ub, rat_ub, ip2_ub, nd_ev, zs, aq, mev, kind, g_sub_lb in ev_opts:
            if q_max * pe > sqrt_x_lo: continue
            m_sl, e_sl = sq_ub.mul(v_sub_ub).mul(rat_ub).trim_ub_sig(26), cnt_ub.mul(SciNat.of_nat(nd_ev).add(ip2_ub.add(rat_ub))).mul(epd_ub).trim_ub_sig(26)
            if best is None or m_sl.add(e_sl).blt(best[0]):
                best = (m_sl.add(e_sl), _mk_sl2ab(q0, q1s, kind, zs, aq, mev, nd_ev, pe, sq_ub, cnt_ub, l0, l1, ip2_ub, v_sub_ub, g_sub_lb, rat_ub, m_sl, e_sl))
        assert best is not None
        slices_w.append(best[1]); sum_m, sum_e = sum_m.add(best[1]["mSl"]), sum_e.add(best[1]["eSl"])
    q_end = min(y, q_sq + 1)
    s_q2_ub = exact_inv_sum_ub(z, min(q_end, P_EXACT), "mul").add(_ONE.div_ub(SciNat.of_nat(P_EXACT - 1), 24) if q_end > P_EXACT else _Z0).trim_ub_sig(26)
    e_lo, e_hi = rat_log_bounds(q_end, 1)[1:] if q_end > P_EXACT else (_Z0, _Z0)
    cnt_lo_ub = slice_bounds_lean(z, q_end, x_lo_lb, x_lo_ub, e_lo, e_hi)[1]
    err_q2_ub = s_q2_ub.add(cnt_lo_ub.mul(epd_ub).add(_Z0 if y <= q_sq + 1 else x_hi_ub.div_ub(SciNat.of_nat(q_sq), 24))).div_ub(SciNat(2, 0), 28).trim_ub_sig(26)
    main_sci = v_full_lb.mul(rat_lb).sub_lb(div_ub_sig(sum_m, SciNat(2, 0), 24)).trim_lb_sig(26)
    err_sci = SciNat.of_nat(n_d).mul(epd_ub).add(err_q2_ub).add(div_ub_sig(sum_e, SciNat(2, 0), 24)).trim_ub_sig(26)
    snet_sci = div_lb_sig(main_sci.sub_lb(err_sci), v_full_ub, 24).trim_lb_sig(26)
    slab_w = {"xLoLogLb": x_lo_lb, "xLoLogUb": x_lo_ub, "xHiLogUb": x_hi_ub, "epdUb": epd_ub,
              "lower": {"a": spec.a, "mOdd": (k_odd - 1) // 2, "nD": n_d, "dMax": d_max, "useAnalytic": use_ana, "ratLb": rat_lb, "vFullLb": v_full_lb, "vFullUb": v_full_ub, "gLb": g_lb},
              "slices": slices_w, "square": {"qSq": q_sq, "sQ2Ub": s_q2_ub, "cntLoUb": cnt_lo_ub, "logEndLb": e_lo, "logEndUb": e_hi, "errQ2Ub": err_q2_ub}}
    return Witness2abResult(slab_w, main_sci.to_dec_floor(18), err_sci.to_dec_ceil(18), snet_sci.to_dec_floor(18))

def build_slab_2c_witness(spec: Slab2CSpec) -> Witness2cResult:
    z = ceil_root_int(spec.x_hi, spec.m_div)
    y = max(ceil_root_int(spec.x_hi + 1, 4), ceil_root_int((spec.x_hi + z - 1) // z, 3))
    sqrt_x_lo, q_sq = floor_root_int(spec.x_lo, 2), floor_root_int(spec.x_lo, 4)
    _, x_lo_lb, x_lo_ub = rat_log_bounds(spec.x_lo, 1)
    x_hi_ub, (_, z_lo, z_hi) = rat_log_bounds(spec.x_hi, 1)[2], rat_log_bounds(z, 1)
    epd_ub, li_r_ub = calc_epd_ub(spec.x_lo, x_lo_lb, x_lo_ub), calc_li_ratio_ub(spec.x_lo, x_lo_lb, x_lo_ub)
    v_full_lb = exact_prod_one_sub_inv_pred(3, z, True) if z <= P_EXACT else V_PREFIX_27000_LB.mul(div_lb_sig(_ONE, exp_ub_bounds(analytic_slice_aux(P_EXACT, z, LOG27000_LO, LOG27000_HI, z_lo, z_hi)[1].add(div_ub_sig(SciNat(26999, 0), SciNat(53996 * 26998, 0), 24)))[1], 24)).trim_lb_sig(26)
    best_low = None
    for mo_k in (7, 9, 11):
        z_k, qp = z**mo_k, 1
        if z_k > sqrt_x_lo: break
        for a in range(35):
            if a > 0: qp *= ODD_PRIMES_EXACT[a - 1]
            p_min = ODD_PRIMES_EXACT[a]
            if qp * z_k > sqrt_x_lo or p_min >= z: break
            s1_ub, _, pi_n = compute_mertens_tail_2c(p_min, z, _Z0, _Z0, z_lo, z_hi); g_lb = v2_tail_lb_2c(p_min, z, _Z0, _Z0, z_lo, z_hi)
            err_t = div_ub_sig(sci_pow_ub(s1_ub, mo_k + 1), SciNat.of_nat(_fact(mo_k + 1)).mul(g_lb), 24)
            if err_t.ble(_ONE):
                rat_lb = _ONE.sub_lb(err_t).trim_lb_sig(26)
                n_d = SciNat.of_nat(1 << a).mul(sum_pow_div_fact_ub(SciNat.of_nat(pi_n), mo_k)).ceil_nat()
                rem_norm = div_ub_sig(SciNat.of_nat(n_d).mul(epd_ub), v_full_lb, 24).trim_ub_sig(26)
                score = rat_lb.sub_lb(rem_norm)
                if best_low is None or best_low[0].blt(score):
                    best_low = (score, {"isBrun": False, "a": a, "mOdd": (mo_k - 1) // 2, "ends": [], "caps": [], "nD": n_d, "dMax": qp * z_k,
                                        "zLogLb": z_lo, "zLogUb": z_hi, "piZUb": SciNat.of_nat(pi_n), "gLb": g_lb, "s1Ub": s1_ub, "s2Ub": _Z0, "ratLb": rat_lb, "remANormUb": rem_norm}, f"Bonf(a={a},m={mo_k})")
    log_cache, tail_cache = {z: (z_lo, z_hi)}, {}
    get_log = lambda x: (_Z0, _Z0) if x < P_EXACT else log_cache.setdefault(x, rat_log_bounds(x, 1)[1:])
    get_tail_z = lambda nxt: tail_cache.setdefault(nxt, (compute_mertens_tail_2c(nxt, z, *get_log(nxt), z_lo, z_hi)[0], v2_tail_lb_2c(nxt, z, *get_log(nxt), z_lo, z_hi)))
    for a in (0, 2, 4, 6, 8, 10, 12):
        qp, pa1 = _prod(ODD_PRIMES_EXACT[:a]), 3 if a == 0 else ODD_PRIMES_EXACT[a - 1] + 1
        if pa1 >= z or qp >= sqrt_x_lo: break
        budget, local_best = sqrt_x_lo // qp, None
        for caps in _BRUN_LOW_CAPS:
            for ends in _candidate_ends(caps, z, pa1, budget):
                e_tot = _Z0
                for i in range(1, len(ends)):
                    s1_t, v_lb = get_tail_z(ends[i])
                    e_tot = e_tot.add(div_ub_sig(sci_pow_ub(s1_t, caps[i - 1] + 1), SciNat.of_nat(_fact(caps[i - 1] + 1)).mul(v_lb), 24))
                if e_tot.ble(_ONE) and (local_best is None or e_tot.blt(local_best[0])): local_best = (e_tot, caps, ends)
        if local_best is not None:
            e_tot, caps, ends = local_best
            n_d = (1 << a) * adm_count(caps, [compute_mertens_tail_2c(ends[i + 1], ends[i], *get_log(ends[i + 1]), *get_log(ends[i]))[2] for i in range(len(caps))])
            mod_b, prev = 1, 0
            for idx_b, m_cap in enumerate(caps): mod_b, prev = mod_b * (ends[idx_b] ** (m_cap - prev)), m_cap
            rat_lb, rem_norm = _ONE.sub_lb(e_tot).trim_lb_sig(26), div_ub_sig(SciNat.of_nat(n_d).mul(epd_ub), v_full_lb, 24).trim_ub_sig(26)
            if best_low is None or best_low[0].blt(rat_lb.sub_lb(rem_norm)):
                best_low = (rat_lb.sub_lb(rem_norm), {"isBrun": True, "a": a, "mOdd": 0, "ends": list(ends), "caps": list(caps), "nD": n_d, "dMax": qp * mod_b,
                                                      "zLogLb": z_lo, "zLogUb": z_hi, "piZUb": _Z0, "gLb": _Z0, "s1Ub": _Z0, "s2Ub": _Z0, "ratLb": rat_lb, "remANormUb": rem_norm},
                            f"Brun(a={a},caps=({','.join(str(c) for c in caps)}))")
    assert best_low is not None; _, lo_w, sa_tag = best_low
    bpts, ev_2c = _build_slices_geom(z, y, 48), []
    for zs in (29, 89, 251, 600, 1500):
        if zs < z:
            for pe, v_sub_ub, rat_ub, ip2_ub, nd_ev, _, aq, mev, _, g_sub_lb in _get_exact_ev_opts((zs,)):
                if pe <= sqrt_x_lo: ev_2c.append((pe, zs, aq, mev, nd_ev, ip2_ub, v_sub_ub, g_sub_lb, rat_ub, div_ub_sig(v_sub_ub.mul(rat_ub), v_full_lb, 24).trim_ub_sig(26)))
    for aq in (0, 2, 4, 6, 8, 10):
        p_min, qq = ODD_PRIMES_EXACT[aq], _prod(ODD_PRIMES_EXACT[:aq])
        if p_min >= z or qq > sqrt_x_lo: break
        s1_ub, _, pi_n = compute_mertens_tail_2c(p_min, z, _Z0, _Z0, z_lo, z_hi)
        g_sub_lb, ip2_ub = v2_tail_lb_2c(p_min, z, _Z0, _Z0, z_lo, z_hi), inv_phi_list_ub(ODD_PRIMES_EXACT[:aq]).mul(exp_ub_bounds(s1_ub)[1]).trim_ub_sig(26)
        for mev in (1, 2, 3, 4):
            k, pe = 2 * mev, qq * (z ** (2 * mev))
            if pe > sqrt_x_lo: break
            rat_ub = _ONE.add(div_ub_sig(sci_pow_ub(s1_ub, k + 1), SciNat.of_nat(_fact(k + 1)).mul(g_sub_lb), 24)).trim_ub_sig(26)
            ev_2c.append((pe, z, aq, mev, SciNat.of_nat(1 << aq).mul(sum_pow_div_fact_ub(SciNat.of_nat(pi_n), k)).ceil_nat(), ip2_ub, _Z0, g_sub_lb, rat_ub, rat_ub))
    l4 = x_lo_ub.mul(x_lo_ub).mul(x_lo_ub).mul(x_lo_ub)
    hq_cands = [hq for km, ke in ((2, 3), (8, 3), (3, 2), (15, 2), (8, 1))
                for hq in [div_lb_sig(sqrt_sci_bounds(spec.x_lo, 18)[1], SciNat(km, ke).mul(l4), 12)] if hq.m > 0 and hq.mul(hq).ble(SciNat.of_nat(spec.x_lo))]
    z_cap_s6, jf_cache, slices_w, sum_m, sum_e, cnt_bonf, cnt_sel = min(floor_root_int((z**297) * (10**600), 100), (z**3) * (10**6) - 1), {}, [], _Z0, _Z0, 0, 0
    for q0, q1s in zip(bpts[:-1], bpts[1:]):
        l0, l1 = get_log(q0), get_log(q1s)
        sq_ub, cnt_ub = slice_bounds_lean(q0, q1s, l0[0], l0[1], l1[0], l1[1]); q_max, best = q1s - 1, None
        for pe, zs, aq, mev, nd_ev, ip2_ub, v_sub_ub, g_sub_lb, rat_ub, m_rat_ub in ev_2c:
            if q_max * pe > sqrt_x_lo: continue
            m_sl, e_sl = sq_ub.mul(m_rat_ub).trim_ub_sig(26), div_ub_sig(cnt_ub.mul(SciNat.of_nat(nd_ev).add(ip2_ub.add(rat_ub))).mul(epd_ub), v_full_lb, 24).trim_ub_sig(26)
            if best is None or m_sl.add(e_sl).blt(best[0]):
                best = (m_sl.add(e_sl), _mk_sl2c(q0, q1s, False, zs, aq, mev, nd_ev, pe, _Z0, _Z0, _Z0, _Z0, _Z0, sq_ub, cnt_ub, l0, l1, ip2_ub, v_sub_ub, g_sub_lb, rat_ub, m_rat_ub, _Z0, _Z0, _Z0, m_sl, e_sl))
        for hq in hq_cands:
            xi2_ub = div_lb_sig(hq, SciNat.of_nat(q_max), 16)
            xi_s6 = min(floor_root_int((xi2_ub.m * (10**12)) // (10**xi2_ub.e), 2), z_cap_s6); xi = SciNat(xi_s6, 6)
            if xi_s6 < 10**6 or not (_ONE.ble(xi) and xi.blt(SciNat.of_nat(z**3)) and SciNat.of_nat(q_max).mul(xi.mul(xi)).ble(hq)): continue
            if xi_s6 not in jf_cache:
                _, xlo, xhi = sci_log_bounds(xi)
                jf_cache[xi_s6] = (xlo, xhi, calc_j_full_lb_2c(z, z_lo, z_hi, xi, xlo, xhi))
            xi_lo, xi_hi, jf_lb = jf_cache[xi_s6]
            if jf_lb.m <= 0: continue
            m_sl = div_ub_sig(sq_ub, v_full_lb.mul(jf_lb), 24).trim_ub_sig(26)
            s3c_a, s3c_b = cnt_ub.mul(xi.mul(xi)), sq_ub.mul(hq)
            s3c = (s3c_a if s3c_a.ble(s3c_b) else s3c_b).trim_ub_sig(26)
            es1 = SciNat(625, 4).mul(s3c).mul(sci_pow_ub(SciNat(2, 0).mul(xi_hi).add(SciNat(6, 0)), 2)).mul(epd_ub).trim_ub_sig(26)
            f0 = xi_hi.add(SciNat(636, 3).add(div_ub_sig(SciNat(78, 2), xi.mul(xi), 24))).trim_ub_sig(26)
            e_sl = div_ub_sig(es1.add(cnt_ub.mul(_ONE.add(sci_pow_ub(SciNat(13, 1).mul(f0), 3))).mul(epd_ub)), v_full_lb, 24).trim_ub_sig(26)
            if best is None or m_sl.add(e_sl).blt(best[0]):
                best = (m_sl.add(e_sl), _mk_sl2c(q0, q1s, True, 0, 0, 0, 0, 0, hq, xi, xi_lo, xi_hi, jf_lb, sq_ub, cnt_ub, l0, l1, _Z0, _Z0, _Z0, _Z0, _Z0, s3c, es1, f0, m_sl, e_sl))
        assert best is not None
        cnt_sel += int(best[1]["isSelberg"]); cnt_bonf += int(not best[1]["isSelberg"])
        slices_w.append(best[1]); sum_m, sum_e = sum_m.add(best[1]["mSl"]), sum_e.add(best[1]["eSl"])
    q_end, s_q2_ub = min(y, q_sq + 1), div_ub_sig(_ONE, SciNat.of_nat(z - 1), 24).trim_ub_sig(26)
    e_lo, e_hi = get_log(q_end); cnt_lo_ub = slice_bounds_lean(z, q_end, z_lo, z_hi, e_lo, e_hi)[1]
    err_q2_ub = s_q2_ub.add(cnt_lo_ub.mul(epd_ub).add(_Z0 if y <= q_sq + 1 else div_ub_sig(x_hi_ub, SciNat.of_nat(q_sq), 24))).div_ub(SciNat(2, 0), 28).trim_ub_sig(26)
    err_q2_norm = div_ub_sig(err_q2_ub, v_full_lb, 24).trim_ub_sig(26)
    main_sci = lo_w["ratLb"].sub_lb(div_ub_sig(sum_m, SciNat(2, 0), 24)).trim_lb_sig(26)
    err_sci = lo_w["remANormUb"].add(err_q2_norm).add(div_ub_sig(sum_e, SciNat(2, 0), 24)).trim_ub_sig(26)
    slab_w = {"xLoLogLb": x_lo_lb, "xLoLogUb": x_lo_ub, "xHiLogUb": x_hi_ub, "zLogLb": z_lo, "zLogUb": z_hi, "epdUb": epd_ub,
              "liRatioUb": li_r_ub, "vFullLb": v_full_lb, "lower": lo_w, "slices": slices_w,
              "square": {"qSq": q_sq, "sQ2Ub": s_q2_ub, "cntLoUb": cnt_lo_ub, "logEndLb": e_lo, "logEndUb": e_hi, "errQ2Ub": err_q2_ub}, "errQ2NormUb": err_q2_norm}
    return Witness2cResult(slab_w, main_sci.to_dec_floor(18), err_sci.to_dec_ceil(18), f"{sa_tag} (F:{cnt_bonf} S:{cnt_sel})")

def _verify_header(c: dict, w: dict, lt27k: bool) -> bool:
    if not (c["den"] > 0 and c["net_num"] > 0 and c["err_num"] > 0 and c["net_num"] + c["err_num"] <= c["main_num"]
            and c["X_lo"] < c["X_hi"] and 2 <= c["z"] <= c["y"] and c["X_hi"] <= c["y"] ** 4
            and c["X_hi"] <= c["z"] * (c["y"] ** 3) and 4 * 10**18 <= c["X_lo"] and ((not lt27k) or c["z"] < P_EXACT)): return False
    ok_xl, xl_lo, xl_hi = rat_log_bounds(c["X_lo"], 1); ok_xh, _, xh_hi = rat_log_bounds(c["X_hi"], 1)
    if not (ok_xl and w["xLoLogLb"].ble(xl_lo) and xl_hi.ble(w["xLoLogUb"]) and ok_xh and xh_hi.ble(w["xHiLogUb"])
            and calc_epd_ub(c["X_lo"], w["xLoLogLb"], w["xLoLogUb"]).ble(w["epdUb"])): return False
    cur = c["z"]
    for sl in w["slices"]:
        if sl["q0"] != cur or sl["q0"] > sl["q1"]: return False
        cur = sl["q1"]
    return cur == c["y"]

def _verify_sl_bounds(sl: dict) -> bool:
    for q_cond, qk, lk0, lk1 in ((sl["q0"] >= P_EXACT, "q0", "logQ0Lb", "logQ0Ub"), (sl["q1"] > P_EXACT, "q1", "logQ1Lb", "logQ1Ub")):
        if q_cond:
            ok, l0, l1 = rat_log_bounds(sl[qk], 1)
            if not (ok and sl[lk0].ble(l0) and l1.ble(sl[lk1])): return False
    sq_r, cnt_r = slice_bounds_lean(sl["q0"], sl["q1"], sl["logQ0Lb"], sl["logQ0Ub"], sl["logQ1Lb"], sl["logQ1Ub"])
    return sq_r.ble(sl["sqUb"]) and cnt_r.ble(sl["cntUb"])

def _verify_eb_small_mode(c: dict, sl: dict, pss: list[int], qqs: list[int], p2s: list[int], ks: int, mode: int) -> bool:
    dp_s = _prod(qqs) * _prod(p2s[-ks:] if ks > 0 else [])
    if not (sl["zSub"] <= P_EXACT and sl["zSub"] <= c["z"] and sl["aQ"] <= len(pss) and dp_s <= sl["dMax"] and ((sl["q1"] - 1) * sl["dMax"]) ** 2 <= c["X_lo"]
            and (1 << sl["aQ"]) * sum(comb_int(len(p2s), j) for j in range(ks + 1)) <= sl["nD"] and exact_prod_one_sub_inv_pred(3, sl["zSub"], False).ble(sl["vSubUb"])):
        return False
    if mode == 1:
        if not p2s: return inv_phi_list_ub(qqs).ble(sl["ip2"]) and _ONE.ble(sl["ratUb"])
        s = elem_sym_sums(elem_sym_interval(p2s, ks))
        return inv_phi_list_ub(qqs).mul(s[1].add(s[3])).ble(sl["ip2"]) and v2_list(p2s, True).m > 0 and s[1].ble(s[2].add(sl["ratUb"].mul(v2_list(p2s, True))))
    if mode == 2:
        s1s, s2s = sum_g_list_ub(p2s), sum_g_list_ub(p2s, True); oke, es1 = exp_ub_bounds(s1s)
        if not (oke and inv_phi_list_ub(qqs).mul(es1).ble(sl["ip2"])): return False
        return (not p2s) or (sl["gSubLb"].m > 0 and sl["gSubLb"].ble(_g_lb_analytic(p2s, s1s, s2s))
                              and _ONE.add(sci_pow_ub(s1s, ks + 1).div_ub(SciNat.of_nat(_fact(ks + 1)).mul(sl["gSubLb"]), 24)).ble(sl["ratUb"]))
    return False

def _verify_sq_common(c: dict, w: dict, log0_lo: SciNat, log0_hi: SciNat, s_req: SciNat, tail_q2: SciNat) -> bool:
    sq, q_end = w["square"], min(c["y"], w["square"]["qSq"] + 1)
    if not (1 <= sq["qSq"] and sq["qSq"] ** 4 <= c["X_lo"] and s_req.ble(sq["sQ2Ub"])): return False
    if q_end > P_EXACT:
        ok, l0, l1 = rat_log_bounds(q_end, 1)
        if not (ok and sq["logEndLb"].ble(l0) and l1.ble(sq["logEndUb"])): return False
    cnt_q = slice_bounds_lean(c["z"], q_end, log0_lo, log0_hi, sq["logEndLb"], sq["logEndUb"])[1]
    return cnt_q.ble(sq["cntLoUb"]) and sq["sQ2Ub"].add(sq["cntLoUb"].mul(w["epdUb"]).add(tail_q2)).ble(sq["errQ2Ub"].mul(SciNat(2, 0)))

def verify_slab_2ab_bool(c: dict, w: dict) -> bool:
    if not _verify_header(c, w, True): return False
    lo, ps = w["lower"], [p for p in ODD_PRIMES_EXACT if p < c["z"]]
    q1, p2, k_lo = ps[: lo["a"]], ps[lo["a"] :], 2 * lo["mOdd"] + 1
    dprod = _prod(q1) * _prod(p2[-k_lo:] if k_lo > 0 else [])
    if not (lo["a"] <= len(ps) and dprod <= lo["dMax"] and lo["dMax"] ** 2 <= c["X_lo"] and (1 << lo["a"]) * sum(comb_int(len(p2), j) for j in range(k_lo + 1)) <= lo["nD"]
            and lo["vFullLb"].ble(exact_prod_one_sub_inv_pred(3, c["z"], True)) and exact_prod_one_sub_inv_pred(3, c["z"], False).ble(lo["vFullUb"])): return False
    if not lo["useAnalytic"]:
        if (p2 and not lo["ratLb"].mul(v2_list(p2, False)).add((s := elem_sym_sums(elem_sym_interval(p2, k_lo)))[3]).ble(s[0])) or (not p2 and not lo["ratLb"].ble(_ONE)): return False
    else:
        s1_ub, s2_ub = sum_g_list_ub(p2), sum_g_list_ub(p2, True)
        if not (lo["gLb"].m > 0 and lo["gLb"].ble(_g_lb_analytic(p2, s1_ub, s2_ub)) and (not p2 or lo["ratLb"].add(sci_pow_ub(s1_ub, k_lo + 1).div_ub(SciNat.of_nat(_fact(k_lo + 1)).mul(lo["gLb"]), 24)).ble(_ONE))): return False
    sum_m = sum_e = _Z0
    for sl in w["slices"]:
        if not _verify_sl_bounds(sl): return False
        if sl["kind"] == 0:
            if not ((sl["q1"] - 1) ** 2 <= c["X_lo"] and sl["sqUb"].ble(sl["mSl"]) and sl["cntUb"].mul(w["epdUb"]).ble(sl["eSl"])): return False
        else:
            pss = [p for p in ODD_PRIMES_EXACT if p < sl["zSub"]]
            if not (_verify_eb_small_mode(c, sl, pss, pss[: sl["aQ"]], pss[sl["aQ"] :], 2 * sl["mEv"], sl["kind"])
                    and sl["sqUb"].mul(sl["vSubUb"]).mul(sl["ratUb"]).ble(sl["mSl"]) and sl["cntUb"].mul(SciNat.of_nat(sl["nD"]).add(sl["ip2"].add(sl["ratUb"]))).mul(w["epdUb"]).ble(sl["eSl"])): return False
        sum_m, sum_e = sum_m.add(sl["mSl"]), sum_e.add(sl["eSl"])
    sq, q_end = w["square"], min(c["y"], w["square"]["qSq"] + 1)
    s_req = exact_inv_sum_ub(c["z"], min(q_end, P_EXACT), "mul").add(_ONE.div_ub(SciNat.of_nat(P_EXACT - 1), 24) if q_end > P_EXACT else _Z0)
    tail_q2 = _Z0 if c["y"] <= sq["qSq"] + 1 else w["xHiLogUb"].div_ub(SciNat.of_nat(sq["qSq"]), 24)
    if not _verify_sq_common(c, w, w["xLoLogLb"], w["xLoLogUb"], s_req, tail_q2): return False
    rem_a = SciNat.of_nat(lo["nD"]).mul(w["epdUb"])
    return (SciNat.of_nat(2 * c["main_num"]).add(SciNat.of_nat(c["den"]).mul(sum_m)).ble(SciNat.of_nat(2 * c["den"]).mul(lo["vFullLb"].mul(lo["ratLb"])))
            and SciNat.of_nat(2).mul(rem_a.add(sq["errQ2Ub"])).add(sum_e).mul(SciNat.of_nat(c["den"])).ble(SciNat.of_nat(2 * c["err_num"])))

def verify_slab_2c_bool(c: dict, w: dict) -> bool:
    if not _verify_header(c, w, False): return False
    if c["z"] >= P_EXACT:
        ok_z, z_lo, z_hi = rat_log_bounds(c["z"], 1)
        if not (ok_z and w["zLogLb"].ble(z_lo) and z_hi.ble(w["zLogUb"])): return False
    v_req = exact_prod_one_sub_inv_pred(3, c["z"], True) if c["z"] <= P_EXACT else V_PREFIX_27000_LB.mul(
        div_lb_sig(_ONE, exp_ub_bounds(analytic_slice_aux(P_EXACT, c["z"], LOG27000_LO, LOG27000_HI, w["zLogLb"], w["zLogUb"])[1].add(div_ub_sig(SciNat(26999, 0), SciNat(53996 * 26998, 0), 24)))[1], 24))
    if not (w["vFullLb"].m > 0 and w["vFullLb"].ble(v_req)) or w["lower"]["a"] >= len(ODD_PRIMES_EXACT): return False
    lo, p_min, q1p = w["lower"], ODD_PRIMES_EXACT[w["lower"]["a"]], _prod(ODD_PRIMES_EXACT[: w["lower"]["a"]])
    if not lo["isBrun"]:
        s1_req, _, pi_n = compute_mertens_tail_2c(p_min, c["z"], _Z0, _Z0, lo["zLogLb"], lo["zLogUb"])
        g_req = v2_tail_lb_2c(p_min, c["z"], _Z0, _Z0, lo["zLogLb"], lo["zLogUb"])
        err_t = div_ub_sig(sci_pow_ub(lo["s1Ub"], 2 * lo["mOdd"] + 2), SciNat.of_nat(_fact(2 * lo["mOdd"] + 2)).mul(lo["gLb"]), 24)
        if not (p_min < c["z"] and q1p * (c["z"] ** (2 * lo["mOdd"] + 1)) <= lo["dMax"] and lo["dMax"] ** 2 <= c["X_lo"] and s1_req.ble(lo["s1Ub"])
                and SciNat.of_nat(pi_n).ble(lo["piZUb"]) and SciNat.of_nat(1 << lo["a"]).mul(sum_pow_div_fact_ub(lo["piZUb"], 2 * lo["mOdd"] + 1)).ble(SciNat.of_nat(lo["nD"]))
                and lo["gLb"].m > 0 and lo["gLb"].ble(g_req) and err_t.ble(_ONE) and lo["ratLb"].ble(_ONE.sub_lb(err_t))
                and div_ub_sig(SciNat.of_nat(lo["nD"]).mul(w["epdUb"]), w["vFullLb"], 24).ble(lo["remANormUb"])): return False
    else:
        ends, caps, mod_b, prev, p_a = lo["ends"], lo["caps"], 1, 0, (2 if lo["a"] == 0 else ODD_PRIMES_EXACT[lo["a"] - 1])
        for idx_b, m_cap in enumerate(caps): mod_b, prev = mod_b * (ends[idx_b] ** (m_cap - prev)), m_cap
        if not (caps and len(ends) == len(caps) + 1 and ends[0] == c["z"] and all(ends[i] > ends[i + 1] for i in range(len(caps)))
                and p_a < ends[-1] <= p_min < c["z"] and all(m % 2 == 1 for m in caps) and all(caps[i] <= caps[i + 1] for i in range(len(caps) - 1))
                and q1p * mod_b <= lo["dMax"] and lo["dMax"] ** 2 <= c["X_lo"]): return False
        szs, e_tot = [], _Z0
        for cur, nxt, cap in zip(ends, ends[1:], caps):
            ulo, uhi = (_Z0, _Z0) if nxt < P_EXACT else rat_log_bounds(nxt, 1)[1:]
            vlo, vhi = (lo["zLogLb"], lo["zLogUb"]) if cur == c["z"] else ((_Z0, _Z0) if cur < P_EXACT else rat_log_bounds(cur, 1)[1:])
            szs.append(compute_mertens_tail_2c(nxt, cur, ulo, uhi, vlo, vhi)[2])
            s1_t, v_lb = compute_mertens_tail_2c(nxt, c["z"], ulo, uhi, lo["zLogLb"], lo["zLogUb"])[0], v2_tail_lb_2c(nxt, c["z"], ulo, uhi, lo["zLogLb"], lo["zLogUb"])
            e_tot = e_tot.add(div_ub_sig(sci_pow_ub(s1_t, cap + 1), SciNat.of_nat(_fact(cap + 1)).mul(v_lb), 24))
        if not ((1 << lo["a"]) * adm_count(caps, szs) <= lo["nD"] and e_tot.ble(_ONE) and lo["ratLb"].ble(_ONE.sub_lb(e_tot))
                and div_ub_sig(SciNat.of_nat(lo["nD"]).mul(w["epdUb"]), w["vFullLb"], 24).ble(lo["remANormUb"])): return False
    sum_m = sum_e = _Z0
    for sl in w["slices"]:
        if not _verify_sl_bounds(sl): return False
        if sl["isSelberg"]:
            jf_req = calc_j_full_lb_2c(c["z"], w["zLogLb"], w["zLogUb"], sl["xiQLb"], sl["xiQLogLb"], sl["xiQLogUb"]); ok_x, xlo, xhi = sci_log_bounds(sl["xiQLb"])
            s3c_ok = sl["cntUb"].mul(sl["xiQLb"].mul(sl["xiQLb"])).ble(sl["s3cUb"]) or sl["sqUb"].mul(sl["hQ"]).ble(sl["s3cUb"])
            es1_lhs = SciNat(625, 4).mul(sl["s3cUb"]).mul(sci_pow_ub(SciNat(2, 0).mul(sl["xiQLogUb"]).add(SciNat(6, 0)), 2)).mul(w["epdUb"])
            f0_lhs = sl["xiQLogUb"].add(SciNat(636, 3).add(div_ub_sig(SciNat(78, 2), sl["xiQLb"].mul(sl["xiQLb"]), 24)))
            e_num = sl["es1Ub"].add(sl["cntUb"].mul(_ONE.add(sci_pow_ub(SciNat(13, 1).mul(sl["f0Ub"]), 3))).mul(w["epdUb"]))
            if not (sl["xiQLb"].ble(sl["xiQUb"]) and SciNat.of_nat(sl["q1"] - 1).mul(sl["xiQUb"].mul(sl["xiQUb"])).ble(sl["hQ"]) and sl["hQ"].mul(sl["hQ"]).ble(SciNat.of_nat(c["X_lo"]))
                    and ok_x and sl["xiQLogLb"].ble(xlo) and xhi.ble(sl["xiQLogUb"]) and sl["jfLb"].m > 0 and sl["jfLb"].ble(jf_req)
                    and div_ub_sig(sl["sqUb"], w["vFullLb"].mul(sl["jfLb"]), 24).ble(sl["mSl"]) and s3c_ok and es1_lhs.ble(sl["es1Ub"]) and f0_lhs.ble(sl["f0Ub"]) and div_ub_sig(e_num, w["vFullLb"], 24).ble(sl["eSl"])): return False
        else:
            if not (div_ub_sig(sl["cntUb"].mul(SciNat.of_nat(sl["nD"]).add(sl["ip2"].add(sl["ratUb"]))).mul(w["epdUb"]), w["vFullLb"], 24).ble(sl["eSl"]) and sl["sqUb"].mul(sl["mRatUb"]).ble(sl["mSl"])): return False
            if sl["zSub"] <= P_EXACT:
                pss = [p for p in ODD_PRIMES_EXACT if p < sl["zSub"]]
                if not (_verify_eb_small_mode(c, sl, pss, pss[: sl["aQ"]], pss[sl["aQ"] :], 2 * sl["mEv"], 1) and div_ub_sig(sl["vSubUb"].mul(sl["ratUb"]), w["vFullLb"], 24).ble(sl["mRatUb"])): return False
            else:
                if sl["aQ"] >= len(ODD_PRIMES_EXACT): return False
                pm, ks, q1ps = ODD_PRIMES_EXACT[sl["aQ"]], 2 * sl["mEv"], _prod(ODD_PRIMES_EXACT[: sl["aQ"]])
                s1s, _, pin = compute_mertens_tail_2c(pm, c["z"], _Z0, _Z0, w["zLogLb"], w["zLogUb"]); glb, (oke, es1) = v2_tail_lb_2c(pm, c["z"], _Z0, _Z0, w["zLogLb"], w["zLogUb"]), exp_ub_bounds(s1s)
                if not (sl["zSub"] == c["z"] and pm < c["z"] and q1ps * (c["z"] ** ks) <= sl["dMax"] and ((sl["q1"] - 1) * sl["dMax"]) ** 2 <= c["X_lo"] and oke
                        and sl["gSubLb"].m > 0 and sl["gSubLb"].ble(glb) and SciNat.of_nat(1 << sl["aQ"]).mul(sum_pow_div_fact_ub(SciNat.of_nat(pin), ks)).ble(SciNat.of_nat(sl["nD"]))
                        and inv_phi_list_ub(ODD_PRIMES_EXACT[: sl["aQ"]]).mul(es1).ble(sl["ip2"])
                        and _ONE.add(div_ub_sig(sci_pow_ub(s1s, ks + 1), SciNat.of_nat(_fact(ks + 1)).mul(sl["gSubLb"]), 24)).ble(sl["ratUb"]) and sl["ratUb"].ble(sl["mRatUb"])): return False
        sum_m, sum_e = sum_m.add(sl["mSl"]), sum_e.add(sl["eSl"])
    sq, q_end = w["square"], min(c["y"], w["square"]["qSq"] + 1)
    s_req = (exact_inv_sum_ub(c["z"], min(q_end, P_EXACT), "mul").add(div_ub_sig(_ONE, SciNat.of_nat(P_EXACT - 1), 24) if q_end > P_EXACT else _Z0)) if c["z"] <= P_EXACT else div_ub_sig(_ONE, SciNat.of_nat(c["z"] - 1), 24)
    tail_q2 = _Z0 if c["y"] <= sq["qSq"] + 1 else div_ub_sig(w["xHiLogUb"], SciNat.of_nat(sq["qSq"]), 24)
    if not (_verify_sq_common(c, w, w["zLogLb"], w["zLogUb"], s_req, tail_q2) and div_ub_sig(sq["errQ2Ub"], w["vFullLb"], 24).ble(w["errQ2NormUb"])): return False
    return (SciNat.of_nat(2 * c["main_num"]).add(SciNat.of_nat(c["den"]).mul(sum_m)).ble(SciNat.of_nat(2 * c["den"]).mul(lo["ratLb"]))
            and SciNat.of_nat(2).mul(lo["remANormUb"].add(w["errQ2NormUb"])).add(sum_e).mul(SciNat.of_nat(c["den"])).ble(SciNat.of_nat(2 * c["err_num"])))

def _fmt_rec(d: dict) -> str:
    return "{ " + ", ".join(f"{k} := {('true' if v else 'false') if isinstance(v, bool) else (v.to_lean() if isinstance(v, SciNat) else ('[' + ', '.join(str(x) for x in v) + ']' if isinstance(v, list) else v))}" for k, v in d.items()) + " }"

def _pack_slices(slices: list[dict]) -> list[str]:
    items = [_fmt_rec(sl) for sl in slices]
    return ["      " + ", ".join(items[i : i + 2]) + ("," if i + 2 < len(items) else "") for i in range(0, len(items), 2)]

def _fmt_slab_2ab(w: dict) -> list[str]:
    hdr = f"  {{ xLoLogLb := {w['xLoLogLb'].to_lean()}, xLoLogUb := {w['xLoLogUb'].to_lean()}, xHiLogUb := {w['xHiLogUb'].to_lean()}, epdUb := {w['epdUb'].to_lean()},"
    return [hdr, f"    lower := {_fmt_rec(w['lower'])},", "    slices := [", *_pack_slices(w["slices"]), "    ],", f"    square := {_fmt_rec(w['square'])} }}"]

def _fmt_slab_2c(w: dict) -> list[str]:
    hdr = (f"  {{ xLoLogLb := {w['xLoLogLb'].to_lean()}, xLoLogUb := {w['xLoLogUb'].to_lean()}, xHiLogUb := {w['xHiLogUb'].to_lean()}, "
           f"zLogLb := {w['zLogLb'].to_lean()}, zLogUb := {w['zLogUb'].to_lean()}, epdUb := {w['epdUb'].to_lean()}, liRatioUb := {w['liRatioUb'].to_lean()}, vFullLb := {w['vFullLb'].to_lean()},")
    return [hdr, f"    lower := {_fmt_rec(w['lower'])},", "    slices := [", *_pack_slices(w["slices"]), "    ],", f"    square := {_fmt_rec(w['square'])},", f"    errQ2NormUb := {w['errQ2NormUb'].to_lean()} }}"]

def _parse_data_lean(root: Path) -> list[dict]:
    pat = re.compile(r"\{\s*X_lo\s*:=\s*(\d+),\s*X_hi\s*:=\s*(\d+),\s*z\s*:=\s*(\d+),\s*y\s*:=\s*(\d+),\s*main_num\s*:=\s*(\d+),\s*err_num\s*:=\s*(\d+),\s*net_num\s*:=\s*(\d+),\s*den\s*:=\s*(\d+)\s*\}")
    return [{k: int(m.group(i)) for i, k in enumerate(("X_lo", "X_hi", "z", "y", "main_num", "err_num", "net_num", "den"), 1)}
            for m in pat.finditer((root / "BuchstabSwitching/Certificates/Data.lean").read_text(encoding="utf-8"))]

def _write_shard(out_path: Path, def_name: str, ty_name: str, blocks: list[list[str]]) -> None:
    lines = ["import BuchstabSwitching.Sieve.Regime2SlabBridge.SlabCertInstDefs", "", "set_option maxRecDepth 200000", "", "/-!", f"# Machine-Generated Witness Shard `{def_name}`",
             "Auto-generated by `scripts/sieve_cert/slab_witness_export.py`. Do not edit by hand.", "-/", "", "namespace BuchstabSwitching.SieveInst", "", f"def {def_name} : List {ty_name} := ["]
    for idx, blk in enumerate(blocks): lines.extend(blk[:-1] + [blk[-1] + ("," if idx + 1 < len(blocks) else "")])
    lines.extend(["]", "", "end BuchstabSwitching.SieveInst", ""])
    assert len(lines) <= 700, f"{out_path.name} exceeded 700 lines: {len(lines)}"
    out_path.write_text("\n".join(lines), encoding="utf-8")

def _rebuild_slice_2ab(q0: int, q1s: int, ref: dict, epd_ub: SciNat) -> dict:
    l0 = rat_log_bounds(q0, 1)[1:] if q0 >= P_EXACT else (_Z0, _Z0)
    l1 = rat_log_bounds(q1s, 1)[1:] if q1s > P_EXACT else (_Z0, _Z0)
    sq_ub, cnt_ub = slice_bounds_lean(q0, q1s, l0[0], l0[1], l1[0], l1[1])
    if ref["kind"] == 0:
        m0, e0 = sq_ub, cnt_ub.mul(epd_ub).trim_ub_sig(26)
        return _mk_sl2ab(q0, q1s, 0, 0, 0, 0, 0, 0, sq_ub, cnt_ub, l0, l1, _Z0, _Z0, _Z0, _Z0, m0, e0)
    m_sl = sq_ub.mul(ref["vSubUb"]).mul(ref["ratUb"]).trim_ub_sig(26)
    e_sl = cnt_ub.mul(SciNat.of_nat(ref["nD"]).add(ref["ip2"].add(ref["ratUb"]))).mul(epd_ub).trim_ub_sig(26)
    return _mk_sl2ab(q0, q1s, ref["kind"], ref["zSub"], ref["aQ"], ref["mEv"], ref["nD"], ref["dMax"], sq_ub, cnt_ub, l0, l1, ref["ip2"], ref["vSubUb"], ref["gSubLb"], ref["ratUb"], m_sl, e_sl)

def _compress_2ab_slices(cert: dict, w: dict) -> dict:
    epd_ub, x_lo, lo, sq = w["epdUb"], cert["X_lo"], w["lower"], w["square"]
    rem_a = SciNat.of_nat(lo["nD"]).mul(epd_ub)
    main_rhs = SciNat.of_nat(2 * cert["den"]).mul(lo["vFullLb"].mul(lo["ratLb"]))
    err_rhs = SciNat.of_nat(2 * cert["err_num"])
    def ok_budget(sls: list[dict]) -> bool:
        sm = se = _Z0
        for s in sls: sm, se = sm.add(s["mSl"]), se.add(s["eSl"])
        return (SciNat.of_nat(2 * cert["main_num"]).add(SciNat.of_nat(cert["den"]).mul(sm)).ble(main_rhs)
                and SciNat.of_nat(2).mul(rem_a.add(sq["errQ2Ub"])).add(se).mul(SciNat.of_nat(cert["den"])).ble(err_rhs))
    sls: list[dict] = []
    for sl in w["slices"]:
        if sls and sl["q1"] <= P_EXACT and (sls[-1]["kind"], sls[-1]["zSub"], sls[-1]["aQ"], sls[-1]["mEv"]) == (sl["kind"], sl["zSub"], sl["aQ"], sl["mEv"]):
            sls[-1] = _rebuild_slice_2ab(sls[-1]["q0"], sl["q1"], sl, epd_ub)
        else:
            sls.append(sl)
    while len(sls) > 1:
        best_merge = None
        for i in range(len(sls) - 1):
            a, b = sls[i], sls[i + 1]
            cands = [b]
            if (a["kind"] == 0 and (b["q1"] - 1) ** 2 <= x_lo) or (a["kind"] != 0 and ((b["q1"] - 1) * a["dMax"]) ** 2 <= x_lo):
                cands.append(a)
            old_m = a["mSl"].add(b["mSl"]).to_dec_ceil(18)
            old_e = a["eSl"].add(b["eSl"]).to_dec_ceil(18)
            for ref in cands:
                c = _rebuild_slice_2ab(a["q0"], b["q1"], ref, epd_ub)
                trial = sls[:i] + [c] + sls[i + 2 :]
                if ok_budget(trial):
                    delta = (c["mSl"].to_dec_ceil(18) - old_m) + (c["eSl"].to_dec_ceil(18) - old_e)
                    key = (delta, c["kind"], c["zSub"])
                    if best_merge is None or key < best_merge[0]:
                        best_merge = (key, i, c)
        if best_merge is None: break
        _, idx, c = best_merge
        sls = sls[:idx] + [c] + sls[idx + 2 :]
    return dict(w, slices=sls)

def _rebuild_slice_2c(q0: int, q1s: int, ref: dict, epd_ub: SciNat, v_full_lb: SciNat) -> dict:
    l0 = rat_log_bounds(q0, 1)[1:] if q0 >= P_EXACT else (_Z0, _Z0)
    l1 = rat_log_bounds(q1s, 1)[1:] if q1s > P_EXACT else (_Z0, _Z0)
    sq_ub, cnt_ub = slice_bounds_lean(q0, q1s, l0[0], l0[1], l1[0], l1[1])
    if ref["isSelberg"]:
        m_sl = div_ub_sig(sq_ub, v_full_lb.mul(ref["jfLb"]), 24).trim_ub_sig(26)
        s3c_a, s3c_b = cnt_ub.mul(ref["xiQLb"].mul(ref["xiQLb"])), sq_ub.mul(ref["hQ"])
        s3c = (s3c_a if s3c_a.ble(s3c_b) else s3c_b).trim_ub_sig(26)
        es1 = SciNat(625, 4).mul(s3c).mul(sci_pow_ub(SciNat(2, 0).mul(ref["xiQLogUb"]).add(SciNat(6, 0)), 2)).mul(epd_ub).trim_ub_sig(26)
        e_sl = div_ub_sig(es1.add(cnt_ub.mul(_ONE.add(sci_pow_ub(SciNat(13, 1).mul(ref["f0Ub"]), 3))).mul(epd_ub)), v_full_lb, 24).trim_ub_sig(26)
        return _mk_sl2c(q0, q1s, True, 0, 0, 0, 0, 0, ref["hQ"], ref["xiQLb"], ref["xiQLogLb"], ref["xiQLogUb"], ref["jfLb"], sq_ub, cnt_ub, l0, l1, _Z0, _Z0, _Z0, _Z0, _Z0, s3c, es1, ref["f0Ub"], m_sl, e_sl)
    m_sl = sq_ub.mul(ref["mRatUb"]).trim_ub_sig(26)
    e_sl = div_ub_sig(cnt_ub.mul(SciNat.of_nat(ref["nD"]).add(ref["ip2"].add(ref["ratUb"]))).mul(epd_ub), v_full_lb, 24).trim_ub_sig(26)
    return _mk_sl2c(q0, q1s, False, ref["zSub"], ref["aQ"], ref["mEv"], ref["nD"], ref["dMax"], _Z0, _Z0, _Z0, _Z0, _Z0, sq_ub, cnt_ub, l0, l1, ref["ip2"], ref["vSubUb"], ref["gSubLb"], ref["ratUb"], ref["mRatUb"], _Z0, _Z0, _Z0, m_sl, e_sl)

def _compress_2c_slices(cert: dict, w: dict) -> dict:
    epd_ub, v_full_lb, x_lo, lo = w["epdUb"], w["vFullLb"], cert["X_lo"], w["lower"]
    main_rhs = SciNat.of_nat(2 * cert["den"]).mul(lo["ratLb"])
    err_rhs = SciNat.of_nat(2 * cert["err_num"])
    base_err = lo["remANormUb"].add(w["errQ2NormUb"])
    def ok_budget(sls: list[dict]) -> bool:
        sm = se = _Z0
        for s in sls: sm, se = sm.add(s["mSl"]), se.add(s["eSl"])
        return (SciNat.of_nat(2 * cert["main_num"]).add(SciNat.of_nat(cert["den"]).mul(sm)).ble(main_rhs)
                and SciNat.of_nat(2).mul(base_err).add(se).mul(SciNat.of_nat(cert["den"])).ble(err_rhs))
    sls = list(w["slices"])
    while len(sls) > 1:
        best_merge = None
        for i in range(len(sls) - 1):
            a, b = sls[i], sls[i + 1]
            cands = [b]
            if (a["isSelberg"] and SciNat.of_nat(b["q1"] - 1).mul(a["xiQUb"].mul(a["xiQUb"])).ble(a["hQ"])) or (
                (not a["isSelberg"]) and ((b["q1"] - 1) * a["dMax"]) ** 2 <= x_lo
            ):
                cands.append(a)
            old_m = a["mSl"].add(b["mSl"]).to_dec_ceil(18)
            old_e = a["eSl"].add(b["eSl"]).to_dec_ceil(18)
            for ref in cands:
                c = _rebuild_slice_2c(a["q0"], b["q1"], ref, epd_ub, v_full_lb)
                trial = sls[:i] + [c] + sls[i + 2 :]
                if ok_budget(trial):
                    delta = (c["mSl"].to_dec_ceil(18) - old_m) + (c["eSl"].to_dec_ceil(18) - old_e)
                    key = (delta, 0 if c["isSelberg"] else 1, c["zSub"])
                    if best_merge is None or key < best_merge[0]:
                        best_merge = (key, i, c)
        if best_merge is None: break
        _, idx, c = best_merge
        sls = sls[:idx] + [c] + sls[idx + 2 :]
    return dict(w, slices=sls)

def export_all_witnesses(root: Path) -> None:
    certs = _parse_data_lean(root)
    assert len(certs) == len(SLABS_2A) + len(SLABS_2B) + len(SLABS_2C)
    bridge_dir, w2a, w2b, w2c, off = root / "BuchstabSwitching/Sieve/Regime2SlabBridge", [], [], [], 0
    for i, sp in enumerate(SLABS_2A):
        res = build_slab_2ab_witness("2a", sp)
        slab_c = _compress_2ab_slices(certs[off + i], res.slab)
        assert verify_slab_2ab_bool(certs[off + i], slab_c), f"2a-{i+1:02d} failed Lean Bool check"
        w2a.append(_fmt_slab_2ab(slab_c))
    off += len(SLABS_2A)
    for i, sp in enumerate(SLABS_2B):
        res = build_slab_2ab_witness("2b", sp)
        slab_c = _compress_2ab_slices(certs[off + i], res.slab)
        assert verify_slab_2ab_bool(certs[off + i], slab_c), f"2b-{i+1:02d} failed Lean Bool check"
        w2b.append(_fmt_slab_2ab(slab_c))
    off += len(SLABS_2B)
    for i, sp in enumerate(SLABS_2C):
        res = build_slab_2c_witness(sp)
        slab_c = _compress_2c_slices(certs[off + i], res.slab)
        assert verify_slab_2c_bool(certs[off + i], slab_c), f"2c-{i+1:02d} failed Lean Bool check"
        w2c.append(_fmt_slab_2c(slab_c))
    for fname, dname, ty, blks in [
        ("SlabCertInstData2a1.lean", "witnesses2a1", "Slab2abWitness", w2a[:10]), ("SlabCertInstData2a2.lean", "witnesses2a2", "Slab2abWitness", w2a[10:]),
        ("SlabCertInstData2b1.lean", "witnesses2b1", "Slab2abWitness", w2b[:10]), ("SlabCertInstData2b2.lean", "witnesses2b2", "Slab2abWitness", w2b[10:20]),
        ("SlabCertInstData2b3.lean", "witnesses2b3", "Slab2abWitness", w2b[20:30]), ("SlabCertInstData2b4.lean", "witnesses2b4", "Slab2abWitness", w2b[30:]),
        ("SlabCertInstData2c1.lean", "witnesses2c1", "Slab2cWitness", w2c[:11]), ("SlabCertInstData2c2.lean", "witnesses2c2", "Slab2cWitness", w2c[11:22]),
        ("SlabCertInstData2c3.lean", "witnesses2c3", "Slab2cWitness", w2c[22:33]), ("SlabCertInstData2c4.lean", "witnesses2c4", "Slab2cWitness", w2c[33:44]),
        ("SlabCertInstData2c5.lean", "witnesses2c5", "Slab2cWitness", w2c[44:55]), ("SlabCertInstData2c6.lean", "witnesses2c6", "Slab2cWitness", w2c[55:]),
    ]:
        _write_shard(bridge_dir / fname, dname, ty, blks)
        print(f"Wrote {fname} ({len(blks)} slabs)")

if __name__ == "__main__":
    export_all_witnesses(Path(__file__).resolve().parents[2])
