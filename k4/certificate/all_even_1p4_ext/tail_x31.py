"""X26 tail (note section 4) under the all-levels linear sieve of note X31: pre-sieve Q0 (any set of odd primes,
certified by hstar_certify for eps' = 1/k on closed prime intervals), constants C1, C2 (certified by
cn_certify for 1/eps = k), true-argument f and F (sieve_fF), squarefree density as a parameter.
Same structure and checks as all_even_1p4.regime3.certify_tail; only these inputs change.
Certifies net > 0 for all even N >= X_LS = 10^e.

Inputs from the committed certificate files (review R22 item 3): use X31Tail.from_files, which reads
  * log Q0 upper bound and the PASS verdict for 1/k from the hstar_certify log (and checks, raising Fail, that the log contains
    the analytic tail beyond the prime scan, "[tail] B = 10000000", and the scan line up to 9999991);
  * C1(1/k), C2(1/k) as exact Fractions from cn_rows_all.json ("k:new" = sharper recursion, "k:old").
The bare constructor remains for experiments only.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from decimal import ROUND_CEILING, ROUND_FLOOR, Context, Decimal, localcontext
from fractions import Fraction
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from all_even_1p4.cited import (HypothesisError, buthe_constants, mertens_large_coeff, mertens_lower_coeff,
                                require_js_lemma_3_1, robin_constant)
from all_even_1p4.checks import CertificationError
import json, re
from all_even_1p4.constants import U_C
from all_even_1p4.elementary import exp_iv, ln_iv, pow_real_iv
from all_even_1p4.interval import ERROR_TRAPS, HALF, ONE, TWO, Iv
from all_even_1p4.remainder import grh_remainder_coeff
from all_even_1p4.regime3 import v_z_delta
from all_even_1p4_ext.sieve_fF import FFGrid

_GRIDS = {}
def grid(h: int = 200):
    if h not in _GRIDS:
        _GRIDS[h] = FFGrid(h=h)
    return _GRIDS[h]


DATA_DIR = os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))),
    "shared", "data", "linear_sieve_inputs",
)


HSTAR_SHA256 = "9db0e31b2ff56e623eb512ab7f058bc5e247a4ba0fbe6e9cfce04e0839ce4eb4"
CN_SHA256 = "b931b6798c2c9f35cba30ead4c54c668d544b79c9a1989aa705352d55d09b906"
"""sha256 of the committed shared/data/linear_sieve_inputs/logs/hstar.log and cn_rows_all.json; load_inputs refuses other files."""

_DEC = re.compile(r"^[0-9]+(?:\.[0-9]+)?$")


def load_inputs(k: int, rec: str, data_dir: str = DATA_DIR):
    """(log_q_hi, c1, c2, q0) for eps' = 1/k from the committed hstar log and cn rows (rec 'new' or 'old').

    Checks (each raises Fail): both files have the pinned sha256; the run header (text before the first target)
    contains exactly one analytic-tail line "[tail] B = 10000000:" and exactly one scan line ending at 9999991;
    exactly one block "== target 1/k ==" exists; inside it there is exactly one "log Q0 <=" line with a plain
    decimal number (scientific notation is refused), exactly one "Q0 =" line, exactly one
    "target 1/k : PASS" verdict and no "FAIL" anywhere.
    """
    import hashlib
    hp = os.path.join(data_dir, "logs", "hstar.log"); cp = os.path.join(data_dir, "cn_rows_all.json")
    raw = open(hp, "rb").read()
    if hashlib.sha256(raw).hexdigest() != HSTAR_SHA256:
        raise Fail("hstar.log sha256 differs from the pinned value")
    craw = open(cp, "rb").read()
    if hashlib.sha256(craw).hexdigest() != CN_SHA256:
        raise Fail("cn_rows_all.json sha256 differs from the pinned value")
    log = raw.decode()
    head, _, _ = log.partition("\n== target ")
    if len(re.findall(r"^\[tail\] B = 10000000:", head, re.M)) != 1:
        raise Fail("hstar run header: need exactly one analytic-tail line [tail] B = 10000000")
    if len(re.findall(r"^\[scan\] \d+ odd primes scanned, largest 9999991$", head, re.M)) != 1:
        raise Fail("hstar run header: need exactly one full scan line up to 9999991")
    blocks = re.findall(r"^== target 1/%d ==\n(.*?)(?=^== target |\Z)" % k, log, re.M | re.S)
    if len(blocks) != 1:
        raise Fail(f"need exactly one hstar block for target 1/{k}, found {len(blocks)}")
    blk = blocks[0]
    if "FAIL" in blk:
        raise Fail(f"hstar block 1/{k} contains FAIL")
    if len(re.findall(r"target 1/%d : PASS" % k, blk)) != 1:
        raise Fail(f"hstar block 1/{k}: need exactly one PASS verdict")
    lq = re.findall(r"log Q0 <= (\S+)", blk)
    if len(lq) != 1 or not _DEC.match(lq[0]):
        raise Fail(f"hstar block 1/{k}: need exactly one plain-decimal 'log Q0 <=' value, got {lq}")
    q0 = re.findall(r"^\s*Q0 = (.*)$", blk, re.M)
    if len(q0) != 1:
        raise Fail(f"hstar block 1/{k}: need exactly one Q0 line")
    cn = json.loads(craw.decode())
    key = f"{k}:{rec}"
    if key not in cn:
        raise Fail(f"no cn row {key}")
    r = cn[key]
    return Decimal(lq[0]), Fraction(r["C1_num"], r["C1_den"]), Fraction(r["C2_num"], r["C2_den"]), q0[0].strip()


@dataclass(frozen=True)
class X31Tail:
    e: int                 # X_LS = 10^e
    m: int                 # z = N^(1/M)
    b: str                 # H = sqrt(N)/log^(B+1) N
    log_q_hi: Decimal      # upper bound for log of prod Q0 (hstar_certify)
    k: int                 # eps' = 1/k, k >= 74
    c1: Fraction           # certified upper bound C1(1/k)
    c2: Fraction           # certified upper bound C2(1/k)
    slices: int = 200
    sqf: str = "0.65"      # squarefree density used in c4G (0.608 = [BS] Lemma 5; 0.65 conservative)
    true_fF: bool = True
    grid_h: int = 200      # sieve_fF mesh (points per unit)
    rec: str = ""          # recursion label when built from files
    q0: str = ""           # Q0 description when built from files

    @classmethod
    def from_files(cls, e: int, m: int, b: str, k: int, rec: str, data_dir: str = DATA_DIR, **kw) -> "X31Tail":
        log_q, c1, c2, q0 = load_inputs(k, rec, data_dir)
        return cls(e=e, m=m, b=b, log_q_hi=log_q, k=k, c1=c1, c2=c2, rec=rec, q0=q0, **kw)


class Fail(Exception):
    pass


def req(cond, what):
    if not cond:
        raise Fail(what)


def certify(p: X31Tail) -> dict:
    req(p.k >= 74, "k >= 74")
    x_ls = 10 ** p.e
    require_js_lemma_3_1(x_ls)
    log_x = ln_iv(Iv(x_ls))
    m_iv = Iv(p.m)
    beta = Iv.from_fraction(Fraction(p.m - 1, 4 * p.m))
    req(p.m > 5, "M > 5")
    b = Iv(Decimal(p.b))
    log_q = Iv(p.log_q_hi)
    alpha_req = (log_q + (b + ONE) * ln_iv(log_x)) / log_x
    with localcontext(Context(prec=20, rounding=ROUND_CEILING, traps=ERROR_TRAPS)):
        alpha_dec = alpha_req.hi.quantize(Decimal("0.0001"))
    alpha = Iv(alpha_dec)
    req((alpha - (b + ONE) / log_x).lo > 0, "alpha > (B+1)/log X")
    req((alpha * log_x - (b + ONE) * ln_iv(log_x) - log_q).lo >= 0, "N^alpha/log^(B+1)N >= Q")
    log_z0 = log_x / m_iv
    z0 = exp_iv(log_z0)
    req(log_z0.lo > Decimal("8.9"), "log z0 > 8.9")
    req(z0.lo > Decimal(10**7), "z0 > 1e7 (Q0 below z; hstar scan range)")
    log_h0 = HALF * log_x - (b + ONE) * ln_iv(log_x)
    log_1e9 = ln_iv(Iv(10**9))
    req((log_h0 - log_1e9).lo > 0, "H >= 1e9")
    req((log_h0 - beta * log_x).lo >= 0, "y <= H")
    req((HALF - beta - (b + ONE) / log_x).lo > 0, "1/2 - beta > (B+1)/log X")
    s = m_iv * (HALF - alpha)
    s_min = m_iv * (HALF - alpha - beta)
    req(s.lo >= 2, "s >= 2")
    req(s_min.lo >= 1, "s_min >= 1")
    eps_used = Iv.from_fraction(Fraction(1, p.k))
    c1 = Iv.from_fraction(p.c1); c2 = Iv.from_fraction(p.c2)
    c1 = Iv(c1.hi); c2 = Iv(c2.hi)
    e2 = exp_iv(TWO)
    from all_even_1p4.sieve_functions import F_upper as F0, f_lower as f0, h_upper
    G = grid(p.grid_h) if p.true_fF else None
    f_lo = G.f_lower if G else f0
    F_hi = G.F_upper if G else F0
    delta_v = v_z_delta(log_x, z0, log_z0)
    f_s = f_lo(s); h_s = h_upper(s)
    lb_a = f_s - eps_used * c2 * e2 * h_s
    du = (beta - ONE / m_iv) / Iv(p.slices)
    # E(t) <= c/log t for every t >= z0: [BJS] L16 gives 2/sqrt(t) <= 2/sqrt(z0) on [z0, 1e12];
    # [JS] (3.3) on t > max(z0, 1e12), with its range guard applied at that point.
    c_up = max((TWO / z0.sqrt()).hi, mertens_large_coeff(max(z0.lo, Decimal(10**12))))
    mert_coeff = Iv(c_up) + Iv(mertens_lower_coeff(z0.lo))
    q_ratio = z0 / (z0 - ONE)
    total = Iv(0)
    for i in range(p.slices):
        u_k = ONE / m_iv + Iv(i) * du
        u_k1 = ONE / m_iv + Iv(i + 1) * du
        sq_lo = m_iv * (HALF - alpha - u_k1)
        phi = F_hi(sq_lo) + eps_used * c1 * e2 * h_upper(sq_lo)
        total = total + phi * q_ratio * (ln_iv(u_k1 / u_k) + mert_coeff / (u_k * log_x))
    half_sum = HALF * total
    main_bracket = lb_a - half_sum
    main = (ONE - delta_v) * main_bracket
    sqrt_x = exp_iv(HALF * log_x)
    _sqf, mu2_phi_coeff = buthe_constants(log_h0.lo, log_1e9.hi)
    sqf = Iv(Decimal(p.sqf))
    req(Decimal(p.sqf) >= _sqf, "squarefree density >= cited 0.608")
    c4g = sqf * (grh_remainder_coeff(log_x, x_ls) + Iv(robin_constant(x_ls)) / (sqrt_x * ln_iv(log_x)))
    req((b - Iv(3)).lo > 0, "B > 3")
    err_r1 = (ONE + HALF) * c4g / (m_iv * U_C * pow_real_iv(log_x, b - TWO))
    err_r2 = Iv(HALF.lo * mu2_phi_coeff * HALF.lo) * c4g / (m_iv * U_C * pow_real_iv(log_x, b - Iv(3)))
    phi_max = F_hi(s_min) + eps_used * c1 * e2 * h_upper(s_min)
    err_rq = HALF * (ONE + delta_v) * phi_max * c4g / pow_real_iv(log_x, b - ONE)
    req((log_x - Iv(2 * p.m)).lo > 0, "log X > 2M")
    err_q2 = (log_x ** 2) / (TWO * m_iv * U_C * (z0 - ONE))
    err = err_r1 + err_r2 + err_rq + err_q2
    net = main - err
    def S(x):   # display only: 10 significant digits, rounded down (exponent kept)
        with localcontext(Context(prec=10, rounding=ROUND_FLOOR, traps=ERROR_TRAPS)):
            return str(+x.lo)
    def U(x):   # display only: 10 significant digits, rounded up
        with localcontext(Context(prec=10, rounding=ROUND_CEILING, traps=ERROR_TRAPS)):
            return str(+x.hi)
    return dict(ok=net.lo > 0 and main_bracket.lo > 0, e=p.e, M=p.m, B=p.b, k=p.k, rec=p.rec, grid_h=p.grid_h,
                slices=p.slices, alpha=str(alpha_dec), s=S(s), s_min=S(s_min),
                f_s=S(f_s), lb_a=S(lb_a), half_sum=U(half_sum), main=S(main), R1=U(err_r1), R2=U(err_r2), rq=U(err_rq),
                q2=U(err_q2), err=U(err), net=S(net), net_lo=str(net.lo))


def try_certify(p):
    try:
        return certify(p)
    except (Fail, HypothesisError, CertificationError) as e:
        return dict(ok=False, e=p.e, M=p.m, B=p.b, k=p.k, fail=f"{type(e).__name__}: {e}", net_lo=-1.0)


if __name__ == "__main__":
    # SMOKE TEST ONLY, NOT A CERTIFICATE: reproduces the superseded X26 tail inputs (u0 = 41 product, BJS row 100
    # constants 276/277, caps f(4), F(5)) to check that this module agrees with all_even_1p4.regime3 on them.
    from all_even_1p4.primes import PRIMES, product
    lq = ln_iv(Iv(product([q for q in PRIMES if 2 < q < 41]))).hi
    for tf, sq in ((True, "0.608"), (True, "0.65")):
        r = try_certify(X31Tail(e=170, m=22, b="3.05", log_q_hi=lq, k=100, c1=Fraction(276), c2=Fraction(277), true_fF=tf, sqf=sq))
        print(tf, sq, r)
