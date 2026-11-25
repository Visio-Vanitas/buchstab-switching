"""Benchmark 0: reproduce published numbers of [JS] v3 with the same machinery.

1. The ranges in the proof of [JS] Theorem 1.4: K = the largest integer with
   theta(p_{K+L+1}) - theta(p_{L+1}) < log X, for (L+1, log X) = (6, 104),
   (13, 149), (21, exp(5.077)).  Expected K <= 25, K = 31, K = 31.
2. The coefficient of [JS] Theorem 5.9 at their parameters, once with their
   product eps * C = 1.312e-2 * 559 and once with the Regime-3 table lookup
   (row 76, eps' = 1/76, C2 = 559).  [JS] report 1.48; both are checked > 1.4.
This tests the table lookup and the sieve functions against a published value;
it certifies nothing about Goldbach.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal

from .checks import Check, CheckList
from .cited import JS_LEMMAS_5_7_5_8_THEOREM_5_9, bjs_table_row
from .constants import E_GAMMA, U_C
from .elementary import exp_iv, ln_iv, pow_real_iv
from .interval import HALF, ONE, TWO, Iv
from .primes import PRIMES
from .remainder import grh_remainder_coeff

REF = "note s5; " + JS_LEMMAS_5_7_5_8_THEOREM_5_9.key


@dataclass(frozen=True)
class BenchmarkResult:
    k_values: tuple[int, int, int]
    log_x2: Iv
    coeff_js: Iv
    coeff_table: Iv
    checks: tuple[Check, ...]


def max_k_for_log_x(l_plus_1: int, log_x: Iv) -> int:
    """Largest K with sum_{i=1}^{K} log p_{L+1+i} certainly < log X (prime indices from 1)."""
    s = Iv(0)
    k = 0
    for p in PRIMES[l_plus_1:]:
        s = s + ln_iv(Iv(p))
        if s.hi < log_x.lo:
            k += 1
        else:
            break
    return k


def run_benchmark() -> BenchmarkResult:
    checks = CheckList("benchmark")
    log_x2 = exp_iv(Iv(Decimal("5.077")))
    k1 = max_k_for_log_x(6, Iv(104))
    k2 = max_k_for_log_x(13, Iv(149))
    k3 = max_k_for_log_x(21, log_x2)
    checks.require("JS T1.4: K(exp 104) <= 25", REF, k1, "<=", 25)
    checks.require("JS T1.4: K(exp 149) == 31", REF, k2, "==", 31)
    checks.require("JS T1.4: K(exp exp 5.077) == 31", REF, k3, "==", 31)

    m = Iv(18)
    alpha = Iv(Decimal("0.285"))
    b = Iv(Decimal("2.01"))
    eps_js = Iv(Decimal("1.312e-2"))
    row = bjs_table_row(eps_js)
    checks.require("table row for eps = 1.312e-2 is 76", REF, row.inv_eps, "==", 76)
    checks.require("C1(1/76) == 559", REF, row.c1, "==", 559)
    checks.require("C2(1/76) == 559", REF, row.c2, "==", 559)
    eps_used = ONE / Iv(row.inv_eps)
    c2 = Iv(row.c2)
    xi = Iv(1244)
    s = m * (HALF - alpha)  # 3.87, in [2, 4] where f(s) = 2e^gamma log(s-1)/s
    f_s = TWO * E_GAMMA * ln_iv(s - ONE) / s
    h_s = (Iv(3) / s) * exp_iv(-s)
    p_g = Iv(Decimal("0.65")) * grh_remainder_coeff(log_x2)            # [JS] Lemma 5.7
    sqrt_x2 = exp_iv(HALF * log_x2)
    c4g = p_g + Iv(Decimal("0.9")) / (sqrt_x2 * ln_iv(log_x2))         # [JS] Lemma 5.8
    e2 = exp_iv(TWO)
    xi_fac = ONE - xi / (log_x2 ** 2)
    log_x2_bm2 = pow_real_iv(log_x2, b - TWO)
    tail = (ONE / m) * (ONE / xi_fac) * (ONE / U_C) * (c4g / log_x2_bm2)
    coeffs = []
    for label, e_c in (("eps=1.312e-2 times C=559", eps_js * c2), ("eps'=1/76 times C2(1/76)=559", eps_used * c2)):
        coeff = m * xi_fac * (f_s - e_c * e2 * h_s - tail)
        checks.require(f"JS T5.9 coefficient > 1.4 ({label})", REF, coeff, ">", Decimal("1.4"))
        coeffs.append(coeff)
    return BenchmarkResult((k1, k2, k3), log_x2, coeffs[0], coeffs[1], checks.frozen())
