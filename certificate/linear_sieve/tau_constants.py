#!/usr/bin/env python3
"""Rigorous upper bounds for C_1(eps) = sum_{n odd} tau_n and C_2(eps) = sum_{n even} tau_n.

Recursion (corrected form of [BJS, eq. (tau)]):  tau_1 = 3 and, for n >= 2,
    tau_n = tau_{n-1} * max(xi_2, ..., xi_2.8, xi_3)      (n even)
    tau_n = tau_{n-1} * max(xi_3, xi~)                    (n odd)
    xi_s  = kappa_s + (gamma_s + kappa_s) eps + 2 gamma_s c_{n-1}^{n-2}/tau_{n-1} + 2 c_n^{n-1}/tau_{n-1}
    xi~   = kappa~ + (5 + 4 eps) eps + 6 (1 + eps) c_{n-1}^{n-2}/tau_{n-1} + 2 (2 + eps) c_n^{n-1}/tau_{n-1}
with gamma_s = e^{s - 1.8} for s in {2, 2.2, 2.4, 2.6, 2.8} (the value e^{s-2} printed in
[BJS, Lemma hsm1] is too small), gamma_3 = 4e/3.

All arithmetic is exact rational arithmetic with every intermediate value rounded UP to
DIGITS decimals.  tau_n * xi is increasing in tau_{n-1}, gamma, c, so rounding up keeps
upper bounds.  Tail n > NMAX: with c = 0.9607 >= c_n, A = kappa_2 + (gamma_2 + kappa_2) eps
and B = 8e/3 + 2 (2 + eps) c one has tau_n <= A tau_{n-1} + B c^{n-2} for all n > NMAX
provided the three inequalities checked in `check_majorant` hold; summing,
    sum_{n > NMAX} tau_n <= (A tau_NMAX + B c^{NMAX-1}/(1 - c)) / (1 - A).
"""
from fractions import Fraction as Fr
import sys

DIGITS = 40
SCALE = 10 ** DIGITS


def up(x):
    """Smallest multiple of 10^-DIGITS that is >= x."""
    x = Fr(x)
    return Fr(-((-x.numerator * SCALE) // x.denominator), SCALE)


def exp_up(x, terms=60):
    """Upper bound for e^x, 0 <= x <= 1 rational: Taylor sum plus remainder x^N/N! * 2."""
    x = Fr(x)
    assert 0 <= x <= 1
    s, t = Fr(0), Fr(1)
    for k in range(terms):
        s += t
        t = t * x / (k + 1)
    return up(s + 2 * t)          # remainder sum_{k>=N} x^k/k! <= 2 x^N/N! for x <= 1


KAPPA = {Fr(2): Fr(9607, 10000), Fr(22, 10): Fr(9557, 10000), Fr(24, 10): Fr(9457, 10000),
         Fr(26, 10): Fr(9261, 10000), Fr(28, 10): Fr(8914, 10000), Fr(3): Fr(8349, 10000)}
KAPPA_T = Fr(9214, 10000)
E_UP = exp_up(1)
GAMMA = {s: exp_up(s - Fr(18, 10)) for s in KAPPA if s < 3}
GAMMA[Fr(3)] = up(4 * E_UP / 3)
C_PROVED = Fr(9607, 10000)

# [BJS, Table cn1]; an input that is NOT certified here.
CN_TABLE = [(2, 2, 33), (3, 3, 39), (4, 4, 45), (5, 5, 51), (6, 6, 54), (7, 7, 57), (8, 8, 58),
            (9, 10, 61), (11, 12, 63), (13, 13, 64), (14, 14, 65), (15, 18, 66), (19, 20, 67),
            (21, 26, 68), (27, 34, 69), (35, 46, 70), (47, 82, 71), (83, 345, 72), (346, 500, 73)]

PAPER = {74: (631, 630), 76: (559, 559), 78: (504, 504), 80: (461, 461), 85: (386, 386),
         90: (336, 337), 95: (302, 302), 100: (276, 277), 120: (218, 219), 140: (189, 190),
         160: (172, 173), 180: (161, 162), 200: (153, 154), 300: (133, 134), 400: (125, 126),
         500: (121, 122), 600: (118, 119), 700: (116, 117), 800: (115, 116), 900: (114, 115),
         1000: (113, 114), 2000: (109, 110), 10000: (106, 108), 100000: (106, 107)}


def c_of(n, use_table):
    if n == 1:
        return Fr(1)
    if use_table:
        for a, b, v in CN_TABLE:
            if a <= n <= b:
                return Fr(v, 100)
    return C_PROVED


def check_majorant(eps):
    """Conditions under which tau_n <= A tau_{n-1} + B c^{n-2} for n beyond the table."""
    A = KAPPA[Fr(2)] + (GAMMA[Fr(2)] + KAPPA[Fr(2)]) * eps
    ok = all(KAPPA[s] + (GAMMA[s] + KAPPA[s]) * eps <= A for s in KAPPA)
    ok = ok and KAPPA_T + (5 + 4 * eps) * eps <= A
    ok = ok and A < 1
    # coefficients: 2 gamma_s <= 8e/3 (gamma_s <= gamma_3), 6(1+eps) <= 8e/3, 2 <= 2(2+eps)
    ok = ok and all(GAMMA[s] <= GAMMA[Fr(3)] for s in GAMMA) and 6 * (1 + eps) <= 2 * GAMMA[Fr(3)]
    return ok, A


def constants(k, use_table, nmax=6000):
    eps = Fr(1, k)
    ok, A = check_majorant(eps)
    if not ok:
        return None
    tau = Fr(3)
    sums = [Fr(0), Fr(3)]                    # sums[0] even n, sums[1] odd n
    pw_prev = Fr(1)                          # c_{n-1}^{n-2} for n = 2
    for n in range(2, nmax + 1):
        a = pw_prev if n == 2 else up(c_of(n - 1, use_table) ** (n - 2))
        b = up(c_of(n, use_table) ** (n - 1))
        cand = [tau * (KAPPA[s] + (GAMMA[s] + KAPPA[s]) * eps) + 2 * GAMMA[s] * a + 2 * b
                for s in (KAPPA if n % 2 == 0 else [Fr(3)])]
        if n % 2 == 1:
            cand.append(tau * (KAPPA_T + (5 + 4 * eps) * eps) + 6 * (1 + eps) * a + 2 * (2 + eps) * b)
        tau = up(max(cand))
        sums[n % 2] += tau
    B = 2 * GAMMA[Fr(3)] + 2 * (2 + eps) * C_PROVED
    tail = up((A * tau + B * up(C_PROVED ** (nmax - 1)) / (1 - C_PROVED)) / (1 - A))
    return sums[1] + tail, sums[0] + tail, tail


def main():
    ks = [int(a) for a in sys.argv[1:]] or sorted(PAPER)
    print("1/eps | C1, C2 with [BJS] c_n table | C1, C2 with c_n = 0.9607 | printed in [BJS] | tail")
    for k in ks:
        row = []
        for use_table in (True, False):
            r = constants(k, use_table)
            row.append("not applicable" if r is None else "%.3f %.3f" % (float(r[0]) + 5e-4, float(r[1]) + 5e-4))
        t = constants(k, True)
        print(k, "|", row[0], "|", row[1], "|", PAPER.get(k, ("-", "-")), "| %.1e" % (float(t[2]) if t else 0))


if __name__ == "__main__":
    main()
