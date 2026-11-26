#!/usr/bin/env python3
"""
bjs_core_check.py -- certified checks for the corrected beta = 2 linear-sieve constants.
Standard library only. Every real quantity is an interval (lo, hi) of Fractions with
lo <= true value <= hi; after each step both ends are rounded OUTWARD to a multiple of
10**-40. No floats.

EXTERNAL INPUT (only one): Euler's constant gamma in [0.57721566490, 0.57721566491].

PART 1 asserts:
  P1a  3*E1(3) < e^{-3}           (monotonicity of e^s H(s)/s on [2,3], Step 7 (h4))
  P1b  e^3*E1(3) < 1/3            (monotonicity of e^s H(s)/3 on [3,4])
  P1c  kappa(s0) := e^{s0}(C - s0 e^{-2})/s0 <= tabulated kappa_{s0},  C = 4e^-2 - e^-3 + 3E1(3)
  P1d  2*kappa(2) - 1 <= 0.9214   (tilde kappa)
  P1e  8e/27 <= 0.8349            (s >= 4 branch)
PART 2: enclosures of tau_n (n <= 500) DEFINED by (eq:tau) of BJS, multiplied out:
  tau_n = max_b [tau_{n-1}*rho_b + beta_b*c_{n-1}^{n-2} + beta'_b*c_n^{n-1}],
  with gamma_{s0} = e^{s0-1.8} ("corrected") or e^{s0-2} ("literal"), gamma_3 = 4e/3,
  c_n from BJS Table tab:cn1. Since all tau_n > 0, the printed partial sums over n <= 500
  are rigorous LOWER bounds for C_1 = sum_{odd} tau_n and C_2 = sum_{even} tau_n.
"""
from fractions import Fraction as Fr

SCALE = 10 ** 40


def rd_down(x):
    x = Fr(x)
    return Fr((x.numerator * SCALE) // x.denominator, SCALE)


def rd_up(x):
    x = Fr(x)
    return Fr(-((-x.numerator * SCALE) // x.denominator), SCALE)


def iv(lo, hi):
    lo, hi = Fr(lo), Fr(hi)
    assert lo <= hi, (lo, hi)
    return (rd_down(lo), rd_up(hi))


def show(x, d=6, up=False):
    """Decimal display of x: floor (up=False) or ceiling (up=True) at d digits."""
    x = Fr(x)
    n = x.numerator * 10 ** d
    q = -((-n) // x.denominator) if up else n // x.denominator
    sign = "-" if q < 0 else ""
    q = abs(q)
    return "%s%d.%0*d" % (sign, q // 10 ** d, d, q % 10 ** d)


def add(a, b):
    return iv(a[0] + b[0], a[1] + b[1])


def sub(a, b):
    return iv(a[0] - b[1], a[1] - b[0])


def mul_pos(a, b):
    assert a[0] >= 0 and b[0] >= 0
    return iv(a[0] * b[0], a[1] * b[1])


def scal(c, a):
    c = Fr(c)
    assert c >= 0
    return iv(c * a[0], c * a[1])


def inv_pos(a):
    assert a[0] > 0
    return iv(1 / a[1], 1 / a[0])


def exp_iv(x, N=80):
    """e^x, rational 0<=x<=4: lo = sum_{k<=N} x^k/k!; tail <= x^{N+1}/(N+1)!/(1-x/(N+2))."""
    x = Fr(x)
    assert 0 <= x <= 4
    term, s = Fr(1), Fr(1)
    for k in range(1, N + 1):
        term = term * x / k
        s += term
    nxt = term * x / (N + 1)
    return iv(s, s + nxt / (1 - x / (N + 2)))


def ln3_iv(J=80):
    """ln3 = 2*sum_{j>=0} 2^-(2j+1)/(2j+1); tail after J terms <= 2*2^-(2J+1)/(2J+1)*4/3."""
    s = Fr(0)
    for j in range(J):
        s += Fr(1, (2 * j + 1) * 2 ** (2 * j + 1))
    s *= 2
    tail = Fr(2, (2 * J + 1) * 2 ** (2 * J + 1)) * Fr(4, 3)
    return iv(s, s + tail)


EULER_GAMMA = (Fr("0.57721566490"), Fr("0.57721566491"))  # EXTERNAL INPUT


def E1_3_iv(K=150):
    """E1(3) = -gamma - ln3 + sum_{k>=1} (-1)^{k+1} 3^k/(k k!); terms decrease
    (ratio 3k/(k+1)^2 <= 3/4), so |sum - partial_K| <= next term."""
    term, s = Fr(1), Fr(0)
    for k in range(1, K + 1):
        term = term * 3 / k
        s += (term / k) if k % 2 == 1 else -(term / k)
    t_next = term * 3 / (K + 1) / (K + 1)
    ln3 = ln3_iv()
    return iv(s - t_next - EULER_GAMMA[1] - ln3[1],
              s + t_next - EULER_GAMMA[0] - ln3[0])


S0 = ["2", "2.2", "2.4", "2.6", "2.8", "3"]
KAPPA = {"2": Fr("0.9607"), "2.2": Fr("0.9557"), "2.4": Fr("0.9457"),
         "2.6": Fr("0.9261"), "2.8": Fr("0.8914"), "3": Fr("0.8349")}
KAPPA_T = Fr("0.9214")


def part1():
    print("PART 1: constants of BJS Lemma lemma:forg")
    e1, e2, e3 = exp_iv(1), exp_iv(2), exp_iv(3)
    em2, em3 = inv_pos(e2), inv_pos(e3)
    E = E1_3_iv()
    print("  E1(3) in [%s, %s]" % (show(E[0], 12), show(E[1], 12, True)))
    t = sub(em3, scal(3, E))
    assert t[0] > 0, "P1a failed"
    print("  P1a: e^-3 - 3 E1(3) >= %s > 0" % show(t[0], 8))
    t = mul_pos(e3, E)
    assert t[1] < Fr(1, 3), "P1b failed"
    print("  P1b: e^3 E1(3) <= %s < 1/3" % show(t[1], 8, True))
    C = add(sub(scal(4, em2), em3), scal(3, E))
    kap = {}
    for key in S0:
        s0 = Fr(key)
        inner = sub(C, scal(s0, em2))
        assert inner[0] > 0
        k = scal(1 / s0, mul_pos(exp_iv(s0), inner))
        kap[key] = k
        ok = k[1] <= KAPPA[key]
        print("  kappa(%s) in [%s, %s]  tabulated %s  %s" % (
            key, show(k[0], 7), show(k[1], 7, True), KAPPA[key], "OK" if ok else "FAIL"))
        assert ok, "P1c failed at " + key
    kt = sub(scal(2, kap["2"]), (Fr(1), Fr(1)))
    print("  2*alpha-1 in [%s, %s]  tabulated %s" % (show(kt[0], 7), show(kt[1], 7, True), KAPPA_T))
    assert kt[1] <= KAPPA_T, "P1d failed"
    t = scal(Fr(8, 27), e1)
    assert t[1] <= KAPPA["3"], "P1e failed"
    print("  P1e: 8e/27 <= %s <= 0.8349" % show(t[1], 7, True))


C_TABLE = [(1, 1, "1"), (2, 2, "0.33"), (3, 3, "0.39"), (4, 4, "0.45"), (5, 5, "0.51"),
           (6, 6, "0.54"), (7, 7, "0.57"), (8, 8, "0.58"), (9, 10, "0.61"), (11, 12, "0.63"),
           (13, 13, "0.64"), (14, 14, "0.65"), (15, 18, "0.66"), (19, 20, "0.67"),
           (21, 26, "0.68"), (27, 34, "0.69"), (35, 46, "0.70"), (47, 82, "0.71"),
           (83, 345, "0.72"), (346, 500, "0.73")]


def c_bjs(n):
    for a, b, v in C_TABLE:
        if a <= n <= b:
            return Fr(v)
    raise ValueError(n)


def gammas(corrected):
    g = {"3": scal(Fr(4, 3), exp_iv(1))}
    for key in S0[:-1]:
        g[key] = exp_iv(Fr(key) - (Fr("1.8") if corrected else Fr(2)))
    return g


def tau_run(eps, corrected, nmax=500):
    eps = Fr(eps)
    G = gammas(corrected)
    tau = {1: (Fr(3), Fr(3))}
    for n in range(2, nmax + 1):
        a = c_bjs(n - 1) ** (n - 2)
        A = iv(a, a)
        b = c_bjs(n) ** (n - 1)
        B = iv(b, b)
        t = tau[n - 1]
        cands = []
        for key in (S0 if n % 2 == 0 else ["3"]):
            k, g = KAPPA[key], G[key]
            lo = t[0] * (k + (g[0] + k) * eps) + 2 * g[0] * A[0] + 2 * B[0]
            hi = t[1] * (k + (g[1] + k) * eps) + 2 * g[1] * A[1] + 2 * B[1]
            cands.append((lo, hi))
        if n % 2 == 1:
            r = KAPPA_T + (5 + 4 * eps) * eps
            lo = t[0] * r + 6 * (1 + eps) * A[0] + 2 * (2 + eps) * B[0]
            hi = t[1] * r + 6 * (1 + eps) * A[1] + 2 * (2 + eps) * B[1]
            cands.append((lo, hi))
        tau[n] = iv(max(c[0] for c in cands), max(c[1] for c in cands))
    return tau


TAB_TAU = {1: 3, 2: 8, 3: 10, 4: 10, 5: 10, 6: 10, 7: 10, 8: 10, 9: 10, 10: 10,
           11: 9, 12: 9, 13: 9, 14: 8, 15: 8, 16: 8}
TABLE1 = {200: (153, 154), 100: (276, 277), 74: (631, 630)}


def part2():
    print("PART 2: tau_n as defined by (eq:tau)")
    tau = tau_run(Fr(1, 200), True, 16)
    print("  eps=1/200, corrected gamma:   n   enclosure of tau_n   BJS tab:tau")
    for n in range(1, 17):
        print("   %3d  [%s, %s]   %s" % (n, show(tau[n][0], 4), show(tau[n][1], 4, True), TAB_TAU[n]))
    assert tau[2][0] > 8
    print("  tau_2 > 8: Table tab:tau does not bound tau_2 as defined by (eq:tau).")
    for inv_eps in (200, 100, 74):
        for corrected in (True, False):
            tau = tau_run(Fr(1, inv_eps), corrected)
            s1 = sum(tau[n][0] for n in range(1, 501, 2))
            s2 = sum(tau[n][0] for n in range(2, 501, 2))
            c1, c2 = TABLE1[inv_eps]
            print("  eps=1/%d %s: sum_odd<=499 >= %s (Table1 C1=%d); sum_even<=500 >= %s "
                  "(Table1 C2=%d); tau_500 <= %s" % (
                      inv_eps, "corrected" if corrected else "literal  ",
                      show(s1, 2), c1, show(s2, 2), c2, show(tau[500][1], 6, True)))
            if s1 > c1:
                print("     -> C1 as defined in lemma:exprec EXCEEDS the Table 1 entry")
            if s2 > c2:
                print("     -> C2 as defined in lemma:exprec EXCEEDS the Table 1 entry")


if __name__ == "__main__":
    part1()
    part2()
