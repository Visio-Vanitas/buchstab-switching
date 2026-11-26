#!/usr/bin/env python3
"""Certified upper bounds for f_n (BJS eq:f11,f22,odd), M_n = sup f_n/(2e^2 h) and c_n,
n = 2..NMAX (default 500), plus tau recursions (old form with certified M_n; sharpened form).

Certified quantities (all arithmetic: decimal, 40 digits, ROUND_CEILING; every operation is
+,*,/ on nonnegative operands, increasing in each argument, divisors exact integers):
  U[i]  >= f_n(a_n + i/1000)               (left Riemann sums, f_{n-1} nonincreasing)
  R[j]  >= 1/(2 e^2 h(1 + j/1000)),  W[j] >= 1/(1000+j) = delta/(1+j delta)
  M_n   <= max_i U[i]*R[j(x_{i+1})]       (f_n nonincr., h nonincr.)   => (Fn) with c_n^(n-1) >= M_n
  p[s0] >= sup_{s in I_s0} f_{n-1}(s-1)/(2e^2h(s)),  q[s0] >= sup_{s in I_s0} f_n(s)/(2e^2h(s)),
  qt >= sup_{[1,3]} f_n/(2e^2h) (n odd), f2 >= f_{n-1}(2) (n odd).
f_n = 0 on [n+2, oo), so the grid [a_n, n+2] is exhaustive (no tail bound needed).
"""
import sys
from decimal import Decimal as D, getcontext, ROUND_CEILING
from fractions import Fraction as Fr
from itertools import accumulate
from operator import mul

getcontext().prec = 40
getcontext().rounding = ROUND_CEILING

CN_TABLE = [(2, 2, 33), (3, 3, 39), (4, 4, 45), (5, 5, 51), (6, 6, 54), (7, 7, 57), (8, 8, 58),
            (9, 10, 61), (11, 12, 63), (13, 13, 64), (14, 14, 65), (15, 18, 66), (19, 20, 67),
            (21, 26, 68), (27, 34, 69), (35, 46, 70), (47, 82, 71), (83, 345, 72), (346, 500, 73)]
S0_IDX = {Fr(2): 0, Fr(22, 10): 200, Fr(24, 10): 400, Fr(26, 10): 600, Fr(28, 10): 800}


def table_c(n):
    for a, b, v in CN_TABLE:
        if a <= n <= b:
            return Fr(v, 100)
    return None


def exp_milli_up():
    """Upper bound for e^(1/1000): Taylor to degree 12 plus 2 x^13/13! (valid for 0<=x<=1/2)."""
    x, s, t = Fr(1, 1000), Fr(0), Fr(1)
    for k in range(13):
        s += t
        t = t * x / (k + 1)
    s += 2 * t
    return D(s.numerator) / D(s.denominator)          # ceiling division


def tables(J):
    """R[j] >= 1/(2e^2 h(1+j/1000)), W[j] >= 1/(1000+j), 0 <= j <= J."""
    E = exp_milli_up()
    R, W = [None] * (J + 1), [None] * (J + 1)
    half, pw = D(1) / D(2), D(1)
    for j in range(J + 1):
        W[j] = D(1) / D(1000 + j)
        if j <= 1000:
            R[j] = half
        else:
            pw = pw * E                                 # >= e^{(j-1000)/1000}
            R[j] = pw / 2 if j <= 2000 else pw * D(1000 + j) / D(6000)
    return R, W


def certify(NMAX):
    R, W = tables(1000 * (NMAX + 1))
    U = [D(2000 - i) / D(1000 + i) for i in range(2001)]          # f_1 on 1 + i/1000
    CO = {}
    for n in range(2, NMAX + 1):
        S = list(accumulate(reversed(U)))
        S.reverse()                                              # S[k] >= sum_{k'>=k} U[k']
        co = {'p': {}, 'q': {}}
        if n % 2 == 0:
            L = 1000 * n + 1                                     # x = 2 + i/1000, i < L
            Un = list(map(mul, S, W[1000:1000 + L]))
            rn = list(map(mul, Un[:L - 1], R[1001:1000 + L]))    # cell i -> x_{i+1}: j = i+1001
            ro = list(map(mul, U[:L - 1], R[1001:1000 + L]))     # f_{n-1}(s-1), s-1 = 1 + i/1000
            for s0, a in S0_IDX.items():
                co['q'][s0] = max(rn[a:a + 200])
                co['p'][s0] = max(ro[a:a + 200])
            co['q'][Fr(3)] = max(rn[1000:])
            co['p'][Fr(3)] = max(ro[1000:])
        else:
            L = 1000 * (n + 1) + 1                               # x = 1 + i/1000, i < L
            Un = [S[0] * W[i] for i in range(2000)] + list(map(mul, S, W[2000:L]))
            rn = list(map(mul, Un[:L - 1], R[1:L]))
            co['qt'] = max(rn[:2000])
            co['q'][Fr(3)] = max(rn[2000:])
            co['p'][Fr(3)] = max(map(mul, U[0:L - 2001], R[2001:L]))   # s-1 = 2 + (i-2000)/1000
            co['f2'] = U[0]                                      # >= f_{n-1}(2)
        co['M'] = max(rn)
        CO[n] = co
        U = Un
    return CO


def c_up(M, n):
    """Least k/10^4 with (k/10^4)^(n-1) >= M (exact Fractions); None if M > 1."""
    Mf = Fr(M)
    if Mf > 1:
        return None
    lo, hi = 0, 10000
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if Fr(mid, 10000) ** (n - 1) >= Mf:
            hi = mid
        else:
            lo = mid
    return Fr(hi, 10000)


# ---------------- tau recursion (constants as in our tau script) ----------------
DIGITS = 40
SCALE = 10 ** DIGITS


def up(x):
    x = Fr(x)
    return Fr(-((-x.numerator * SCALE) // x.denominator), SCALE)


def exp_up(x, terms=60):
    x = Fr(x)
    assert 0 <= x <= 1
    s, t = Fr(0), Fr(1)
    for k in range(terms):
        s += t
        t = t * x / (k + 1)
    return up(s + 2 * t)


KAPPA = {Fr(2): Fr(9607, 10000), Fr(22, 10): Fr(9557, 10000), Fr(24, 10): Fr(9457, 10000),
         Fr(26, 10): Fr(9261, 10000), Fr(28, 10): Fr(8914, 10000), Fr(3): Fr(8349, 10000)}
KAPPA_T = Fr(9214, 10000)
E_UP = exp_up(1)
GAMMA = {s: exp_up(s - Fr(18, 10)) for s in KAPPA if s < 3}
GAMMA[Fr(3)] = up(4 * E_UP / 3)
C = Fr(9607, 10000)


def check_majorant(eps):
    A = KAPPA[Fr(2)] + (GAMMA[Fr(2)] + KAPPA[Fr(2)]) * eps
    ok = all(KAPPA[s] + (GAMMA[s] + KAPPA[s]) * eps <= A for s in KAPPA)
    ok = ok and KAPPA_T + (5 + 4 * eps) * eps <= A and A < 1
    ok = ok and all(GAMMA[s] <= GAMMA[Fr(3)] for s in GAMMA) and 6 * (1 + eps) <= 2 * GAMMA[Fr(3)]
    return ok, A


def run(k, step, nmax=6000):
    eps = Fr(1, k)
    ok, A = check_majorant(eps)
    if not ok:
        return None
    tau, sums, first = Fr(3), [Fr(0), Fr(3)], []
    for n in range(2, nmax + 1):
        tau = up(max(step(n, tau, eps)))
        sums[n % 2] += tau
        if n <= 3:
            first.append(tau)
    B = 2 * GAMMA[Fr(3)] + 2 * (2 + eps) * C
    tail = up((A * tau + B * up(C ** (nmax - 1)) / (1 - C)) / (1 - A))
    return sums[1] + tail, sums[0] + tail, first


def make_steps(CO, NMAX, nmax=6000):
    CP = [Fr(1), Fr(1)]
    for n in range(2, nmax + 1):
        CP.append(up(CP[-1] * C))                    # CP[n] >= 0.9607^(n-1)
    Mf = {n: up(Fr(CO[n]['M'])) for n in CO}

    def Mof(n):                                      # admissible bound for c_n^(n-1)
        return Fr(1) if n == 1 else (Mf[n] if n <= NMAX else CP[n])

    def old(n, tau, eps):
        a, b = Mof(n - 1), Mof(n)
        if n % 2 == 0:
            return [tau * (KAPPA[s] + (GAMMA[s] + KAPPA[s]) * eps) + 2 * GAMMA[s] * a + 2 * b for s in KAPPA]
        s = Fr(3)
        return [tau * (KAPPA[s] + (GAMMA[s] + KAPPA[s]) * eps) + 2 * GAMMA[s] * a + 2 * b,
                tau * (KAPPA_T + (5 + 4 * eps) * eps) + 6 * (1 + eps) * a + 2 * (2 + eps) * b]

    def new(n, tau, eps):
        if n > NMAX:
            return old(n, tau, eps)
        co = CO[n]
        P = {s: up(Fr(v)) for s, v in co['p'].items()}
        Q = {s: up(Fr(v)) for s, v in co['q'].items()}
        if n % 2 == 0:
            return [tau * (KAPPA[s] + (GAMMA[s] + KAPPA[s]) * eps) + 2 * P[s] + 2 * Q[s] for s in KAPPA]
        s = Fr(3)
        return [tau * (KAPPA[s] + (GAMMA[s] + KAPPA[s]) * eps) + 2 * P[s] + 2 * Q[s],
                tau * (KAPPA_T + (5 + 4 * eps) * eps) + 3 * (1 + eps) * up(Fr(co['f2']))
                + 2 * (2 + eps) * up(Fr(co['qt']))]
    return old, new


def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    CO = certify(NMAX)
    print("n | certified c_n (4 dp, up) | [BJS] c_n | M_n upper (8 sig) | flag")
    getcontext().prec = 8
    for n in range(2, NMAX + 1):
        M = +CO[n]['M']                               # re-rounded up to 8 digits
        c = c_up(CO[n]['M'], n)
        t = table_c(n)
        flag = "OK" if (c is not None and t is not None and c <= t) else "TABLE NOT CONFIRMED"
        print(n, "|", "%.4f" % c if c is not None else ">1", "|", t and "%.2f" % t, "|", M, "|", flag)
    getcontext().prec = 40
    old, new = make_steps(CO, NMAX)
    for k in (74, 100, 200):
        for name, st in (("old recursion, certified M_n", old), ("sharpened recursion (Thm 3)", new)):
            r = run(k, st)
            if r is None:
                print(k, name, "not applicable")
            else:
                print("1/eps=%d %s: C1<=%.3f C2<=%.3f tau2<=%.4f tau3<=%.4f" %
                      (k, name, float(r[0]) + 5e-4, float(r[1]) + 5e-4,
                       float(r[2][0]) + 5e-5, float(r[2][1]) + 5e-5))


if __name__ == "__main__":
    main()
