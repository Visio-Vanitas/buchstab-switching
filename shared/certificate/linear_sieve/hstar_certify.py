#!/usr/bin/env python3
"""
hstar_certify.py -- certified verification of hypothesis (H*) (closed prime intervals,
equivalently all real levels 1<u<w<=z) for X26 Regime 3, g(p)=1/(p-1).

Run:  python3 hstar_certify.py [B] [G]
   B : bound for the exhaustive scan            (default 10**7; need G <= B <= 10**12)
   G : range for the greedy construction of Q0  (default 20000; need 300 <= G)

CERTIFIED (each 'PASS' line):  for the printed Q0 and S0 = odd primes minus Q0,
   eps*(S0) = sup_{a<=b primes of S0} prod_{p in S0, a<=p<=b}(p-1)/(p-2) * log a/log b - 1
   <= eps_hi < 1/k.      (note: Theorems A, D, Proposition E)
   Inputs: E1 [BJS mertencomplem], E2 [JS (3.3)], E3 [BJS small1p], used only via
   the constants t1, t2, t3 in tail_constants().
ARITHMETIC: fixed point, ONE = 2**PREC; a real x is a pair of ints lo <= ONE*x <= hi.
   Divisions are explicit floor/ceil. Logs from the atanh series with an explicit
   tail bound. No floats anywhere. decimal is used only (a) for printing with
   directed rounding, (b) in n3_estimate(), which is HEURISTIC.
NOT CERTIFIED: the greedy choice of Q0 (a candidate that the certificate then checks)
   and the N_3 estimates (hand-estimated alpha*, see note).
"""
import sys
import bisect
from fractions import Fraction
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING

PREC = 160
ONE = 1 << PREC


# ---------------------------------------------------------------- integer helpers
def ceil_div(a, b):
    """Exact ceil(a/b) for ints with b > 0."""
    if b <= 0:
        raise ValueError("ceil_div needs b > 0")
    return -((-a) // b)


def isqrt(n):
    """floor(sqrt(n)) for int n >= 0 (Newton from above; exact integer arithmetic)."""
    if n < 0:
        raise ValueError
    if n < 2:
        return n
    x = 1 << ((n.bit_length() + 1) // 2)      # x >= sqrt(n)
    while True:
        y = (x + n // x) // 2
        if y >= x:
            return x
        x = y


# ------------------------------------------------- certified elementary functions
def atanh_fp(num, den):
    """(lo, hi) ints with lo <= ONE*atanh(num/den) <= hi.
    Needs ints num >= 0, den > 0, 2*num <= den (x <= 1/2). Series terms x^(2k+1)/(2k+1)>=0.
    lo = sum of floors (k<=K); hi = sum of ceilings (k<=K) + 1, where K is the first k
    with floor(ONE*term_k) = 0; the tail is < ONE*term_K * x^2/(1-x^2) < 1/3."""
    if not (isinstance(num, int) and isinstance(den, int)):
        raise TypeError("atanh_fp needs ints")
    if num < 0 or den <= 0 or 2 * num > den:
        raise ValueError("atanh_fp needs 0 <= num and 2*num <= den")
    if num == 0:
        return 0, 0
    n2, d2 = num * num, den * den
    pn, pd, k = num, den, 0
    lo = hi = 0
    while True:
        q, r = divmod(pn << PREC, pd * (2 * k + 1))
        lo += q
        hi += q + (1 if r else 0)
        if q == 0:
            return lo, hi + 1
        pn *= n2
        pd *= d2
        k += 1


_a, _b = atanh_fp(1, 3)
LN2 = (2 * _a, 2 * _b)                         # log 2 = 2 atanh(1/3)


def ln_int_fp(n):
    """(lo, hi) enclosing ONE*log(n), int n >= 1: n = 2^k*m, m in [1,2),
    log n = k log 2 + 2 atanh((n-2^k)/(n+2^k)), argument <= 1/3."""
    k = n.bit_length() - 1
    lo, hi = atanh_fp(n - (1 << k), n + (1 << k))
    return k * LN2[0] + 2 * lo, k * LN2[1] + 2 * hi


def ln1p_inv_fp(k):
    """(lo, hi) enclosing ONE*log(1+1/k) = ONE*2 atanh(1/(2k+1))."""
    lo, hi = atanh_fp(1, 2 * k + 1)
    return 2 * lo, 2 * hi


def exp_hi_fp(x):
    """hi >= ONE*exp(x/ONE) for 0 <= x <= ONE/2. Ceiling Taylor terms dominate the true
    terms; stop at first J>=1 with t_J <= 1; tail < t_J*(1/4)/(3/4) < 1, hence +1."""
    if x < 0 or 2 * x > ONE:
        raise ValueError("exp_hi_fp range")
    total, t, j = 0, ONE, 0
    while True:
        total += t
        if t <= 1:
            return total + 1
        j += 1
        t = ceil_div(t * x, ONE * j)


def exp_lo_fp(x):
    """lo <= ONE*exp(x/ONE) for x >= 0: truncated Taylor sum with floored terms (all >= 0)."""
    if x < 0:
        raise ValueError("exp_lo_fp needs x >= 0")
    total, t, j = 0, ONE, 0
    while t > 0:
        total += t
        j += 1
        t = (t * x) // (ONE * j)
    return total


def fp_dec(x, up, digits=30):
    """Decimal rounding of x/ONE upward (up=True) or downward; Decimal(int) is exact."""
    with localcontext() as c:
        c.prec = digits
        c.rounding = ROUND_CEILING if up else ROUND_FLOOR
        return Decimal(x) / Decimal(ONE)


# ---------------------------------------------------------------------- primes
def odd_primes_upto(n):
    """All odd primes <= n (sieve of Eratosthenes on a bytearray)."""
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    i = 2
    while i * i <= n:
        if s[i]:
            st = i * i
            s[st::i] = bytes(len(range(st, n + 1, i)))
        i += 1
    return [p for p in range(3, n + 1, 2) if s[p]]


def prime_data(primes):
    """Yield (p, lnlo, lnhi, lamlo, lamhi, elllo, ellhi) for consecutive odd primes from 3:
    enclosures of ONE*log p, ONE*loglog p, ONE*log((p-1)/(p-2)). Recursions in note Step 6."""
    if not primes or primes[0] != 3:
        raise ValueError("primes must start at 3")
    a, b = atanh_fp(1, 2)
    L_lo, L_hi = 2 * a, 2 * b                         # log 3
    assert ONE < L_lo and L_hi <= 3 * ONE
    lam_lo = 2 * atanh_fp(L_lo - ONE, L_lo + ONE)[0]  # log log 3, increasing in L
    lam_hi = 2 * atanh_fp(L_hi - ONE, L_hi + ONE)[1]
    prev = 3
    for p in primes:
        if p != 3:
            d_lo, d_hi = atanh_fp(p - prev, p + prev)  # raises unless p <= 3*prev
            d_lo *= 2
            d_hi *= 2
            s_lo = atanh_fp(d_lo, 2 * L_hi + d_lo)[0]  # uses log(prev) before update
            s_hi = atanh_fp(d_hi, 2 * L_lo + d_hi)[1]
            L_lo += d_lo
            L_hi += d_hi
            lam_lo += 2 * s_lo
            lam_hi += 2 * s_hi
            prev = p
        e_lo, e_hi = atanh_fp(1, 2 * p - 3)
        yield p, L_lo, L_hi, lam_lo, lam_hi, 2 * e_lo, 2 * e_hi


# ------------------------------------------------------- scan / greedy / lower bound
def scan(data, excluded, tau):
    """Upper bound mx >= ONE*max_{a<=b in S} F_S(a,b), S = primes of data not in excluded,
    via F = X_b - Y_a and a running minimum of the lower bounds of Y (note Step 6.5).
    Also returns the realising pair and phi = sum_b max(0, val_b - tau) (heuristic use)."""
    Ls_lo = Ls_hi = 0
    minY = minYp = mx = pair = None
    phi = 0
    for (p, _l1, _l2, lam_lo, lam_hi, e_lo, e_hi) in data:
        if p in excluded:
            continue
        Y = Ls_lo - lam_hi
        if minY is None or Y < minY:
            minY, minYp = Y, p
        Ls_lo += e_lo
        Ls_hi += e_hi
        val = Ls_hi - lam_lo - minY
        if mx is None or val > mx:
            mx, pair = val, (minYp, p)
        if tau is not None and val > tau:
            phi += val - tau
    return mx, pair, phi


def greedy_Q(data, primes_G, lnlo, forced, tau):
    """HEURISTIC candidate Q0 (note Step 7); inclusion-minimal w.r.t. tau on primes <= G."""
    excl = set(forced)
    while True:
        mx, pair, phi = scan(data, excl, tau)
        if mx is None or mx < tau:
            break
        a, b = pair
        i0, i1 = bisect.bisect_left(primes_G, a), bisect.bisect_right(primes_G, b)
        best_r, best_gain, best_w = None, 0, 1
        for r in primes_G[i0:i1]:
            if r in excl:
                continue
            excl.add(r)
            _, _, phi_r = scan(data, excl, tau)
            excl.discard(r)
            gain, w = phi - phi_r, lnlo[r]
            if best_r is None or gain * best_w > best_gain * w:
                best_r, best_gain, best_w = r, gain, w
        if best_gain <= 0:
            best_r = b
        excl.add(best_r)
    for r in sorted(excl - forced, reverse=True):     # reverse delete
        excl.discard(r)
        mx, _, _ = scan(data, excl, tau)
        if mx is not None and mx >= tau:
            excl.add(r)
    return excl


def lower_bound_rest(data, forced, thr_hi):
    """CERTIFIED lower bound (ONE-scaled) for log of the product of Q0 \\ F_k (Prop. C(iii)):
    max-weight packing of disjoint intervals [a,b] of S' = primes of data not in forced
    with certified F_{S'}(a,b) >= log(1+1/k) (lower bound of F >= upper bound of the log);
    the weight is the lower bound of ONE*log a."""
    rest = [r for r in data if r[0] not in forced]
    n = len(rest)
    Plo = [0] * (n + 1)
    for i, r in enumerate(rest):
        Plo[i + 1] = Plo[i] + r[5]
    best = [0] * (n + 1)
    for j in range(n):
        bj, lamhi_j = best[j], rest[j][4]
        for i in range(j + 1):
            if Plo[j + 1] - Plo[i] - lamhi_j + rest[i][3] >= thr_hi:
                c = best[i] + rest[i][1]
                if c > bj:
                    bj = c
        best[j + 1] = bj
    return best[n]


def pair_bounds(data, excl, a, b):
    """(lo, hi) enclosing ONE*F_S(a,b), with a, b in S, both in data."""
    s_lo = s_hi = 0
    ra = rb = None
    for r in data:
        if a <= r[0] <= b and r[0] not in excl:
            s_lo += r[5]
            s_hi += r[6]
            if r[0] == a:
                ra = r
            if r[0] == b:
                rb = r
    return s_lo - rb[4] + ra[3], s_hi - rb[3] + ra[4]


# ------------------------------------------------------------ Theorem D constants
def tail_constants(B):
    """(d1, d2) >= ONE*(delta_B, delta'_B) of Theorem D; needs 5 <= B <= 10**12 (int).
    t1 >= 2/(sqrt B log B) [E1], t2 >= 6.836e-6/log 1e12 [E2], t3 >= 2.964e-6/log 1e12 [E3],
    t4 >= 1/(B-1)."""
    if not (5 <= B <= 10**12):
        raise ValueError("B out of range for Theorem D")
    lnB_lo = ln_int_fp(B)[0]
    ln12_lo = ln_int_fp(10**12)[0]
    t1 = ceil_div(2 * ONE * ONE, isqrt(B) * lnB_lo)
    t2 = ceil_div(6836 * ONE * ONE, 10**9 * ln12_lo)
    t3 = ceil_div(2964 * ONE * ONE, 10**9 * ln12_lo)
    t4 = ceil_div(ONE, B - 1)
    return max(t1, t2) + t4, max(t1, t2 + t3) + 2 * t4


# --------------------------------------------------- BJS Table 1, heuristic N_3
TABLE = {74: (631, 630), 76: (559, 559), 78: (504, 504), 80: (461, 461), 85: (386, 386),
         90: (336, 337), 95: (302, 302), 100: (276, 277), 120: (218, 219), 140: (189, 190),
         160: (172, 173), 180: (161, 162), 200: (153, 154), 300: (133, 134), 400: (125, 126)}


def table_row(k):
    rows = [r for r in TABLE if r <= k]
    if not rows:
        raise ValueError("k < 74 not allowed by BJS")
    return max(rows)


# HEURISTIC alpha* (largest alpha with model main term >= 0.01), note section 'Trade-off'.
ALPHA_STAR_EST = {74: "0.0957", 80: "0.110", 90: "0.1235", 100: "0.1344",
                  120: "0.1458", 140: "0.1551", 200: "0.1684"}


def n3_estimate(logQ, alpha_str):
    """HEURISTIC, NOT CERTIFIED: solve L = (logQ + 4.05 log L)/alpha (X26 level rule)."""
    with localcontext() as c:
        c.prec = 28
        a, L = Decimal(alpha_str), Decimal(1000)
        for _ in range(200):
            L = (logQ + Decimal("4.05") * L.ln()) / a
        Lc = Decimal(170) * Decimal(10).ln()
        al170 = (logQ + Decimal("4.05") * Lc.ln()) / Lc
        return L, L / Decimal(10).ln(), al170, Decimal("5.75") - 22 * al170


# --------------------------------------------------------------- sanity checks
def sanity_checks(data):
    idx = {r[0]: r for r in data}
    L2 = Fraction("0.6931471805599453094172321214581765680755")
    assert LN2[0] <= (L2 + Fraction(1, 10**40)) * ONE and LN2[1] >= L2 * ONE, "log 2"
    print("[sanity] log 2 in [%s, %s]" % (fp_dec(LN2[0], False), fp_dec(LN2[1], True)))
    print("[sanity] loglog 3 in [%s, %s]  (expect 0.0940478276...)"
          % (fp_dec(idx[3][3], False), fp_dec(idx[3][4], True)))
    ps = (97, 101, 103, 107, 109)
    P = Fraction(1)
    for p in ps:
        P *= Fraction(p - 1, p - 2)
    assert P == Fraction(11209881600, 10672182675), "exact product (R18/X30 value)"
    xl, xh = atanh_fp(P.numerator - P.denominator, P.numerator + P.denominator)
    s_lo, s_hi = sum(idx[p][5] for p in ps), sum(idx[p][6] for p in ps)
    assert s_lo <= 2 * xh and 2 * xl <= s_hi, "ell sums vs exact log of the product"
    F_lo = s_lo - idx[113][4] + idx[97][3]
    F_hi = s_hi - idx[113][3] + idx[97][4]
    e_lo, e_hi = exp_lo_fp(F_lo) - ONE, exp_hi_fp(F_hi) - ONE
    assert Fraction(16459, 10**6) * ONE <= e_lo and e_hi <= Fraction(16461, 10**6) * ONE
    print("[sanity] half-open [97,113): eps in [%s, %s]  (expect 0.0164598)"
          % (fp_dec(e_lo, False, 8), fp_dec(e_hi, True, 8)))
    lo, hi = pair_bounds(data, set(), 103, 113)
    print("[sanity] closed [103,113], all primes: eps in [%s, %s]  (expect ~0.01797)"
          % (fp_dec(exp_lo_fp(lo) - ONE, False, 8), fp_dec(exp_hi_fp(hi) - ONE, True, 8)))


class St:
    __slots__ = ("name", "k", "Q", "forced", "thr_lo", "lb", "Ls_lo", "Ls_hi",
                 "minY", "minYp", "best", "pair")


def main():
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 10**7
    G = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    targets = [74, 80, 90, 100, 120, 140, 150, 200]
    if not (300 <= G <= B <= 10**12) or max(targets) + 2 > G:
        raise ValueError("need 300 <= G <= B <= 1e12 and G >= max target + 2")
    GLB = min(5000, G)
    primes = odd_primes_upto(B)
    data_G = []
    for rec in prime_data(primes):
        if rec[0] > G:
            break
        data_G.append(rec)
    primes_G = [r[0] for r in data_G]
    lnlo = {r[0]: r[1] for r in data_G}
    lnhi = {r[0]: r[2] for r in data_G}
    data_LB = [r for r in data_G if r[0] <= GLB]
    sanity_checks(data_G)
    d1, d2 = tail_constants(B)
    print("[tail] B = %d: delta_B <= %s, delta'_B <= %s" % (B, fp_dec(d1, True, 6),
                                                        fp_dec(d2, True, 6)))
    states = []
    for k in targets:
        st = St()
        st.name, st.k = "target 1/%d" % k, k
        thr_lo, thr_hi = ln1p_inv_fp(k)
        st.thr_lo = thr_lo
        st.forced = frozenset(p for p in primes_G if p <= k + 2)
        st.Q = frozenset(greedy_Q(data_G, primes_G, lnlo, st.forced, thr_lo - d1 - 1))
        st.lb = sum(lnlo[p] for p in st.forced) + lower_bound_rest(data_LB, st.forced, thr_hi)
        states.append(st)
    st = St()
    st.name, st.k = "X26 current (Q0 = odd primes < 41)", None
    st.Q = st.forced = frozenset(p for p in primes_G if p < 41)
    st.thr_lo = st.lb = None
    states.append(st)
    for st in states:
        st.Ls_lo = st.Ls_hi = 0
        st.minY = st.minYp = st.best = st.pair = None
    last = None
    for (p, _a, _b, lam_lo, lam_hi, e_lo, e_hi) in prime_data(primes):   # exhaustive, v <= B
        for st in states:
            if p in st.Q:
                continue
            Y = st.Ls_lo - lam_hi
            if st.minY is None or Y < st.minY:
                st.minY, st.minYp = Y, p
            st.Ls_lo += e_lo
            st.Ls_hi += e_hi
            val = st.Ls_hi - lam_lo - st.minY
            if st.best is None or val > st.best:
                st.best, st.pair = val, (st.minYp, p)
        last = p
    print("[scan] %d odd primes scanned, largest %d" % (len(primes), last))
    allpass = True
    for st in states:
        T = max(st.best + d1, d2)
        eps_hi = exp_hi_fp(T) - ONE
        print("\n== %s ==" % st.name)
        print("   worst closed pair (scan, v <= B): %s" % (st.pair,))
        logQ_hi = sum(lnhi[p] for p in st.Q)
        if st.k is None:
            print("   eps*(S) <= %s" % fp_dec(eps_hi, True, 8))
            a, b = st.pair
            if b <= G:
                lo, _ = pair_bounds(data_G, set(st.Q), a, b)
                if lo >= 0:
                    print("   eps*(S) >= %s (certified, at that pair)"
                          % fp_dec(exp_lo_fp(lo) - ONE, False, 8))
            continue
        ok = T < st.thr_lo and eps_hi * st.k < ONE
        allpass = allpass and ok
        extras = sorted(st.Q - st.forced)
        row = table_row(st.k)
        print("   Q0 = {odd p <= %d} U %s" % (st.k + 2, extras))
        print("   log Q0 <= %s   (certified LB for any admissible Q0: %s)"
              % (fp_dec(logQ_hi, True, 10), fp_dec(st.lb, False, 10)))
        print("   eps*(S0) <= eps_hi = %s ; 1/eps_hi >= %s ; target 1/%d : %s"
              % (fp_dec(eps_hi, True, 10),
                 fp_dec(ONE * ONE // eps_hi, False, 10), st.k, "PASS" if ok else "FAIL"))
        print("   BJS row %d: C1 = %d, C2 = %d (theorem applied at eps' = 1/%d)"
              % (row, TABLE[row][0], TABLE[row][1], row))
        if str(row) in map(str, ALPHA_STAR_EST):
            L, l10, al, sm = n3_estimate(fp_dec(logQ_hi, True, 20), ALPHA_STAR_EST[row])
            print("   HEURISTIC: alpha*~%s -> log N_3 ~ %.1f (N_3 ~ 10^%.0f); at 1e170: "
                  "alpha >= %.4f, s_min <= %.3f" % (ALPHA_STAR_EST[row], L, l10, al, sm))
    print("\nALL TARGETS PASS" if allpass else "\nSOME TARGET FAILED (enlarge G or B)")
    return 0 if allpass else 1


if __name__ == "__main__":
    sys.exit(main())
