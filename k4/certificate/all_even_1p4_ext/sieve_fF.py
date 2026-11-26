"""Rigorous one-sided bounds for the linear-sieve functions f (increasing) and F (decreasing) at their true
arguments, replacing the caps f(s) >= f(4) for s > 4 and F(s) <= F(5) for s > 5.

Facts used ([BJS] Lemma 19 / [JS] section 2, as quoted in note X26 section 0.1):
  F(s) = 2e^gamma/s on (0, 3];  f(s) = 2e^gamma log(s-1)/s on [2, 4];
  (s F(s))' = f(s-1) for s > 3;  (s f(s))' = F(s-1) for s > 2;  f increasing, F decreasing.
Grid t_j = 2 + j/H. For t_j > 4:  t_j f(t_j) = 4 f(4) + int_4^{t_j} F(t-1) dt, and since F is decreasing the
integral lies between the right-endpoint and left-endpoint Riemann sums (lower uses F_lo at right ends, upper
uses F_hi at left ends). For t_j > 3: t_j F(t_j) = 3 F(3) + int_3^{t_j} f(t-1) dt with f increasing (lower uses
f_lo at left ends, upper f_hi at right ends). H divides 1, so t-1 is a grid point. All in outward intervals.
Returned bounds are uniform: f_lower(s) <= f(s') and F_upper(s) >= F(s') for every s' >= s.lo.
"""
from __future__ import annotations
from decimal import Decimal
from fractions import Fraction
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from all_even_1p4.constants import E_GAMMA
from all_even_1p4.elementary import ln_iv
from all_even_1p4.interval import ONE, TWO, Iv
from all_even_1p4 import sieve_functions as SF

H = 200          # grid points per unit
S_MAX = 40       # grid end


class FFGrid:
    def __init__(self, h: int = H, s_max: int = S_MAX):
        self.h = h
        n = (s_max - 2) * h
        self.t = [Iv.from_fraction(Fraction(2 * h + j, h)) for j in range(n + 1)]
        step = Iv.from_fraction(Fraction(1, h))
        two_eg = TWO * E_GAMMA
        fl = [None] * (n + 1); fu = [None] * (n + 1); Fl = [None] * (n + 1); Fu = [None] * (n + 1)
        j3, j4 = h, 2 * h
        for j in range(n + 1):
            t = self.t[j]
            if j <= j4:                     # f exact on [2, 4]
                v = two_eg * ln_iv(t - ONE) / t
                fl[j], fu[j] = v, v
            if j <= j3:                     # F exact on [2, 3]
                v = two_eg / t
                Fl[j], Fu[j] = v, v
        # running integrals
        intF_lo = Iv(0); intF_hi = Iv(0)   # int_4^{t_j} F(t-1) dt
        intf_lo = Iv(0); intf_hi = Iv(0)   # int_3^{t_j} f(t-1) dt
        f4 = fl[j4]; F3 = Fl[j3]
        for j in range(j3 + 1, n + 1):
            # F at t_j: interval [t_{j-1}, t_j], f(t-1) between f(t_{j-1}-1) and f(t_j-1): indices j-1-h, j-h
            intf_lo = intf_lo + step * Iv(fl[j - 1 - h].lo)
            intf_hi = intf_hi + step * Iv(fu[j - h].hi)
            Fl[j] = Iv(((Iv(3) * Iv(F3.lo) + Iv(intf_lo.lo)) / self.t[j]).lo)
            Fu[j] = Iv(((Iv(3) * Iv(F3.hi) + Iv(intf_hi.hi)) / self.t[j]).hi)
            if j > j4:
                intF_lo = intF_lo + step * Iv(Fl[j - h].lo)
                intF_hi = intF_hi + step * Iv(Fu[j - 1 - h].hi)
                fl[j] = Iv(((Iv(4) * Iv(f4.lo) + Iv(intF_lo.lo)) / self.t[j]).lo)
                fu[j] = Iv(((Iv(4) * Iv(f4.hi) + Iv(intF_hi.hi)) / self.t[j]).hi)
        # monotonicity: f increasing, F decreasing, so f(s') >= max_{t_i <= s'} fl[i], F(s') <= min_{t_i <= s'} Fu[i]
        for j in range(1, n + 1):
            if fl[j].lo < fl[j - 1].lo: fl[j] = fl[j - 1]
            if Fu[j].hi > Fu[j - 1].hi: Fu[j] = Fu[j - 1]
        self.fl, self.fu, self.Fl, self.Fu, self.n = fl, fu, Fl, Fu, n

    def _idx(self, s0: Decimal) -> int:
        # HEURISTIC guess of the index, then verified exactly: t_j.hi <= s0 (t_j <= s0 for certain)
        from decimal import localcontext, Context, ROUND_FLOOR
        with localcontext(Context(prec=50, rounding=ROUND_FLOOR)):
            j = int((s0 - 2) * self.h)
        j = max(0, min(j, self.n))
        while j > 0 and self.t[j].hi > s0:
            j -= 1
        while j < self.n and self.t[j + 1].hi <= s0:
            j += 1
        if self.t[j].hi > s0:
            raise ValueError("s below grid")
        return j

    def f_lower(self, s: Iv) -> Iv:
        s0 = s.lo
        if s0 <= 4:
            return SF.f_lower(s)
        return Iv(self.fl[self._idx(s0)].lo)

    def F_upper(self, s: Iv) -> Iv:
        s0 = s.lo
        if s0 <= 3:
            return SF.F_upper(s)
        j = self._idx(s0)
        return Iv(self.Fu[j].hi)


if __name__ == "__main__":
    g = FFGrid()
    for s in ["3", "4", "5", "6", "8", "10", "15"]:
        x = Iv(Decimal(s))
        print(s, "f>=", str(g.f_lower(x).lo)[:10], "F<=", str(g.F_upper(x).hi)[:10],
              "| caps: f>=", str(SF.f_lower(x).lo)[:10], "F<=", str(SF.F_upper(x).hi)[:10] if Decimal(s) > 1 else "")
