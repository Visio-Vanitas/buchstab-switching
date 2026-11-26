"""Cross-check of the Brun block certificate against the package's Bonferroni certify_slab on a slab where
both apply.  usage: brun_crosscheck.py E_LO E_HI M a m_odd m_even

Prints, for the same slab:
  (1) package certify_slab(M, a, m_odd, m_even): ratio_odd, ratio_even, bracket, main, err, net;
  (2) block certificate with single blocks (m_odd,) / (m_even,): must match (1) up to the S, V bounds,
      since Lemma D with r = 1 is the package's analytic Bonferroni bound;
  (3) block certificate with the default block caps;
  (4) an upper reference U >= V(Q1 P2) (1 - 1/2 sum_{z<=q<y} 1/(q-1)) >= every true main term with
      R- <= 1 <= R+; every certified main lower bound must be <= U.
"""
import sys, os
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from all_even_1p4.regime2 import SlabParams, certify_slab
from all_even_1p4.interval import Iv, ONE, HALF
from all_even_1p4.elementary import ln_iv, exp_iv
from all_even_1p4.prime_bounds import sum_inv_p_lower, sum_inv_p_upper
from all_even_1p4.primes import PRIMES, P_CUT
from all_even_1p4_ext import regime2_brun as RB

f = lambda x: f"{float(str(x)):.6e}"
e0, e1, M, a, mo, me = map(int, sys.argv[1:7])
x_lo, x_hi = 10 ** e0, 10 ** e1
r = certify_slab(SlabParams(0, x_lo, x_hi, M, a, mo, me))
print(f"slab [10^{e0}, 10^{e1}) M={M} a={a} z={r.z} y={r.y}")
print(f"(1) package Bonferroni ({mo},{me}) [{r.sieve.branch}]: R_odd>={f(r.sieve.ratio_odd.lo)} R_even<={f(r.sieve.ratio_even.hi)} "
      f"V>={f(r.v_lower.lo)} b>={f(r.bracket.lo)} main>={f(r.main.lo)} err<={f(r.err_total.hi)} net>={f(r.net.lo)}")
b1 = RB.certify_brun_slab(x_lo, x_hi, M, a, low_caps=((mo,),), up_caps=((me,),))
print(f"(2) block, single blocks: R->={f((ONE - b1.e_minus).lo)} R+<={f((ONE + b1.e_plus).hi)} V>={f(b1.v_lower.lo)} "
      f"b>={f(b1.bracket.lo)} main>={f(b1.main.lo)} err<={f(b1.err_total.hi)} net>={f(b1.net.lo)}")
b2 = RB.certify_brun_slab(x_lo, x_hi, M, a)
print(f"(3) block, caps low={b2.low_caps} up={b2.up_caps}: E-<={f(b2.e_minus.hi)} E+<={f(b2.e_plus.hi)} "
      f"b>={f(b2.bracket.lo)} main>={f(b2.main.lo)} err<={f(b2.err_total.hi)} net>={f(b2.net.lo)}")
# (4) upper reference
z, y = r.z, r.y
pa = PRIMES[a]
v_hi = ONE
for p in PRIMES:
    if 3 <= p < min(z, P_CUT + 1):
        v_hi = v_hi * Iv.from_fraction(Fraction(p - 2, p - 1))
if z > P_CUT + 1:   # prod (1 - w) <= exp(-sum w), sum_{P_CUT<p<z} 1/(p-1) >= sum 1/p
    c, zi = Iv(P_CUT + 1), Iv(z)
    v_hi = v_hi * exp_iv(-(sum_inv_p_lower(zi, ln_iv(zi)) - sum_inv_p_upper(c, ln_iv(c))))
yi, zi = Iv(y), Iv(z)
sig_lo = sum_inv_p_lower(yi, ln_iv(yi)) - sum_inv_p_upper(zi, ln_iv(zi))
U = (v_hi * (ONE - HALF * sig_lo)).hi
print(f"(4) upper reference U <= {f(U)}  (V<={f(v_hi.hi)}, sum_q 1/(q-1) >= {f(sig_lo.lo)})")
ok = all(x <= U for x in (r.main.lo, b1.main.lo, b2.main.lo))
print("consistency: every certified main lower bound <= U:", ok)
print("single-block block certificate vs package main: ratio", f"{float(str(b1.main.lo)) / float(str(r.main.lo)):.6f}")
