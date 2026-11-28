#!/usr/bin/env python3
"""Check numerical input boxes of the one-plus-three reduction and the small-x Mertens bound.

Python 3.8 or later, standard library only. Each interval stores integer endpoints
in units of 10^-48. No binary floating point or system transcendental functions.
"""
from dataclasses import dataclass
from fractions import Fraction
from math import isqrt

S = 10**48
T = 4_000_000


def ceil_div(n, d):
    return -((-n) // d)


@dataclass(frozen=True)
class I:
    lo: int
    hi: int

    def __post_init__(self):
        if self.lo > self.hi:
            raise ArithmeticError("empty interval")

    def __add__(self, other):
        return I(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other):
        return I(self.lo - other.hi, self.hi - other.lo)

    def __mul__(self, other):
        values = [x*y for x in (self.lo, self.hi) for y in (other.lo, other.hi)]
        return I(min(values)//S, ceil_div(max(values), S))

    def __truediv__(self, other):
        if other.lo <= 0:
            raise ValueError("positive divisor required")
        return self * I(S*S//other.hi, ceil_div(S*S, other.lo))


def r(value):
    value = Fraction(value)
    n, d = value.numerator, value.denominator
    return I((S*n)//d, ceil_div(S*n, d))


zero, one, two = r(0), r(1), r(2)


def log_unit(x):
    """2*atanh((x-1)/(x+1)), valid on 1 <= x <= 2."""
    if not (S <= x.lo and x.hi <= 2*S):
        raise ValueError("log scaling failure")
    t = (x-one)/(x+one)
    sq = t*t
    power, partial = t, zero
    for j in range(55):
        partial = partial + power/r(2*j+1)
        power = power*sq
    tail = power/(r(111)*(one-sq))
    return two*(partial + I(0, tail.hi))


LOG2 = log_unit(two)


def log_endpoint(n):
    if n <= 0:
        raise ValueError("nonpositive endpoint")
    x = Fraction(n, S)
    k = 0
    while x < 1:
        x *= 2
        k -= 1
    while x > 2:
        x /= 2
        k += 1
    return log_unit(r(x)) + r(k)*LOG2


def ln(x):
    return I(log_endpoint(x.lo).lo, log_endpoint(x.hi).hi)


def exp_pos(x):
    if x.lo < 0:
        raise ValueError("nonnegative argument required")
    if x.hi > 2*S:
        half = exp_pos(x/two)
        return half*half
    partial = term = one
    for n in range(1, 66):
        term = term*x/r(n)
        partial = partial + term
    next_term = term*x/r(66)
    tail = next_term/(one-x/r(67))
    return partial + I(0, tail.hi)


def primes(limit):
    is_prime = bytearray([1]) * (limit+1)
    is_prime[0:2] = bytes(2)
    for p in range(2, isqrt(limit)+1):
        if is_prime[p]:
            is_prime[p*p::p] = bytes((limit-p*p)//p+1)
    return (p for p in range(2,limit+1) if is_prime[p])


def elementary():
    n = 128
    harmonic = sum((Fraction(1,k) for k in range(1,n+1)), Fraction(0))
    base = (r(harmonic - Fraction(1,2*n) + Fraction(1,12*n**2)
              - Fraction(1,120*n**4) + Fraction(1,252*n**6)
              - Fraction(1,240*n**8)) - ln(r(n)))
    gamma = base + I(0, r(Fraction(1,132*n**10)).hi)
    # Ei(log 2) = gamma + log(log 2) + sum (log 2)^k/(k*k!).
    partial, term = gamma + ln(LOG2), one
    for k in range(1, 45):
        term = term*LOG2/r(k)
        partial = partial + term/r(k)
    next_term = term*LOG2/r(45*45)
    tail = next_term/(one-LOG2/r(46))
    return gamma, partial + I(0, tail.hi)


def prime_constants(gamma):
    """Twin-prime product and Mertens' convergent series, through T."""
    prod_lo = prod_hi = S
    loss_lo = loss_hi = 0
    small_primes = []
    span = exp_pos(r("8.9"))
    for p in primes(T):
        if p*S <= span.hi:
            small_primes.append(p)
        if p > 2:
            d = (p-1)**2
            prod_lo = prod_lo*(d-1)//d
            prod_hi = ceil_div(prod_hi*(d-1), d)
        # -log(1-1/p)-1/p = sum_{j>=2} 1/(j*p^j).
        j, power = 2, p*p
        while power < S:
            denom = j*power
            loss_lo += S//denom
            loss_hi += ceil_div(S, denom)
            j, power = j+1, power*p
        # The uncomputed geometric tail is <= p/(j*p^j*(p-1)).
        loss_hi += ceil_div(S*p, j*power*(p-1))
    # For p>T, sum 1/(p-1)^2 <= 1/(T-1), by the integral test.
    # The Mertens loss per p is <= 1/(2*p*(p-1)), a telescoping series.
    tail_prod = r(Fraction(1,T-1))
    twin = I(prod_lo, prod_hi)*I(S-tail_prod.hi,S)
    tail_loss = r(Fraction(1,2*T))
    m0 = gamma-I(loss_lo,loss_hi+tail_loss.hi)
    return twin, m0, small_primes


def small_mertens(m0, small_primes):
    partial = zero
    max_excursion = None
    for p in small_primes:
        partial = partial + r(Fraction(1,p))
        # On (p,p_next] the prime sum is constant and log log x increases.
        point = partial-ln(ln(r(p)))-m0
        if max_excursion is None:
            max_excursion = point
        else:
            max_excursion = I(max(max_excursion.lo,point.lo),max(max_excursion.hi,point.hi))
    if max_excursion.hi > S:
        raise AssertionError("small-x Mertens cap failed")
    return max_excursion


def outward(x, digits):
    unit = 10**(48-digits)
    def fmt(n):
        sign = "-" if n < 0 else ""
        a,b = divmod(abs(n),10**digits)
        return f"{sign}{a}.{b:0{digits}d}"
    return "["+fmt(x.lo//unit)+", "+fmt(ceil_div(x.hi,unit))+"]"


def check():
    gamma, li2 = elementary()
    ctwin, m0, small_primes = prime_constants(gamma)
    alpha = (gamma+LOG2)/two
    hs, ht = r("5.360998310866785"), r("1.295731517927648")
    # H_sigma and H_tilde have box constraints in the record. C_J also
    # satisfies the displayed algebraic identity. Rational choices suffice.
    values = dict(
        gamma=gamma, eGamma=exp_pos(gamma), eNegGamma=one/exp_pos(gamma),
        M0=m0, C2_twin=ctwin, U_c=two*ctwin, H0=one/ctwin, li2=li2,
        alpha0=alpha, C_f0=r("0.78"), H_sigma=hs, C_J=(alpha+r("0.78"))*hs,
        H_tilde=ht, ln2=LOG2, e2=exp_pos(two),
    )
    boxes = {
        "gamma": ("0.577215664901532","0.577215664901533"),
        "eGamma": ("1.781072417990197","1.781072417990198"),
        "eNegGamma": ("0.561459483566885","0.561459483566886"),
        "M0": ("0.261496246734501","0.261497246735500"),
        "C2_twin": ("0.660161530508911","0.660161860589840"),
        "U_c": ("1.320323061017821","1.320323721179681"),
        "H0": ("1.514780025472119","1.514780782862509"),
        "li2": ("1.045163780117492","1.045163780117493"),
        "alpha0": ("0.635181422730739","0.635181422730740"),
        "C_f0": ("0.78","0.78"),
        "H_sigma": ("5.360998310866784","5.360998310866785"),
        "C_J": ("7.586785216829545","7.586785216829546"),
        "H_tilde": ("1.295731517927647","1.295731517927648"),
        "ln2": ("0.693147180559945","0.693147180559946"),
        "e2": ("7.389056098930650","7.389056098930651"),
    }
    for name,x in values.items():
        lo, hi = boxes[name]
        if not (r(lo).hi <= x.lo and x.hi <= r(hi).lo):
            raise AssertionError((name,outward(x,25),lo,hi))
        print(f"{name:9s} {outward(x,19)}")
    if not (r("0.261497").hi <= m0.lo and m0.hi <= r("0.261498").lo):
        raise AssertionError("Mertens premise's additional box failed")
    peak = small_mertens(m0,small_primes)
    print(f"Small-x Mertens supremum {outward(peak,10)} ({len(small_primes)} primes)")
    print(f"All constant boxes and the small-x upper bound passed; prime cutoff {T}.")


if __name__ == "__main__":
    check()
