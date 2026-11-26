"""
Outward-rounded pure Decimal / Fraction / int interval arithmetic engine.

Contains zero IEEE-754 floating-point constants, conversions, or `math` imports.
"""

from __future__ import annotations

from decimal import Context, Decimal, Inexact, Rounded, getcontext, localcontext, ROUND_CEILING, ROUND_FLOOR
from fractions import Fraction

PREC = 90

# Trap any accidental unguarded rounding or inexact decimal operation outside explicit
# directed-rounding localcontext blocks.
getcontext().traps[Inexact] = True
getcontext().traps[Rounded] = True

D_ZERO = Decimal(0)
D_ONE = Decimal(1)
D_TWO = Decimal(2)
D_THREE = Decimal(3)
D_FOUR = Decimal(4)


def directed_context(rounding, prec: int = PREC):
    """Return a context manager with directed rounding and Inexact/Rounded traps cleared."""
    ctx = getcontext().copy()
    ctx.prec = prec
    ctx.rounding = rounding
    ctx.traps[Inexact] = False
    ctx.traps[Rounded] = False
    return localcontext(ctx)


def _round_floor(d: Decimal) -> Decimal:
    with directed_context(ROUND_FLOOR):
        return +d


def _round_ceil(d: Decimal) -> Decimal:
    with directed_context(ROUND_CEILING):
        return +d


def _add(a: Decimal, b: Decimal, r) -> Decimal:
    with directed_context(r):
        return a + b


def _sub(a: Decimal, b: Decimal, r) -> Decimal:
    with directed_context(r):
        return a - b


def _mul(a: Decimal, b: Decimal, r) -> Decimal:
    with directed_context(r):
        return a * b


def _div(a: Decimal, b: Decimal, r) -> Decimal:
    with directed_context(r):
        return a / b


def _square_exact(r: Decimal) -> Decimal:
    """Compute `r * r` without rounding; raises `Inexact`/`Rounded` on precision loss."""
    with localcontext(Context(prec=2 * PREC + 6, traps=[Inexact, Rounded])):
        return r * r


def sqrt_down(a: Decimal) -> Decimal:
    """Return a `PREC`-digit Decimal `r >= 0` with `r * r <= a`."""
    if a < D_ZERO:
        raise ValueError(f"sqrt of negative number {a}")
    with directed_context(ROUND_FLOOR):
        r = a.sqrt()
        while _square_exact(r) > a:
            r = r.next_minus()
    return r


def sqrt_up(a: Decimal) -> Decimal:
    """Return a `PREC`-digit Decimal `r >= 0` with `r * r >= a`."""
    if a < D_ZERO:
        raise ValueError(f"sqrt of negative number {a}")
    with directed_context(ROUND_CEILING):
        r = a.sqrt()
        while _square_exact(r) < a:
            r = r.next_plus()
    return r


def _ln_dec(x: Decimal, r) -> Decimal:
    # Guard against Table Maker's Dilemma at PREC+12 with a 2-ulp outward pad before
    # directed rounding back to PREC.
    with directed_context(r, PREC + 12):
        val = x.ln()
        val = val.next_minus().next_minus() if r == ROUND_FLOOR else val.next_plus().next_plus()
    return _round_floor(val) if r == ROUND_FLOOR else _round_ceil(val)


def _exp_dec(x: Decimal, r) -> Decimal:
    with directed_context(r, PREC + 12):
        val = x.exp()
        val = val.next_minus().next_minus() if r == ROUND_FLOOR else val.next_plus().next_plus()
    return _round_floor(val) if r == ROUND_FLOOR else _round_ceil(val)


def fmt_dec(d: Decimal, places: int, rounding: str = ROUND_FLOOR) -> str:
    """Format a Decimal with explicit directed rounding inside a safe localcontext."""
    fmt_str = f"1e-{places}" if places > 0 else "1"
    with directed_context(rounding, 120):
        q = d.quantize(Decimal(fmt_str))
    return f"{q:.{places}f}"


def sub_ceil(a: Decimal, b: Decimal) -> Decimal:
    """Outward-rounded ceiling subtraction `a - b`."""
    return _sub(a, b, ROUND_CEILING)


class Iv:
    """Closed interval [lo, hi] with Decimal endpoints outward-rounded to `PREC` digits."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None) -> None:
        if hi is None:
            hi = lo
        lo_d = lo if isinstance(lo, Decimal) else Decimal(lo)
        hi_d = hi if isinstance(hi, Decimal) else Decimal(hi)
        self.lo = _round_floor(lo_d)
        self.hi = _round_ceil(hi_d)
        if self.lo > self.hi:
            raise ValueError(f"Inverted interval: [{self.lo}, {self.hi}]")

    @staticmethod
    def from_int(n: int) -> "Iv":
        d = Decimal(n)
        return Iv(d, d)

    @staticmethod
    def from_str(s: str) -> "Iv":
        d = Decimal(s)
        return Iv(d, d)

    @staticmethod
    def from_frac(num_or_frac, den: int = 1) -> "Iv":
        if isinstance(num_or_frac, Fraction):
            num = Decimal(num_or_frac.numerator)
            den_d = Decimal(num_or_frac.denominator)
        else:
            num = Decimal(num_or_frac)
            den_d = Decimal(den)
        return Iv(_div(num, den_d, ROUND_FLOOR), _div(num, den_d, ROUND_CEILING))

    def __add__(self, o: "Iv") -> "Iv":
        return Iv(_add(self.lo, o.lo, ROUND_FLOOR), _add(self.hi, o.hi, ROUND_CEILING))

    def __sub__(self, o: "Iv") -> "Iv":
        return Iv(_sub(self.lo, o.hi, ROUND_FLOOR), _sub(self.hi, o.lo, ROUND_CEILING))

    def __neg__(self) -> "Iv":
        return Iv(self.hi.copy_negate(), self.lo.copy_negate())

    @staticmethod
    def sym(d: Decimal) -> "Iv":
        """Symmetric outward-rounded interval `[-d, +d]` for non-negative `Decimal` `d`."""
        return Iv(d.copy_negate(), d)

    def __mul__(self, o: "Iv") -> "Iv":
        prods = []
        for x in (self.lo, self.hi):
            for y in (o.lo, o.hi):
                prods.append(_mul(x, y, ROUND_FLOOR))
                prods.append(_mul(x, y, ROUND_CEILING))
        return Iv(min(prods), max(prods))

    def __truediv__(self, o: "Iv") -> "Iv":
        if o.lo <= D_ZERO <= o.hi:
            raise ZeroDivisionError(f"Division by interval containing 0: {o}")
        quots = []
        for x in (self.lo, self.hi):
            for y in (o.lo, o.hi):
                quots.append(_div(x, y, ROUND_FLOOR))
                quots.append(_div(x, y, ROUND_CEILING))
        return Iv(min(quots), max(quots))

    def __pow__(self, n: int) -> "Iv":
        if not isinstance(n, int) or n < 0:
            raise ValueError("Integer power >= 0 only")
        if n == 0:
            return Iv(D_ONE, D_ONE)
        res = Iv(D_ONE, D_ONE)
        base = self
        k = n
        while k > 0:
            if k & 1:
                res = res * base
            k >>= 1
            if k:
                base = base * base
        return res

    def sqrt(self) -> "Iv":
        if self.lo < D_ZERO:
            raise ValueError(f"sqrt of negative interval {self}")
        return Iv(sqrt_down(self.lo), sqrt_up(self.hi))

    def ln(self) -> "Iv":
        if self.lo <= D_ZERO:
            raise ValueError(f"ln of non-positive interval {self}")
        return Iv(_ln_dec(self.lo, ROUND_FLOOR), _ln_dec(self.hi, ROUND_CEILING))

    def exp(self) -> "Iv":
        return Iv(_exp_dec(self.lo, ROUND_FLOOR), _exp_dec(self.hi, ROUND_CEILING))

    def __repr__(self) -> str:
        return f"[{self.lo}, {self.hi}]"


def ln_iv(x: Iv) -> Iv:
    return x.ln()


def exp_iv(x: Iv) -> Iv:
    return x.exp()


def pow_real_iv(base: Iv, exponent: Iv) -> Iv:
    return (exponent * base.ln()).exp()


def max_iv(a: Iv, b: Iv) -> Iv:
    return Iv(a.lo if a.lo >= b.lo else b.lo, a.hi if a.hi >= b.hi else b.hi)


def min_iv(a: Iv, b: Iv) -> Iv:
    return Iv(a.lo if a.lo <= b.lo else b.lo, a.hi if a.hi <= b.hi else b.hi)


def clamp_pos_iv(a: Iv) -> Iv:
    return Iv(a.lo if a.lo > D_ZERO else D_ZERO, a.hi if a.hi > D_ZERO else D_ZERO)


def ceil_root_int(n: int, k: int) -> int:
    """Exact integer `ceil(n^(1/k))` via binary search."""
    if n <= 1:
        return n
    lo, hi = 1, 1
    while hi ** k < n:
        lo = hi
        hi <<= 1
    while lo < hi:
        mid = (lo + hi) // 2
        if mid ** k >= n:
            hi = mid
        else:
            lo = mid + 1
    return lo


def floor_root_int(n: int, k: int) -> int:
    """Exact integer `floor(n^(1/k))`."""
    c = ceil_root_int(n, k)
    return c if c ** k == n else c - 1
