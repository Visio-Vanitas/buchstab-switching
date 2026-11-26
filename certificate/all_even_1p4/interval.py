"""Outward-rounded interval arithmetic on ``decimal.Decimal``.

An ``Iv(lo, hi)`` stands for the closed real interval [lo, hi].  Every
operation returns an interval that contains the exact result of the operation
applied to every pair of points of its operands ("outward rounding").  This is
achieved by computing the lower endpoint in a Decimal context with rounding
ROUND_FLOOR and the upper endpoint with ROUND_CEILING, at ``PREC`` significant
digits.

Rounding audit
--------------
Importing this module sets the traps ``Inexact`` and ``Rounded`` in the
*default* Decimal context of the importing thread.  From then on any Decimal
operation that would round outside one of the directed contexts below raises
an exception.  The directed helpers switch the traps off only inside their own
``localcontext``.  Integer arithmetic (Python ``int``) is exact and is used
for every integer condition.

Square roots (fix of review R18, X26r_v2 finding 1)
--------------------------------------------------
``Decimal.sqrt`` rounds half-even whatever the context rounding is (General
Decimal Arithmetic specification; CPython follows it).  The original script
called it inside a ROUND_FLOOR / ROUND_CEILING context and therefore could
return a lower endpoint above sqrt(a) or an upper endpoint below it, by at
most half a unit in the last place.  Here ``sqrt_down`` / ``sqrt_up`` take the
half-even result as a candidate and then step it with ``next_minus`` /
``next_plus`` until the *exact* square (computed with enough digits that the
Inexact trap proves exactness) is <= a, respectively >= a.  So the returned
values r_lo, r_hi satisfy r_lo^2 <= a <= r_hi^2, which is the outward
property, verified by exact arithmetic rather than assumed.
"""

from __future__ import annotations

from decimal import (
    ROUND_CEILING,
    ROUND_FLOOR,
    Context,
    Decimal,
    DivisionByZero,
    Inexact,
    InvalidOperation,
    Overflow,
    Rounded,
    getcontext,
    localcontext,
)
from fractions import Fraction
from typing import Union

PREC = 90
"""Significant decimal digits of every interval endpoint."""


def enable_rounding_audit() -> None:
    """Trap Inexact and Rounded in the default context of the current thread."""
    ctx = getcontext()
    ctx.traps[Inexact] = True
    ctx.traps[Rounded] = True


enable_rounding_audit()


ERROR_TRAPS = [InvalidOperation, DivisionByZero, Overflow]
"""The traps of Python's default context; they stay on in every context used here."""


_DIRECTED = {
    r: Context(prec=PREC, rounding=r, traps=ERROR_TRAPS) for r in (ROUND_FLOOR, ROUND_CEILING)
}
"""The two directed contexts: PREC digits, Inexact/Rounded not trapped (errors still are).
``localcontext`` installs a copy, so these templates are never modified."""


def _directed(rounding: str) -> Context:
    """The directed context for ROUND_FLOOR or ROUND_CEILING (any other rounding is refused)."""
    return _DIRECTED[rounding]


# ---------------------------------------------------------------------------
# Directed primitives on Decimal.  The suffix says the rounding direction.
# ---------------------------------------------------------------------------

def round_down(a: Decimal) -> Decimal:
    """Largest PREC-digit Decimal <= a."""
    with localcontext(_directed(ROUND_FLOOR)):
        return +a


def round_up(a: Decimal) -> Decimal:
    """Smallest PREC-digit Decimal >= a."""
    with localcontext(_directed(ROUND_CEILING)):
        return +a


def add_dir(a: Decimal, b: Decimal, rounding: str) -> Decimal:
    """a + b rounded in the given direction."""
    with localcontext(_directed(rounding)):
        return a + b


def sub_dir(a: Decimal, b: Decimal, rounding: str) -> Decimal:
    """a - b rounded in the given direction."""
    with localcontext(_directed(rounding)):
        return a - b


def mul_dir(a: Decimal, b: Decimal, rounding: str) -> Decimal:
    """a * b rounded in the given direction."""
    with localcontext(_directed(rounding)):
        return a * b


def div_dir(a: Decimal, b: Decimal, rounding: str) -> Decimal:
    """a / b rounded in the given direction."""
    with localcontext(_directed(rounding)):
        return a / b


def _square_exact(r: Decimal) -> Decimal:
    """r * r exactly.  The Inexact trap is on, so a rounded square would raise."""
    with localcontext(Context(prec=2 * PREC + 4, traps=ERROR_TRAPS + [Inexact, Rounded])):
        return r * r


def sqrt_down(a: Decimal) -> Decimal:
    """A PREC-digit Decimal r with r >= 0 and r * r <= a (so r <= sqrt(a)); requires a >= 0."""
    if a < 0:
        raise ValueError(f"sqrt of negative number {a}")
    with localcontext(_directed(ROUND_FLOOR)):
        r = a.sqrt()  # correctly rounded half-even, NOT floor (see module docstring)
        while _square_exact(r) > a:
            r = r.next_minus()
    return r


def sqrt_up(a: Decimal) -> Decimal:
    """A PREC-digit Decimal r with r * r >= a (so r >= sqrt(a)); requires a >= 0."""
    if a < 0:
        raise ValueError(f"sqrt of negative number {a}")
    with localcontext(_directed(ROUND_CEILING)):
        r = a.sqrt()  # correctly rounded half-even, NOT ceiling (see module docstring)
        while _square_exact(r) < a:
            r = r.next_plus()
    return r


def neg_exact(a: Decimal) -> Decimal:
    """-a, exactly: copy_negate does not consult the context (unary minus does round)."""
    return a.copy_negate()


# ---------------------------------------------------------------------------
# The interval type
# ---------------------------------------------------------------------------

Scalar = Union[int, str, Decimal]
"""Exact inputs accepted by ``Iv``: an int, a decimal string, or a Decimal."""


class Iv:
    """Closed interval [lo, hi] with PREC-digit Decimal endpoints; immutable.

    ``Iv(x)`` is the point x and ``Iv(lo, hi)`` the interval.  Inputs are
    converted exactly (``Decimal(int)`` and ``Decimal(str)`` are exact) and
    then rounded outward to PREC digits: lo down, hi up.
    """

    __slots__ = ("lo", "hi")
    lo: Decimal
    hi: Decimal

    def __init__(self, lo: Scalar, hi: Scalar | None = None) -> None:
        if hi is None:
            hi = lo
        lo_d = round_down(lo if isinstance(lo, Decimal) else Decimal(lo))
        hi_d = round_up(hi if isinstance(hi, Decimal) else Decimal(hi))
        if lo_d > hi_d:
            raise ValueError(f"Invalid interval: [{lo_d}, {hi_d}]")
        object.__setattr__(self, "lo", lo_d)
        object.__setattr__(self, "hi", hi_d)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("Iv is immutable")

    @classmethod
    def from_fraction(cls, f: Fraction) -> Iv:
        """An enclosure of the rational number f (one directed division)."""
        return cls(Decimal(f.numerator)) / cls(Decimal(f.denominator))

    def __repr__(self) -> str:
        return f"Iv({self.lo}, {self.hi})"

    def __neg__(self) -> Iv:
        """[-hi, -lo], exact."""
        return Iv(neg_exact(self.hi), neg_exact(self.lo))

    def __add__(self, other: Iv | Scalar) -> Iv:
        """[lo+lo' rounded down, hi+hi' rounded up]."""
        o = other if isinstance(other, Iv) else Iv(other)
        return Iv(add_dir(self.lo, o.lo, ROUND_FLOOR), add_dir(self.hi, o.hi, ROUND_CEILING))

    def __sub__(self, other: Iv | Scalar) -> Iv:
        """[lo-hi' rounded down, hi-lo' rounded up]."""
        o = other if isinstance(other, Iv) else Iv(other)
        return Iv(sub_dir(self.lo, o.hi, ROUND_FLOOR), sub_dir(self.hi, o.lo, ROUND_CEILING))

    def __mul__(self, other: Iv | Scalar) -> Iv:
        """[min of the 4 endpoint products rounded down, max of them rounded up]."""
        o = other if isinstance(other, Iv) else Iv(other)
        p_lo = (
            mul_dir(self.lo, o.lo, ROUND_FLOOR),
            mul_dir(self.lo, o.hi, ROUND_FLOOR),
            mul_dir(self.hi, o.lo, ROUND_FLOOR),
            mul_dir(self.hi, o.hi, ROUND_FLOOR),
        )
        p_hi = (
            mul_dir(self.lo, o.lo, ROUND_CEILING),
            mul_dir(self.lo, o.hi, ROUND_CEILING),
            mul_dir(self.hi, o.lo, ROUND_CEILING),
            mul_dir(self.hi, o.hi, ROUND_CEILING),
        )
        return Iv(min(p_lo), max(p_hi))

    def __truediv__(self, other: Iv | Scalar) -> Iv:
        """[min of the 4 endpoint quotients rounded down, max rounded up]; 0 not in divisor."""
        o = other if isinstance(other, Iv) else Iv(other)
        if o.lo <= 0 <= o.hi:
            raise ZeroDivisionError(f"Interval division straddles zero: {o}")
        q_lo = (
            div_dir(self.lo, o.lo, ROUND_FLOOR),
            div_dir(self.lo, o.hi, ROUND_FLOOR),
            div_dir(self.hi, o.lo, ROUND_FLOOR),
            div_dir(self.hi, o.hi, ROUND_FLOOR),
        )
        q_hi = (
            div_dir(self.lo, o.lo, ROUND_CEILING),
            div_dir(self.lo, o.hi, ROUND_CEILING),
            div_dir(self.hi, o.lo, ROUND_CEILING),
            div_dir(self.hi, o.hi, ROUND_CEILING),
        )
        return Iv(min(q_lo), max(q_hi))

    def __pow__(self, n: int) -> Iv:
        """self**n for an integer n >= 0 by binary powering with interval products.

        Each product is outward, so the result encloses x**n for every x in self.
        """
        if not isinstance(n, int) or n < 0:
            raise ValueError("Only non-negative integer powers are supported")
        if n == 0:
            return Iv(1)
        if n == 1:
            return self
        res = Iv(1)
        base = self
        e = n
        while e > 0:
            if e & 1:
                res = res * base
            e >>= 1
            if e > 0:
                base = base * base
        return res

    def sqrt(self) -> Iv:
        """[sqrt_down(lo), sqrt_up(hi)], an enclosure of sqrt on [lo, hi] (lo >= 0)."""
        if self.lo < 0:
            raise ValueError(f"sqrt of negative interval {self}")
        return Iv(sqrt_down(self.lo), sqrt_up(self.hi))

    def abs_hi(self) -> Decimal:
        """An upper bound for |x|, x in self (exact)."""
        return max(neg_exact(self.lo), self.hi)


ONE = Iv(1)
TWO = Iv(2)
HALF = Iv(Decimal("0.5"))
