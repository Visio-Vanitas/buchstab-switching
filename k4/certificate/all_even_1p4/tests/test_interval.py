"""Outwardness of the interval arithmetic, checked against exact Fractions."""

from __future__ import annotations

import random
import unittest
from decimal import ROUND_CEILING, ROUND_FLOOR, Context, Decimal, Inexact, localcontext
from fractions import Fraction

from all_even_1p4.elementary import LN2, exp_iv, ln_iv
from all_even_1p4.interval import PREC, Iv, sqrt_down, sqrt_up

RNG_SEED = 20261125
TRIALS = 400


def _frac(d: Decimal) -> Fraction:
    return Fraction(d)


def _contains(iv: Iv, exact: Fraction) -> bool:
    return _frac(iv.lo) <= exact <= _frac(iv.hi)


def _random_fraction(rng: random.Random) -> Fraction:
    num = rng.randint(-10**40, 10**40)
    den = rng.randint(1, 10**35)
    return Fraction(num, den) * Fraction(10) ** rng.randint(-20, 20)


class OutwardnessTest(unittest.TestCase):
    def setUp(self) -> None:
        self.rng = random.Random(RNG_SEED)

    def test_from_fraction_encloses(self) -> None:
        for _ in range(TRIALS):
            f = _random_fraction(self.rng)
            self.assertTrue(_contains(Iv.from_fraction(f), f))

    def test_arithmetic_encloses_exact_result(self) -> None:
        for _ in range(TRIALS):
            fa, fb = _random_fraction(self.rng), _random_fraction(self.rng)
            a, b = Iv.from_fraction(fa), Iv.from_fraction(fb)
            # every endpoint combination: the result must contain op(x, y) for x, y endpoints
            pts_a = (_frac(a.lo), _frac(a.hi))
            pts_b = (_frac(b.lo), _frac(b.hi))
            for x in pts_a:
                for y in pts_b:
                    self.assertTrue(_contains(a + b, x + y))
                    self.assertTrue(_contains(a - b, x - y))
                    self.assertTrue(_contains(a * b, x * y))
                    if not (b.lo <= 0 <= b.hi):
                        self.assertTrue(_contains(a / b, x / y))
            self.assertTrue(_contains(-a, -fa))

    def test_power_encloses(self) -> None:
        for _ in range(100):
            f = _random_fraction(self.rng)
            n = self.rng.randint(0, 12)
            self.assertTrue(_contains(Iv.from_fraction(f) ** n, f ** n))

    def test_sqrt_is_outward(self) -> None:
        for _ in range(TRIALS):
            f = abs(_random_fraction(self.rng))
            iv = Iv.from_fraction(f).sqrt()
            self.assertLessEqual(_frac(iv.lo) ** 2, f)
            self.assertGreaterEqual(_frac(iv.hi) ** 2, f)

    def test_sqrt_fix_needed(self) -> None:
        """Decimal.sqrt ignores directed rounding (the leak of review R18); sqrt_down/up do not."""
        with localcontext(Context(prec=PREC, rounding=ROUND_FLOOR)):
            r_floor = Decimal(3).sqrt()
        with localcontext(Context(prec=PREC, rounding=ROUND_CEILING)):
            r_ceil = Decimal(3).sqrt()
        self.assertEqual(r_floor, r_ceil)  # the leak: both contexts give the same half-even result
        self.assertGreater(_frac(r_floor) ** 2, 3)  # ... which is above sqrt(3): a false lower bound
        lo, hi = sqrt_down(Decimal(3)), sqrt_up(Decimal(3))
        self.assertLess(lo, hi)
        self.assertLessEqual(_frac(lo) ** 2, 3)
        self.assertGreaterEqual(_frac(hi) ** 2, 3)

    def test_exact_squares(self) -> None:
        for n in (0, 1, 4, 4 * 10**18, 10**34):
            r = Iv(n).sqrt()
            self.assertEqual(_frac(r.lo) ** 2, n)
            self.assertEqual(_frac(r.hi) ** 2, n)

    def test_division_by_interval_containing_zero_refused(self) -> None:
        with self.assertRaises(ZeroDivisionError):
            Iv(1) / Iv(-1, 1)

    def test_immutable(self) -> None:
        with self.assertRaises(AttributeError):
            Iv(1).lo = Decimal(0)

    def test_rounding_audit_is_active(self) -> None:
        """Importing the package traps Inexact in the default context."""
        with self.assertRaises(Inexact):
            Decimal(1) / Decimal(3)

    def test_rejects_float(self) -> None:
        """Iv rejects float/complex arguments at runtime."""
        with self.assertRaises(TypeError):
            Iv(1.0)
        with self.assertRaises(TypeError):
            Iv(0, 1.0)
        with self.assertRaises(TypeError):
            Iv(1.0, 2)
        with self.assertRaises(TypeError):
            _ = Iv(1) + 0.5

    def test_ln_exp_consistency(self) -> None:
        self.assertTrue(ln_iv(Iv(2)).lo <= LN2.hi and LN2.lo <= ln_iv(Iv(2)).hi)
        for _ in range(30):
            f = Fraction(self.rng.randint(1, 10**12), self.rng.randint(1, 10**6))
            x = Iv.from_fraction(f)
            back = exp_iv(ln_iv(x))
            self.assertTrue(_contains(back, f))
            self.assertLess(_frac(back.hi) - _frac(back.lo), Fraction(1, 10**80) * _frac(back.hi))


if __name__ == "__main__":
    unittest.main()
