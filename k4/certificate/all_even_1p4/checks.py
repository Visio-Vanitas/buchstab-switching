"""Named, recorded inequality checks.

Every inequality the certificate relies on is established by
``CheckList.require``.  It compares a certified bound for the left side with
a certified bound for the right side in the direction that makes the
comparison rigorous (e.g. for ``lhs > rhs`` it compares lhs.lo with rhs.hi),
records a ``Check`` (name, note section, the two bounds, a certified lower
bound for the margin, and the inputs), and raises ``CertificationError`` if
the inequality is not established.  Integers are compared exactly.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from decimal import ROUND_FLOOR, Decimal
from typing import Union

from .interval import Iv, sub_dir

Bound = Union[Iv, Decimal, int]
"""A quantity in a check: an interval enclosure, an exact Decimal, or an exact int."""


class CertificationError(Exception):
    """A required inequality could not be established."""


def _lower(x: Bound) -> Decimal | int:
    return x.lo if isinstance(x, Iv) else x


def _upper(x: Bound) -> Decimal | int:
    return x.hi if isinstance(x, Iv) else x


def _margin(big: Decimal | int, small: Decimal | int) -> Decimal | int:
    """A lower bound for big - small: exact for two ints, rounded down otherwise."""
    if isinstance(big, int) and isinstance(small, int):
        return big - small
    return sub_dir(Decimal(big), Decimal(small), ROUND_FLOOR)


@dataclass(frozen=True)
class Check:
    """One established inequality ``lhs <relation> rhs``.

    lhs_bound / rhs_bound are the certified one-sided bounds that were compared
    (for '>' and '>=': lower bound of lhs, upper bound of rhs; for '<' and '<=':
    upper bound of lhs, lower bound of rhs; for '==': the exact ints).
    margin is a certified lower bound for |lhs - rhs| in the direction of the
    relation (0 for '==').
    """

    name: str
    note_ref: str
    relation: str
    lhs_bound: Decimal | int
    rhs_bound: Decimal | int
    margin: Decimal | int
    inputs: tuple[tuple[str, Bound | str], ...] = field(default=())


@dataclass
class CheckList:
    """Collects the checks of one part of the certificate (a slab, the tail, ...)."""

    scope: str
    checks: list[Check] = field(default_factory=list)

    def require(self, name: str, note_ref: str, lhs: Bound, relation: str, rhs: Bound,
                **inputs: Bound | str) -> Check:
        """Establish ``lhs <relation> rhs`` rigorously and record it; raise if it fails."""
        if relation in (">", ">="):
            a, b = _lower(lhs), _upper(rhs)
            ok = a > b if relation == ">" else a >= b
            margin = _margin(a, b)
        elif relation in ("<", "<="):
            a, b = _upper(lhs), _lower(rhs)
            ok = a < b if relation == "<" else a <= b
            margin = _margin(b, a)
        elif relation == "==":
            if not (isinstance(lhs, int) and isinstance(rhs, int)):
                raise TypeError("'==' checks are for exact integers only")
            a, b = lhs, rhs
            ok = a == b
            margin = 0
        else:
            raise ValueError(f"unknown relation {relation!r}")
        check = Check(name, note_ref, relation, a, b, margin, tuple(inputs.items()))
        if not ok:
            raise CertificationError(f"{self.scope}: check '{name}' ({note_ref}) FAILED: {a} {relation} {b} is false")
        self.checks.append(check)
        return check

    def frozen(self) -> tuple[Check, ...]:
        return tuple(self.checks)
