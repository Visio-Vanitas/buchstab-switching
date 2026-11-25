"""The primes up to P_CUT (exact integers) and small exact integer helpers."""

from __future__ import annotations

P_CUT = 30000
"""Every prime <= P_CUT is listed explicitly; above it only analytic bounds are used.
P_CUT is composite, so sums over primes < P_CUT and <= P_CUT agree."""


def isqrt_floor(n: int) -> int:
    """floor(sqrt(n)) for an integer n >= 0, by integer Newton iteration (exact)."""
    if n < 0:
        raise ValueError("isqrt of a negative integer")
    if n < 2:
        return n
    x = 1 << ((n.bit_length() + 1) // 2)  # x >= sqrt(n)
    while True:
        y = (x + n // x) // 2
        if y >= x:
            return x
        x = y


def sieve_primes(limit: int) -> tuple[int, ...]:
    """All primes p <= limit, by the sieve of Eratosthenes."""
    is_p = bytearray([1]) * (limit + 1)
    is_p[0] = 0
    is_p[1] = 0
    for i in range(2, isqrt_floor(limit) + 1):
        if is_p[i]:
            is_p[i * i : limit + 1 : i] = bytearray(len(range(i * i, limit + 1, i)))
    return tuple(i for i, v in enumerate(is_p) if v)


PRIMES = sieve_primes(P_CUT)
"""(2, 3, 5, ..., 29989): all primes <= P_CUT."""


def binomial(n: int, k: int) -> int:
    """The binomial coefficient C(n, k), exactly (0 if k < 0 or k > n)."""
    if k < 0 or k > n:
        return 0
    k = min(k, n - k)
    num = 1
    den = 1
    for i in range(1, k + 1):
        num *= n - k + i
        den *= i
    return num // den


def factorial(n: int) -> int:
    """n!, exactly."""
    out = 1
    for j in range(1, n + 1):
        out *= j
    return out


def product(values: list[int] | tuple[int, ...]) -> int:
    """The product of a sequence of integers, exactly."""
    out = 1
    for v in values:
        out *= v
    return out
