"""The remainder bound (*) of the note, section 1, per modulus.

Setting (note section 1): N even, A = {N - p : p <= N prime, p does not divide N},
A_d = {a in A : d | a}, r(d) = |A_d| - |A|/phi(d).  For 3 <= d <= sqrt(N) with
(d, N) = 1, and N >= X2 >= 4e18:

    |r(d)| <= |pi(N;d,N) - li N/phi(d)| + |pi(N) - li N|/phi(d) + omega(N)
           <= (c_pi(X2) + 1/(16 pi)) sqrt(N) log N + 1.3841 log N/log log N.     (*)

The first term is [JS] Lemma 5.1, the second Schoenfeld ([BS] Lemma 1) with
phi(d) >= 2, the third comes from |A| = pi(N) - omega(N) and
|A_d| = pi(N;d,N) - omega(N;d,N) ([JS] Lemma 5.8 proof) with Robin ([BS] Lemma 4).
"""

from __future__ import annotations

from .cited import js_lemma_5_1_c_pi, robin_constant, schoenfeld_denominator
from .constants import PI
from .elementary import ln_iv
from .interval import ONE, Iv

PHI_MIN = 2
"""phi(d) >= 2 for every modulus d >= 3."""


def grh_remainder_coeff(log_x2: Iv, x2: int | None = None) -> Iv:
    """c_pi(X2) + 1/(16 pi): the coefficient of sqrt(N) log N in (*), valid for N >= X2.

    The 16 is Schoenfeld's 8 times phi(d) >= 2.  Schoenfeld's range x >= 2657 is
    implied by X2 >= 4e18, which ``js_lemma_5_1_c_pi`` validates.
    """
    c_pi = js_lemma_5_1_c_pi(log_x2, x2)
    return c_pi + ONE / (Iv(PHI_MIN * schoenfeld_denominator(4 * 10**18)) * PI)


def omega_upper(log_n: Iv, n_min: int) -> Iv:
    """Upper end bounds omega(N) < 1.3841 log N/log log N ([BS] Lemma 4), for N >= n_min >= 3.

    The interval is evaluated at the given log N.  Callers use it in the
    normalised error omega(N) log N/N, which is decreasing in N, so they pass
    log of the LOWER end of their range of N.
    """
    return Iv(robin_constant(n_min)) * log_n / ln_iv(log_n)
