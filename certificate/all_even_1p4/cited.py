"""Every result imported from the literature, with provenance and range checks.

Each cited result is a ``Citation`` record (source, version, exact number and
TeX label, statement as quoted in note X26 section 0, hypotheses) together
with one accessor function.  The accessor validates the hypotheses of the
result *at call time* and only then returns the numerical constants the
certificate uses.  Validation raises ``HypothesisError`` (not ``assert``, so it
also runs under ``python -O``); a cited bound therefore cannot be used outside
its stated range.

The certificate checks arithmetic GIVEN these statements.  It does not prove
them.  Known doubts about the statements themselves are recorded in the
package README ("Issues found") and in review R18.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal

from .constants import LI2, PI
from .elementary import exp_iv, ln_iv
from .interval import ONE, Iv

# ---------------------------------------------------------------------------
# Records
# ---------------------------------------------------------------------------


class HypothesisError(Exception):
    """A cited result was invoked outside the range in which it is stated."""


@dataclass(frozen=True)
class Citation:
    """One imported result.

    key           short id used in check names and the README
    source        authors and arXiv id with version (or journal)
    reference     theorem/lemma number in that version, and its TeX label if known
    statement     the statement as used (quoted in note X26, section 0)
    hypotheses    the range conditions that the accessor validates
    assumption    "GRH", "RH" or "unconditional"
    note_section  where note X26 quotes it
    """

    key: str
    source: str
    reference: str
    statement: str
    hypotheses: str
    assumption: str
    note_section: str


def _require(condition: bool, citation: Citation, detail: str) -> None:
    if not condition:
        raise HypothesisError(f"[{citation.key}] {citation.reference}: hypothesis fails: {detail}")


BJS = "Bordignon, Johnston, Starichkova, arXiv:2207.09452v6"
JS = "Johnston, Starichkova, arXiv:2208.01229v3 (numbering of the v3 PDF)"
BS = "Bordignon, Starichkova, arXiv:2211.08844v1"

# ---------------------------------------------------------------------------
# Regime 1
# ---------------------------------------------------------------------------

GOLDBACH_VERIFICATION = Citation(
    key="OeSHP",
    source="Oliveira e Silva, Herzog, Pardi, Math. Comp. 83 (2014), as quoted in [BJS] section 1 and [JS] section 1",
    reference="main result (primary paper not read)",
    statement="Every even N with 4 <= N <= 4e18 is a sum of two primes.",
    hypotheses="4 <= N <= 4e18, N even",
    assumption="unconditional (computation)",
    note_section="X26 section 0.6",
)

# ---------------------------------------------------------------------------
# GRH bound for primes in progressions
# ---------------------------------------------------------------------------

JS_LEMMA_5_1 = Citation(
    key="JS-L5.1",
    source=JS,
    reference="Lemma 5.1 (TeX label epilem)",
    statement=(
        "Let x >= X2 >= 4e18 and 3 <= q <= sqrt(x), (a,q) = 1. Assuming GRH, "
        "|pi(x;q,a) - li(x)/phi(q)| <= c_pi(X2) sqrt(x) log x with c_pi(X2) = 3/(8 pi) "
        "+ (6 + 1/pi)/(4 log X2) + 6/log^2 X2 + li(2)/(sqrt(X2) log X2)."
    ),
    hypotheses="X2 >= 4e18 (validated here); x >= X2 and 3 <= q <= sqrt(x), (q, a) = 1 (validated by the caller as named checks)",
    assumption="GRH",
    note_section="X26 section 0.2",
)
JS_LEMMA_5_1_X2_MIN = 4 * 10**18


def js_lemma_5_1_c_pi(log_x2: Iv, x2: int | None = None) -> Iv:
    """c_pi(X2) of [JS] Lemma 5.1, an enclosure.

    ``x2`` is X2 as an exact integer when known; otherwise ``log_x2`` must be
    >= log(4e18), checked in intervals.  The modulus range 3 <= q <= sqrt(x) is
    a property of the caller's moduli and is checked there.
    """
    if x2 is not None:
        _require(x2 >= JS_LEMMA_5_1_X2_MIN, JS_LEMMA_5_1, f"X2 = {x2} < 4e18")
    else:
        _require(log_x2.lo >= ln_iv(Iv(JS_LEMMA_5_1_X2_MIN)).hi, JS_LEMMA_5_1, f"log X2 = {log_x2.lo} < log 4e18")
    sqrt_x2 = exp_iv(Iv(Decimal("0.5")) * log_x2)
    t1 = Iv(3) / (Iv(8) * PI)
    t2 = (Iv(6) + ONE / PI) / (Iv(4) * log_x2)
    t3 = Iv(6) / (log_x2 ** 2)
    t4 = LI2 / (sqrt_x2 * log_x2)
    return t1 + t2 + t3 + t4


# ---------------------------------------------------------------------------
# RH / unconditional prime-counting results
# ---------------------------------------------------------------------------

SCHOENFELD = Citation(
    key="BS-L1",
    source=BS + ", quoting Schoenfeld, Math. Comp. 30 (1976), Corollary 1",
    reference="Lemma 1",
    statement="If RH holds, |pi(x) - li(x)| <= sqrt(x) log x/(8 pi).",
    hypotheses=(
        "x >= 2657.  [BS] prints 'for 3 <= x', which is false at x = 3 (review R18); the range "
        "x >= 2657 is the one usually attributed to Schoenfeld and is the one validated here. "
        "Every use in the certificate has x >= 30000."
    ),
    assumption="RH",
    note_section="X26 section 0.3",
)
SCHOENFELD_X_MIN = 2657


def schoenfeld_denominator(x_min: int) -> int:
    """The 8 in |pi(x) - li(x)| <= sqrt(x) log x/(8 pi), for every x >= x_min (x_min >= 2657)."""
    _require(x_min >= SCHOENFELD_X_MIN, SCHOENFELD, f"x >= {x_min} is not inside x >= 2657")
    return 8


ROBIN = Citation(
    key="BS-L4",
    source=BS + ", quoting Robin (1983)",
    reference="Lemma 4",
    statement="omega(N) < 1.3841 log N/log log N for N >= 3.",
    hypotheses="N >= 3",
    assumption="unconditional",
    note_section="X26 section 0.3",
)


def robin_constant(n_min: int) -> Decimal:
    """1.3841, valid for omega(N) with every N >= n_min (n_min >= 3)."""
    _require(n_min >= 3, ROBIN, f"N >= {n_min}")
    return Decimal("1.3841")


BUTHE = Citation(
    key="BS-L5",
    source=BS + ", quoting Buthe",
    reference="Lemma 5",
    statement=(
        "For x >= 1e9: sum_{n<=x} mu^2(n) <= 0.608 x and "
        "sum_{n<=x} mu^2(n)/phi(n) <= log x + 1.333 + 58/sqrt(x) <= 1.1 log x."
    ),
    hypotheses="x >= 1e9 (checked as log x > log 1e9 in intervals)",
    assumption="unconditional",
    note_section="X26 section 0.3",
)


def buthe_constants(log_x_lo: Decimal, log_1e9_hi: Decimal) -> tuple[Decimal, Decimal]:
    """(0.608, 1.1): squarefree density and mu^2/phi coefficient, valid for x >= 1e9.

    The caller passes a lower bound for log x and an upper bound for log 1e9.
    """
    _require(log_x_lo > log_1e9_hi, BUTHE, f"log x >= {log_x_lo} not > log 1e9")
    return Decimal("0.608"), Decimal("1.1")


# ---------------------------------------------------------------------------
# |A| and Mertens
# ---------------------------------------------------------------------------

JS_LEMMA_3_1 = Citation(
    key="JS-L3.1",
    source=JS,
    reference="Lemma 3.1 (TeX label Alem)",
    statement="For all N >= 71, |A| > N/log N, where A = {N - p : p <= N, p does not divide N}.",
    hypotheses="N >= 71",
    assumption="unconditional",
    note_section="X26 section 0.2",
)


def require_js_lemma_3_1(n_min: int) -> None:
    """Validate that |A| > N/log N may be used for every N >= n_min."""
    _require(n_min >= 71, JS_LEMMA_3_1, f"N >= {n_min}")


JS_LEMMA_3_2 = Citation(
    key="JS-L3.2",
    source=JS,
    reference="Lemma 3.2 (TeX label mertenlem), inequalities (3.1), (3.2), (3.3)",
    statement=(
        "(3.1) sum_{p<x} 1/p >= log log x + M0 - 2.964e-6/log x, x >= 2; "
        "(3.2) sum_{p<x} 1/p <= log log x + M0 + 1.614e-3, x > exp(8.9); "
        "(3.3) sum_{p<x} 1/p <= log log x + M0 + 6.836e-6/log x, x > 1e12."
    ),
    hypotheses="as stated per inequality",
    assumption="unconditional",
    note_section="X26 section 0.2",
)
BJS_LEMMA_16 = Citation(
    key="BJS-L16",
    source=BJS,
    reference="Lemma 16 (TeX label mertencomplem)",
    statement="For 2 <= x <= 1e12: log log x + M < sum_{p<=x} 1/p < log log x + M + 2/(sqrt(x) log x).",
    hypotheses="2 <= x <= 1e12",
    assumption="unconditional (computation)",
    note_section="X26 section 0.2",
)
MERTENS_TEN12 = 10**12


def mertens_lower_coeff(x_min: Decimal) -> Decimal:
    """[JS] (3.1): the 2.964e-6 in sum_{p<x} 1/p >= log log x + M0 - 2.964e-6/log x, x >= x_min >= 2."""
    _require(x_min >= 2, JS_LEMMA_3_2, f"(3.1) needs x >= 2, got x >= {x_min}")
    return Decimal("2.964e-6")


def mertens_cap(log_x_lo: Decimal) -> Decimal:
    """[JS] (3.2): the 1.614e-3, valid for x > exp(8.9); the caller passes a lower bound of log x."""
    _require(log_x_lo > Decimal("8.9"), JS_LEMMA_3_2, f"(3.2) needs x > exp(8.9), log x >= {log_x_lo}")
    return Decimal("1.614e-3")


def mertens_large_coeff(x_min: Decimal) -> Decimal:
    """[JS] (3.3): the 6.836e-6 in E_<(x) <= 6.836e-6/log x, valid for x > 1e12.

    ``x_min`` is the lower end of the x-range; x = 1e12 itself is allowed
    because the caller covers x <= 1e12 by [BJS] Lemma 16 and uses (3.3) only
    for x > max(x_min, 1e12)."""
    _require(x_min >= MERTENS_TEN12, JS_LEMMA_3_2, f"(3.3) needs x > 1e12, range starts at {x_min}")
    return Decimal("6.836e-6")


def bjs_lemma_16_numerator(x_lo: Decimal, x_hi: Decimal) -> int:
    """[BJS] Lemma 16: the 2 in E(x) < 2/(sqrt(x) log x), for 2 <= x_lo <= x <= x_hi <= 1e12."""
    _require(x_lo >= 2 and x_hi <= MERTENS_TEN12, BJS_LEMMA_16, f"range [{x_lo}, {x_hi}] not in [2, 1e12]")
    return 2


# ---------------------------------------------------------------------------
# The explicit linear sieve
# ---------------------------------------------------------------------------

BJS_THEOREM_6 = Citation(
    key="BJS-T6",
    source=BJS,
    reference="Theorem 6 'The linear-sieve, explicit version' (TeX label theo:JR) and Table 1",
    statement=(
        "If 0 < eps <= 1/74 and prod_{p in P\\Q, u <= p < z} (1 - g_n(p))^{-1} < (1+eps) log z/log u "
        "for all n and 1 < u < z, then for D >= z: S(A,P,z) < (F(s) + eps C1(eps) e^2 h(s)) X_A + R, "
        "and for D >= z^2: S(A,P,z) > (f(s) - eps C2(eps) e^2 h(s)) X_A - R, s = log D/log z, "
        "R = sum_{d | P(z), d < QD} |r(d)|; h(s) = e^-2 (1<=s<=2), e^-s (2<=s<=3), 3 s^-1 e^-s (s>=3)."
    ),
    hypotheses=(
        "0 < eps <= 1/74 (validated: the row used has eps' = 1/k with k >= 74 and eps < eps'); "
        "D >= z^2 for the lower bound and D >= z for the upper bound (validated by the caller as s >= 2, "
        "s_min >= 1).  The product hypothesis is proved in note section 4.2 under the fixed-z reading; "
        "review R18 leaves open whether the proof of the theorem needs it at levels below z."
    ),
    assumption="unconditional",
    note_section="X26 sections 0.1, 4.2",
)


@dataclass(frozen=True)
class SieveTableRow:
    """One row of [BJS] v6 Table 1: eps^-1 = inv_eps, C1(1/inv_eps) (upper bound), C2 (lower bound)."""

    inv_eps: int
    c1: int
    c2: int


BJS_TABLE_1: tuple[SieveTableRow, ...] = tuple(
    SieveTableRow(k, c1, c2)
    for (k, c1, c2) in (
        (74, 631, 630), (76, 559, 559), (78, 504, 504), (80, 461, 461),
        (85, 386, 386), (90, 336, 337), (95, 302, 302), (100, 276, 277),
        (120, 218, 219), (140, 189, 190), (160, 172, 173), (180, 161, 162),
        (200, 153, 154), (300, 133, 134), (400, 125, 126), (500, 121, 122),
        (600, 118, 119), (700, 116, 117), (800, 115, 116), (900, 114, 115),
        (1000, 113, 114), (2000, 109, 110), (10000, 106, 108), (100000, 106, 107),
    )
)
"""Table 1 "Values for C_1(eps) and C_2(eps)" of arXiv:2207.09452v6, transcribed from the
v6 TeX source (note X26 section 0.1; all 24 rows compared with the TeX by review R18 v3).
By [BJS] Lemma 14, C1 = sum tau_{2n-1} belongs to the upper bound and C2 = sum tau_{2n}
to the lower bound."""


# SUPERSEDED (reviews R18, R20, R22): this is the original X26 Regime 3 path (half-open hypothesis below a fixed
# z0 with u0 = 41, [BJS] Table 1 row 100, C1 = 276, C2 = 277). It does not certify the tail. The tail in use is
# all_even_1p4_ext/tail_x31.py with constants from cn_certify and Q0 from hstar_certify. Kept only so that the
# original X26 output stays reproducible.
def bjs_table_row(eps: Iv) -> SieveTableRow:
    """SUPERSEDED (reviews R18, R20, R22): see the comment above. The row used for a proved hypothesis constant eps: the largest k with k <= 1/eps.hi.

    If the hypothesis of Theorem 6 holds with eps, it holds with every eps' in
    [eps, 1/74]; the theorem is applied at eps' = 1/k with the tabulated
    C_i(1/k).  No interpolation and no monotonicity in eps is used (note 0.1).
    Raises HypothesisError if 1/eps < 74 (Theorem 6 does not apply).
    """
    inv_lo = (ONE / Iv(eps.hi)).lo
    chosen = None
    for row in BJS_TABLE_1:
        if Decimal(row.inv_eps) <= inv_lo:
            chosen = row
    _require(chosen is not None, BJS_THEOREM_6, f"1/eps >= {inv_lo} < 74")
    return chosen


BJS_LEMMA_19 = Citation(
    key="BJS-L19",
    source=BJS + " (= Cai, Lemma 2); monotonicity of f, F from " + JS + " section 2",
    reference="Lemma 19 (TeX label lem: estimetes-f-F)",
    statement=(
        "F(s) = 2e^gamma/s for 0 < s <= 3; F(s) = (2e^gamma/s)(1 + int_2^{s-1} log(t-1)/t dt) for 3 <= s <= 4; "
        "f(s) = 0 for 0 < s <= 2; f(s) = 2e^gamma log(s-1)/s for 2 <= s <= 4.  [JS]: F decreases, f increases."
    ),
    hypotheses=(
        "formula domains as stated; the F formula is extended to [3, 5] from the delay equation "
        "(sF)' = f(s-1) (note X26 section 0.1)"
    ),
    assumption="unconditional",
    note_section="X26 section 0.1",
)

BJS_LEMMA_38 = Citation(
    key="BJS-L38",
    source=BJS,
    reference="Lemma 38 (TeX label vjlem), case j = 0",
    statement=(
        "For x >= 285: V(x) = U_N/log x [1 + 1.45 th1 log N/(x-1) (1 + 10 log log N/log N)] "
        "(1 + 1.002 th2/(x-3)) (1 + th3/(2 log^2 x)), |th_i| <= 1, V(x) = prod_{p<x, p nmid N} (1 - 1/(p-1))."
    ),
    hypotheses="x >= 285",
    assumption="unconditional",
    note_section="X26 section 0.1",
)


def bjs_lemma_38_constants(x_min: Decimal) -> tuple[Decimal, int, Decimal]:
    """(1.45, 10, 1.002) of [BJS] Lemma 38, valid for x >= x_min >= 285."""
    _require(x_min >= 285, BJS_LEMMA_38, f"x >= {x_min}")
    return Decimal("1.45"), 10, Decimal("1.002")


# ---------------------------------------------------------------------------
# Used only by the benchmark
# ---------------------------------------------------------------------------

BJS_LEMMA_23 = Citation(
    key="BJS-L23",
    source=BJS,
    reference="Lemma 23 (TeX label squarefreelem)",
    statement="For all x >= 45, sum_{n<=x} mu^2(n) <= 0.65 x.",
    hypotheses="x >= 45",
    assumption="unconditional",
    note_section="X26 section 0.1 (benchmark only)",
)
JS_LEMMAS_5_7_5_8_THEOREM_5_9 = Citation(
    key="JS-L5.7/5.8/T5.9",
    source=JS,
    reference="Lemma 5.7, Lemma 5.8, Theorem 5.9, Lemma 3.3 (eps = 1.312e-2), Lemma 3.4 (xi = 1244)",
    statement=(
        "p_G(X2) = 0.65 (c_pi(X2) + 1/(16 pi)); c_4G(X2) = p_G(X2) + 0.9/(sqrt(X2) log log X2); "
        "Theorem 5.9 at X2 = exp(exp(5.077)), M = 18, alpha = 0.285, B = 2.01 gives S(A,P(z)) > 1.48 U_N N/log^2 N."
    ),
    hypotheses="parameters as printed in [JS]",
    assumption="GRH",
    note_section="X26 sections 0.2, 5",
)

ALL_CITATIONS: tuple[Citation, ...] = (
    GOLDBACH_VERIFICATION, JS_LEMMA_5_1, SCHOENFELD, ROBIN, BUTHE, JS_LEMMA_3_1, JS_LEMMA_3_2,
    BJS_LEMMA_16, BJS_THEOREM_6, BJS_LEMMA_19, BJS_LEMMA_38, BJS_LEMMA_23, JS_LEMMAS_5_7_5_8_THEOREM_5_9,
)
