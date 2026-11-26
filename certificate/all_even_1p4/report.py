"""Formatting only: run log lines, the JSON summary, the Markdown parameter table.

Display rounding is directed (fix of review R18, X26r_v2 finding 2): a printed
lower bound is rounded down and a printed upper bound is rounded up, so every
printed bound is itself a true bound.  JSON values are the full 90-digit
endpoints as strings.  Nothing here computes a certified quantity.
"""

from __future__ import annotations

import json
from decimal import ROUND_CEILING, ROUND_FLOOR, Context, Decimal, localcontext

from .benchmark import BenchmarkResult
from .certificate import STATUS_LINE, CertificateRun, min_net_slab
from .checks import Check
from .cited import ALL_CITATIONS, GOLDBACH_VERIFICATION
from .constants import C2_TWIN, E5_OVER_3, GAMMA, LI2, LI_E5, M0, PI, U_C
from .elementary import LN2
from .interval import ERROR_TRAPS, PREC, Iv
from .regime2 import SlabResult
from .regime3 import TailResult

# ---------------------------------------------------------------------------
# Directed decimal display
# ---------------------------------------------------------------------------


def _ctx(rounding: str) -> Context:
    return Context(prec=PREC + 10, rounding=rounding, traps=ERROR_TRAPS)


def fixed(x: Decimal | int, places: int, rounding: str) -> str:
    """x with ``places`` decimals, rounded in the given direction."""
    with localcontext(_ctx(rounding)):
        return str(Decimal(x).quantize(Decimal(1).scaleb(-places)))


def sci(x: Decimal | int, digits: int, rounding: str) -> str:
    """x as m.mmmm e+k with ``digits`` decimals in the mantissa, rounded in the given direction."""
    x = Decimal(x)
    if x == 0:
        return "0"
    with localcontext(_ctx(rounding)):
        exp = x.adjusted()
        mant = x.scaleb(-exp).quantize(Decimal(1).scaleb(-digits))
        if abs(mant) >= 10:
            exp += 1
            mant = x.scaleb(-exp).quantize(Decimal(1).scaleb(-digits))
    sign = "+" if exp >= 0 else "-"
    return f"{mant}e{sign}{abs(exp)}"


def lo_fixed(x: Iv, places: int = 6) -> str:
    return fixed(x.lo, places, ROUND_FLOOR)


def hi_fixed(x: Iv, places: int = 6) -> str:
    return fixed(x.hi, places, ROUND_CEILING)


def lo_sci(x: Iv, digits: int = 4) -> str:
    return sci(x.lo, digits, ROUND_FLOOR)


def hi_sci(x: Iv, digits: int = 4) -> str:
    return sci(x.hi, digits, ROUND_CEILING)


def power_of_ten(n: int) -> str:
    """An exact short form of c * 10^k (1 <= c <= 9), e.g. 4e18; otherwise the integer."""
    s = str(n)
    stripped = s.rstrip("0")
    if len(stripped) == 1:
        return f"{stripped}e{len(s) - 1}"
    return s


# ---------------------------------------------------------------------------
# Run log
# ---------------------------------------------------------------------------


def constants_lines() -> list[str]:
    def enc(name: str, x: Iv, places: int) -> str:
        return f"  {name:<7} in [{lo_fixed(x, places)}, {hi_fixed(x, places)}]"

    return [
        f"Outward-rounded Decimal/Fraction/int verification (PREC = {PREC}); default context traps Inexact, Rounded",
        "Printed lower bounds are rounded down and printed upper bounds up.",
        enc("pi", PI, 25), enc("ln(2)", LN2, 25), enc("gamma", GAMMA, 25),
        enc("C2", C2_TWIN, 12), enc("M0", M0, 12), enc("U_c", U_C, 12), enc("li(2)", LI2, 12),
        f"  li(e^5) <= {hi_fixed(LI_E5, 12)} < {lo_fixed(E5_OVER_3, 12)} <= e^5/3",
    ]


def benchmark_lines(b: BenchmarkResult) -> list[str]:
    k1, k2, k3 = b.k_values
    return [
        "=== BENCHMARK 0: Johnston-Starichkova (2208.01229v3), Thm 1.4 ranges and Thm 5.9 ===",
        f"  N < exp(104) (L+1=6):  K = {k1}",
        f"  N < exp(149) (L+1=13): K = {k2}",
        f"  N < exp(exp(5.077)) >= exp({lo_fixed(b.log_x2, 4)}) (L+1=21): K = {k3}",
        f"  Theorem 5.9 (JS: eps=1.312e-2 times C=559): coeff in [{lo_fixed(b.coeff_js, 4)}, {hi_fixed(b.coeff_js, 4)}]",
        f"  Theorem 5.9 (as Regime 3: eps'=1/76 times C2(1/76)=559): coeff in "
        f"[{lo_fixed(b.coeff_table, 4)}, {hi_fixed(b.coeff_table, 4)}]",
    ]


def regime1_lines() -> list[str]:
    return [
        "=== REGIME 1: 4 <= N <= 4 * 10^18 ===",
        f"  Cited, not computed: {GOLDBACH_VERIFICATION.source}. K = 1 <= 4.",
    ]


REGIME2_HEADER = "=== REGIME 2: Finite Slab Ladder [4*10^18, 10^170) for K = 4 ==="


def slab_line(r: SlabResult) -> str:
    p = r.params
    return (
        f"  Slab {p.index:2d}: [{power_of_ten(p.x_lo)}, {power_of_ten(p.x_hi)}) M={p.m:2d} a={p.a:2d} "
        f"odd={p.m_odd:2d} even={p.m_even:2d} z={r.z} y={r.y} "
        f"| main>={lo_fixed(r.main)} err<={hi_fixed(r.err_total)} net>={lo_fixed(r.net)}"
    )


def regime2_summary_line(slabs: tuple[SlabResult, ...]) -> str:
    worst = min_net_slab(slabs)
    n = len(slabs)
    scope = f"all {n} contiguous slabs" if n == 30 else f"{n} selected slab(s)"
    return f"  Regime 2 PASSED across {scope} (min net_lo >= {lo_fixed(worst.net)}, slab {worst.params.index})"


def tail_lines(r: TailResult) -> list[str]:
    p = r.params
    e = r.epsilon
    return [
        "=== REGIME 3: N >= 10^170, [BJS] Theorem 6 with pre-sieve, K = 4 ===",
        f"  X_LS = {power_of_ten(p.x_ls)} (log X_LS in [{lo_fixed(r.log_x, 4)}, {hi_fixed(r.log_x, 4)}])",
        f"  M = {p.m}, beta >= {lo_fixed(r.beta)}, u0 = {p.u0}, B = {p.b}, alpha = {r.alpha.lo}",
        f"  z0 >= {lo_sci(r.z0)}, eps <= {hi_sci(e.eps, 6)}, 1/eps >= {fixed((Iv(1) / e.eps).lo, 2, ROUND_FLOOR)}",
        f"  [BJS] Table 1 row eps^-1 = {e.row.inv_eps}: applied with eps' = 1/{e.row.inv_eps}, "
        f"C1 = {e.row.c1}, C2 = {e.row.c2}",
        f"  s in [{lo_fixed(r.s, 4)}, {hi_fixed(r.s, 4)}], s_min in [{lo_fixed(r.s_min, 4)}, {hi_fixed(r.s_min, 4)}]",
        f"  delta_V <= {hi_sci(r.delta_v, 6)}, c_4G <= {hi_fixed(r.c4g)}",
        f"  f(s) - eps'*C2*e^2*h(s) >= {lo_fixed(r.lb_a)}",
        f"  0.5 * sum_q phi(s_q)/(q-1) <= {hi_fixed(r.half_sum)}",
        f"  main_coeff >= {lo_fixed(r.main)}",
        f"  tot_err    <= {hi_fixed(r.err_total)} (R1<={hi_fixed(r.err_r1)}, R2<={hi_fixed(r.err_r2)}, "
        f"rq<={hi_fixed(r.err_rq)}, q2<={hi_sci(r.err_q2, 2)})",
        f"  NET COEFF  >= {lo_fixed(r.net)} (pi_4(N) > NET * {p.m} * U_N * N / log^2 N for all even N >= 10^170)",
    ]


def result_lines(run: CertificateRun) -> list[str]:
    n = len(run.all_checks())
    if run.complete:
        return [
            "=== RESULT ===",
            f"  All {n} recorded checks hold: Regimes 2 and 3 checked; Regime 1 is the cited Goldbach verification.",
            "  Together with the quoted lemmas (note X26, section 0), this gives K = 4 for all even N >= 4 under GRH,",
            "  subject to the status below.",
            f"  STATUS: {STATUS_LINE}",
        ]
    return [
        "=== RESULT (PARTIAL RUN) ===",
        f"  All {n} recorded checks of the parts that were run hold. This is NOT the full certificate.",
        f"  STATUS: {STATUS_LINE}",
    ]


# ---------------------------------------------------------------------------
# JSON summary (deterministic: no timestamps, no platform data)
# ---------------------------------------------------------------------------


def _js(x: object) -> object:
    if isinstance(x, Iv):
        return {"lo": str(x.lo), "hi": str(x.hi)}
    if isinstance(x, Decimal):
        return str(x)
    if isinstance(x, bool) or x is None or isinstance(x, str):
        return x
    if isinstance(x, int):
        return x if abs(x) < 2**53 else str(x)
    raise TypeError(f"unexpected value in summary: {type(x).__name__}")


def check_json(scope: str, c: Check) -> dict:
    return {
        "scope": scope, "name": c.name, "note_ref": c.note_ref, "relation": c.relation,
        "lhs_bound": _js(c.lhs_bound), "rhs_bound": _js(c.rhs_bound), "margin": _js(c.margin),
        "inputs": {k: _js(v) for k, v in c.inputs},
    }


def slab_json(r: SlabResult) -> dict:
    p = r.params
    return {
        "index": p.index, "X_lo": _js(p.x_lo), "X_hi": _js(p.x_hi), "M": p.m, "a": p.a, "p_a": r.p_a,
        "m_odd": p.m_odd, "m_even": p.m_even, "z": _js(r.z), "y": _js(r.y),
        "max_d_odd": _js(r.max_d_odd), "max_d_even": _js(r.max_d_even),
        "sieve_branch": r.sieve.branch, "p2_size": r.sieve.p2_size, "q_sum_branch": r.q_sums.branch,
        "q2_branch": r.q2_branch,
        "V_lower": _js(r.v_lower), "R_odd": _js(r.sieve.ratio_odd), "R_even": _js(r.sieve.ratio_even),
        "num_q": _js(r.q_sums.count), "sum_q_inv": _js(r.q_sums.inv), "sum_q2_inv": _js(r.q_sums.inv_sq),
        "num_d_odd": _js(r.sieve.num_d_odd), "num_d_even": _js(r.sieve.num_d_even),
        "bracket": _js(r.bracket), "main": _js(r.main), "err_per_modulus": _js(r.err_per_modulus),
        "err_A": _js(r.err_a), "err_Aq": _js(r.err_aq), "err_q2": _js(r.err_q2),
        "err_total": _js(r.err_total), "net": _js(r.net),
    }


def tail_json(r: TailResult) -> dict:
    p = r.params
    e = r.epsilon
    return {
        "X_LS": _js(p.x_ls), "M": p.m, "u0": p.u0, "B": p.b, "slices": p.slices, "Q_max": _js(r.q_prod),
        "log_X": _js(r.log_x), "alpha": _js(r.alpha), "beta": _js(r.beta), "z0": _js(r.z0),
        "log_H0": _js(r.log_h0), "s": _js(r.s), "s_min": _js(r.s_min),
        "epsilon": {
            "twin_tail": _js(e.twin_tail), "E_max": _js(e.e_max), "E_low": _js(e.e_low),
            "c_log": _js(e.c_log), "sum_p_ge_u0_p^-2": _js(e.p2_tail), "eps": _js(e.eps),
            "table_row": {"inv_eps": e.row.inv_eps, "C1": e.row.c1, "C2": e.row.c2}, "eps_used": _js(e.eps_used),
        },
        "delta_V": _js(r.delta_v), "f(s)_lower[f(4)]": _js(r.f_s), "h(s)_upper": _js(r.h_s),
        "lower_sieve_bracket": _js(r.lb_a), "half_q_sum": _js(r.half_sum), "main_bracket": _js(r.main_bracket),
        "main": _js(r.main), "c4G": _js(r.c4g), "phi(s_min)_upper": _js(r.phi_max),
        "R1": _js(r.err_r1), "R2": _js(r.err_r2), "rq": _js(r.err_rq), "q2": _js(r.err_q2),
        "err_total": _js(r.err_total), "net": _js(r.net),
    }


def summary(run: CertificateRun) -> dict:
    worst = run.min_slab()
    out: dict = {
        "certificate": "note X26: every even N >= 4 is p + eta with Omega(eta) <= 4, under GRH (arithmetic check)",
        "status": STATUS_LINE,
        "complete_run": run.complete,
        "precision_digits": PREC,
        "constants": {
            "pi": _js(PI), "ln2": _js(LN2), "gamma": _js(GAMMA), "C2_twin": _js(C2_TWIN), "M0": _js(M0),
            "U_c": _js(U_C), "li(2)": _js(LI2), "li(e^5)": _js(LI_E5), "e^5/3": _js(E5_OVER_3),
        },
        "regime1": {"range": "4 <= N <= 4e18", "cited": GOLDBACH_VERIFICATION.source},
        "benchmark": None,
        "regime2": {
            "slabs": [slab_json(s) for s in run.slabs],
            "min_net": None if worst is None else {"slab": worst.params.index, "lower_bound": _js(worst.net.lo)},
        },
        "regime3": None if run.tail is None else tail_json(run.tail),
        "citations": [
            {"key": c.key, "source": c.source, "reference": c.reference, "statement": c.statement,
             "hypotheses": c.hypotheses, "assumption": c.assumption, "note_section": c.note_section}
            for c in ALL_CITATIONS
        ],
        "checks": [check_json(scope, c) for scope, c in run.all_checks()],
    }
    if run.benchmark is not None:
        b = run.benchmark
        out["benchmark"] = {"K": list(b.k_values), "coeff_js": _js(b.coeff_js), "coeff_table": _js(b.coeff_table)}
    out["number_of_checks"] = len(out["checks"])
    return out


def summary_json(run: CertificateRun) -> str:
    return json.dumps(summary(run), indent=1) + "\n"


# ---------------------------------------------------------------------------
# Markdown parameter table
# ---------------------------------------------------------------------------


def parameter_table(run: CertificateRun) -> str:
    lines = [
        "# Parameter table: note X26 certificate (all even N >= 4 are p + eta, Omega(eta) <= 4, under GRH)",
        "",
        "Generated by `python -m all_even_1p4`. Lower bounds (>=) are rounded down and upper bounds (<=) up,",
        "so every printed number is a true bound. Full-precision values are in `summary.json`.",
        "",
        f"Status: {STATUS_LINE}",
        "",
        "## Regime 2 slabs (note sections 2-3), terms normalised by N/log N",
        "",
        "Columns: M gives z (z^M >= X_hi); y is shown to 4 digits (exact in the JSON); Q1 = first a odd primes (exact inclusion-exclusion, largest p_a);",
        "m_odd / m_even = Bonferroni truncation order of the lower / upper sieve on P2 = (p_a, z);",
        "P2 = exact or analytic branch; q-sums = how sums over z <= q < y are bounded; q^2 = branch of the",
        "q^2 term. err_A, err_Aq, err_q2 are the three error terms; net = main - (err_A + err_Aq + err_q2).",
        "",
        "| slab | N range | M | z | y | Q1: a, p_a | m_odd/m_even | P2 | q-sums | q^2 | main >= | err_A <= "
        "| err_Aq <= | err_q2 <= | net >= |",
        "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|",
    ]
    for r in run.slabs:
        p = r.params
        lines.append(
            f"| {p.index} | [{power_of_ten(p.x_lo)}, {power_of_ten(p.x_hi)}) | {p.m} | {r.z} | {sci(r.y, 4, ROUND_FLOOR)} "
            f"| {p.a}, {r.p_a} | {p.m_odd}/{p.m_even} | {r.sieve.branch} "
            f"| {r.q_sums.branch} | {r.q2_branch} | {lo_sci(r.main)} | {hi_sci(r.err_a)} | {hi_sci(r.err_aq)} "
            f"| {hi_sci(r.err_q2)} | {lo_sci(r.net)} |"
        )
    worst = run.min_slab()
    if worst is not None:
        lines += ["", f"Minimum slab margin: net >= {lo_fixed(worst.net, 9)} (slab {worst.params.index})."]
    if run.tail is not None:
        t = run.tail
        e = t.epsilon
        p = t.params
        rows = [
            ("range", f"N >= {power_of_ten(p.x_ls)}", "s4"),
            ("M (z = N^(1/M)), beta (y = N^beta)", f"{p.m}, beta = {p.m - 1}/{4 * p.m}", "s4.1"),
            ("pre-sieve Q = {3 <= p < u0}, Q <=", f"u0 = {p.u0}, Q <= {t.q_prod}", "s4.1"),
            ("B (H = sqrt N/log^(B+1) N)", p.b, "s4.1"),
            ("alpha (D = N^(1/2-alpha))", str(t.alpha.lo), "s4.1"),
            ("s = M(1/2 - alpha)", f"[{lo_fixed(t.s, 6)}, {hi_fixed(t.s, 6)}]", "s4.1"),
            ("s_min = M(1/2 - alpha - beta)", f"[{lo_fixed(t.s_min, 6)}, {hi_fixed(t.s_min, 6)}]", "s4.1"),
            ("z_0 = X_LS^(1/M)", f">= {lo_sci(t.z0, 6)}", "s4.1"),
            ("epsilon bound", f"eps <= {hi_sci(e.eps, 6)}", "s4.2"),
            ("table row used ([BJS] v6 Table 1)", f"eps^-1 = {e.row.inv_eps}, eps' = 1/{e.row.inv_eps}", "s0.1, s4.2"),
            ("C_1(eps') (upper bound), C_2(eps') (lower bound)", f"{e.row.c1}, {e.row.c2}", "s0.1"),
            ("f(s) >= f(4)", f">= {lo_fixed(t.f_s, 6)}", "s4.3"),
            ("h(s)", f"<= {hi_sci(t.h_s, 4)}", "s4.3"),
            ("F(s_min) + eps' C_1 e^2 h(s_min)", f"<= {hi_fixed(t.phi_max, 6)}", "s4.4"),
            ("delta_V ([BJS] Lemma 38)", f"<= {hi_sci(t.delta_v, 6)}", "s4.3"),
            ("lower sieve bracket f(s) - eps' C_2 e^2 h(s)", f">= {lo_fixed(t.lb_a, 6)}", "s4.3"),
            ("1/2 sum_q phi(s_q)/(q-1)", f"<= {hi_fixed(t.half_sum, 6)}", "s4.3"),
            ("main = (1 - delta_V)(bracket - half sum)", f">= {lo_fixed(t.main, 6)}", "s4.3"),
            ("c_4G", f"<= {hi_fixed(t.c4g, 6)}", "s4.4"),
            ("R1", f"<= {hi_sci(t.err_r1, 4)}", "s4.4"),
            ("R2", f"<= {hi_sci(t.err_r2, 4)}", "s4.4"),
            ("rq", f"<= {hi_sci(t.err_rq, 4)}", "s4.4"),
            ("q2", f"<= {hi_sci(t.err_q2, 4)}", "s4.4"),
            ("total error", f"<= {hi_fixed(t.err_total, 6)}", "s4.4"),
            ("net (units of M U_N N/log^2 N)", f">= {lo_fixed(t.net, 9)}", "s4.4"),
        ]
        lines += [
            "",
            "## Regime 3 tail (note section 4), terms normalised by M U_N N/log^2 N",
            "",
            "| quantity | value | note |",
            "|---|---|---|",
        ]
        lines += [f"| {a} | {b} | {c} |" for a, b, c in rows]
    if not run.complete:
        lines += ["", "**Partial run: not every part of the certificate was checked.**"]
    return "\n".join(lines) + "\n"
