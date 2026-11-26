"""
Linear sieve functions `f(s)`, `F(s)`, Lyapunov weight `h(s)`, and certified
pre-sieve `Q0_100` / rational `(C1, C2)` bounds from `cn_rows_all.json`.
"""

from __future__ import annotations

from decimal import Decimal, ROUND_FLOOR
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from .constants import E2, E_GAMMA, ODD_PRIMES
from .interval import D_FOUR, D_THREE, D_TWO, Iv, directed_context, exp_iv, ln_iv

HSTAR_SHA256 = "9db0e31b2ff56e623eb512ab7f058bc5e247a4ba0fbe6e9cfce04e0839ce4eb4"
CN_SHA256 = "b931b6798c2c9f35cba30ead4c54c668d544b79c9a1989aa705352d55d09b906"

# Certified closed-interval (H*) pre-sieve Q_0 for target eps* < 1/100
Q0_100: tuple[int, ...] = tuple(
    [p for p in ODD_PRIMES if p <= 102] + [107, 109, 137, 149, 191, 227]
)

# Exact rational C_1, C_2 bounds at eps = 1/100 from certified c_n tables
CERTIFIED_LINEAR_SIEVE_ROWS: dict[str, tuple[Fraction, Fraction]] = {
    "100:old": (
        Fraction(
            3457139049358105116966496278616105757354589,
            10000000000000000000000000000000000000000,
        ),
        Fraction(
            870914708555023798088925674508698778550311,
            2500000000000000000000000000000000000000,
        ),
    ),
    "100:new": (
        Fraction(
            1178153096032567943071672720479654754602799,
            5000000000000000000000000000000000000000,
        ),
        Fraction(
            1175456455562758182319093093263708021252459,
            5000000000000000000000000000000000000000,
        ),
    ),
}


def load_certified_linear_sieve_row(
    k_target: int = 100, rec_mode: str = "old"
) -> tuple[tuple[int, ...], Fraction, Fraction, Fraction]:
    """
    Return `(Q0_primes, eps_frac, C1_frac, C2_frac)` for `(k_target, rec_mode)`.
    Verifies presence, SHA-256 digests, and exact rational equality against
    `shared/data/linear_sieve_inputs/` at repository root.
    """
    row_key = f"{k_target}:{rec_mode}"
    if row_key not in CERTIFIED_LINEAR_SIEVE_ROWS:
        raise ValueError(f"Unsupported certified linear sieve row: {row_key}")
    c1_frac, c2_frac = CERTIFIED_LINEAR_SIEVE_ROWS[row_key]

    repo_root = Path(__file__).resolve().parents[3]
    inputs_dir = repo_root / "shared" / "data" / "linear_sieve_inputs"
    cn_path = inputs_dir / "cn_rows_all.json"
    hstar_path = inputs_dir / "logs" / "hstar.log"
    assert cn_path.is_file(), f"Missing linear-sieve provenance file: {cn_path}"
    assert hstar_path.is_file(), f"Missing linear-sieve provenance file: {hstar_path}"
    assert hashlib.sha256(hstar_path.read_bytes()).hexdigest() == HSTAR_SHA256
    cn_bytes = cn_path.read_bytes()
    assert hashlib.sha256(cn_bytes).hexdigest() == CN_SHA256
    row = json.loads(cn_bytes.decode("utf-8"))[f"{k_target}:{rec_mode}"]
    assert Fraction(int(row["C1_num"]), int(row["C1_den"])) == c1_frac
    assert Fraction(int(row["C2_num"]), int(row["C2_den"])) == c2_frac

    return Q0_100, Fraction(1, k_target), c1_frac, c2_frac


def _trap_step_error(coeff_str: str, h: Iv) -> Iv:
    return (Iv.from_str(coeff_str) * h * h * h) / Iv(12, 12)


def _i1_grid_build(n_panels: int = 2000) -> tuple[Iv, list[Iv]]:
    """Outward-rounded cumulative `I_F(u) = int_2^u ln(t-1)/t dt` on `[2, 4]`."""
    h = Iv.from_frac(Fraction(2, n_panels))
    err = _trap_step_error("1.3", h)
    grid = [Iv(0, 0)]
    acc = Iv(0, 0)
    g_prev = Iv(0, 0)
    for k in range(n_panels):
        u1 = Iv(2, 2) + Iv(k + 1, k + 1) * h
        g_cur = ln_iv(u1 - Iv(1, 1)) / u1
        trap = Iv.from_frac(Fraction(1, 2)) * (g_prev + g_cur) * h
        acc = Iv((acc + trap - err).lo, (acc + trap + err).hi)
        grid.append(acc)
        g_prev = g_cur
    return h, grid


_IF_N = 2000
_IF_H, _IF_GRID = _i1_grid_build(_IF_N)


def f_sieve_iv(s: Iv) -> Iv:
    """Outward-rounded monotone enclosure of Buchstab lower function `f(s)` on `s in [0, 6]`."""
    if s.hi <= D_TWO:
        return Iv(0, 0)
    if s.lo != s.hi:
        return Iv(f_sieve_iv(Iv(s.lo, s.lo)).lo, f_sieve_iv(Iv(s.hi, s.hi)).hi)
    if s.hi <= D_FOUR:
        return (Iv(2, 2) * E_GAMMA * ln_iv(s - Iv(1, 1))) / s
    if s.hi <= Decimal(6):
        a_out = Iv(3, 3)
        b_out = s - Iv(1, 1)
        n_out = 200
        h_out = (b_out - a_out) / Iv(n_out, n_out)
        err_i = _trap_step_error("1.3", h_out)
        err_phi = _trap_step_error("0.3", h_out)
        i_cur = Iv(0, 0)
        tot = Iv(0, 0)
        phi0 = Iv(0, 0)
        g0 = ln_iv(a_out - Iv(2, 2)) / (a_out - Iv(1, 1))
        for k in range(n_out):
            t1 = a_out + Iv(k + 1, k + 1) * h_out
            g1 = ln_iv(t1 - Iv(2, 2)) / (t1 - Iv(1, 1))
            trap_i = Iv.from_frac(Fraction(1, 2)) * (g0 + g1) * h_out
            i_next = Iv((i_cur + trap_i - err_i).lo, (i_cur + trap_i + err_i).hi)
            phi1 = i_next / t1
            trap_phi = Iv.from_frac(Fraction(1, 2)) * (phi0 + phi1) * h_out
            tot = Iv((tot + trap_phi - err_phi).lo, (tot + trap_phi + err_phi).hi)
            i_cur, phi0, g0 = i_next, phi1, g1
        return (Iv(2, 2) * E_GAMMA * (ln_iv(s - Iv(1, 1)) + tot)) / s
    raise ValueError(f"f_sieve_iv out of domain [0, 6]: {s}")


def f_lin_lb(s: Iv) -> Iv:
    """Monotone lower bound on `f(s)` for any `s >= 2` (clamped at `6` when `s > 6`)."""
    s_pt = s.lo
    if s_pt <= D_TWO:
        return Iv(0, 0)
    if s_pt <= Decimal(6):
        return f_sieve_iv(Iv(s_pt, s_pt))
    return f_sieve_iv(Iv(6, 6))


def F_sieve_iv(s: Iv) -> Iv:
    """Outward-rounded monotone enclosure of Buchstab upper function `F(s)` on `[1, 5]`."""
    if s.lo != s.hi:
        return Iv(F_sieve_iv(Iv(s.hi, s.hi)).lo, F_sieve_iv(Iv(s.lo, s.lo)).hi)
    if s.hi <= D_THREE:
        return (Iv(2, 2) * E_GAMMA) / s
    if s.hi <= Decimal(5):
        b = s - Iv(1, 1)
        with directed_context(ROUND_FLOOR, 40):
            idx = int(((b.lo - D_TWO) * Decimal(_IF_N) / D_TWO))
        idx = max(0, min(_IF_N - 1, idx))
        if_val = Iv(_IF_GRID[idx].lo, _IF_GRID[min(_IF_N, idx + 1)].hi)
        return (Iv(2, 2) * E_GAMMA * (Iv(1, 1) + if_val)) / s
    raise ValueError(f"F_sieve_iv out of domain [1, 5]: {s}")


def h_lin_ub(s: Iv) -> Iv:
    """Decreasing BJS error weight `h(s)` (`e^-2`, `e^-s`, or `3 e^-s / s`)."""
    s_pt = s.lo
    if s_pt <= D_TWO:
        return Iv(1, 1) / E2
    if s_pt <= D_THREE:
        return exp_iv(Iv(-s_pt, -s_pt))
    return (Iv(3, 3) / Iv(s_pt, s_pt)) * exp_iv(Iv(-s_pt, -s_pt))
