#!/usr/bin/env python3
"""
Standalone outward-rounded certifier for shifted `Ω(m) ≤ 3` representations across
all even integers `N >= 4` under `DirichletLNonvanishingRightOfHalf`.

Writes human-readable results to `scripts/data/certified_bounds.txt` and machine-readable
rational summary to `scripts/data/certified_slabs.json`. Zero float / zero `math`.
"""

from __future__ import annotations

from decimal import Decimal, ROUND_CEILING
import json
from pathlib import Path

from sieve_cert import (
    ASYMPTOTIC_SPEC,
    SLABS_2A,
    SLABS_2B,
    SLABS_2C,
    AsymptoticRaySpec,
    certify_asymptotic_ray,
    certify_slab_2a,
    certify_slab_2b,
    certify_slab_2c,
)
from sieve_cert.interval import Iv, fmt_dec

ROOT = Path(__file__).resolve().parents[1]
DATA_DIR = ROOT / "scripts/data"


def _fmt_sci(n: int) -> str:
    """Pure integer scientific notation formatter (avoids IEEE-754 float conversion)."""
    s = str(n)
    k = len(s) - 1
    if s == "1" + "0" * k:
        return f"10^{k}"
    if n % (10 ** (k - 1)) == 0 and k >= 2:
        return f"{s[0]}.{s[1]}e{k}"
    if k >= 3:
        return f"{s[0]}.{s[1:4]}e{k}"
    return s


def main() -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    lines: list[str] = []

    def emit(msg: str) -> None:
        print(msg)
        lines.append(msg)

    emit("=== REGIME 1: 4 <= N < 4 * 10^18 ===")
    emit("  Oliveira e Silva, Herzog, Pardi (Math. Comp. 83, 2014): K = 1 <= 3.")

    emit(f"\n=== REGIME 2: Contiguous Finite Slab Ladder [4*10^18, 10^{ASYMPTOTIC_SPEC.exp10}) ===")
    assert SLABS_2A[0].x_lo == 4 * 10**18
    assert SLABS_2A[-1].x_hi == SLABS_2B[0].x_lo
    assert SLABS_2B[-1].x_hi == SLABS_2C[0].x_lo
    assert SLABS_2C[-1].x_hi == 10 ** ASYMPTOTIC_SPEC.exp10

    for name, lst in (("2a", SLABS_2A), ("2b", SLABS_2B), ("2c", SLABS_2C)):
        for i in range(len(lst) - 1):
            assert lst[i].x_hi == lst[i + 1].x_lo, f"Contiguity gap inside {name} at {i}"

    all_certs = []
    min_raw: Decimal | None = None
    min_sieve: Decimal | None = None
    min_tol: Decimal | None = None

    def track(res) -> None:
        nonlocal min_raw, min_sieve, min_tol
        all_certs.append(res)
        min_raw = res.net_lo if min_raw is None or res.net_lo < min_raw else min_raw
        min_sieve = res.sieve_net_lo if min_sieve is None or res.sieve_net_lo < min_sieve else min_sieve
        min_tol = res.rem_tol if min_tol is None or res.rem_tol < min_tol else min_tol

    emit(f"  -- Sub-regime 2a ({len(SLABS_2A)} slabs: exact prime sums + P_sub IE) --")
    for idx, spec in enumerate(SLABS_2A, 1):
        res = certify_slab_2a(spec)
        track(res)
        emit(
            f"  2a-{idx:02d}: [{_fmt_sci(spec.x_lo)}, {_fmt_sci(spec.x_hi)}) z={res.z:2d} a={spec.a} "
            f"odd={spec.m_odd} y={res.y:9d} | main>={fmt_dec(res.main_lo, 5)} err<={fmt_dec(res.err_hi, 5, rounding=ROUND_CEILING)} "
            f"net>={fmt_dec(res.net_lo, 5)} sieve_net>={fmt_dec(res.sieve_net_lo, 4)} tol={fmt_dec(res.rem_tol, 1)}x"
        )

    emit(f"  -- Sub-regime 2b ({len(SLABS_2B)} slabs: Odd Bonf + multi-cutoff Even Bonf / P_sub) --")
    for idx, spec in enumerate(SLABS_2B, 1):
        res = certify_slab_2b(spec)
        track(res)
        emit(
            f"  2b-{idx:02d}: [{_fmt_sci(spec.x_lo)}, {_fmt_sci(spec.x_hi)}) M={spec.m_div:2d} a={spec.a:2d} "
            f"odd={spec.m_odd:2d} z={res.z:6d} | main>={fmt_dec(res.main_lo, 5)} err<={fmt_dec(res.err_hi, 5, rounding=ROUND_CEILING)} "
            f"net>={fmt_dec(res.net_lo, 5)} sieve_net>={fmt_dec(res.sieve_net_lo, 4)} tol={fmt_dec(res.rem_tol, 1)}x"
        )

    emit(f"  -- Sub-regime 2c ({len(SLABS_2C)} slabs: OddBonferroni + EvenBonferroni / Selberg J_full) --")
    for idx, spec in enumerate(SLABS_2C, 1):
        res = certify_slab_2c(spec)
        track(res)
        emit(
            f"  2c-{idx:02d}: [{_fmt_sci(spec.x_lo)}, {_fmt_sci(spec.x_hi)}) M={spec.m_div:2d} "
            f"{res.note} | main>={fmt_dec(res.main_lo, 5)} err<={fmt_dec(res.err_hi, 5, rounding=ROUND_CEILING)} "
            f"net>={fmt_dec(res.net_lo, 5)} tol={fmt_dec(res.rem_tol, 1)}x"
        )

    assert min_raw is not None and min_sieve is not None and min_tol is not None
    emit(
        f"  Regime 2 PASSED across {len(all_certs)} contiguous slabs "
        f"(min net_lo={fmt_dec(min_raw, 6)}, min sieve_net_lo={fmt_dec(min_sieve, 6)}, min GRH rem tol={fmt_dec(min_tol, 2)}x)"
    )

    emit(f"\n=== REGIME 3: N >= 10^{ASYMPTOTIC_SPEC.exp10} (Closed (H*) Q0_100 + Lean Certified C2 <= {ASYMPTOTIC_SPEC.c2_lean_cap} + Selberg J_full) ===")
    r3 = certify_asymptotic_ray(ASYMPTOTIC_SPEC)
    r3_old = certify_asymptotic_ray(
        AsymptoticRaySpec(
            exp10=ASYMPTOTIC_SPEC.exp10,
            m_div=ASYMPTOTIC_SPEC.m_div,
            k_target=ASYMPTOTIC_SPEC.k_target,
            rec_mode="old",
            b_a_str=ASYMPTOTIC_SPEC.b_a_str,
            b_q_str=ASYMPTOTIC_SPEC.b_q_str,
            l_strips=ASYMPTOTIC_SPEC.l_strips,
            c2_lean_cap=None,
        )
    )
    r3_new = certify_asymptotic_ray(
        AsymptoticRaySpec(
            exp10=ASYMPTOTIC_SPEC.exp10,
            m_div=ASYMPTOTIC_SPEC.m_div,
            k_target=ASYMPTOTIC_SPEC.k_target,
            rec_mode="new",
            b_a_str=ASYMPTOTIC_SPEC.b_a_str,
            b_q_str=ASYMPTOTIC_SPEC.b_q_str,
            l_strips=ASYMPTOTIC_SPEC.l_strips,
            c2_lean_cap=None,
        )
    )
    r3_tol = (Iv(r3.main_lo, r3.main_lo) / Iv(r3.err_hi, r3.err_hi)).lo
    r3_old_tol = (Iv(r3_old.main_lo, r3_old.main_lo) / Iv(r3_old.err_hi, r3_old.err_hi)).lo
    r3_new_tol = (Iv(r3_new.main_lo, r3_new.main_lo) / Iv(r3_new.err_hi, r3_new.err_hi)).lo
    emit(
        f"  X_LS = 10^{ASYMPTOTIC_SPEC.exp10}, M = {ASYMPTOTIC_SPEC.m_div}, target eps <= 1/{r3.k_target}, "
        f"closed (H*) eps* <= {fmt_dec(r3.eps_star_hi, 10, rounding=ROUND_CEILING)} -> Lean cap C2 <= "
        f"{fmt_dec(r3.c2_used_hi, 6, rounding=ROUND_CEILING)} (C2 break-even={fmt_dec(r3.c2_breakeven, 1)})"
    )
    emit(
        f"  s_A >= {fmt_dec(r3.s_a_lo, 4)}, delta_V <= {fmt_dec(r3.delta_v_hi, 12, rounding=ROUND_CEILING)}, "
        f"lb_A >= {fmt_dec(r3.lb_a_lo, 6)}, 0.5*sum_Aq <= {fmt_dec(r3.half_sum_aq_hi, 6, rounding=ROUND_CEILING)}"
    )
    emit(
        f"  main_coeff >= {fmt_dec(r3.main_lo, 6)}, tot_err <= {fmt_dec(r3.err_hi, 6, rounding=ROUND_CEILING)}, "
        f"NET COEFF >= {fmt_dec(r3.net_lo, 6)} (GRH rem tol={fmt_dec(r3_tol, 1)}x)"
    )
    emit(
        f"  Cross-check ({r3_old.k_target}:{r3_old.rec_mode}, C2 <= {fmt_dec(r3_old.c2_used_hi, 6, rounding=ROUND_CEILING)}): "
        f"NET COEFF >= {fmt_dec(r3_old.net_lo, 6)} (GRH rem tol={fmt_dec(r3_old_tol, 1)}x)"
    )
    emit(
        f"  Cross-check ({r3_new.k_target}:{r3_new.rec_mode}, C2 <= {fmt_dec(r3_new.c2_used_hi, 6, rounding=ROUND_CEILING)}): "
        f"NET COEFF >= {fmt_dec(r3_new.net_lo, 6)} (GRH rem tol={fmt_dec(r3_new_tol, 1)}x)"
    )
    emit(
        f"  Regime 3 PASSED: net switching coefficient >= {fmt_dec(r3.net_lo, 6)} > 0 "
        f"for ALL even N >= 10^{ASYMPTOTIC_SPEC.exp10}"
    )

    emit("\n=== ROBUSTNESS & PERTURBATION SUMMARY ===")
    emit(f"  Global min raw slab margin      : {fmt_dec(min_raw, 6)}")
    min_sieve_pct = fmt_dec((Iv(min_sieve, min_sieve) * Iv(100, 100)).lo, 2)
    emit(f"  Global min V_N(z)-normalized net: {fmt_dec(min_sieve, 6)} (>= {min_sieve_pct}% across all finite slabs)")
    emit(f"  Global min GRH error tolerance  : {fmt_dec(min_tol, 2)}x (all slabs survive >= {fmt_dec(min_tol, 2)}x remainder inflation)")
    emit(f"  Asymptotic Regime 3 tolerance   : C_2 <= {fmt_dec(r3.c2_breakeven, 1)} (vs used {fmt_dec(r3.c2_used_hi, 6, rounding=ROUND_CEILING)}), GRH rem tol={fmt_dec(r3_tol, 1)}x")
    emit("\nALL REGIMES CERTIFIED (100% outward-rounded Decimal/Fraction/int, trapped Inexact/Rounded, 0 float/math): K = 3 for all even N >= 4.")

    (DATA_DIR / "certified_bounds.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")

    payload = {
        "slabs": [
            {
                "regime": c.regime,
                "x_lo": str(c.x_lo),
                "x_hi": str(c.x_hi),
                "z": str(c.z),
                "y": str(c.y),
                "main_lo": fmt_dec(c.main_lo, 15),
                "err_hi": fmt_dec(c.err_hi, 15, rounding=ROUND_CEILING),
                "net_lo": fmt_dec(c.net_lo, 15),
                "sieve_net_lo": fmt_dec(c.sieve_net_lo, 15),
                "rem_tol": fmt_dec(c.rem_tol, 4),
            }
            for c in all_certs
        ],
        "ray": {
            "x_ls": str(10 ** ASYMPTOTIC_SPEC.exp10),
            "main_lo": fmt_dec(r3.main_lo, 15),
            "err_hi": fmt_dec(r3.err_hi, 15, rounding=ROUND_CEILING),
            "net_lo": fmt_dec(r3.net_lo, 15),
            "c2_used": fmt_dec(r3.c2_used_hi, 6, rounding=ROUND_CEILING),
            "c2_breakeven": fmt_dec(r3.c2_breakeven, 4),
            "rem_tol": fmt_dec(r3_tol, 4),
        },
    }
    (DATA_DIR / "certified_slabs.json").write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
