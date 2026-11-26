"""
Generate `BuchstabSwitching/Certificates/Data.lean` from `scripts/data/certified_slabs.json`.

Writes exact integers `X_lo, X_hi, z, y` and exact natural-number rational numerators
`main_num, err_num, net_num, den` (`den = 10^10`) satisfying `net_num + err_num <= main_num`.
"""

from __future__ import annotations

from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
JSON_PATH = ROOT / "scripts/data/certified_slabs.json"
OUT_LEAN = ROOT / "BuchstabSwitching/Certificates/Data.lean"

DENOM = 10_000_000_000


def dec_to_rat_floor(d_str: str) -> tuple[int, int]:
    val = Decimal(d_str)
    num = int((val * DENOM).to_integral_value(rounding=ROUND_FLOOR))
    return num, DENOM


def dec_to_rat_ceil(d_str: str) -> tuple[int, int]:
    val = Decimal(d_str)
    num = int((val * DENOM).to_integral_value(rounding=ROUND_CEILING))
    return num, DENOM


def main() -> None:
    payload = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    slabs = payload["slabs"]
    ray = payload["ray"]

    lines = [
        "import BuchstabSwitching.Certificates.Types",
        "",
        "/-!",
        "# Machine-Generated Rational Slab & Ray Certificates",
        "",
        "Auto-generated from `scripts/data/certified_slabs.json` by",
        "`scripts/generate_lean_data.py`. Do not edit by hand.",
        "-/",
        "",
        "namespace BuchstabSwitching",
        "",
        "/-- Contiguous certified slab chain `[4 * 10^18, asymptoticCert.X_LS)`. -/",
        "def allSlabs : List SlabCert := [",
    ]

    for idx, s in enumerate(slabs):
        m_n, m_d = dec_to_rat_floor(s["main_lo"])
        e_n, _ = dec_to_rat_ceil(s["err_hi"])
        net_num = m_n - e_n
        assert net_num > 0, f"Slab {idx + 1} non-positive rational net numerator: {net_num}"
        comma = "," if idx + 1 < len(slabs) else ""
        lines.extend(
            [
                f"  {{ X_lo := {s['x_lo']}, X_hi := {s['x_hi']},",
                f"    z := {s['z']}, y := {s['y']},",
                f"    main_num := {m_n}, err_num := {e_n},",
                f"    net_num := {net_num}, den := {m_d} }}{comma}",
            ]
        )

    rm_n, rm_d = dec_to_rat_floor(ray["main_lo"])
    re_n, _ = dec_to_rat_ceil(ray["err_hi"])
    rnet_n = rm_n - re_n
    assert rnet_n > 0, f"Ray non-positive rational net numerator: {rnet_n}"

    lines.extend(
        [
            "]",
            "",
            "/-- Uniform certified asymptotic ray `[X_LS, ∞)`. -/",
            "def asymptoticCert : RayCert :=",
            f"  {{ X_LS := {ray['x_ls']},",
            f"    main_num := {rm_n},",
            f"    err_num := {re_n},",
            f"    net_num := {rnet_n},",
            f"    den := {rm_d} }}",
            "",
            "end BuchstabSwitching",
            "",
        ]
    )

    OUT_LEAN.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {len(slabs)} slabs + 1 ray certificate to {OUT_LEAN}")


if __name__ == "__main__":
    main()
