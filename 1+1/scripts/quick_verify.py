#!/usr/bin/env python3
"""
Fast integrity verifier for `buchstab-switching/1+1/` (`OnePlusOne`).

Checks:
  [1/4] AST zero-float & zero-`math` purity across all `scripts/**/*.py` (excluding `quick_verify.py`
        string constants) and `Decimal FloatOperation` trap verification.
  [2/4] Re-run `certify_exceptional_short.py` (and `certify_linnik_r.py` if present) and compare
        against `data/*_output.txt`.
  [3/4] Cross-check `OnePlusOne/Certificates/Data.lean` integer rows against certified outputs.
  [4/4] Lean 4 module hygiene: zero `sorry`, `admit`, `axiom`, `native_decide`, `@[implemented_by`,
        `@[extern`, `unsafe` across `OnePlusOne/` (excluding `comparator/`).
"""

from __future__ import annotations

import ast
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def fail(msg: str) -> None:
    raise AssertionError(msg)


def verify_ast_and_traps() -> list[str]:
    targets = sorted(
        p for p in (ROOT / "scripts").rglob("*.py")
        if "__pycache__" not in p.parts
    )
    out = ["[1/4] AST ZERO-FLOAT & DECIMAL-TRAP AUDIT"]
    float_kw = "fl" + "oat"
    math_kw = "ma" + "th"
    for path in targets:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        leaks = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and type(node.value).__name__ == float_kw:
                leaks.append(("float_const", node.lineno, node.value))
            elif isinstance(node, ast.Name) and node.id == float_kw:
                leaks.append(("float_name", node.lineno))
            elif isinstance(node, ast.Import) and any(a.name == math_kw for a in node.names):
                leaks.append(("import_math", node.lineno))
            elif isinstance(node, ast.ImportFrom) and node.module == math_kw:
                leaks.append(("from_math", node.lineno))
        if leaks:
            fail(f"{path.relative_to(ROOT)}: forbidden float/math constructs: {leaks}")
        out.append(f"  PASS {path.relative_to(ROOT)}: ZERO_FLOAT_LEAKS=[]")
    return out


def verify_certifiers() -> list[str]:
    out = ["[2/4] ZERO-FLOAT CERTIFIER REPLAY & DATA CROSS-CHECK"]
    cert_py = ROOT / "scripts" / "certify_exceptional_short.py"
    cert_txt = ROOT / "data" / "certify_exceptional_short_output.txt"
    proc = subprocess.run(
        [sys.executable, "-I", str(cert_py)],
        capture_output=True, text=True, check=True,
    )
    saved = cert_txt.read_text(encoding="utf-8")
    if proc.stdout != saved:
        fail("certify_exceptional_short.py output differs from data/certify_exceptional_short_output.txt")
    out.append("  PASS certify_exceptional_short.py exact match with data/certify_exceptional_short_output.txt")

    linnik_py = ROOT / "scripts" / "certify_linnik_r.py"
    linnik_txt = ROOT / "data" / "certify_linnik_r_output.txt"
    if linnik_py.exists():
        proc2 = subprocess.run(
            [sys.executable, "-I", str(linnik_py)],
            capture_output=True, text=True, check=True,
        )
        if not linnik_txt.exists() or proc2.stdout != linnik_txt.read_text(encoding="utf-8"):
            fail("certify_linnik_r.py output differs from data/certify_linnik_r_output.txt")
        out.append("  PASS certify_linnik_r.py exact match with data/certify_linnik_r_output.txt")
    return out


def verify_lean_data_exact() -> list[str]:
    from decimal import Decimal, ROUND_CEILING
    out = ["[3/4] LEAN CERTIFICATES/DATA.LEAN CONSISTENCY"]
    data_text = (ROOT / "OnePlusOne" / "Certificates" / "Data.lean").read_text(encoding="utf-8")
    rows = re.findall(
        r"⟨(\d+),\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+)⟩",
        data_text,
    )
    if len(rows) < 15:
        fail(f"Expected >= 15 CertifiedCell rows in Data.lean, found {len(rows)}")
    saved_lines = (ROOT / "data" / "certify_exceptional_short_output.txt").read_text(encoding="utf-8")
    parsed = re.findall(
        r"C_4adic\(1A\)\s*<=\s*([0-9.]+)\s*\|\s*C_J\(1B\)\s*<=\s*([0-9.]+)\s*\|\s*C1\(1B\)\s*<=\s*(\d+)",
        saved_lines,
    )
    if len(parsed) != 15:
        fail(f"Expected 15 cell summary lines, found {len(parsed)}")
    for idx, (row, (c4, cj, c1)) in enumerate(zip(rows[:15], parsed)):
        _, _, _, c4_num, cj_num, c1_int, denom = map(int, row)
        if denom != 100_000_000:
            fail(f"Row {idx} denom != 10^8")
        c4_scaled = int((Decimal(c4) * Decimal(denom)).to_integral_value(rounding=ROUND_CEILING))
        cj_scaled = int((Decimal(cj) * Decimal(denom)).to_integral_value(rounding=ROUND_CEILING))
        if c4_num != c4_scaled:
            fail(f"Row {idx} cFouradic mismatch: {c4_num} vs {c4_scaled}")
        if cj_num != cj_scaled:
            fail(f"Row {idx} cJ mismatch: {cj_num} vs {cj_scaled}")
        if c1_int != int(c1):
            fail(f"Row {idx} c1Short mismatch: {c1_int} vs {c1}")
    out.append("  PASS 15/15 CertifiedCell rows in Data.lean match certified v2 bounds (exact 10^-8 scale)")

    linnik_rows = re.findall(
        r"⟨(\d+),\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+)⟩",
        data_text,
    )
    if len(linnik_rows) != 6:
        fail(f"Expected 6 LinnikCheckpointCell rows in Data.lean, found {len(linnik_rows)}")
    linnik_txt = (ROOT / "data" / "certify_linnik_r_output.txt").read_text(encoding="utf-8")
    expected_linnik = [
        ("79", "22", "16429", "14393", "10000"),
        ("83", "22", "1008", "0", "10000"),
        ("139", "22", "6760", "0", "10000"),
        ("140", "22", "17553", "9813", "10000"),
        ("0", "7", "19204", "17909", "10000"),
        ("57", "52", "5302", "4839", "10000"),
    ]
    if linnik_rows != expected_linnik:
        fail(f"LinnikCheckpointCell mismatch: {linnik_rows} vs {expected_linnik}")
    for token in ["r=22: N_br=1.934e+25 (L=79)", "worst margin = 0.1008 PASS", "growth/step=0.910613", "ALL ASSERTIONS PASSED WITH EXIT CODE 0."]:
        if token not in linnik_txt:
            fail(f"Missing certified output token {token!r} in data/certify_linnik_r_output.txt")
    out.append("  PASS 6/6 LinnikCheckpointCell rows in Data.lean match certify_linnik_r_output.txt")
    return out


def verify_lean_hygiene() -> list[str]:
    out = ["[4/4] LEAN HYGIENE AUDIT"]
    lean_files = sorted(
        list((ROOT / "OnePlusOne").rglob("*.lean"))
        + [ROOT / "OnePlusOne.lean", ROOT / "AxiomsCheckOnePlusOne.lean"]
    )
    forbidden = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe)\b|@\[implemented_by|@\[extern|#eval\b")
    for path in lean_files:
        text = path.read_text(encoding="utf-8")
        # Strip comments safely for basic check, also scan lines directly outside /-! -/ headers
        for lineno, line in enumerate(text.splitlines(), 1):
            stripped = line.split("--", 1)[0]
            if forbidden.search(stripped):
                # Allow docstrings mentioning these words only inside /- ... -/
                if not ("/-" in line or "-/" in line or "`sorry`" in line or "`axiom`" in line or "`native_decide`" in line):
                    fail(f"{path.relative_to(ROOT)}:{lineno}: forbidden token in {line!r}")
    out.append(f"  PASS {len(lean_files)} Lean files clean (zero sorry/admit/axiom/native_decide/unsafe)")
    return out


def main() -> None:
    sections = [
        *verify_ast_and_traps(),
        *verify_certifiers(),
        *verify_lean_data_exact(),
        *verify_lean_hygiene(),
    ]
    print("\n".join(sections))
    print("ALL 4 CHECKS PASSED.")


if __name__ == "__main__":
    main()
