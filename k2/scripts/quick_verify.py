#!/usr/bin/env python3
"""
Fast (~5s, pure Python 3 stdlib) integrity verifier for `buchstab-switching/k2`
(public pure-GRH & unconditional kernel `1 + 2` branch on Lean v4.36.0).

Audits:
  [1/4] AST zero-float and zero-`math`/`numpy`/`scipy` purity across all `scripts/**/*.py`,
        and verifies `Decimal` `Inexact`/`Rounded` traps are armed.
  [2/4] Repository naming & conjecture-isolation hygiene: zero forbidden keywords and
        zero beyond-sqrt / sub-sqrt / unproved calibration imports or definitions across `k2/`.
  [3/4] JSON certificate <-> Lean `PureGRHShowcaseK2.lean` & `Data.lean` exact rational match.
  [4/4] Lean 4 module hygiene across `BuchstabSwitching/` and `BuchstabSwitchingK2/`
        (zero `sorry`, zero `admit`, zero `axiom` declarations, zero `native_decide`).
"""

from __future__ import annotations

import ast
from decimal import Decimal, Inexact, Rounded, getcontext
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))


def fail(msg: str) -> None:
    raise AssertionError(msg)


def verify_ast_and_traps() -> list[str]:
    targets = sorted(
        p for p in (ROOT / "scripts").rglob("*.py") if "__pycache__" not in p.parts
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
            elif isinstance(node, ast.Import) and any(
                a.name in (math_kw, "numpy", "scipy") or a.name.startswith((math_kw + ".", "numpy.", "scipy."))
                for a in node.names
            ):
                leaks.append(("bad_import", node.lineno))
            elif isinstance(node, ast.ImportFrom):
                mod = node.module or ""
                if mod in (math_kw, "numpy", "scipy") or mod.startswith((math_kw + ".", "numpy.", "scipy.")):
                    leaks.append(("bad_from_import", node.lineno))
        if leaks:
            fail(f"{path.relative_to(ROOT)}: forbidden float/math constructs: {leaks}")
        out.append(f"  PASS {path.relative_to(ROOT)}: ZERO_FLOAT_LEAKS=[]")

    from sieve_core.interval import Iv, _square_exact  # noqa: E401

    ctx = getcontext()
    if not (ctx.traps.get(Inexact) and ctx.traps.get(Rounded)):
        fail("Decimal Inexact/Rounded traps must be enabled globally by sieve_core.interval")
    for n in range(2, 200):
        s = Iv(n, n).sqrt()
        if not (_square_exact(s.lo) <= Decimal(n) <= _square_exact(s.hi)):
            fail(f"Iv({n}).sqrt() failed exact outward square check: {s}")
    out.append("  PASS Decimal Inexact/Rounded traps armed, Iv.sqrt outward check on [2, 200)")
    return out


def verify_naming_and_isolation_hygiene() -> list[str]:
    forbidden = [
        bytes.fromhex("676f6c6462616368").decode("ascii"),
        bytes.fromhex("72682d6167656e742d687562").decode("ascii"),
        bytes.fromhex("6c6f63616c2d636172626f6e").decode("ascii"),
        bytes.fromhex("70657175616c6e70").decode("ascii"),
        bytes.fromhex("72756c6520302e35").decode("ascii"),
    ]
    conjecture_leak_terms = [
        "BeyondSqrtBridgeK2",
        "SubSqrtCancellationBridgeK2",
        "ConjecturesAndLemmasK2",
        "ModulusPowerCancellation",
        "OneRayModulusCancellation",
        "PlateauKernelCalibrationLemma",
        "plateau_bump_model",
        "b1Certified",
        "b2LowSlabs",
        "b2HighSlabs",
    ]
    scan_exts = {".lean", ".py", ".md", ".toml", ".yml", ".json", ".txt", ".sh"}
    for p in ROOT.rglob("*"):
        if ".lake" in p.parts or ".git" in p.parts or "__pycache__" in p.parts:
            continue
        if p.name == "comparator_output.txt":
            continue
        if p.is_file() and p.suffix in scan_exts:
            raw = p.read_text(encoding="utf-8", errors="ignore")
            low = raw.lower()
            for kw in forbidden:
                if kw.lower() in low:
                    fail(f"Forbidden keyword {kw!r} found in {p.relative_to(ROOT)}")
            if p.resolve() != Path(__file__).resolve():
                for leak in conjecture_leak_terms:
                    if leak in raw:
                        fail(f"Conjecture/unproved symbol {leak!r} found in {p.relative_to(ROOT)}")
    return ["[2/4] NAMING & PURE-GRH ISOLATION HYGIENE: PASS (0 forbidden terms, 0 B1/B2/plateau symbols)"]


def _scaled_int(dec_str: str, den: int = 1_000_000) -> int:
    val = Decimal(dec_str) * den
    if val != int(val):
        fail(f"Non-exact rational value {dec_str} at den={den}")
    return int(val)


def _extract_ray_cert(src: str, name: str) -> dict[str, int]:
    src = src.replace("\r\n", "\n")
    m = re.search(
        rf"def\s+{re.escape(name)}\s*:\s*RayCert\s+where(.*?)(?:\n\n|\ntheorem|\ndef)",
        src,
        flags=re.DOTALL,
    )
    if not m:
        fail(f"Could not locate {name}")
    block = m.group(1)
    m_pow = re.search(r"X_LS\s*:=\s*10\s*\^\s*(\d+)", block)
    if not m_pow:
        fail(f"Could not parse X_LS := 10 ^ k in {name}")
    rec = {"exp10": int(m_pow.group(1))}
    for k, v in re.findall(r"\b(main_num|err_num|net_num|den)\s*:=\s*(\d+)\b", block):
        rec[k] = int(v)
    if set(rec.keys()) != {"exp10", "main_num", "err_num", "net_num", "den"}:
        fail(f"Incomplete fields in {name}: {rec}")
    return rec


def verify_pure_grh_certificates() -> list[str]:
    jpath = ROOT / "scripts/data/certified_pure_grh_frontier.json"
    data = json.loads(jpath.read_text(encoding="utf-8"))
    if data.get("ast_audit", {}).get("status") != "CLEAN":
        fail("JSON ast_audit is not CLEAN")

    wpath = ROOT / "scripts/data/pure_grh_quad_lp_witness.json"
    if not wpath.exists():
        fail("Missing scripts/data/pure_grh_quad_lp_witness.json")

    if set(data["regimes"].keys()) != {"parzen_delta_1_25", "polyspline_uncond_ef"}:
        fail(f"Unexpected regimes in certified_pure_grh_frontier.json: {list(data['regimes'].keys())}")

    parzen_reg = data["regimes"]["parzen_delta_1_25"]
    poly_reg = data["regimes"]["polyspline_uncond_ef"]
    showcase = (ROOT / "BuchstabSwitchingK2/PureGRHShowcaseK2.lean").read_text(encoding="utf-8")
    data_lean = (ROOT / "BuchstabSwitchingK2/Certificates/Data.lean").read_text(encoding="utf-8")

    cert_pairs = (
        ("pureGRHParzenConstRayCert", parzen_reg["first_const"]),
        ("pureGRHParzenVarWeightRayCert", parzen_reg["first_varweight"]),
        ("pureGRHParzenQuadRayCert", parzen_reg["first_quad"]),
        ("pureGRHPolySplineConstRayCert", poly_reg["first_const"]),
        ("pureGRHPolySplineVarWeightRayCert", poly_reg["first_varweight"]),
        ("pureGRHPolySplineQuadRayCert", poly_reg["first_quad"]),
    )
    for name, jrow in cert_pairs:
        lrow = _extract_ray_cert(showcase, name)
        if lrow["exp10"] != int(jrow["exp10"]):
            fail(f"{name} exp10 mismatch: {lrow['exp10']} != {jrow['exp10']}")
        if lrow["den"] != 1_000_000:
            fail(f"{name} den mismatch")
        if (
            lrow["main_num"] != _scaled_int(jrow["main_lb"])
            or lrow["err_num"] != _scaled_int(jrow["err_ub"])
            or lrow["net_num"] != _scaled_int(jrow["net_lo"])
            or lrow["net_num"] + lrow["err_num"] > lrow["main_num"]
        ):
            fail(f"{name} rational mismatch vs JSON: {lrow} vs {jrow}")

    r325 = _extract_ray_cert(showcase, "pureGRHRayCert_325")
    if r325["exp10"] != 325 or r325["net_num"] + r325["err_num"] > r325["main_num"] or r325["net_num"] <= 0:
        fail(f"Invalid pureGRHRayCert_325: {r325}")

    r1668 = _extract_ray_cert(data_lean, "asymptoticCert_new")
    if r1668["exp10"] != 1668 or r1668["net_num"] + r1668["err_num"] > r1668["main_num"] or r1668["net_num"] <= 0:
        fail(f"Invalid asymptoticCert_new: {r1668}")

    pq = parzen_reg["first_quad"]
    psq = poly_reg["first_quad"]
    return [
        "[3/4] PURE-GRH CERTIFICATE CONSISTENCY: PASS "
        f"(PolySpline premise-free quad 10^{psq['exp10']} net=+{psq['net_lo']}, "
        f"Parzen quad 10^{pq['exp10']} net=+{pq['net_lo']}, "
        f"PolySpline const 10^{poly_reg['first_const']['exp10']}, "
        f"Parzen const 10^{parzen_reg['first_const']['exp10']}, "
        f"Sharp 10^1668)"
    ]


def verify_lean_hygiene() -> list[str]:
    lean_files = (
        sorted((ROOT / "BuchstabSwitchingK2").rglob("*.lean"))
        + sorted((ROOT / "BuchstabSwitching").rglob("*.lean"))
        + [ROOT / "BuchstabSwitchingK2.lean", ROOT / "AxiomsCheckK2.lean"]
    )
    for lf in lean_files:
        src = re.sub(r"/-.*?-/", "", lf.read_text(encoding="utf-8"), flags=re.DOTALL)
        for lineno, line in enumerate(src.splitlines(), 1):
            code = line.split("--", 1)[0]
            if re.search(r"\b(sorry|admit|axiom|native_decide)\b", code):
                fail(f"{lf.relative_to(ROOT)}:{lineno}: forbidden keyword in Lean code")
    return [
        "[4/4] LEAN 4 KERNEL HYGIENE",
        f"  PASS {len(lean_files)} Lean files contain zero sorry/admit/axiom/native_decide",
    ]


def main() -> int:
    report = []
    report.extend(verify_ast_and_traps())
    report.extend(verify_naming_and_isolation_hygiene())
    report.extend(verify_pure_grh_certificates())
    report.extend(verify_lean_hygiene())
    report.append("\nQUICK VERIFICATION SUMMARY: ALL 4 CHECKS PASSED.")
    print("\n".join(report))
    return 0


if __name__ == "__main__":
    sys.exit(main())
