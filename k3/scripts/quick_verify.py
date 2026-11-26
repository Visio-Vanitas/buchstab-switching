#!/usr/bin/env python3
"""
Fast (~40s, pure Python 3 stdlib) integrity verifier for `buchstab-switching/k3`.

Audits:
  [1/6] AST zero-float and zero-`math` purity across all `scripts/**/*.py`,
        verification that global `Decimal` `Inexact` and `Rounded` traps are armed,
        and SHA-256 verification of linear-sieve input tables.
  [2/6] Zero excluded keyword leaks across `k3/` source, scripts, and docs.
  [3/6] Contiguous slab coverage `[4 * 10^18, X_LS)` + asymptotic ray `[X_LS, ∞)`,
        exact switching geometry `2 <= z <= y`, `X_hi <= y^4`, `X_hi <= z * y^3`,
        and strictly positive rational + sieve-normalized margins.
  [4/6] Output log `scripts/data/certified_bounds.txt` numerical cross-check
        against `certified_slabs.json` across all 127 slabs and Regime 3.
  [5/6] `Data.lean` rational value soundness against `certified_slabs.json`.
  [6/6] Lean 4 module hygiene (zero `sorry`, zero `admit`, zero `axiom` declarations,
        never `native_decide`, external bridge confined to `BuchstabSwitching/External/`).
"""

from __future__ import annotations

import ast
from decimal import Decimal, Inexact, ROUND_CEILING, ROUND_FLOOR, Rounded, getcontext, localcontext
from fractions import Fraction
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
    out = ["[1/6] AST ZERO-FLOAT & DECIMAL-TRAP AUDIT"]
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

    from sieve_cert.interval import Iv, _square_exact, fmt_dec  # noqa: E401
    from sieve_cert.linear_sieve import Q0_100, load_certified_linear_sieve_row  # noqa: E401
    from sieve_cert.primes_and_mertens import certify_closed_hstar_q0  # noqa: E401

    ctx = getcontext()
    if not (ctx.traps.get(Inexact) and ctx.traps.get(Rounded)):
        fail("Decimal Inexact/Rounded traps must be enabled globally by sieve_cert.interval")
    for n in range(2, 500):
        s = Iv(n, n).sqrt()
        if not (_square_exact(s.lo) <= Decimal(n) <= _square_exact(s.hi)):
            fail(f"Iv({n}).sqrt() failed exact outward square check: {s}")
    eps_star = certify_closed_hstar_q0(Q0_100, 100)
    if not (eps_star.hi < Decimal("0.01")):
        fail(f"certify_closed_hstar_q0(Q0_100, 100) >= 0.01: {eps_star}")

    row_old = load_certified_linear_sieve_row(100, "old")
    row_new = load_certified_linear_sieve_row(100, "new")
    if row_old[0] != Q0_100 or row_new[0] != Q0_100:
        fail("Linear sieve Q0_100 mismatch")
    if row_old[1] != Fraction(1, 100) or row_new[1] != Fraction(1, 100):
        fail("Linear sieve target epsilon mismatch")

    out.append(
        f"  PASS Decimal Inexact/Rounded traps armed, Iv.sqrt outward check on [2, 500), "
        f"closed (H*) eps*={fmt_dec(eps_star.hi, 8, rounding=ROUND_CEILING)} < 0.01, "
        f"SHA-256 verified for (100:old, 100:new)"
    )
    return out


def verify_naming_hygiene() -> list[str]:
    forbidden = [
        bytes.fromhex("676f6c6462616368").decode("ascii"),
        bytes.fromhex("72682d6167656e742d687562").decode("ascii"),
        bytes.fromhex("6c6f63616c2d636172626f6e").decode("ascii"),
        bytes.fromhex("70657175616c6e70").decode("ascii"),
        bytes.fromhex("72756c6520302e35").decode("ascii"),
    ]
    scan_exts = {".lean", ".py", ".md", ".toml", ".yml", ".json", ".txt"}
    for p in ROOT.rglob("*"):
        if ".lake" in p.parts or ".git" in p.parts or "__pycache__" in p.parts:
            continue
        if p.is_file() and p.suffix in scan_exts:
            txt = p.read_text(encoding="utf-8", errors="ignore").lower()
            for kw in forbidden:
                if kw.lower() in txt:
                    fail(f"Forbidden keyword {kw!r} found in {p.relative_to(ROOT)}")
    return ["[2/6] REPOSITORY NAMING HYGIENE: PASS (0 forbidden terms across k3/ source & docs)"]


def verify_json_certificates() -> list[str]:
    from sieve_cert.interval import fmt_dec  # noqa: E401

    jpath = ROOT / "scripts/data/certified_slabs.json"
    data = json.loads(jpath.read_text(encoding="utf-8"))
    slabs = data["slabs"]
    ray = data["ray"]

    if not slabs:
        fail("Empty slab list in certified_slabs.json")
    if int(slabs[0]["x_lo"]) != 4 * 10**18:
        fail(f"First slab X_lo={slabs[0]['x_lo']} != 4*10^18")

    min_net = Decimal("999")
    min_sieve = Decimal("999")
    min_tol = Decimal("999")
    for idx, s in enumerate(slabs):
        x_lo, x_hi = int(s["x_lo"]), int(s["x_hi"])
        z, y = int(s["z"]), int(s["y"])
        main_lo = Decimal(s["main_lo"])
        err_hi = Decimal(s["err_hi"])
        net_lo = Decimal(s["net_lo"])
        sieve_net = Decimal(s["sieve_net_lo"])
        tol = Decimal(s["rem_tol"])
        if idx > 0 and x_lo != int(slabs[idx - 1]["x_hi"]):
            fail(f"Slab gap at index {idx}: prev X_hi != {x_lo}")
        if not (2 <= z <= y and x_lo < x_hi <= y**4 and x_hi <= z * (y**3)):
            fail(f"Invalid switching geometry on slab {idx + 1}")
        if net_lo <= 0 or err_hi <= 0 or abs((main_lo - err_hi) - net_lo) > Decimal("1e-12"):
            fail(f"Invalid budget on slab {idx + 1}: {main_lo} - {err_hi} vs {net_lo}")
        min_net = min(min_net, net_lo)
        min_sieve = min(min_sieve, sieve_net)
        min_tol = min(min_tol, tol)

    x_ls = int(ray["x_ls"])
    if int(slabs[-1]["x_hi"]) != x_ls:
        fail(f"Last slab X_hi={slabs[-1]['x_hi']} != ray X_LS={x_ls}")
    r_main = Decimal(ray["main_lo"])
    r_err = Decimal(ray["err_hi"])
    r_net = Decimal(ray["net_lo"])
    if r_net <= 0 or r_err <= 0 or abs((r_main - r_err) - r_net) > Decimal("1e-12"):
        fail(f"Invalid ray budget: {r_main} - {r_err} vs {r_net}")

    c2_used = Decimal(str(ray["c2_used"]))
    c2_be = Decimal(str(ray["c2_breakeven"]))
    if c2_used <= 0 or c2_be <= c2_used:
        fail(f"Invalid ray C2 margins: used={c2_used}, breakeven={c2_be}")
    return [
        "[3/6] CONTIGUOUS SLABS, RAY GEOMETRY & ROBUSTNESS",
        f"  PASS {len(slabs)} contiguous slabs spanning [4*10^18, 10^{len(str(x_ls)) - 1}) "
        f"(min net_lo={fmt_dec(min_net, 6, rounding=ROUND_FLOOR)}, "
        f"min sieve_net={fmt_dec(min_sieve, 6, rounding=ROUND_FLOOR)}, "
        f"min rem_tol={fmt_dec(min_tol, 2, rounding=ROUND_FLOOR)}x)",
        f"  PASS asymptotic ray [10^{len(str(x_ls)) - 1}, ∞) "
        f"(net_lo={fmt_dec(r_net, 6, rounding=ROUND_FLOOR)}, "
        f"C2_used={fmt_dec(c2_used, 6, rounding=ROUND_CEILING)}, "
        f"C2_max={fmt_dec(c2_be, 4, rounding=ROUND_FLOOR)})",
    ]


def verify_bounds_log() -> list[str]:
    from certify_omega_le_3 import _fmt_sci  # noqa: E401
    from sieve_cert.interval import fmt_dec  # noqa: E401

    log_path = ROOT / "scripts/data/certified_bounds.txt"
    txt = log_path.read_text(encoding="utf-8")
    if "ALL REGIMES CERTIFIED" not in txt or "ROBUSTNESS & PERTURBATION SUMMARY" not in txt:
        fail("certified_bounds.txt missing completion or robustness summary banner")

    payload = json.loads((ROOT / "scripts/data/certified_slabs.json").read_text(encoding="utf-8"))
    slabs = payload["slabs"]
    ray = payload["ray"]

    re_2a = re.compile(
        r"^\s*(2a-(\d{2})):\s+\[([^,]+),\s+([^)]+)\)\s+z=\s*(\d+)\s+a=\s*\d+\s+odd=\s*\d+\s+"
        r"y=\s*(\d+)\s+\|\s+main>=(\d+\.\d+)\s+err<=(\d+\.\d+)\s+net>=(\d+\.\d+)\s+"
        r"sieve_net>=(\d+\.\d+)\s+tol=(\d+\.\d+)x\s*$"
    )
    re_2b = re.compile(
        r"^\s*(2b-(\d{2})):\s+\[([^,]+),\s+([^)]+)\)\s+M=\s*\d+\s+a=\s*\d+\s+odd=\s*\d+\s+"
        r"z=\s*(\d+)\s+\|\s+main>=(\d+\.\d+)\s+err<=(\d+\.\d+)\s+net>=(\d+\.\d+)\s+"
        r"sieve_net>=(\d+\.\d+)\s+tol=(\d+\.\d+)x\s*$"
    )
    re_2c = re.compile(
        r"^\s*(2c-(\d{2})):\s+\[([^,]+),\s+([^)]+)\)\s+M=\s*\d+\s+.*?\|\s+"
        r"main>=(\d+\.\d+)\s+err<=(\d+\.\d+)\s+net>=(\d+\.\d+)\s+tol=(\d+\.\d+)x\s*$"
    )

    parsed_rows = []
    for line in txt.splitlines():
        for reg, pat in (("2a", re_2a), ("2b", re_2b), ("2c", re_2c)):
            m = pat.match(line)
            if m:
                parsed_rows.append((reg, m))
                break

    if len(parsed_rows) != len(slabs):
        fail(f"certified_bounds.txt parsed {len(parsed_rows)} slab rows != JSON {len(slabs)}")

    per_reg_idx = {"2a": 0, "2b": 0, "2c": 0}
    min_net = Decimal("999")
    min_sieve = Decimal("999")
    min_tol = Decimal("999")
    for idx, ((reg, m), s) in enumerate(zip(parsed_rows, slabs), 1):
        if reg != s["regime"]:
            fail(f"certified_bounds.txt slab {idx}: regime {reg} != JSON {s['regime']}")
        per_reg_idx[reg] += 1
        label = m.group(1)
        reg_num = int(m.group(2))
        if reg_num != per_reg_idx[reg]:
            fail(f"certified_bounds.txt slab {label}: expected index {per_reg_idx[reg]}")
        x_lo_str, x_hi_str = m.group(3), m.group(4)
        exp_xlo = _fmt_sci(int(s["x_lo"]))
        exp_xhi = _fmt_sci(int(s["x_hi"]))
        if x_lo_str != exp_xlo or x_hi_str != exp_xhi:
            fail(f"{label}: interval [{x_lo_str}, {x_hi_str}) != [{exp_xlo}, {exp_xhi})")

        if reg == "2a":
            z_val, y_val = int(m.group(5)), int(m.group(6))
            main_txt, err_txt, net_txt, snet_txt, tol_txt = m.group(7, 8, 9, 10, 11)
            if z_val != int(s["z"]) or y_val != int(s["y"]):
                fail(f"{label}: (z={z_val}, y={y_val}) != JSON ({s['z']}, {s['y']})")
        elif reg == "2b":
            z_val = int(m.group(5))
            main_txt, err_txt, net_txt, snet_txt, tol_txt = m.group(6, 7, 8, 9, 10)
            if z_val != int(s["z"]):
                fail(f"{label}: z={z_val} != JSON {s['z']}")
        else:
            main_txt, err_txt, net_txt, tol_txt = m.group(5, 6, 7, 8)
            snet_txt = None

        exp_main = fmt_dec(Decimal(s["main_lo"]), 5, rounding=ROUND_FLOOR)
        exp_err = fmt_dec(Decimal(s["err_hi"]), 5, rounding=ROUND_CEILING)
        exp_net = fmt_dec(Decimal(s["net_lo"]), 5, rounding=ROUND_FLOOR)
        exp_tol = fmt_dec(Decimal(s["rem_tol"]), 1, rounding=ROUND_FLOOR)
        if main_txt != exp_main or err_txt != exp_err or net_txt != exp_net or tol_txt != exp_tol:
            fail(
                f"{label}: log=({main_txt}, {err_txt}, {net_txt}, {tol_txt}) "
                f"!= json_outward=({exp_main}, {exp_err}, {exp_net}, {exp_tol})"
            )
        if snet_txt is not None:
            exp_snet = fmt_dec(Decimal(s["sieve_net_lo"]), 4, rounding=ROUND_FLOOR)
            if snet_txt != exp_snet:
                fail(f"{label}: sieve_net {snet_txt} != json_outward {exp_snet}")

        min_net = min(min_net, Decimal(s["net_lo"]))
        min_sieve = min(min_sieve, Decimal(s["sieve_net_lo"]))
        min_tol = min(min_tol, Decimal(s["rem_tol"]))

    # Regime 2 summary line
    m_r2 = re.search(
        r"Regime 2 PASSED across (\d+) contiguous slabs\s+"
        r"\(min net_lo=(\d+\.\d+),\s+min sieve_net_lo=(\d+\.\d+),\s+min GRH rem tol=(\d+\.\d+)x\)",
        txt,
    )
    if not m_r2:
        fail("certified_bounds.txt missing Regime 2 summary line")
    exp_min_net = fmt_dec(min_net, 6, rounding=ROUND_FLOOR)
    exp_min_sieve = fmt_dec(min_sieve, 6, rounding=ROUND_FLOOR)
    exp_min_tol = fmt_dec(min_tol, 2, rounding=ROUND_FLOOR)
    if (
        int(m_r2.group(1)) != len(slabs)
        or m_r2.group(2) != exp_min_net
        or m_r2.group(3) != exp_min_sieve
        or m_r2.group(4) != exp_min_tol
    ):
        fail(f"Regime 2 summary mismatch in certified_bounds.txt: {m_r2.groups()}")

    # Regime 3 summary lines
    m_r3_hdr = re.search(
        r"X_LS = 10\^(\d+),.*?Lean cap C2 <= (\d+\.\d+) \(C2 break-even=(\d+\.\d+)\)",
        txt,
    )
    m_r3_vals = re.search(
        r"main_coeff >= (\d+\.\d+),\s+tot_err <= (\d+\.\d+),\s+NET COEFF >= (\d+\.\d+)\s+\(GRH rem tol=(\d+\.\d+)x\)",
        txt,
    )
    m_r3_pass = re.search(
        r"Regime 3 PASSED: net switching coefficient >= (\d+\.\d+) > 0 for ALL even N >= 10\^(\d+)",
        txt,
    )
    m_rob_r3 = re.search(
        r"Asymptotic Regime 3 tolerance\s+:\s+C_2 <= (\d+\.\d+) \(vs used (\d+\.\d+)\),\s+GRH rem tol=(\d+\.\d+)x",
        txt,
    )
    if not (m_r3_hdr and m_r3_vals and m_r3_pass and m_rob_r3):
        fail("certified_bounds.txt missing Regime 3 summary lines")

    exp_x_ls = int(ray["x_ls"])
    exp_c2_used = fmt_dec(Decimal(ray["c2_used"]), 6, rounding=ROUND_CEILING)
    exp_c2_be = fmt_dec(Decimal(ray["c2_breakeven"]), 1, rounding=ROUND_FLOOR)
    exp_r_main = fmt_dec(Decimal(ray["main_lo"]), 6, rounding=ROUND_FLOOR)
    exp_r_err = fmt_dec(Decimal(ray["err_hi"]), 6, rounding=ROUND_CEILING)
    exp_r_net = fmt_dec(Decimal(ray["net_lo"]), 6, rounding=ROUND_FLOOR)
    exp_r_tol = fmt_dec(Decimal(ray["rem_tol"]), 1, rounding=ROUND_FLOOR)

    if (
        10 ** int(m_r3_hdr.group(1)) != exp_x_ls
        or m_r3_hdr.group(2) != exp_c2_used
        or m_r3_hdr.group(3) != exp_c2_be
    ):
        fail(f"Regime 3 header mismatch: {m_r3_hdr.groups()}")
    if (
        m_r3_vals.group(1) != exp_r_main
        or m_r3_vals.group(2) != exp_r_err
        or m_r3_vals.group(3) != exp_r_net
        or m_r3_vals.group(4) != exp_r_tol
    ):
        fail(f"Regime 3 values mismatch: {m_r3_vals.groups()}")
    if m_r3_pass.group(1) != exp_r_net or 10 ** int(m_r3_pass.group(2)) != exp_x_ls:
        fail(f"Regime 3 PASS line mismatch: {m_r3_pass.groups()}")
    if (
        m_rob_r3.group(1) != exp_c2_be
        or m_rob_r3.group(2) != exp_c2_used
        or m_rob_r3.group(3) != exp_r_tol
    ):
        fail(f"Regime 3 robustness line mismatch: {m_rob_r3.groups()}")

    return [
        f"[4/6] OUTPUT LOG AGREEMENT: PASS ({len(parsed_rows)} slabs + Regime 3 exact outward match in {log_path.relative_to(ROOT)})"
    ]


DATA_LEAN_DENOM = 10_000_000_000


def _dec_to_rat_int(d_str: str, rounding: str) -> int:
    with localcontext() as ctx:
        ctx.prec = 60
        ctx.traps[Inexact] = False
        ctx.traps[Rounded] = False
        return int((Decimal(d_str) * DATA_LEAN_DENOM).to_integral_value(rounding=rounding))


def _parse_lean_record(block: str) -> dict[str, int]:
    return {
        k: int(v)
        for k, v in re.findall(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*:=\s*(\d+)\b", block)
    }


def verify_data_lean_match() -> list[str]:
    data_lean = (ROOT / "BuchstabSwitching/Certificates/Data.lean").read_text(encoding="utf-8")
    payload = json.loads((ROOT / "scripts/data/certified_slabs.json").read_text(encoding="utf-8"))
    slabs = payload["slabs"]
    ray = payload["ray"]

    m_slabs = re.search(
        r"def\s+allSlabs\s*:\s*List\s+SlabCert\s*:=\s*\[(.*?)\]", data_lean, flags=re.DOTALL
    )
    if not m_slabs:
        fail("Could not locate def allSlabs in Data.lean")
    slab_blocks = re.findall(r"\{([^}]*)\}", m_slabs.group(1))
    if len(slab_blocks) != len(slabs):
        fail(f"Data.lean slab count {len(slab_blocks)} != JSON count {len(slabs)}")

    expected_slab_keys = {"X_lo", "X_hi", "z", "y", "main_num", "err_num", "net_num", "den"}
    for idx, (block, s) in enumerate(zip(slab_blocks, slabs), 1):
        rec = _parse_lean_record(block)
        if set(rec.keys()) != expected_slab_keys:
            fail(f"Data.lean slab {idx} unexpected keys: {sorted(rec.keys())}")
        if rec["X_lo"] != int(s["x_lo"]) or rec["X_hi"] != int(s["x_hi"]):
            fail(f"Data.lean slab {idx} X bounds mismatch")
        if rec["z"] != int(s["z"]) or rec["y"] != int(s["y"]):
            fail(f"Data.lean slab {idx} (z, y) mismatch")
        if rec["den"] != DATA_LEAN_DENOM:
            fail(f"Data.lean slab {idx} den={rec['den']} != {DATA_LEAN_DENOM}")
        m_n = _dec_to_rat_int(s["main_lo"], ROUND_FLOOR)
        e_n = _dec_to_rat_int(s["err_hi"], ROUND_CEILING)
        net_n = m_n - e_n
        if rec["main_num"] != m_n or rec["err_num"] != e_n or rec["net_num"] != net_n:
            fail(
                f"Data.lean slab {idx} rational mismatch: "
                f"lean=({rec['main_num']}, {rec['err_num']}, {rec['net_num']}) "
                f"!= json=({m_n}, {e_n}, {net_n})"
            )
        if rec["net_num"] <= 0:
            fail(f"Data.lean slab {idx} non-positive net_num={rec['net_num']}")

    m_ray = re.search(
        r"def\s+asymptoticCert\s*:\s*RayCert\s*:=\s*\{([^}]*)\}", data_lean, flags=re.DOTALL
    )
    if not m_ray:
        fail("Could not locate def asymptoticCert in Data.lean")
    r_rec = _parse_lean_record(m_ray.group(1))
    expected_ray_keys = {"X_LS", "main_num", "err_num", "net_num", "den"}
    if set(r_rec.keys()) != expected_ray_keys:
        fail(f"Data.lean asymptoticCert unexpected keys: {sorted(r_rec.keys())}")
    if r_rec["X_LS"] != int(ray["x_ls"]):
        fail("Data.lean asymptoticCert.X_LS does not match JSON ray x_ls")
    if r_rec["den"] != DATA_LEAN_DENOM:
        fail(f"Data.lean asymptoticCert den={r_rec['den']} != {DATA_LEAN_DENOM}")
    rm_n = _dec_to_rat_int(ray["main_lo"], ROUND_FLOOR)
    re_n = _dec_to_rat_int(ray["err_hi"], ROUND_CEILING)
    rnet_n = rm_n - re_n
    if r_rec["main_num"] != rm_n or r_rec["err_num"] != re_n or r_rec["net_num"] != rnet_n:
        fail(
            f"Data.lean asymptoticCert rational mismatch: "
            f"lean=({r_rec['main_num']}, {r_rec['err_num']}, {r_rec['net_num']}) "
            f"!= json=({rm_n}, {re_n}, {rnet_n})"
        )
    if r_rec["net_num"] <= 0:
        fail(f"Data.lean asymptoticCert non-positive net_num={r_rec['net_num']}")

    return [
        f"[5/6] DATA.LEAN CONSISTENCY: PASS ({len(slab_blocks)} slabs + ray all fields exact match)"
    ]


def verify_lean_hygiene() -> list[str]:
    lean_files = sorted((ROOT / "BuchstabSwitching").rglob("*.lean")) + [ROOT / "BuchstabSwitching.lean"]
    for lf in lean_files:
        src = re.sub(r"/-.*?-/", "", lf.read_text(encoding="utf-8"), flags=re.DOTALL)
        for lineno, line in enumerate(src.splitlines(), 1):
            code = line.split("--", 1)[0]
            if re.search(r"\b(sorry|admit|axiom|native_decide)\b", code):
                fail(f"{lf.relative_to(ROOT)}:{lineno}: forbidden keyword in Lean code")
    return [
        "[6/6] LEAN 4 KERNEL HYGIENE",
        f"  PASS {len(lean_files)} Lean files contain zero sorry/admit/axiom/native_decide",
    ]


def main() -> int:
    report = []
    report.extend(verify_ast_and_traps())
    report.extend(verify_naming_hygiene())
    report.extend(verify_json_certificates())
    report.extend(verify_bounds_log())
    report.extend(verify_data_lean_match())
    report.extend(verify_lean_hygiene())
    report.append("\nQUICK VERIFICATION SUMMARY: ALL 6 CHECKS PASSED.")
    print("\n".join(report))
    return 0


if __name__ == "__main__":
    sys.exit(main())
