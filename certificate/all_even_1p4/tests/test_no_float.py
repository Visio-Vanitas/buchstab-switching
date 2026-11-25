"""No binary floating point in the package: a static AST scan plus a runtime scan of the summary.

The static scan rejects, in every module of the package (not the tests): float or
complex literals, the names float/complex/round, imports of math, cmath, random,
statistics, numpy, and the float-valued clocks time.time/perf_counter/monotonic;
and true division '/' between two integer literals.  The runtime scan checks
that no float appears anywhere in a JSON summary.  (A static scan cannot see
int / int between two variables; every '/' in the package acts on Iv or
Decimal operands, which the arithmetic modules enforce by construction.)
"""

from __future__ import annotations

import ast
import json
import unittest
from pathlib import Path

PACKAGE = Path(__file__).resolve().parent.parent
FORBIDDEN_MODULES = {"math", "cmath", "random", "statistics", "numpy"}
FORBIDDEN_NAMES = {"float", "complex", "round"}
FORBIDDEN_ATTRS = {"time", "perf_counter", "monotonic", "process_time"}


def package_modules() -> list[Path]:
    return sorted(PACKAGE.glob("*.py"))


def violations(path: Path) -> list[str]:
    tree = ast.parse(path.read_text(), filename=str(path))
    out = []
    for node in ast.walk(tree):
        where = f"{path.name}:{getattr(node, 'lineno', '?')}"
        if isinstance(node, ast.Constant) and isinstance(node.value, (float, complex)):
            out.append(f"{where}: float/complex literal {node.value!r}")
        elif isinstance(node, ast.Name) and node.id in FORBIDDEN_NAMES:
            out.append(f"{where}: use of {node.id}")
        elif isinstance(node, ast.Import):
            out += [f"{where}: import {a.name}" for a in node.names if a.name.split(".")[0] in FORBIDDEN_MODULES]
        elif isinstance(node, ast.ImportFrom) and (node.module or "").split(".")[0] in FORBIDDEN_MODULES:
            out.append(f"{where}: from {node.module} import")
        elif isinstance(node, ast.Attribute) and node.attr in FORBIDDEN_ATTRS:
            out.append(f"{where}: float-valued clock .{node.attr}")
        elif (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div)
              and all(isinstance(s, ast.Constant) and isinstance(s.value, int) for s in (node.left, node.right))):
            out.append(f"{where}: int / int")
    return out


class NoFloatTest(unittest.TestCase):
    def test_modules_found(self) -> None:
        names = {p.name for p in package_modules()}
        for required in ("interval.py", "elementary.py", "constants.py", "cited.py", "regime2.py", "regime3.py"):
            self.assertIn(required, names)

    def test_static_scan(self) -> None:
        found = [v for p in package_modules() for v in violations(p)]
        self.assertEqual(found, [], "\n".join(found))

    def test_scanner_detects_floats(self) -> None:
        sample = PACKAGE / "tests" / "data" / "float_sample.py.txt"
        found = violations(sample)
        self.assertEqual(len(found), 6, found)

    def test_summary_has_no_float(self) -> None:
        from all_even_1p4 import report
        from all_even_1p4.certificate import run_certificate

        run = run_certificate(slab_indices=(1,), with_benchmark=False, with_tail=False)

        def refuse(text: str) -> None:
            raise AssertionError(f"float in summary: {text}")

        json.loads(report.summary_json(run), parse_float=refuse)


if __name__ == "__main__":
    unittest.main()
