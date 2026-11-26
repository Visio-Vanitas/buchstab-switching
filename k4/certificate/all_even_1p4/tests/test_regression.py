"""Regression against the original monolithic script.

``data/original_reference.json`` holds the full-precision bounds returned by the
unmodified original (made by ``make_original_reference.py``).  The fast tests
compare two slabs; the full test (set ALL_EVEN_1P4_FULL=1, several minutes)
runs the whole certificate and compares every bound the original returns.

Expected result: equality of every 90-digit endpoint.  The square-root fix
(see interval.py) changes some intermediate endpoints by one unit in the 90th
digit, but in this run none of these changes survives the outward rounding of
the subsequent operations; if a future change made a value differ, the test
accepts it only in the conservative direction and by at most 1e-80.
"""

from __future__ import annotations

import json
import os
import re
import unittest
from decimal import Decimal
from fractions import Fraction
from pathlib import Path

from all_even_1p4 import constants
from all_even_1p4.certificate import run_certificate
from all_even_1p4.elementary import LN2
from all_even_1p4.interval import Iv
from all_even_1p4.regime2 import SLABS, SlabResult, certify_slab

HERE = Path(__file__).resolve().parent
REFERENCE = json.loads((HERE / "data" / "original_reference.json").read_text())
ORIGINAL_OUTPUT = HERE / "data" / "earlier_split_output.txt"
TOLERANCE = Fraction(1, 10**80)
FULL = os.environ.get("ALL_EVEN_1P4_FULL") == "1"


class _Compare(unittest.TestCase):
    def assert_lower(self, name: str, new: Decimal, old: str) -> None:
        """A certified lower bound: equal, or lower by at most TOLERANCE."""
        old_d = Decimal(old)
        self.assertLessEqual(new, old_d, f"{name}: new lower bound {new} above original {old}")
        self.assertLessEqual(Fraction(old_d) - Fraction(new), TOLERANCE, name)

    def assert_upper(self, name: str, new: Decimal, old: str) -> None:
        """A certified upper bound: equal, or higher by at most TOLERANCE."""
        old_d = Decimal(old)
        self.assertGreaterEqual(new, old_d, f"{name}: new upper bound {new} below original {old}")
        self.assertLessEqual(Fraction(new) - Fraction(old_d), TOLERANCE, name)

    def assert_encloses(self, name: str, new: Iv, old: list[str]) -> None:
        self.assert_lower(name + ".lo", new.lo, old[0])
        self.assert_upper(name + ".hi", new.hi, old[1])

    def compare_slab(self, r: SlabResult) -> None:
        old = REFERENCE["regime2"][r.params.index - 1]
        self.assertEqual(old["index"], r.params.index)
        self.assertEqual((str(r.params.x_lo), str(r.params.x_hi)), (old["X_lo"], old["X_hi"]))
        self.assertEqual((r.z, r.y), (old["z"], old["y"]))
        self.assert_lower(f"slab {r.params.index} main", r.main.lo, old["main_lo"])
        self.assert_upper(f"slab {r.params.index} err", r.err_total.hi, old["err_hi"])
        self.assert_lower(f"slab {r.params.index} net", r.net.lo, old["net_lo"])


class ReferenceFileTest(unittest.TestCase):
    """The reference file agrees with the original's committed text output (6 decimals)."""

    def test_reference_matches_original_output(self) -> None:
        text = ORIGINAL_OUTPUT.read_text()
        pattern = re.compile(r"Slab\s+(\d+):.*main>=([\d.]+) err<=([\d.]+) net>=([\d.]+)")
        rows = {int(m.group(1)): m.groups()[1:] for m in pattern.finditer(text)}
        self.assertEqual(len(rows), 30)
        half_unit = Fraction(5, 10**7)
        for old in REFERENCE["regime2"]:
            printed = rows[old["index"]]
            for value, shown in zip((old["main_lo"], old["err_hi"], old["net_lo"]), printed):
                self.assertLessEqual(abs(Fraction(value) - Fraction(shown)), half_unit)
        net = re.search(r"NET COEFF\s+>= ([\d.]+)", text).group(1)
        self.assertLessEqual(abs(Fraction(REFERENCE["regime3"]["net"][0]) - Fraction(net)), half_unit)


class ConstantsTest(_Compare):
    def test_constants_equal_original(self) -> None:
        ours = {
            "PI": constants.PI, "LN2": LN2, "GAMMA": constants.GAMMA, "E_GAMMA": constants.E_GAMMA,
            "E_NEG_GAMMA": constants.E_NEG_GAMMA, "C2_TWIN": constants.C2_TWIN, "M0": constants.M0,
            "U_c": constants.U_C, "LI2": constants.LI2, "LI_E5": constants.LI_E5,
        }
        for name, iv in ours.items():
            self.assert_encloses(name, iv, REFERENCE["constants"][name])


class FastSlabRegressionTest(_Compare):
    """Slab 1 (exact branch, the (*) q^2 branch) and slab 22 (analytic branch, minimum margin)."""

    def test_slab_1_and_22(self) -> None:
        for index in (1, 22):
            self.compare_slab(certify_slab(SLABS[index - 1]))


@unittest.skipUnless(FULL, "full regression: set ALL_EVEN_1P4_FULL=1 (several minutes)")
class FullRegressionTest(_Compare):
    def test_full_certificate(self) -> None:
        run = run_certificate()
        self.assertTrue(run.complete)
        self.assertEqual(len(run.slabs), 30)
        for r in run.slabs:
            self.compare_slab(r)

        t = run.tail
        old = REFERENCE["regime3"]
        self.assertEqual((t.epsilon.row.inv_eps, t.epsilon.row.c1, t.epsilon.row.c2), (old["k"], old["c1"], old["c2"]))
        pairs = {
            "alpha": t.alpha, "z0": t.z0, "eps": t.epsilon.eps, "s": t.s, "s_min": t.s_min, "delta_V": t.delta_v,
            "c4G": t.c4g, "lb_A": t.lb_a, "half_sum": t.half_sum, "main": t.main, "err": t.err_total,
            "R1": t.err_r1, "R2": t.err_r2, "rq": t.err_rq, "q2": t.err_q2, "net": t.net, "logX": t.log_x,
            "beta": t.beta,
        }
        for name, iv in pairs.items():
            self.assert_encloses("tail " + name, iv, old[name])

        b = run.benchmark
        self.assertEqual(b.k_values, (25, 31, 31))
        printed = re.findall(r"coeff in \[([\d.]+), ([\d.]+)\]", REFERENCE["benchmark_stdout"])
        for iv, (lo, hi) in zip((b.coeff_js, b.coeff_table), printed):
            self.assertLessEqual(abs(Fraction(iv.lo) - Fraction(lo)), Fraction(5, 10**5))
            self.assertLessEqual(abs(Fraction(iv.hi) - Fraction(hi)), Fraction(5, 10**5))


if __name__ == "__main__":
    unittest.main()
