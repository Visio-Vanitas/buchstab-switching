"""Every cited bound refuses to be used outside its stated range; the sieve table is intact."""

from __future__ import annotations

import unittest
from decimal import Decimal

from all_even_1p4 import cited
from all_even_1p4.cited import HypothesisError
from all_even_1p4.elementary import ln_iv
from all_even_1p4.interval import Iv
from all_even_1p4.prime_bounds import mertens_upper_error, prime_count_upper


class RangeRefusalTest(unittest.TestCase):
    def test_js_lemma_5_1(self) -> None:
        with self.assertRaises(HypothesisError):
            cited.js_lemma_5_1_c_pi(ln_iv(Iv(10**18)), 10**18)
        with self.assertRaises(HypothesisError):
            cited.js_lemma_5_1_c_pi(ln_iv(Iv(10**18)))
        self.assertLess(cited.js_lemma_5_1_c_pi(ln_iv(Iv(4 * 10**18)), 4 * 10**18).hi, Decimal("0.16"))

    def test_schoenfeld(self) -> None:
        with self.assertRaises(HypothesisError):
            cited.schoenfeld_denominator(2656)
        with self.assertRaises(HypothesisError):
            cited.schoenfeld_denominator(3)  # the range printed in [BS] Lemma 1, false at x = 3
        self.assertEqual(cited.schoenfeld_denominator(2657), 8)

    def test_prime_count_bound_uses_schoenfeld_range(self) -> None:
        x = Iv(1000)
        with self.assertRaises(HypothesisError):
            prime_count_upper(x, ln_iv(x), 1000)

    def test_robin(self) -> None:
        with self.assertRaises(HypothesisError):
            cited.robin_constant(2)
        self.assertEqual(cited.robin_constant(3), Decimal("1.3841"))

    def test_buthe(self) -> None:
        log_1e9 = ln_iv(Iv(10**9))
        with self.assertRaises(HypothesisError):
            cited.buthe_constants(ln_iv(Iv(10**8)).hi, log_1e9.hi)
        self.assertEqual(cited.buthe_constants(ln_iv(Iv(10**10)).lo, log_1e9.hi), (Decimal("0.608"), Decimal("1.1")))

    def test_js_lemma_3_1(self) -> None:
        with self.assertRaises(HypothesisError):
            cited.require_js_lemma_3_1(70)
        cited.require_js_lemma_3_1(71)

    def test_mertens(self) -> None:
        with self.assertRaises(HypothesisError):
            cited.mertens_lower_coeff(Decimal(1))
        with self.assertRaises(HypothesisError):
            cited.mertens_cap(Decimal("8.9"))
        with self.assertRaises(HypothesisError):
            cited.mertens_large_coeff(Decimal(10**12 - 1))
        with self.assertRaises(HypothesisError):
            cited.bjs_lemma_16_numerator(Decimal(1), Decimal(100))
        with self.assertRaises(HypothesisError):
            cited.bjs_lemma_16_numerator(Decimal(100), Decimal(10**12 + 1))
        small = Iv(7000)  # log 7000 < 8.9
        with self.assertRaises(HypothesisError):
            mertens_upper_error(small, ln_iv(small))

    def test_bjs_theorem_6_table(self) -> None:
        with self.assertRaises(HypothesisError):
            cited.bjs_table_row(Iv(1) / Iv(73))
        self.assertEqual(cited.bjs_table_row(Iv(1) / Iv(100)).inv_eps, 100)
        row = cited.bjs_table_row(Iv(Decimal("8.525989e-3")))
        self.assertEqual((row.inv_eps, row.c1, row.c2), (100, 276, 277))
        self.assertEqual(cited.bjs_table_row(Iv(Decimal("1.312e-2"))).inv_eps, 76)

    def test_bjs_table_integrity(self) -> None:
        rows = cited.BJS_TABLE_1
        self.assertEqual(len(rows), 24)
        self.assertEqual(rows[0].inv_eps, 74)
        for a, b in zip(rows, rows[1:]):
            self.assertLess(a.inv_eps, b.inv_eps)
            self.assertGreaterEqual(a.c1, b.c1)  # "C1, C2 are decreasing in eps^-1" ([BJS] after Table 1)
            self.assertGreaterEqual(a.c2, b.c2)

    def test_bjs_lemma_38(self) -> None:
        with self.assertRaises(HypothesisError):
            cited.bjs_lemma_38_constants(Decimal(284))
        self.assertEqual(cited.bjs_lemma_38_constants(Decimal(285)), (Decimal("1.45"), 10, Decimal("1.002")))

    def test_every_citation_has_provenance(self) -> None:
        keys = set()
        for c in cited.ALL_CITATIONS:
            self.assertTrue(c.source and c.reference and c.statement and c.hypotheses and c.note_section)
            self.assertNotIn(c.key, keys)
            keys.add(c.key)


if __name__ == "__main__":
    unittest.main()
