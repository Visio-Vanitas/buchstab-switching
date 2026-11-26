"""The tail certificate used with the block ladder: N_3 = 10^500, eps' = 1/80, both recursions, inputs read from
the committed hstar and cn files. Prints every certified quantity as JSON.  usage: tail_at_500.py [OUT]"""
import sys, os, json
from dataclasses import replace
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from all_even_1p4_ext.tail_x31 import X31Tail, certify

R = []
for rec, M in (("new", 22), ("old", 24)):
    p = X31Tail.from_files(500, M, "3.01", 80, rec, grid_h=2000, slices=2000)
    r = certify(p); r["q0"] = p.q0; r["c1"] = f"{p.c1.numerator}/{p.c1.denominator}"; r["c2"] = f"{p.c2.numerator}/{p.c2.denominator}"
    rob = certify(replace(p, c1=p.c1 * Fraction(105, 100), c2=p.c2 * Fraction(105, 100)))
    r["net_with_C1_C2_times_1_05"] = rob["net"]
    print(json.dumps(r), flush=True); R.append(r)
    if not r["ok"]:
        raise SystemExit(f"tail certificate at 10^500 failed: {r}")
if len(sys.argv) > 1:
    json.dump(R, open(sys.argv[1], "w"), indent=1)
