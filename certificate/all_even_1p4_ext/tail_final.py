"""X31 tail nets at chosen starting points, inputs read from the committed certificate files (X31Tail.from_files).

For each k, recursion and e: best net over M, B with a fine sieve_fF mesh and many slices, plus the same certificate
with C1 and C2 multiplied by 1.05 (a robustness margin, not a certificate of anything else).
usage: tail_final.py KS ES OUT [H] [SLICES]     e.g. tail_final.py 74,76,80,85,90,100 399,420,441,460,480,500 out.json
"""
import sys, os, json, time
from dataclasses import replace
from fractions import Fraction
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from all_even_1p4_ext.tail_x31 import X31Tail, try_certify

MS = list(range(20, 31)); BS = ["3.01", "3.05"]


def job(a):
    k, rec, e, M, B, h, sl = a
    p = X31Tail.from_files(e, M, B, k, rec, grid_h=h, slices=sl)
    r = try_certify(p)
    r["q0"] = p.q0
    return r


if __name__ == "__main__":
    ks = [int(x) for x in sys.argv[1].split(",")]; es = [int(x) for x in sys.argv[2].split(",")]; out = sys.argv[3]
    h = int(sys.argv[4]) if len(sys.argv) > 4 else 2000; sl = int(sys.argv[5]) if len(sys.argv) > 5 else 2000
    R = []
    with Pool(os.cpu_count()) as P:
        for k in ks:
            for rec in ("new", "old"):
                for e in es:
                    t = time.time()
                    res = P.map(job, [(k, rec, e, M, B, h, sl) for M in MS for B in BS], chunksize=1)
                    ok = [r for r in res if r["ok"]]
                    best = max(ok, key=lambda r: r["net_lo"]) if ok else None
                    rob = None
                    if best:
                        p = X31Tail.from_files(e, best["M"], best["B"], k, rec, grid_h=h, slices=sl)
                        p = replace(p, c1=p.c1 * Fraction(105, 100), c2=p.c2 * Fraction(105, 100))
                        rob = try_certify(p)
                    R.append(dict(k=k, rec=rec, e=e, best=best, c_times_1_05=rob))
                    print(f"k={k} {rec} e={e}: " + ("NO PASS" if not best else
                          f"M={best['M']} B={best['B']} alpha={best['alpha']} net>={best['net']} "
                          f"(C1,C2 x1.05: {'net>=' + rob['net'] if rob.get('ok') else 'FAILS'})") + f" t={time.time()-t:.0f}s",
                          flush=True)
                    json.dump(R, open(out, "w"), indent=0)
    print("DONE", flush=True)
