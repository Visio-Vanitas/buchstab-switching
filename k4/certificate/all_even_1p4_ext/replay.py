"""Independent replay of the committed block ladder and tail (no search).

usage: replay.py LADDER_JSON TAIL_JSON
For every slab: certify_brun_slab(x_lo, x_hi, M, a, fixed=recorded blocks) once; checks that z, y equal the recorded
values and that the recomputed net lower bound equals the recorded one; PASS/FAIL per slab. Then checks contiguity
from 4e18 to exactly 10^500, and re-runs each tail certificate (inputs read from the committed hstar/cn files) at its
recorded (e, M, B, k, recursion, mesh, slices), requiring e = 500 and the recorded net. Prints sha256 of both inputs.
"""
import sys, os, json, hashlib, time
from decimal import Context, Decimal, ROUND_HALF_EVEN, localcontext
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from all_even_1p4.constants import E5_OVER_3, LI_E5
from all_even_1p4.interval import ERROR_TRAPS
from all_even_1p4_ext.regime2_brun import certify_brun_slab
from all_even_1p4_ext.tail_x31 import X31Tail, certify

_DISP_CTX = Context(prec=28, rounding=ROUND_HALF_EVEN, traps=ERROR_TRAPS)

assert LI_E5.hi < E5_OVER_3.lo, f"global check li(e^5) < e^5/3 failed: {LI_E5} vs {E5_OVER_3}"

lad, tail = sys.argv[1], sys.argv[2]
for f in (lad, tail):
    print(f"sha256 {hashlib.sha256(open(f, 'rb').read()).hexdigest()}  {os.path.basename(f)}", flush=True)
L = json.load(open(lad)); T = json.load(open(tail))
assert len(L) == 58, f"expected 58 ladder slabs, got {len(L)}"
assert len(T) >= 1, "expected non-empty tail JSON"
assert {"new", "old"}.issubset({r.get("rec") for r in T}), "tail JSON must cover both 'new' and 'old'"
bad = 0
for i, r in enumerate(L, 1):
    t = time.perf_counter_ns()
    x_lo, x_hi = int(r["x_lo"]), int(r["x_hi"])
    try:
        s = certify_brun_slab(x_lo, x_hi, r["M"], r["a"],
                              fixed=((r["low_caps"], r["low_ends"]), (r["up_caps"], r["up_ends"])))
        ok = (s.z == r["z"] and str(s.y) == str(r["y"]) and str(s.net.lo) == r["net_lo"] and s.net.lo > 0)
        with localcontext(_DISP_CTX):
            net_disp = f"{s.net.lo:.6e}"
        msg = f"net>={net_disp}" + ("" if ok else f" MISMATCH recorded {r['net_lo'][:12]} z {s.z}/{r['z']}")
    except Exception as e:
        ok, msg = False, f"{type(e).__name__}: {e}"
    bad += not ok
    ds = (time.perf_counter_ns() - t) // 10**8
    print(f"slab {i:2d} [{len(r['x_lo'])-1}d, {len(r['x_hi'])-1}d) M={r['M']} a={r['a']} {'PASS' if ok else 'FAIL'} {msg} ({ds // 10}.{ds % 10}s)", flush=True)
cont = L[0]["x_lo"] == str(4 * 10**18) and L[-1]["x_hi"] == str(10**500) and all(u["x_hi"] == v["x_lo"] for u, v in zip(L, L[1:]))
print(f"contiguity 4e18 .. 10^500 (exact integer endpoints): {'PASS' if cont else 'FAIL'}", flush=True)
bad += not cont
for r in T:
    p = X31Tail.from_files(r["e"], r["M"], r["B"], r["k"], r["rec"], grid_h=r["grid_h"], slices=r["slices"])
    s = certify(p)
    ok = (
        r["e"] == 500
        and s["ok"]
        and s["net"] == r["net"]
        and "net_lo" in r
        and s["net_lo"] == r["net_lo"]
        and Decimal(s["net_lo"]) > 0
    )
    bad += not ok
    print(f"tail k={r['k']} {r['rec']} e={r['e']} M={r['M']} B={r['B']} H={r['grid_h']} slices={r['slices']}: "
          f"{'PASS' if ok else 'FAIL'} net>={s['net']} (recorded {r['net']})", flush=True)
print(f"tail starts at exactly 10^500 = ladder end: {'PASS' if all(r['e'] == 500 for r in T) and L[-1]['x_hi'] == str(10**500) else 'FAIL'}")
print("ALL PASS" if bad == 0 else f"{bad} FAILURES", flush=True)
sys.exit(0 if bad == 0 else 1)
