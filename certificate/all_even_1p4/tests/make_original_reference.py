"""Record the full-precision numbers of the ORIGINAL monolithic script.

The original (``scripts/certify_all_even_1p4.py``) prints its bounds to six
decimals only.  This tool imports it by file path (it is not modified), calls
its certification functions, and writes every returned bound as an exact
Decimal string to ``tests/data/original_reference.json``.  The regression
tests compare the package against that file.

Run from ``research/goldbach/scripts``::

    python -m all_even_1p4.tests.make_original_reference

It takes as long as one full run of the original (a few minutes).
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ORIGINAL = HERE.parent.parent / "certify_all_even_1p4.py"
OUT = HERE / "data" / "original_reference.json"


def _load_original():
    spec = importlib.util.spec_from_file_location("certify_all_even_1p4_original", ORIGINAL)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _iv(x) -> list[str]:
    return [str(x.lo), str(x.hi)]


def main() -> int:
    t0 = time.perf_counter()
    orig = _load_original()
    t_import = time.perf_counter() - t0
    ref: dict = {
        "source": "scripts/certify_all_even_1p4.py (unmodified), imported by path",
        "constants": {
            "PI": _iv(orig.PI), "LN2": _iv(orig.LN2), "GAMMA": _iv(orig.GAMMA),
            "E_GAMMA": _iv(orig.E_GAMMA), "E_NEG_GAMMA": _iv(orig.E_NEG_GAMMA),
            "C2_TWIN": _iv(orig.C2_TWIN), "M0": _iv(orig.M0_CONST), "U_c": _iv(orig.U_CONST),
            "LI2": _iv(orig.LI2), "LI_E5": _iv(orig.LI_E5),
        },
    }
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        orig.verify_benchmark_0()
    ref["benchmark_stdout"] = buf.getvalue()

    slabs = []
    t1 = time.perf_counter()
    for idx, (x_lo, x_hi, m, a, m_odd, m_even) in enumerate(orig.SLABS, 1):
        res = orig.certify_slab_K4(x_lo, x_hi, m, a, m_odd, m_even)
        slabs.append({
            "index": idx, "X_lo": str(x_lo), "X_hi": str(x_hi),
            "z": res["z"], "y": res["y"],
            "main_lo": str(res["main_lo"]), "err_hi": str(res["err_hi"]), "net_lo": str(res["net_lo"]),
        })
        print(f"slab {idx} done", file=sys.stderr, flush=True)
    t_r2 = time.perf_counter() - t1
    ref["regime2"] = slabs

    t2 = time.perf_counter()
    m, u0, b = orig.R3_PARAMS
    r3 = orig.regime3(10 ** 170, m, u0, b)
    t_r3 = time.perf_counter() - t2
    ref["regime3"] = {k: (_iv(v) if isinstance(v, orig.Iv) else v) for k, v in r3.items()}
    ref["timing_seconds"] = {"import": round(t_import), "regime2": round(t_r2), "regime3": round(t_r3)}
    OUT.write_text(json.dumps(ref, indent=1, sort_keys=True) + "\n")
    print(f"wrote {OUT.name}; import {t_import:.0f}s, regime2 {t_r2:.0f}s, regime3 {t_r3:.0f}s",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
