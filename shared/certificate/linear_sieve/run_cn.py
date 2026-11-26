import sys, os, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cn_certify as cc
from decimal import getcontext
KS = [int(x) for x in sys.argv[1].split(",")]
t = time.time(); CO = cc.certify(500); print("certify", round(time.time()-t), flush=True)
getcontext().prec = 40
old, new = cc.make_steps(CO, 500)
out = {}
for k in KS:
    for name, st in (("old", old), ("new", new)):
        r = cc.run(k, st)
        out[f"{k}:{name}"] = None if r is None else {"C1": str(r[0]), "C2": str(r[1]), "C1_hi": str(r[0].numerator // r[0].denominator + 1) if False else None}
        if r is not None:
            out[f"{k}:{name}"] = {"C1_num": r[0].numerator, "C1_den": r[0].denominator, "C2_num": r[1].numerator, "C2_den": r[1].denominator,
                                  "C1_up": cc._up(r[0], 3), "C2_up": cc._up(r[1], 3)}
        print(k, name, out[f"{k}:{name}"] and (out[f"{k}:{name}"]["C1_up"], out[f"{k}:{name}"]["C2_up"]), flush=True)
        json.dump(out, open(f"cn_rows_{sys.argv[1].replace(',','_')}.json", "w"))
print("DONE", round(time.time()-t), flush=True)
