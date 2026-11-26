"""Drivers for the Brun block Regime 2 certificate (regime2_brun.certify_brun_slab).

ladder E0 E1 OUT [Ms] [as] [small|big]   (E0 may be xNNN, a literal X_lo) contiguous greedy ladder from 10^E0 to exactly 10^E1 (widest slab that
                             certifies, best net over the (M, a) grid); writes OUT (json, exact endpoints)
probe  E_LIST WIDTH OUT Ms as small|big   one slab [10^e, 10^e * WIDTH) per e (WIDTH a fraction like 10 or 11/10),
                             wide grid, best net or the failure; for the exploration up and down
Ms / as: comma lists or ranges "24-30".
"""
import sys, os, json, time
from decimal import Decimal
from fractions import Fraction
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from all_even_1p4_ext import regime2_brun as RB

MULTS = [Fraction(10**10), Fraction(10**5), Fraction(100), Fraction(10), Fraction(5), Fraction(2),
         Fraction(5, 4), Fraction(11, 10), Fraction(101, 100)]

LOW_SMALL = ((1,), (3,), (5,), (7,), (9,), (11,), (13,), (3, 7), (5, 9), (7, 11), (9, 13), (11, 13), (11, 15), (9, 13, 15))
UP_SMALL = ((0,), (2,), (4,), (6,), (2, 4), (2, 6), (4, 6), (4, 8), (6, 8), (2, 4, 6), (4, 8, 10), (4, 6, 10), (4, 8, 12), (4, 6, 10, 12))
LOW_BIG = RB.LOW_CAPS + ((11, 15, 17), (13, 17), (13, 17, 19))
UP_BIG = RB.UPP_CAPS + ((4, 6, 8, 12), (4, 6, 10, 14), (4, 8, 12, 14), (2, 4, 8, 12))


def rng(s):
    out = []
    for part in s.split(','):
        if '-' in part:
            a, b = part.split('-'); out += list(range(int(a), int(b) + 1))
        else:
            out.append(int(part))
    return out


def fmt(x):
    return f"{Decimal(str(RB.ln_iv(RB.Iv(x)).lo)) / Decimal(str(RB.ln_iv(RB.Iv(10)).hi)):.3f}"


def job(args):
    x_lo, x_hi, M, a, caps = args
    kw = {} if caps is None else dict(low_caps=caps[0], up_caps=caps[1])
    t = time.time()
    r = RB.try_brun(x_lo, x_hi, M, a, **kw)
    if r is None:
        return None
    return dict(x_lo=str(x_lo), x_hi=str(x_hi), M=M, a=a, z=r.z, y=r.y, low_caps=r.low_caps, low_ends=r.low_ends,
                up_caps=r.up_caps, up_ends=r.up_ends, E_minus_hi=str(r.e_minus.hi), E_plus_hi=str(r.e_plus.hi),
                bracket_lo=str(r.bracket.lo), main_lo=str(r.main.lo), err_a_hi=str(r.err_a.hi),
                err_aq_hi=str(r.err_aq.hi), err_q2_hi=str(r.err_q2.hi), err_hi=str(r.err_total.hi),
                net_lo=str(r.net.lo), n_d_low=str(r.n_d_low), n_d_up=str(r.n_d_up), sec=f"{time.time() - t:.1f}")


def best(P, x_lo, x_hi, Ms, As, caps=None):
    res = [r for r in P.map(job, [(x_lo, x_hi, M, a, caps) for M in Ms for a in As], chunksize=1) if r]
    return max(res, key=lambda r: Decimal(r['net_lo'])) if res else None


def ladder(e0, e1, out, Ms, As, caps=None):
    x = int(e0[1:]) if str(e0).startswith('x') else 10 ** int(e0)
    start = x
    end, L, i = 10 ** int(e1), [], 0
    with Pool(os.cpu_count()) as P:
        while x < end:
            for m in MULTS:
                xh = min(x * m.numerator // m.denominator, end)
                if xh <= x:
                    continue
                r = best(P, x, xh, Ms, As, caps)
                if r:
                    i += 1; r['slab'] = i; L.append(r)
                    print(f"slab {i}: [10^{fmt(x)}, 10^{fmt(xh)}) M={r['M']} a={r['a']} low={r['low_caps']} "
                          f"up={r['up_caps']} E-<={Decimal(r['E_minus_hi']):.2e} E+<={Decimal(r['E_plus_hi']):.3e} "
                          f"main>={Decimal(r['main_lo']):.4e} err<={Decimal(r['err_hi']):.2e} net>={Decimal(r['net_lo']):.4e}",
                          flush=True)
                    json.dump(L, open(out, 'w'), indent=0)
                    x = xh
                    break
            else:
                print(f"STOP at 10^{fmt(x)}", flush=True)
                return
    if not L or L[0]['x_lo'] != str(start) or L[-1]['x_hi'] != str(end):
        raise RuntimeError("ladder does not run from the requested start to the requested end")
    for u, v in zip(L, L[1:]):
        if u['x_hi'] != v['x_lo']:
            raise RuntimeError(f"gap between slabs {u['slab']} and {v['slab']}")
    print(f"DONE {len(L)} slabs from {L[0]['x_lo'][:4]}.. to 10^{fmt(int(L[-1]['x_hi']))}, contiguous (checked), "
          f"least net {min(Decimal(r['net_lo']) for r in L):.4e}", flush=True)


def probe(es, width, out, Ms, As, which):
    caps = (LOW_SMALL, UP_SMALL) if which == 'small' else (LOW_BIG, UP_BIG)
    w = Fraction(width)
    R = []
    with Pool(os.cpu_count()) as P:
        for e in es:
            x = int(e[1:]) if e.startswith('x') else 10 ** int(e)
            xh = x * w.numerator // w.denominator
            t = time.time()
            r = best(P, x, xh, Ms, As, caps)
            print(f"e={e} w={width}: " + ("NOT certified" if r is None else
                  f"M={r['M']} a={r['a']} low={r['low_caps']} up={r['up_caps']} E+<={Decimal(r['E_plus_hi']):.3e} "
                  f"main>={Decimal(r['main_lo']):.4e} err<={Decimal(r['err_hi']):.2e} net>={Decimal(r['net_lo']):.4e}")
                  + f" t={time.time() - t:.0f}s", flush=True)
            R.append(dict(e=e, width=width, result=r))
            json.dump(R, open(out, 'w'), indent=0)
    print("DONE", flush=True)


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'ladder':
        cp = None
        if len(sys.argv) > 7:
            cp = (LOW_SMALL, UP_SMALL) if sys.argv[7] == 'small' else (LOW_BIG, UP_BIG)
        ladder(sys.argv[2], int(sys.argv[3]), sys.argv[4], rng(sys.argv[5]) if len(sys.argv) > 5 else rng('25-29'),
               rng(sys.argv[6]) if len(sys.argv) > 6 else rng('6-9'), cp)
    elif cmd == 'probe':
        es = sys.argv[2].split(',')   # exponents, or xNNN for a literal X_lo
        probe(es, sys.argv[3], sys.argv[4], rng(sys.argv[5]), rng(sys.argv[6]), sys.argv[7])
