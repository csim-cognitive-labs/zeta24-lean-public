# -*- coding: utf-8 -*-
"""E450(c) — jumeau déterministe de e450b à 30 chiffres (mpmath), rangs 1 et 100, β = 0,4, 2 000 premiers ≥ 10^3 (sympy) :
H1, H2, H3, H4, H5 ; seuils 10^-25 sur les identités, 0 violation sur les encadrements."""
import os, sys, json, mpmath as mp, sympy
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
mp.mp.dps = 30
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
lg = Logger(os.path.join(OUT, "logs", "e450b_twin.log"))
G, sha = load_zeros(lg)
primes = [mp.mpf(p) for p in list(sympy.primerange(1000, 10 ** 6))[:2000]]
B = mp.mpf("0.4"); TOL = mp.mpf("1e-25"); pi = mp.pi
def member(b, T, x):
    ph = mp.atan2(T, b); n = mp.sqrt(b * b + T * T); s = (T * mp.log(x) - ph) / pi; k = mp.floor(s); f = s - k
    C = mp.exp((ph + k * pi) / T); return ph, n, k, f, C ** b / n, x ** b * mp.exp(-b * pi * f / T) / n
res = {"dps": 30, "beta": float(B), "primes": len(primes), "cases": []}; all_ok = True
for r in [1, 100]:
    T = mp.mpf(repr(float(G[r - 1])))
    e1 = e2 = e3 = e5 = mp.mpf(0); kd = 0; nd = 0; v4 = 0; fmin = mp.mpf(1); fmax = mp.mpf(0)
    for x in primes:
        ph, n1, k1, f1, v1, w1 = member(B, T, x); ph2, n2, k2, f2, v2, w2 = member(1 - B, T, x); sh = ph - ph2
        e1 = max(e1, abs(v1 - w1) / w1, abs(v2 - w2) / w2)
        d = abs(f2 - mp.frac(f1 + sh / pi)); e2 = max(e2, min(d, 1 - d)); kd = max(kd, int(abs(k2 - k1))); nd += int(k2 != k1)
        feff = B * f1 + (1 - B) * f2; fmin = min(fmin, feff); fmax = max(fmax, feff)
        e3 = max(e3, abs(v1 * v2 - x * mp.exp(-pi * feff / T) / (n1 * n2)) / (v1 * v2))
        lo = mp.exp(-pi / T) * (x ** B / n1 + x ** (1 - B) / n2); hi = x ** B / n1 + x ** (1 - B) / n2
        v4 += int(not (lo <= v1 + v2 <= hi))
        e5 = max(e5, abs(v1 / v2 - x ** (2 * B - 1) * mp.exp(-pi * (B * f1 - (1 - B) * f2) / T) * n2 / n1) / (v1 / v2))
    ok = bool(e1 <= TOL and e2 <= TOL and kd <= 1 and e3 <= TOL and fmin >= 0 and fmax < 1 and v4 == 0 and e5 <= TOL)
    all_ok &= ok
    c = {"rank": r, "T": float(T), "H1": float(e1), "H2": float(e2), "word_diff_max": kd, "word_differ": nd, "H3": float(e3),
         "feff": [float(fmin), float(fmax)], "H4_viol": v4, "H5": float(e5), "ok": ok}
    res["cases"].append(c); lg("rang %d : %s" % (r, c))
res["all_ok"] = bool(all_ok)
json.dump(res, open(os.path.join(OUT, "data", "e450b_twin.json"), "w"), indent=1)
lg("FIN e450b_twin all_ok=%s" % all_ok)
