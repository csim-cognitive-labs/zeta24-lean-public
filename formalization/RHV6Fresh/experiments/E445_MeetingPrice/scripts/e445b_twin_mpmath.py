# -*- coding: utf-8 -*-
"""E445(b) — jumeau à 30 chiffres : identité du prix (P1) et borne P5 sur un échantillon, pour les sept Tours."""
import os, sys, json, mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
mp.mp.dps = 30
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e445b.log"))
G, sha = load_zeros(log)
import sympy
PRIMES = [int(p) for p in sympy.primerange(3, 1000000)][::3001][:40]
RANKS = [1, 10, 100, 1000, 10000, 100000, 2000000]; EPS = mp.mpf(10) ** -26
out = {"dps": 30, "towers": {}}
for rank in RANKS:
    T = mp.mpf(repr(float(G[rank - 1]))); v = {}
    worst1 = mp.mpf(0)
    for bw in (mp.mpf("0.3"), mp.mpf("0.4"), mp.mpf("0.45")):
        for p in PRIMES:
            lhs = mp.mpf(p) ** bw + mp.mpf(p) ** (1 - bw); rhs = 2 * mp.sqrt(p) * mp.cosh((bw - mp.mpf(1) / 2) * mp.log(p))
            worst1 = max(worst1, abs(lhs - rhs) / lhs)
    v["P1_max_rel_dev"] = mp.nstr(worst1, 5); v["P1_ok"] = bool(worst1 < EPS)
    # P5 : bilan pondéré borné (β = ½), pentes de cellule remplacées par des pentes test ±D (le théorème vaut pour toute suite bornée)
    b = mp.mpf(1) / 2; ph = mp.atan(T / b); nrm = mp.sqrt(b ** 2 + T ** 2); q = mp.exp(b * mp.pi / T)
    contact = lambda k: mp.exp((ph + k * mp.pi) / T); value = lambda k: (-1) ** int(k) * contact(k) ** b / nrm
    ok5 = True; worst5 = mp.mpf(0)
    for k0 in (0, 7, 40):
        for m in (0, 3, 20):
            d = [((-1) ** (j * j // 2 % 2)) * mp.mpf(1 + (j * 7) % 5) for j in range(m + 1)]; D = max(abs(x) for x in d)
            s = mp.fsum(value(k0 + j) * d[j] for j in range(m + 1)); bound = abs(value(k0 + m)) * D * q / (q - 1)
            r = abs(s) / bound; worst5 = max(worst5, r); ok5 = ok5 and r <= 1
    v["P5_max_ratio"] = mp.nstr(worst5, 5); v["P5_ok"] = ok5
    out["towers"][str(rank)] = v; log("rang %d : %s" % (rank, json.dumps(v)))
out["all_ok"] = all(v["P1_ok"] and v["P5_ok"] for v in out["towers"].values()); log("all_ok = %s" % out["all_ok"])
json.dump(out, open(os.path.join(OUT, "data", "e445b_twin.json"), "w"), indent=1)
