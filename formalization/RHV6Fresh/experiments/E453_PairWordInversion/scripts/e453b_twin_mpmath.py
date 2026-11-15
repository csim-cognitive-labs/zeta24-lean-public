#!/usr/bin/env python3
"""E453 (b) — jumeau déterministe mpmath (30 chiffres) : 10 premiers par couple ; H1 inversion tangentielle du miroir,
H2 encadrement, mots de la Tour et du miroir, écart aux mots numpy (doivent être identiques)."""
import os, sys, json, math, numpy as np
from mpmath import mp, mpf, log, exp, atan, tan, floor, pi
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
mp.dps = 30
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
lg = Logger(os.path.join(OUT, "logs", "e453b.log"))
G, sha = load_zeros(lg)
N = 10**7
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
P = np.nonzero(sieve)[0]
idx = np.linspace(0, len(P)-1, 10).astype(int); Q = [int(P[i]) for i in idx]

def word_mp(beta, T, x):
    phi = atan(T/beta); s = (T*log(x) - phi)/pi; k = floor(s); return int(k), s-k, phi
def word_np(beta, T, x):
    phi = math.atan2(T, beta); s = (T*math.log(x) - phi)/math.pi; k = math.floor(s); return int(k)

res = []; viol = 0; max_gap = 0
for r_ in [1, 10, 100, 1000, 10000, 100000]:
    T = mpf(str(float(G[r_-1])))
    for b in ["0.3", "0.4", "0.45", "0.5"]:
        beta = mpf(b)
        for q in Q:
            kb, fb, phib = word_mp(beta, T, q); km, fm, phim = word_mp(1-beta, T, q)
            C0 = exp((phim + km*pi)/T); C1 = exp((phim + (km+1)*pi)/T)
            T_rec = pi/log(C1/C0); ph_rec = T_rec*log(C0) - km*pi; b_rec = T_rec/tan(ph_rec)
            h1 = max(abs(T_rec-T)/T, abs(b_rec-(1-beta)))
            h2 = abs(mpf(km)/log(q) - T/pi) <= (abs(phim)+pi)/(pi*log(q))
            kb_np = word_np(float(beta), float(T), q); km_np = word_np(1-float(beta), float(T), q)
            gap = abs(kb - kb_np) + abs(km - km_np)
            bad = (h1 > mpf("1e-20")) or (not h2) or gap != 0
            viol += int(bad); max_gap = max(max_gap, gap)
            res.append(dict(rank=r_, beta=b, q=q, k=kb, k_mirror=km, H1=float(h1), H2=bool(h2), word_gap_numpy=int(gap), ok=not bad))
lg(f"{len(res)} cas ; violations {viol} ; écart maximal des mots à numpy {max_gap}")
json.dump(dict(zeros_sha=sha, dps=30, cases=len(res), violations=viol, max_word_gap=max_gap, results=res),
          open(os.path.join(OUT, "data", "e453b_results.json"), "w"), indent=1)
