#!/usr/bin/env python3
"""E452 (b) — jumeau déterministe mpmath (30 chiffres) : sur 10 premiers par couple (mêmes 24 couples, même échantillon
graine 452), recalcul de k, k*, s, v, v* et vérification de H1, H3, H4 à 10^-25 ; écart aux valeurs numpy ≤ 10^-12."""
import os, sys, json, math, numpy as np
from mpmath import mp, mpf, log, exp, atan, floor, pi, sqrt, fabs
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
mp.dps = 30
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
lg = Logger(os.path.join(OUT, "logs", "e452b.log"))
G, sha = load_zeros(lg)
N = 10**7
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
P = np.nonzero(sieve)[0].astype(np.float64)
rng = np.random.default_rng(452)
S = np.sort(rng.choice(P, 100000, replace=False))
idx = np.linspace(0, len(S)-1, 10).astype(int)
lg(f"jumeau mpmath dps={mp.dps} ; 10 premiers par couple aux indices {idx.tolist()}")

def word_np(beta, T, x):
    phi = math.atan2(T, beta); s = (T*math.log(x) - phi)/math.pi; k = math.floor(s); f = s - k
    return k, f, ((-1.0)**k) * math.exp((phi + k*math.pi)/T)**beta / math.hypot(beta, T)
def word_mp(beta, T, x):
    phi = atan(T/beta); s = (T*log(x) - phi)/pi; k = int(floor(s)); f = s - k
    return k, f, ((-1)**k) * exp((phi + k*pi)/T)**beta / sqrt(beta*beta + T*T)

ranks = [1, 10, 100, 1000, 10000, 100000]
results = []; worst_np = 0.0; worst_id = mpf(0); viol = 0
for r_ in ranks:
    T = mpf(str(float(G[r_-1])))
    for beta in [mpf('0.3'), mpf('0.4'), mpf('0.45'), mpf('0.5')]:
        delta = atan(T/beta) - atan(T/(1-beta))
        for i in idx:
            x = mpf(int(S[i]))
            kb, fb, vb = word_mp(beta, T, x); km, fm, vm = word_mp(1-beta, T, x)
            s = int(floor(fb + delta/pi))
            h1 = (km == kb + s)
            h3 = ((vb*vm > 0) == (s == 0))
            h4 = fabs(fabs(vb+vm) - fabs(fabs(vb) + (-1)**s*fabs(vm))) / max(fabs(vb), fabs(vm))
            kb2, fb2, vb2 = word_np(float(beta), float(T), float(x)); km2, fm2, vm2 = word_np(1-float(beta), float(T), float(x))
            dnp = max(abs(float(vb) - vb2)/abs(vb2), abs(float(vm) - vm2)/abs(vm2))
            ok = h1 and h3 and h4 <= mpf('1e-25') and kb2 == kb and km2 == km and dnp <= 1e-12
            viol += (not ok); worst_np = max(worst_np, dnp); worst_id = max(worst_id, h4)
            results.append(dict(rank=r_, beta=float(beta), prime=int(x), k=kb, k_mirror=km, s=s, H1=h1, H3=h3,
                                H4_rel=float(h4), numpy_rel_gap=dnp, ok=bool(ok)))
lg(f"{len(results)} cas ; violations {viol} ; pire identité H4 {float(worst_id):.1e} ; pire écart numpy {worst_np:.1e}")
json.dump(dict(zeros_sha=sha, dps=mp.dps, cases=len(results), violations=viol, worst_H4=float(worst_id),
               worst_numpy_gap=worst_np, results=results), open(os.path.join(OUT, "data", "e452b_results.json"), "w"), indent=1)
