# -*- coding: utf-8 -*-
"""E441(b) — jumeau déterministe mpmath (30 chiffres) : indices de cellule de rencontre, encadrement, forme close de la
descente signée (M5) et encadrement M6 sur des sous-échantillons ; comparaison aux valeurs double précision d'E441(a)."""
import os, sys, math, json, numpy as np, mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e441b.log"))
mp.mp.dps = 30
G, sha = load_zeros(log)
BETA = mp.mpf("0.5"); RANKS = [1, 100, 1000, 10000, 100000, 1000000, 2001052]; N = 200000
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N ** 0.5) + 1):
    if sieve[i]: sieve[i * i::i] = False
P = np.flatnonzero(sieve).astype(np.int64); PR = P[P >= 3]
def stage_mp(T, x): return (T * mp.log(x) - mp.atan(T / BETA)) / mp.pi
def contact_mp(T, k): return mp.exp((mp.atan(T / BETA) + k * mp.pi) / T)
def stage64(T, x): return (float(T) * math.log(x) - math.atan2(float(T), 0.5)) / math.pi
res = {"sha256": sha, "dps": 30, "towers": {}}
for rank in RANKS:
    T = mp.mpf(repr(float(G[rank - 1]))); r = mp.exp(mp.pi / T)
    sample = list(PR[::997]) + [int(p) for p in PR[np.argsort(np.abs(np.array([stage64(T, p) for p in PR[:20000]]) - np.round([stage64(T, p) for p in PR[:20000]])))[:50]]]
    idx_mismatch = 0; bracket_viol = 0
    for p in sample:
        s = stage_mp(T, p); m = int(mp.floor(s)); m64 = int(math.floor(stage64(T, p)))
        if m != m64: idx_mismatch += 1
        if not (contact_mp(T, m) <= p < contact_mp(T, m + 1)): bracket_viol += 1
    # M5/M6 : séries (k₀, M) autour de rencontres de l'échantillon
    cf_err = mp.mpf(0); fl_err = mp.mpf(0); m6_viol = 0
    for p in sample[:40]:
        k0 = int(mp.floor(stage_mp(T, p)))
        for M in (1, 2, 3, 7, 20):
            L = [contact_mp(T, k0 + i + 1) - contact_mp(T, k0 + i) for i in range(M)]
            sl = mp.fsum([(-1) ** i * L[i] for i in range(M)])
            cf = L[0] * (1 - (-r) ** M) / (1 + r)
            fl = (L[0] - (-1) ** M * r * L[M - 1]) / (1 + r)
            cf_err = max(cf_err, abs(sl - cf) / max(abs(sl), mp.mpf("1e-300")))
            fl_err = max(fl_err, abs(sl - fl) / max(abs(sl), mp.mpf("1e-300")))
            # M6 : cellule k0+M−1 < rencontre q ⇒ L < q(r−1) ; cellule ≥ k0 ⇒ L > p(1 − 1/r)
            if not (L[0] > p * (1 - 1 / r)): m6_viol += 1
            qs = [int(x) for x in PR[np.searchsorted(PR, p):np.searchsorted(PR, p) + 400] if mp.floor(stage_mp(T, int(x))) >= k0 + M]
            if qs and not (L[M - 1] < qs[0] * (r - 1)): m6_viol += 1   # première rencontre dans une cellule ≥ k0+M
    res["towers"]["rank%d" % rank] = {"T": float(T), "sample": len(sample), "meeting_index_mismatch_vs_float64": idx_mismatch,
                                      "bracket_violations": bracket_viol, "M5_closed_form_relerr": float(cf_err),
                                      "M5_first_last_relerr": float(fl_err), "M6_violations": m6_viol}
    log("rang %d : échantillon %d, indices ≠ double %d, encadrement viol %d, M5 %.1e / %.1e, M6 viol %d" % (
        rank, len(sample), idx_mismatch, bracket_viol, float(cf_err), float(fl_err), m6_viol))
json.dump(res, open(os.path.join(OUT, "data", "e441b_twin.json"), "w"), indent=1)
log("terminé")
