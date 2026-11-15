# -*- coding: utf-8 -*-
"""E444(b) — jumeau déterministe à 30 chiffres (mpmath) des contrôles B2, B3, B4, B7 et des déplacements de phase R9,
sur un échantillon de rencontres par Tour. Aucune dépendance à e444a sinon les mêmes données (zéros d'Odlyzko, premiers)."""
import os, sys, math, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
import mpmath as mp
mp.mp.dps = 30
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e444b.log"))
G, sha = load_zeros(log)
RANKS = [1, 10, 100, 1000, 10000, 100000, 2000000]; BETA = mp.mpf(1) / 2; BETAS_ALT = [mp.mpf(x) for x in ("0.1", "0.3", "0.7", "0.9", "1")]
import sympy
PRIMES = [int(p) for p in sympy.primerange(3, 1000000)]
SAMPLE = PRIMES[::1571][:50]
out = {"dps": 30, "sha256": sha, "towers": {}}
EPS = mp.mpf(10) ** (-mp.mp.dps + 2)   # budget explicite à 30 chiffres : annulation de T·log p et sensibilité de tan près de π/2
for rank in RANKS:
    T = mp.mpf(repr(float(G[rank - 1]))); ph = mp.atan(T / BETA); nrm = mp.sqrt(BETA ** 2 + T ** 2)
    stage = lambda x, b=BETA: (T * mp.log(x) - mp.atan(T / b)) / mp.pi
    contact = lambda k: mp.exp((ph + k * mp.pi) / T)
    value = lambda k: (-1) ** int(k) * contact(k) ** BETA / nrm
    v = {}
    # B2
    worst2 = mp.mpf(0)
    for p in SAMPLE:
        s = stage(p); mcell = mp.floor(s)
        b = T / mp.tan(T * mp.log(p) - mp.pi * s); worst2 = max(worst2, abs(b - BETA))
    tol2 = EPS * T * T * mp.log(1000000)
    v["B2_max_abs_dev"] = mp.nstr(worst2, 5); v["B2_budget"] = mp.nstr(tol2, 5); v["B2_ok"] = bool(worst2 < tol2)
    # B3 sur 50 cellules
    worst3T = mp.mpf(0); worst3b = mp.mpf(0)
    for k in range(0, 500, 10):
        L0 = contact(k + 1) - contact(k); L1 = contact(k + 2) - contact(k + 1)
        worst3T = max(worst3T, abs(mp.pi / mp.log(L1 / L0) - T) / T)
        worst3b = max(worst3b, abs(mp.log(abs(value(k + 1)) / abs(value(k))) / mp.log(L1 / L0) - BETA))
    tol3 = EPS * (contact(500) / (contact(501) - contact(500))) * T / mp.pi
    v["B3_max_rel_dev_T"] = mp.nstr(worst3T, 5); v["B3_max_abs_dev_beta"] = mp.nstr(worst3b, 5); v["B3_budget"] = mp.nstr(tol3, 5); v["B3_ok"] = bool(worst3T < tol3 and worst3b < tol3)
    # B4 : forme close M = 50, k0 = 3
    q = mp.exp((BETA + 1) * mp.pi / T); k0 = 3; M = 50
    direct = mp.fsum(value(k0 + i) * (contact(k0 + i + 1) - contact(k0 + i)) for i in range(M))
    closed = value(k0) * (contact(k0 + 1) - contact(k0)) * (1 - (-q) ** M) / (1 + q)
    d4 = abs(direct - closed) / abs(direct); v["B4_rel_dev"] = mp.nstr(d4, 5); v["B4_ok"] = bool(d4 < tol3)
    # B7 : β lu depuis deux rencontres consécutives de l'échantillon (déplacement > 0)
    worst7 = mp.mpf(0); n7 = 0
    for p, p2 in zip(SAMPLE[:-1], SAMPLE[1:]):
        m1 = int(mp.floor(stage(p))); m2 = int(mp.floor(stage(p2)))
        if m2 > m1:
            b = T * mp.log(abs(value(m2)) / abs(value(m1))) / ((m2 - m1) * mp.pi); worst7 = max(worst7, abs(b - BETA)); n7 += 1
    v["B7_max_abs_dev"] = mp.nstr(worst7, 5); v["B7_count"] = n7; v["B7_ok"] = bool(worst7 < EPS)
    # R9 : déplacement de phase prédit, en cellules
    v["R9_phase_shift_cells"] = {mp.nstr(b2, 3): mp.nstr(abs(ph - mp.atan(T / b2)) / mp.pi, 12) for b2 in BETAS_ALT}
    out["towers"][str(rank)] = v
    log("rang %d : %s" % (rank, json.dumps(v)))
out["all_ok"] = all(v[k] for v in out["towers"].values() for k in ("B2_ok", "B3_ok", "B4_ok", "B7_ok"))
log("all_ok = %s" % out["all_ok"])
json.dump(out, open(os.path.join(OUT, "data", "e444b_twin.json"), "w"), indent=1)
log("fin")
