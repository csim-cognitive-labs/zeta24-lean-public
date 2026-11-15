# -*- coding: utf-8 -*-
"""E450(a) — K0, recensement sur la ligne (β = 1/2), §19.72. Six zéros (rangs 1, 10, 100, 1000, 10000, 100000) et trois
contrôles (milieux entre zéros consécutifs, rangs 1–2, 100–101, 10000–10001), premiers ≤ 10^7 : statistiques du mot
(fractions de cellule aux premiers ; part des paires consécutives en même cellule par décade), de la suite des amplitudes
(rapport |v|·‖ρ‖/√q, min/max), et bilan pondéré valueCellSum sur blocs de 50 cellules par décade normalisé par la borne P5
(E445). Critère H6 : les plages des zéros et des contrôles se recouvrent. Aucune obligation n'en est tirée (R-E446)."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
lg = Logger(os.path.join(OUT, "logs", "e450a.log"))
G, sha = load_zeros(lg)
RANKS = [1, 10, 100, 1000, 10000, 100000]; CTRL = [1, 100, 10000]; N = 10_000_000; BETA = 0.5; XMIN = 1000.0
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N ** 0.5) + 1):
    if sieve[i]: sieve[i * i::i] = False
P = np.flatnonzero(sieve).astype(np.int64)
lam = np.zeros(N + 1)
for p in P:
    q = p
    while q <= N:
        lam[q] = math.log(p); q *= p
PS = np.cumsum(lam)
lg("premiers ≤ %d : %d" % (N, len(P)))
Pq = P[P >= XMIN].astype(np.float64); Lq = np.log(Pq)
def census(T, label):
    ph = math.atan2(T, BETA); norm = math.sqrt(BETA ** 2 + T ** 2); rho = math.exp(BETA * math.pi / T)
    s = (T * Lq - ph) / math.pi; k = np.floor(s); f = s - k
    out = {"label": label, "T": T, "f_mean": float(f.mean()), "f_min": float(f.min()), "f_max": float(f.max()),
           "amp_over_sqrt_min": float(np.exp(-math.pi * f / (2 * T)).min()),
           "amp_over_sqrt_max": float(np.exp(-math.pi * f / (2 * T)).max()), "same_cell_share": [], "abel_norm": []}
    for dec in [3, 4, 5, 6]:
        sel = (Pq >= 10.0 ** dec) & (Pq < 10.0 ** (dec + 1)); idx = np.flatnonzero(sel)
        if len(idx) < 2: continue
        same = float(np.mean(k[idx[1:]] == k[idx[:-1]]))
        out["same_cell_share"].append({"decade": dec, "pairs": int(len(idx) - 1), "same_cell": same})
    kmin = int(math.ceil((T * math.log(XMIN) - ph) / math.pi)); kmax = int(math.floor((T * math.log(N) - ph) / math.pi))
    K = np.arange(kmin, kmax + 1, dtype=np.int64); C = np.exp((ph + K * math.pi) / T)
    R = PS[np.floor(C).astype(np.int64)] - C; V = np.where(K % 2 == 0, 1.0, -1.0) * np.sqrt(C) / norm; D = R[1:] - R[:-1]
    for dec in [3, 4, 5, 6]:
        i0 = int(np.searchsorted(C, 10.0 ** dec)); M = 50
        if i0 + M >= len(C): continue
        lhs = float(np.sum(V[i0:i0 + M] * D[i0:i0 + M])); Dmax = float(np.max(np.abs(D[i0:i0 + M])))
        bound = abs(V[i0 + M - 1]) * Dmax * rho / (rho - 1)
        out["abel_norm"].append({"decade": dec, "valueCellSum": lhs, "P5_bound": float(bound), "ratio": abs(lhs) / bound if bound > 0 else None})
    lg("%s T=%.4f f̄=%.4f amp/√q∈[%.6f,%.6f] même cellule=%s |bilan|/P5=%s" % (label, T, out["f_mean"], out["amp_over_sqrt_min"],
        out["amp_over_sqrt_max"], ["%.4f" % a["same_cell"] for a in out["same_cell_share"]], ["%.3f" % a["ratio"] for a in out["abel_norm"]]))
    return out
res = {"zeros": int(len(G)), "sha256": sha, "N": N, "beta": BETA, "towers": [], "controls": []}
for r in RANKS: res["towers"].append(census(float(G[r - 1]), "zéro rang %d" % r))
for r in CTRL: res["controls"].append(census(0.5 * (float(G[r - 1]) + float(G[r])), "contrôle milieu rangs %d-%d" % (r, r + 1)))
# H6 : recouvrement des plages par statistique
def rng(lst, key): v = [x[key] for x in lst]; return (min(v), max(v))
comp = {}
for key in ["f_mean", "amp_over_sqrt_min", "amp_over_sqrt_max"]:
    z = rng(res["towers"], key); c = rng(res["controls"], key)
    comp[key] = {"zeros": z, "controls": c, "overlap": bool(max(z[0], c[0]) <= min(z[1], c[1]))}
zs = [a["same_cell"] for t in res["towers"] for a in t["same_cell_share"]]; cs = [a["same_cell"] for t in res["controls"] for a in t["same_cell_share"]]
comp["same_cell_share"] = {"zeros": (min(zs), max(zs)), "controls": (min(cs), max(cs)), "overlap": bool(max(min(zs), min(cs)) <= min(max(zs), max(cs)))}
zr = [a["ratio"] for t in res["towers"] for a in t["abel_norm"]]; cr = [a["ratio"] for t in res["controls"] for a in t["abel_norm"]]
comp["abel_ratio"] = {"zeros": (min(zr), max(zr)), "controls": (min(cr), max(cr)), "overlap": bool(max(min(zr), min(cr)) <= min(max(zr), max(cr)))}
res["comparison"] = comp; res["H6_all_overlap"] = bool(all(v["overlap"] for v in comp.values()))
lg("H6 recouvrement par statistique : %s ; tout recouvre = %s" % ({k: v["overlap"] for k, v in comp.items()}, res["H6_all_overlap"]))
json.dump(res, open(os.path.join(OUT, "data", "e450a_results.json"), "w"), indent=1)
lg("FIN e450a")
