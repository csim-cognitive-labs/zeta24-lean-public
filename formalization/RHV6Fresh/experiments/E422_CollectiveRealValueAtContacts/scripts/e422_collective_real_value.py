# -*- coding: utf-8 -*-
"""E422 — somme collective des valeurs réelles aux positions des contacts. Aucune donnée arithmétique."""
import os, sys, math, json, numpy as np, mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import load_zeros, Logger, contacts_in, CHUNK
phase = lambda b, T: np.arctan2(T, b)
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e422.log"))
G, sha = load_zeros(log)
A, X = 100.0, 1000.0; RANKS = [1, 2, 3, 100, 1000]; NS = [10, 100, 1000, 10000, 100000, 2001052]
def sum_raw_many(xs, gam):
    """Σ_j 2Re(x^ρ_j/ρ_j) pour chaque x de xs, ρ_j = ½ + iγ_j ; retourne tableau (len xs)."""
    lx = np.log(xs); out = np.zeros(len(xs)); B = 32
    for i in range(0, len(gam), CHUNK):
        rho = 0.5 + 1j * gam[i:i + CHUNK]
        for j in range(0, len(xs), B):
            out[j:j + B] += (2.0 * np.real(np.exp(np.outer(lx[j:j + B], rho)) / rho)).sum(axis=1)
    return out
res = {}
for rk in RANKS:
    T = float(G[rk - 1]); k, C = contacts_in(0.5, T, A, X)
    own = 2 * ((-1.0) ** k) * C ** 0.5 / math.hypot(0.5, T)
    prev = None; per = dict(T=T, n_contacts=int(len(C)), rms_valeur_propre=float(np.sqrt(np.mean(own ** 2))), par_N={})
    for N in NS:
        S = sum_raw_many(C, G[:N].astype(float))
        rest = S - own
        gam = G[:N].astype(float); mask = np.arange(N) != (rk - 1)
        # histogramme des phases des autres Tours à x : sous-échantillon déterministe (≤ 2000 Tours, ≤ 50 contacts)
        others = gam[mask]; sel = others[:: max(1, len(others) // 2000)]; Csel = C[:: max(1, len(C) // 50)]
        fr = np.mod(np.outer(np.log(Csel), sel) - phase(0.5, sel)[None, :], math.pi) / math.pi
        h, _ = np.histogram(fr, bins=10, range=(0, 1))
        d = dict(part_propre_mediane=float(np.median(np.abs(own) / np.abs(S))), part_propre_max=float(np.max(np.abs(own) / np.abs(S))),
                 accord_signe=float(np.mean(np.sign(own) == np.sign(S))), rms_S=float(np.sqrt(np.mean(S ** 2))),
                 rms_reste=float(np.sqrt(np.mean(rest ** 2))), max_abs_S=float(np.max(np.abs(S))),
                 rms_variation_vs_N_precedent=(float(np.sqrt(np.mean((S - prev) ** 2))) if prev is not None else None),
                 histogramme_phase_autres=h.tolist(), S_aux_contacts=S.tolist() if len(S) <= 20 else S[:20].tolist())
        per["par_N"][N] = d; prev = S
        log("rang %d, N=%d : part propre méd. %.3e, accord signe %.2f, rms S %.3f, rms reste %.3f, var vs N préc. %s" % (rk, N, d["part_propre_mediane"], d["accord_signe"], d["rms_S"], d["rms_reste"], d["rms_variation_vs_N_precedent"]))
    res[rk] = per
# jumeau mpmath : N = 100, 3 contacts de la Tour 1
mp.mp.dps = 25; T = float(G[0]); k, C = contacts_in(0.5, T, A, X); tw = []
for x in C[:3]:
    s = mp.mpf(0)
    for g in G[:100]:
        r = mp.mpc(0.5, float(g)); s += 2 * (mp.exp(r * mp.log(mp.mpf(x))) / r).real
    tw.append(float(s))
S100 = sum_raw_many(C[:3], G[:100].astype(float))
res["jumeau_mpmath_N100_tour1_max_err"] = float(np.max(np.abs(S100 - np.array(tw))))
log("jumeau mpmath : %.2e" % res["jumeau_mpmath_N100_tour1_max_err"])
json.dump(res, open(os.path.join(OUT, "data", "e422_collective.json"), "w"), indent=1)
log("terminé")
