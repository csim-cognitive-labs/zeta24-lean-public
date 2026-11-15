# -*- coding: utf-8 -*-
"""E447(a) — mécanisme de cassure sur la ligne (β = 1/2), §19.69. Pour 7 hauteurs réelles : (a) résidu de l'identité
d'Abel (valueCellSum_abel_signed) sur des blocs de 50 cellules à chaque décade ; (b) amplitude exacte à la cassure
(line_break_amplitude_exact) et encadrement (line_break_amplitude_bounds) sur les premiers ; (c) |v_k R(C_k)| / C_k^{3/2}
par décade (line_weighted_demand_at_contact_small) ; (d) cassure puis descente (break_then_descent) sur les cellules à un
seul poids premier. Premiers ≤ 10^7. Jumeau : e447b_twin_mpmath.py. Une Tour à la fois, aucun objet spectral, aucun OFF."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e447a.log"))
G, sha = load_zeros(log)
RANKS = [1, 10, 100, 1000, 10000, 100000, 2000000]; N = 10_000_000; BETA = 0.5; XMIN = 1000.0
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N ** 0.5) + 1):
    if sieve[i]: sieve[i * i::i] = False
P = np.flatnonzero(sieve).astype(np.int64)
lam = np.zeros(N + 1)
for p in P:
    q = p
    while q <= N:
        lam[q] = math.log(p); q *= p
PS = np.cumsum(lam)                      # ψ(n) aux entiers
NW = np.cumsum(lam > 0)                  # nombre d'entiers à poids non nul ≤ n
NPR = np.cumsum(sieve)                   # nombre de premiers ≤ n
log("premiers ≤ %d : %d" % (N, len(P)))
def phase(T, b): return math.atan2(T, b)
res = {"zeros": int(len(G)), "sha256": sha, "N": N, "beta": BETA, "towers": []}
rng = np.random.default_rng(447)
for rank in RANKS:
    T = float(G[rank - 1]); ph = phase(T, BETA); norm = math.sqrt(BETA ** 2 + T ** 2); rho = math.exp(BETA * math.pi / T)
    out = {"rank": rank, "T": T}
    kmin = int(math.ceil((T * math.log(XMIN) - ph) / math.pi)); kmax = int(math.floor((T * math.log(N) - ph) / math.pi))
    K = np.arange(kmin, kmax + 1, dtype=np.int64)
    C = np.exp((ph + K * math.pi) / T)                     # contacts
    R = PS[np.floor(C).astype(np.int64)] - C               # rawDemand aux contacts
    V = np.where(K % 2 == 0, 1.0, -1.0) * np.sqrt(C) / norm  # contactRealValue sur la ligne
    D = R[1:] - R[:-1]                                     # cellDemand
    out["n_cells"] = int(len(D))
    # (a) Abel sur blocs de 50 cellules au début de chaque décade
    abel = []
    for dec in [3, 4, 5, 6]:
        x0 = 10.0 ** dec; i0 = int(np.searchsorted(C, x0)); M = 50
        if i0 + M >= len(C): continue
        lhs = float(np.sum(V[i0:i0 + M] * D[i0:i0 + M]))
        rhs = float(V[i0 + M] * R[i0 + M] - V[i0] * R[i0] + (1 + rho) * np.sum(V[i0:i0 + M] * R[i0 + 1:i0 + M + 1]))
        scale = float(np.max(np.abs(V[i0:i0 + M + 1] * R[i0:i0 + M + 1]))) + 1e-300
        abel.append({"decade": dec, "k0": int(K[i0]), "lhs": lhs, "rhs": rhs, "rel_residual": abs(lhs - rhs) / scale,
                     "telescope_residual": abs(float(np.sum(D[i0:i0 + M])) - float(R[i0 + M] - R[i0]))})
    out["abel"] = abel
    # (b) amplitude exacte à la cassure sur un échantillon de premiers
    Pq = P[P >= XMIN]; samp = np.sort(rng.choice(Pq, size=min(100000, len(Pq)), replace=False))
    s = (T * np.log(samp) - ph) / math.pi; k = np.floor(s).astype(np.int64); f = s - k
    Ck = np.exp((ph + k * math.pi) / T); vdir = np.sqrt(Ck) / norm
    vex = np.sqrt(samp) * np.exp(-math.pi * f / (2 * T)) / norm
    lo = np.sqrt(samp) * math.exp(-math.pi / (2 * T)) / norm; hi = np.sqrt(samp) / norm
    out["amp_max_rel_err"] = float(np.max(np.abs(vdir - vex) / vex))
    out["amp_bounds_violations"] = int(np.sum((vdir <= lo) | (vdir > hi)))
    out["amp_sample"] = int(len(samp))
    out["amp_ratio_to_sqrt_q_minmax"] = [float(np.min(vdir * norm / np.sqrt(samp))), float(np.max(vdir * norm / np.sqrt(samp)))]
    out["exp_minus_pi_over_2T"] = math.exp(-math.pi / (2 * T))
    # (c) demande pondérée aux contacts / C^{3/2} par décade
    wd = []
    for dec in [3, 4, 5, 6]:
        sel = (C >= 10.0 ** dec) & (C < 10.0 ** (dec + 1))
        if sel.sum() == 0: continue
        val = np.abs(V[sel] * R[sel]) / (C[sel] ** 1.5)
        wd.append({"decade": dec, "cells": int(sel.sum()), "max": float(np.max(val)), "mean": float(np.mean(val)),
                   "max_R_over_C": float(np.max(np.abs(R[sel]) / C[sel]))})
    out["weighted_demand"] = wd
    # (d) cassure puis descente : cellules dont ]⌊C_k⌋, ⌊C_{k+1}⌋] contient exactement un entier à poids, premier
    fl = np.floor(C).astype(np.int64)
    nw = NW[fl[1:]] - NW[fl[:-1]]; npr = NPR[fl[1:]] - NPR[fl[:-1]]
    solo = np.flatnonzero((nw == 1) & (npr == 1))
    out["solo_cells"] = int(len(solo))
    if len(solo):
        sub = solo if len(solo) <= 200000 else np.sort(rng.choice(solo, size=200000, replace=False))
        # le premier q de la cellule : seul premier dans ]fl_k, fl_{k+1}]
        qidx = NPR[fl[sub]]                                  # index du premier suivant dans P
        q = P[qidx].astype(np.float64)
        lhs = (PS[P[qidx]] - q) - R[sub]
        rhs = np.log(q) - (q - C[sub])
        out["solo_checked"] = int(len(sub)); out["solo_max_abs_err"] = float(np.max(np.abs(lhs - rhs)))
        out["solo_strict_ok"] = bool(np.all(C[sub] < q))
    res["towers"].append(out)
    log("rang %d T=%.4f cellules=%d | Abel rel max=%.2e | amp err max=%.2e viol=%d | solo=%d err=%.2e" % (
        rank, T, out["n_cells"], max([a["rel_residual"] for a in abel] or [0]), out["amp_max_rel_err"],
        out["amp_bounds_violations"], out["solo_cells"], out.get("solo_max_abs_err", -1)))
json.dump(res, open(os.path.join(OUT, "data", "e447a_results.json"), "w"), indent=1)
log("FIN e447a")
