# -*- coding: utf-8 -*-
"""E448(a) — suite des amplitudes de paiement d'une Tour de la ligne (β = 1/2), §19.70. Pour 7 hauteurs réelles, sur les
premiers consécutifs ≤ 10^7 : (a) orbite de la fraction de cellule (cellFraction_step) ; (b) rapport des amplitudes sous
ses deux formes (line_break_amplitude_ratio_cells / _exact) contre le calcul direct ; (c) violations de monotonie et
d'encadrement (attendu 0) ; (d) paires de premiers consécutifs dans une même cellule, par décade ; (e) télescopage par
décade (line_break_amplitude_telescope). Jumeau : e448b_twin_mpmath.py. Une Tour à la fois, aucun objet spectral, aucun OFF."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
lg = Logger(os.path.join(OUT, "logs", "e448a.log"))
G, sha = load_zeros(lg)
RANKS = [1, 10, 100, 1000, 10000, 100000, 2000000]; N = 10_000_000; BETA = 0.5
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N ** 0.5) + 1):
    if sieve[i]: sieve[i * i::i] = False
P = np.flatnonzero(sieve).astype(np.float64)
lg("premiers ≤ %d : %d" % (N, len(P)))
LP = np.log(P); DLOG = LP[1:] - LP[:-1]            # log(p_{n+1}/p_n)
dec = np.floor(np.log10(P[:-1])).astype(int)      # décade de p_n pour chaque paire
res = {"zeros": int(len(G)), "sha256": sha, "N": N, "beta": BETA, "towers": []}
for rank in RANKS:
    T = float(G[rank - 1]); ph = math.atan2(T, BETA); norm = math.sqrt(BETA ** 2 + T ** 2)
    s = (T * LP - ph) / math.pi; k = np.floor(s); f = s - k          # position d'étage, cellule, fraction
    A = np.exp((ph + k * math.pi) / T) ** 0.5 / norm                 # |v_{k(p)}| sur la ligne
    d = T * DLOG / math.pi; dk = k[1:] - k[:-1]
    out = {"rank": rank, "T": T, "pairs": int(len(dk))}
    # (a) orbite : f' = fract(f + d) ; résidu circulaire (une égalité à 1 près est un enroulement flottant)
    pred = np.mod(f[:-1] + d, 1.0); diff = np.abs(f[1:] - pred); circ = np.minimum(diff, 1.0 - diff)
    out["orbit_max_circ_residual"] = float(np.max(circ)); out["orbit_wraps"] = int(np.sum(diff > 0.5))
    # déplacement + variation de fraction = d (displacement_add_fraction_eq)
    out["displacement_identity_max_residual"] = float(np.max(np.abs(dk + (f[1:] - f[:-1]) - d)))
    # (b) rapport des amplitudes, deux formes
    ratio = A[1:] / A[:-1]
    r_cells = np.exp(math.pi * dk / (2 * T))
    r_exact = np.sqrt(P[1:] / P[:-1]) * np.exp(-math.pi * (f[1:] - f[:-1]) / (2 * T))
    out["ratio_cells_max_rel_err"] = float(np.max(np.abs(ratio - r_cells) / r_cells))
    out["ratio_exact_max_rel_err"] = float(np.max(np.abs(ratio - r_exact) / r_exact))
    # (c) monotonie et encadrement
    out["mono_violations"] = int(np.sum(A[1:] < A[:-1]))
    lo = np.sqrt(P[1:] / P[:-1]) * math.exp(-math.pi / (2 * T)); hi = np.sqrt(P[1:] / P[:-1]) * math.exp(math.pi / (2 * T))
    out["bounds_violations"] = int(np.sum((ratio <= lo) | (ratio >= hi)))
    out["same_cell_iff_equal_amp_violations"] = int(np.sum((dk == 0) != (A[1:] == A[:-1])))
    out["new_cell_step_violations"] = int(np.sum((dk > 0) & (ratio < math.exp(math.pi / (2 * T)) * (1 - 1e-12))))
    # (d) paires dans une même cellule, par décade
    sc = []
    for dd in range(0, 7):
        sel = dec == dd
        if sel.sum() == 0: continue
        sc.append({"decade": dd, "pairs": int(sel.sum()), "same_cell": int(np.sum(dk[sel] == 0)),
                   "max_dk": int(np.max(dk[sel])), "mean_dk": float(np.mean(dk[sel]))})
    out["same_cell_by_decade"] = sc
    # (e) télescopage par décade : log(A_last/A_first) contre π (k_last − k_first)/(2T)
    tel = []
    for dd in range(0, 7):
        idx = np.flatnonzero(np.floor(np.log10(P)).astype(int) == dd)
        if len(idx) < 2: continue
        i0, i1 = idx[0], idx[-1]
        lhs = math.log(A[i1] / A[i0]); rhs = math.pi * (k[i1] - k[i0]) / (2 * T)
        tel.append({"decade": dd, "p_first": float(P[i0]), "p_last": float(P[i1]), "cells": int(k[i1] - k[i0]),
                    "lhs": lhs, "rhs": rhs, "residual": abs(lhs - rhs)})
    out["telescope"] = tel
    res["towers"].append(out)
    lg("rang %d T=%.4f paires=%d | orbite circ=%.2e enroul=%d | ratio cells=%.2e exact=%.2e | mono=%d bornes=%d iff=%d | même cellule total=%d" % (
        rank, T, out["pairs"], out["orbit_max_circ_residual"], out["orbit_wraps"], out["ratio_cells_max_rel_err"],
        out["ratio_exact_max_rel_err"], out["mono_violations"], out["bounds_violations"],
        out["same_cell_iff_equal_amp_violations"], sum(x["same_cell"] for x in sc)))
json.dump(res, open(os.path.join(OUT, "data", "e448a_results.json"), "w"), indent=1)
lg("FIN e448a")
