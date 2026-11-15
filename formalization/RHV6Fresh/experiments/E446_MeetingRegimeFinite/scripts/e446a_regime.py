# -*- coding: utf-8 -*-
"""E446(a) — le régime « une rencontre par cellule » est fini (§19.68). Pour chaque Tour (β, T) : (a) dernier rang N_obs
où l'écart n et l'écart n+1 contiennent chacun un contact, nombre de tels rangs, contrôle F2 (π/T ≤ log(p_{n+2}/p_n)) ;
(b) cellWeight/cellLength et cellDemand/cellLength par décade de C_k ; (c) pas de la Tour sur sa cellule / longueur
(formule F7). Premiers ≤ 10^7. Jumeau : e446b_twin_mpmath.py. Aucune somme de Tours, aucun objet spectral."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e446a.log"))
G, sha = load_zeros(log)
RANKS = [1, 10, 100, 1000, 10000, 100000, 2000000]; N = 10_000_000; BETAS = [0.5, 0.3, 0.7, 0.4, 0.6, 0.45, 0.55]
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
LOGP = np.log(P.astype(np.float64))
log("premiers ≤ %d : %d" % (N, len(P)))
def phase(T, b): return math.atan2(T, b)
def contact(T, k, b): return np.exp((phase(T, b) + k * math.pi) / T)
res = {"zeros": int(len(G)), "sha256": sha, "N": N, "towers": []}
for rank in RANKS:
    T = float(G[rank - 1])
    for b in BETAS:
        out = {"rank": rank, "T": T, "beta": b}
        s = (T * LOGP - phase(T, b)) / math.pi; m = np.floor(s).astype(np.int64)   # lastContactBefore(p_n)
        hasc = m[1:] > m[:-1]                                                        # écart n a un contact (n indexé par p_n)
        both = hasc[:-1] & hasc[1:]                                                  # écarts n et n+1
        idx = np.flatnonzero(both)
        # (a) régime
        out["n_both"] = int(len(idx)); out["N_obs"] = int(idx[-1]) if len(idx) else -1
        out["p_at_N_obs"] = int(P[idx[-1]]) if len(idx) else -1
        viol = int(np.sum(np.log(P[idx + 2] / P[idx]) < math.pi / T - 1e-12)) if len(idx) else 0
        out["F2_violations"] = viol
        out["pi_over_T"] = math.pi / T
        # (b) budget par cellule
        kmin = int(math.floor((T * math.log(100.0) - phase(T, b)) / math.pi)); kmax = int(m[-1]) - 1
        K = np.arange(kmin, kmax + 1); C = contact(T, K.astype(np.float64), b)
        FL = np.floor(C).astype(np.int64); FL = np.minimum(FL, N)
        W = PS[FL[1:]] - PS[FL[:-1]]; L = C[1:] - C[:-1]
        rw = W / L; rd = rw - 1.0
        dec = {}
        for d in range(2, 8):
            sel = (C[:-1] >= 10 ** d) & (C[:-1] < 10 ** (d + 1))
            if sel.any():
                dec[str(d)] = {"cells": int(sel.sum()), "max_abs_weight_ratio_minus_1": float(np.max(np.abs(rd[sel]))),
                               "mean_weight_ratio": float(np.mean(rw[sel]))}
        out["cell_budget_by_decade"] = dec
        # (c) pas de la Tour sur sa cellule / longueur
        nrm = math.hypot(b, T); q = math.exp(b * math.pi / T); r = math.exp(math.pi / T)
        V = np.where(K % 2 == 0, 1.0, -1.0) * C ** b / nrm
        step = np.abs(V[1:] - V[:-1]) / L
        formula = (1 + q) / (nrm * (r - 1)) * C[:-1] ** (b - 1)
        out["F7_formula_max_rel_err"] = float(np.max(np.abs(step - formula) / formula))
        out["F7_ratio_first_cell"] = float(step[0]); out["F7_ratio_last_cell"] = float(step[-1])
        out["F7_C_first"] = float(C[0]); out["F7_C_last"] = float(C[-2])
        log("rang %7d T=%.3f β=%.2f | both=%d N_obs=%d p=%d F2viol=%d | poids/longueur: %s | F7 err=%.1e ratio %.3e→%.3e" % (
            rank, T, b, out["n_both"], out["N_obs"], out["p_at_N_obs"], viol,
            " ".join("10^%s:%.3f" % (d, v["max_abs_weight_ratio_minus_1"]) for d, v in dec.items()),
            out["F7_formula_max_rel_err"], step[0], step[-1]))
        res["towers"].append(out)
json.dump(res, open(os.path.join(OUT, "data", "e446a_results.json"), "w"), indent=1)
log("terminé : %d Tours" % len(res["towers"]))
