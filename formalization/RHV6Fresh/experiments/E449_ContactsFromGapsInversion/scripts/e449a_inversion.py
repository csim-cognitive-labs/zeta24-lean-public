# -*- coding: utf-8 -*-
"""E449(a) — chemin inverse, §19.71. Pour 6 hauteurs de la ligne et 3 contrôles (milieux entre zéros) : (a) le mot
k(p_n) = ⌊(T log p_n − φ)/π⌋ est calculé puis seuls les entiers sont gardés ; polygone des (T, φ) compatibles
(phase_bracket pour chaque premier ≤ X, X = 10^3..10^7) : intervalle de T par bissection sur g(T) = min_n(T L_n − k_n π)
− max_n(T L_n − (k_n+1)π) (concave), plage de φ et de β = T/tan φ sur une grille de T ; le vrai point doit être dedans ;
(b) contrôles identiques (H6) ; (c) cause : min f, 1 − max f, pas maximal par décade ; (d) formule tangentielle depuis deux
contacts (tower_of_two_contacts). Jumeau : e449b_twin_mpmath.py. Une Tour à la fois, aucun objet spectral, aucun OFF."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
lg = Logger(os.path.join(OUT, "logs", "e449a.log"))
G, sha = load_zeros(lg)
N = 10_000_000; BETA = 0.5
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N ** 0.5) + 1):
    if sieve[i]: sieve[i * i::i] = False
P = np.flatnonzero(sieve).astype(np.float64); L = np.log(P)
lg("premiers ≤ %d : %d" % (N, len(P)))
def polygon(Lx, k, T0):
    """intervalle de T, plage de φ et de β du polygone {k_n π ≤ T L_n − φ ≤ (k_n+1)π}."""
    lo_b = (k + 1) * math.pi; hi_b = k * math.pi
    def phi_lo(T): return np.max(T * Lx - lo_b)
    def phi_hi(T): return np.min(T * Lx - hi_b)
    def g(T): return phi_hi(T) - phi_lo(T)
    g0 = g(T0)
    # bissection : g concave, g(T0) ≥ 0 (à l'arrondi près) ; chercher les racines de part et d'autre
    def root(a, b):  # g(a) ≥ 0 > g(b)
        for _ in range(80):
            m = 0.5 * (a + b)
            if g(m) >= 0: a = m
            else: b = m
        return a
    step = 1.0
    while g(T0 - step) >= 0: step *= 2
    T_lo = root(T0, T0 - step)
    step = 1.0
    while g(T0 + step) >= 0: step *= 2
    T_hi = root(T0, T0 + step)
    grid = np.linspace(T_lo, T_hi, 2001)
    plo = np.array([phi_lo(t) for t in grid]); phi_ = np.array([phi_hi(t) for t in grid])
    ok = phi_ >= plo
    grid, plo, phi_ = grid[ok], plo[ok], phi_[ok]
    beta_lo = float(np.min(grid / np.tan(phi_))); beta_hi = float(np.max(grid / np.tan(plo)))
    return {"g_at_true": float(g0), "T_lo": float(T_lo), "T_hi": float(T_hi), "T_width": float(T_hi - T_lo),
            "phi_lo": float(np.min(plo)), "phi_hi": float(np.max(phi_)), "phi_width": float(np.max(phi_) - np.min(plo)),
            "beta_lo": beta_lo, "beta_hi": beta_hi, "beta_width": beta_hi - beta_lo}
XS = [10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7]
res = {"zeros": int(len(G)), "sha256": sha, "N": N, "beta": BETA, "towers": [], "controls": []}
def run(T, label, store):
    ph = math.atan2(T, BETA)
    s = (T * L - ph) / math.pi; k = np.floor(s); f = s - k
    out = {"label": label, "T": T, "phi": ph, "by_X": [], "cause": [], "tangential": []}
    for X in XS:
        sel = P <= X
        r = polygon(L[sel], k[sel], T); r["X"] = X; r["primes"] = int(sel.sum())
        r["true_inside"] = bool(r["T_lo"] - 1e-9 <= T <= r["T_hi"] + 1e-9 and r["phi_lo"] - 1e-9 <= ph <= r["phi_hi"] + 1e-9)
        r["beta_inside"] = bool(r["beta_lo"] - 1e-9 <= BETA <= r["beta_hi"] + 1e-9)
        out["by_X"].append(r)
        # (c) cause
        fs = f[sel]; d = T * (L[sel][1:] - L[sel][:-1]) / math.pi
        out["cause"].append({"X": X, "min_f": float(np.min(fs)), "one_minus_max_f": float(1 - np.max(fs)),
                             "max_step_last_decade": float(np.max(d[P[sel][:-1] >= X / 10])) if np.any(P[sel][:-1] >= X / 10) else None,
                             "phase_window_pi_units": float(np.min(fs) + 1 - np.max(fs))})
    # (d) formule tangentielle depuis deux contacts
    for kk in [int(k[0]), int(k[len(k) // 2]), int(k[-1])]:
        C0 = math.exp((ph + kk * math.pi) / T); C1 = math.exp((ph + (kk + 1) * math.pi) / T)
        T_rec = math.pi / math.log(C1 / C0); ph_rec = T_rec * math.log(C0) - kk * math.pi; b_rec = T_rec / math.tan(ph_rec)
        out["tangential"].append({"k": kk, "T_err": abs(T_rec - T), "phi_err": abs(ph_rec - ph), "beta_err": abs(b_rec - BETA)})
    store.append(out)
    r7 = out["by_X"][-1]
    lg("%s T=%.4f | X=10^7 : T∈[%.10f, %.10f] (largeur %.1e) φ largeur %.2e β∈[%.6f, %.6f] vrai dedans=%s | X=10^3 : T largeur %.1e β largeur %.2e | tangentielle β err max %.1e" % (
        label, T, r7["T_lo"], r7["T_hi"], r7["T_width"], r7["phi_width"], r7["beta_lo"], r7["beta_hi"], r7["true_inside"],
        out["by_X"][0]["T_width"], out["by_X"][0]["beta_width"], max(t["beta_err"] for t in out["tangential"])))
for rank in [1, 10, 100, 1000, 10000, 100000]:
    run(float(G[rank - 1]), "zéro rang %d" % rank, res["towers"])
for rank in [1, 100, 10000]:
    run(0.5 * (float(G[rank - 1]) + float(G[rank])), "contrôle milieu rangs %d-%d" % (rank, rank + 1), res["controls"])
json.dump(res, open(os.path.join(OUT, "data", "e449a_results.json"), "w"), indent=1)
lg("FIN e449a")
