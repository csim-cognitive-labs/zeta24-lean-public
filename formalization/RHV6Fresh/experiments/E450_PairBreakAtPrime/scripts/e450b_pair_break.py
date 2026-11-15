# -*- coding: utf-8 -*-
"""E450(b) — K1, la cassure de la paire au premier partagé, §19.72. Paires témoins β ∈ {0,3 ; 0,4 ; 0,45} aux fréquences des
six zéros (rangs 1, 10, 100, 1000, 10000, 100000) ; échantillon de 100 000 premiers dans [10^3, 10^7] : H1 amplitude exacte
(break_amplitude_exact) pour chaque membre ; H2 fraction du miroir = fract(f + décalage/π) (mirror_cellFraction), mots
différant d'au plus 1 (mirror_word_difference_le_one), comptage des points où les deux mots diffèrent ; H3 produit
(pair_break_product), fraction effective dans [0,1) ; H4 encadrement de la somme (pair_break_sum_bounds) ; H5 rapport
(pair_break_ratio) et valeur du rapport au premier suivant 10^3..10^7. Jumeau : e450b_twin_mpmath.py. Aucun OFF réel n'est
testé : paires témoins aux fréquences de la ligne, objets du corpus seulement."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
lg = Logger(os.path.join(OUT, "logs", "e450b.log"))
G, sha = load_zeros(lg)
RANKS = [1, 10, 100, 1000, 10000, 100000]; BETAS = [0.3, 0.4, 0.45]; N = 10_000_000; XMIN = 1000.0; TOL = 1e-12
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N ** 0.5) + 1):
    if sieve[i]: sieve[i * i::i] = False
P = np.flatnonzero(sieve).astype(np.int64); Pq = P[P >= XMIN]
rng = np.random.default_rng(450)
samp = np.sort(rng.choice(Pq, size=100000, replace=False)).astype(np.float64); Ls = np.log(samp)
marks = np.array([float(P[np.searchsorted(P, 10 ** j)]) for j in range(3, 7)] + [float(P[-1])])  # premier suivant 10^3..10^6, dernier premier ≤ 10^7
lg("premiers ≤ %d : %d ; échantillon %d ; repères %s" % (N, len(P), len(samp), marks.tolist()))
def member(b, T, x):
    ph = math.atan2(T, b); norm = math.sqrt(b * b + T * T)
    s = (T * np.log(x) - ph) / math.pi; k = np.floor(s); f = s - k
    C = np.exp((ph + k * math.pi) / T); v = C ** b / norm            # |contactRealValue| directe
    vex = x ** b * np.exp(-b * math.pi * f / T) / norm               # break_amplitude_exact
    return ph, norm, k, f, v, vex
res = {"zeros": int(len(G)), "sha256": sha, "N": N, "sample": int(len(samp)), "tol": TOL, "cases": []}
all_ok = True
for r in RANKS:
    T = float(G[r - 1])
    for b in BETAS:
        ph, n1, k1, f1, v1, vex1 = member(b, T, samp); ph2, n2, k2, f2, v2, vex2 = member(1 - b, T, samp)
        shift = ph - ph2                                               # mirrorPhaseShift β T
        c = {"rank": r, "T": T, "beta": b, "shift": shift}
        c["H1_err"] = float(max(np.max(np.abs(v1 - vex1) / vex1), np.max(np.abs(v2 - vex2) / vex2)))
        f2_pred = np.mod(f1 + shift / math.pi, 1.0)
        c["H2_fract_err"] = float(np.max(np.minimum(np.abs(f2 - f2_pred), 1 - np.abs(f2 - f2_pred))))
        c["H2_word_diff_max"] = int(np.max(np.abs(k2 - k1))); c["H2_word_differ_share"] = float(np.mean(k2 != k1))
        prod = v1 * v2; feff = b * f1 + (1 - b) * f2
        prod_ex = samp * np.exp(-math.pi * feff / T) / (n1 * n2)
        c["H3_err"] = float(np.max(np.abs(prod - prod_ex) / prod_ex)); c["H3_feff_min"] = float(feff.min()); c["H3_feff_max"] = float(feff.max())
        ssum = v1 + v2; lo = math.exp(-math.pi / T) * (samp ** b / n1 + samp ** (1 - b) / n2); hi = samp ** b / n1 + samp ** (1 - b) / n2
        c["H4_violations"] = int(np.sum((ssum < lo * (1 - 1e-13)) | (ssum > hi * (1 + 1e-13))))
        c["H4_sum_over_price_minmax"] = [float(np.min(ssum / hi)), float(np.max(ssum / hi))]
        ratio = v1 / v2; ratio_ex = samp ** (2 * b - 1) * np.exp(-math.pi * (b * f1 - (1 - b) * f2) / T) * (n2 / n1)
        c["H5_err"] = float(np.max(np.abs(ratio - ratio_ex) / ratio_ex))
        _, _, _, _, m1, _ = member(b, T, marks); _, _, _, _, m2, _ = member(1 - b, T, marks)
        c["H5_ratio_at_marks"] = (m1 / m2).tolist(); c["H5_mirror_over_tower_at_marks"] = (m2 / m1).tolist()
        c["ok"] = bool(c["H1_err"] <= TOL and c["H2_fract_err"] <= 1e-9 and c["H2_word_diff_max"] <= 1 and c["H3_err"] <= TOL
                       and 0 <= c["H3_feff_min"] and c["H3_feff_max"] < 1 and c["H4_violations"] == 0 and c["H5_err"] <= TOL)
        all_ok &= c["ok"]; res["cases"].append(c)
        lg("rang %d β=%.2f décalage=%.3e | H1 %.1e | H2 fract %.1e mots≠ %.4f max|Δk|=%d | H3 %.1e feff∈[%.3f,%.3f] | H4 viol=%d | H5 %.1e miroir/Tour@10^7=%.3e | ok=%s" % (
            r, b, shift, c["H1_err"], c["H2_fract_err"], c["H2_word_differ_share"], c["H2_word_diff_max"], c["H3_err"], c["H3_feff_min"],
            c["H3_feff_max"], c["H4_violations"], c["H5_err"], c["H5_mirror_over_tower_at_marks"][-1], c["ok"]))
res["all_ok"] = bool(all_ok)
json.dump(res, open(os.path.join(OUT, "data", "e450b_results.json"), "w"), indent=1)
lg("FIN e450b all_ok=%s" % all_ok)
