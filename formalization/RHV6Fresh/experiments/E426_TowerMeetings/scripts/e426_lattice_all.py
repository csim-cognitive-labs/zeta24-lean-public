# -*- coding: utf-8 -*-
"""E426(a) — rencontres lentes/rapides de toutes les paires consécutives (réseaux compilés), succession (cassure),
contacts encadrant la première rencontre lente, raccordement de la première rencontre lente aux écarts premiers."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import load_zeros, Logger
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e426a.log"))
G, sha = load_zeros(log)
BETA = 0.5; TWO_PI = 2 * math.pi; LIM = 10 ** 8; SEED = 20261103
N = len(G) - 1
T1 = G[:-1]; T2 = G[1:]; g = T2 - T1
phi1 = np.arctan2(T1, BETA); phi2 = np.arctan2(T2, BETA)
dphi = phi2 - phi1
# réseau lent de la paire (T2 en premier) : u_m = (φ2 − φ1 + 2mπ)/(T2 − T1)  (= slowMeetingLog β T2 β T1 m)
u0 = dphi / g; u1 = (dphi + TWO_PI) / g; u2 = (dphi + 2 * TWO_PI) / g
# réseau rapide : v_m = (φ1 + φ2 + 2mπ)/(T1 + T2)
S = T1 + T2
res = {"zeros": int(len(G)), "sha256": sha, "pairs": int(N)}
# (1) prédictions compilées
viol0 = int(np.sum(~((u0 > 0) & (u0 < 1 / (2 * T1)))))
gap_back = TWO_PI / (u2 - u1)
res["slow_zero_in_(0,1/2T1)_violations"] = viol0
res["gap_read_back_max_rel_err"] = float(np.max(np.abs(gap_back / g - 1)))
v0 = (phi1 + phi2) / S; v1 = (phi1 + phi2 + TWO_PI) / S
res["sum_read_back_max_rel_err"] = float(np.max(np.abs(TWO_PI / (v1 - v0) / S - 1)))
log("prédictions compilées : u0 hors (0,1/(2T1)) : %d ; écart relu max err rel %.2e ; somme relue %.2e"
    % (viol0, res["gap_read_back_max_rel_err"], res["sum_read_back_max_rel_err"]))
# bandes de hauteur
bands = {"T<1e3": T1 < 1e3, "1e3-1e4": (T1 >= 1e3) & (T1 < 1e4), "1e4-1e5": (T1 >= 1e4) & (T1 < 1e5),
         "1e5-1e6": (T1 >= 1e5) & (T1 < 1e6), "T>=1e6": T1 >= 1e6}
# (2) première rencontre lente u1 : comparaison à log(T/2π) (densité) — mesure, pas loi
logT = np.log(T1 / TWO_PI)
res["u1_by_band"] = {}
for name, m in bands.items():
    if m.sum() == 0: continue
    r = u1[m] / logT[m]
    res["u1_by_band"][name] = {"pairs": int(m.sum()), "u1_mean": float(u1[m].mean()), "u1_median": float(np.median(u1[m])),
                               "logT_mean": float(logT[m].mean()), "ratio_u1_over_logT_mean": float(r.mean()),
                               "ratio_median": float(np.median(r)), "ratio_q10": float(np.quantile(r, .1)), "ratio_q90": float(np.quantile(r, .9))}
    log("bande %s : %d paires, u1 moyen %.4f, log(T/2π) moyen %.4f, rapport médian %.4f [q10 %.3f, q90 %.3f]"
        % (name, m.sum(), u1[m].mean(), logT[m].mean(), np.median(r), np.quantile(r, .1), np.quantile(r, .9)))
# (3) contacts encadrant la première rencontre lente : indices et fractions dans la cellule de chaque Tour
s1 = (T1 * u1 - phi1) / math.pi; s2 = (T2 * u1 - phi2) / math.pi
k1 = np.floor(s1); k2 = np.floor(s2); f1 = s1 - k1; f2 = s2 - k2
h1 = np.histogram(f1, bins=20, range=(0, 1))[0]; h2 = np.histogram(f2, bins=20, range=(0, 1))[0]
res["slow1_contact_cell"] = {"frac_T1_hist20": h1.tolist(), "frac_T2_hist20": h2.tolist(),
    "frac_T1_hist20_maxdev_rel": float(np.max(np.abs(h1 / h1.mean() - 1))), "frac_T2_hist20_maxdev_rel": float(np.max(np.abs(h2 / h2.mean() - 1))),
    "k1_even_fraction": float(np.mean(k1 % 2 == 0)), "k2_even_fraction": float(np.mean(k2 % 2 == 0)),
    "same_parity_fraction": float(np.mean((k1 % 2) == (k2 % 2))),
    "exact_contact_coincidence_at_slow1_(|f|<1e-9)": int(np.sum((np.minimum(f1, 1 - f1) < 1e-9) & (np.minimum(f2, 1 - f2) < 1e-9)))}
# valeur unitaire des deux Tours à la rencontre lente u1 (égales par construction) : cos(πs1) vs cos(πs2)
c1 = np.cos(math.pi * s1); c2 = np.cos(math.pi * s2)
res["slow1_unit_value"] = {"max_|cos1-cos2|": float(np.max(np.abs(c1 - c2))), "mean_cos": float(c1.mean()),
                           "hist20_cos": np.histogram(c1, bins=20, range=(-1, 1))[0].tolist()}
log("rencontre lente 1 : fractions de cellule T1/T2 écart max à l'uniforme %.3f/%.3f ; parités égales %.4f ; |cos1−cos2| max %.1e"
    % (res["slow1_contact_cell"]["frac_T1_hist20_maxdev_rel"], res["slow1_contact_cell"]["frac_T2_hist20_maxdev_rel"],
       res["slow1_contact_cell"]["same_parity_fraction"], res["slow1_unit_value"]["max_|cos1-cos2|"]))
# (4) cassure : première rencontre lente de la paire suivante (n+1,n+2) sur le réseau lent de la paire (n,n+1)
uB = u1[1:]; tA = (uB * g[:-1] - dphi[:-1]) / TWO_PI; frA = tA - np.floor(tA)
hA = np.histogram(frA, bins=20, range=(0, 1))[0]
res["break_next_slow1_on_prev_lattice"] = {"hist20": hA.tolist(), "maxdev_rel": float(np.max(np.abs(hA / hA.mean() - 1))),
    "exact_coincidences_(|d|<1e-9)": int(np.sum(np.minimum(frA, 1 - frA) < 1e-9)),
    "mean_index_m": float(np.floor(tA).mean()), "gap_ratio_median": float(np.median(g[1:] / g[:-1]))}
log("cassure : fraction de la rencontre lente suivante sur le réseau précédent, écart max à l'uniforme %.3f ; coïncidences exactes %d"
    % (res["break_next_slow1_on_prev_lattice"]["maxdev_rel"], res["break_next_slow1_on_prev_lattice"]["exact_coincidences_(|d|<1e-9)"]))
# (5) raccordement : abscisse x1 = exp(u1) de la première rencontre lente et écart premier qui la contient
x1 = np.exp(np.minimum(u1, 700.0))
inlim = (x1 >= 2) & (x1 <= LIM)
res["x1_within_[2,1e8]_fraction"] = float(inlim.mean()); res["x1_median"] = float(np.median(x1[np.isfinite(x1)]))
log("x1 = exp(u1) : médiane %.1f ; fraction dans [2, 1e8] : %.4f" % (res["x1_median"], inlim.mean()))
sieve = np.ones(LIM + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(LIM ** 0.5) + 1):
    if sieve[i]: sieve[i * i::i] = False
P = np.flatnonzero(sieve).astype(np.float64); del sieve
log("premiers ≤ 1e8 : %d" % len(P))
# jumeau déterministe : pseudo-premiers de densité 1/log n (graine fixe), même procédure
rng = np.random.default_rng(SEED); Q = []
for a in range(2, LIM + 1, 10 ** 7):
    b = min(a + 10 ** 7, LIM + 1); n = np.arange(a, b, dtype=np.float64)
    Q.append(n[rng.random(len(n)) < 1.0 / np.log(n)])
Q = np.concatenate(Q); log("pseudo-premiers (jumeau, graine %d) ≤ 1e8 : %d" % (SEED, len(Q)))
def raccord(P, x, gg, label):
    j = np.searchsorted(P, x, side="right") - 1; ok = (j >= 0) & (j + 1 < len(P)); j = j[ok]; xx = x[ok]; gq = gg[ok]
    lp, lq = np.log(P[j]), np.log(P[j + 1]); L = lq - lp
    f = (np.log(xx) - lp) / L; prod = gq * L; prod2 = gq * np.log(xx)
    hf = np.histogram(f, bins=20, range=(0, 1))[0]
    d = {"n": int(ok.sum()), "frac_hist20": hf.tolist(), "frac_maxdev_rel": float(np.max(np.abs(hf / hf.mean() - 1))),
         "prod_gap_times_logprimegap_mean": float(prod.mean()), "prod_median": float(np.median(prod)),
         "prod_q10": float(np.quantile(prod, .1)), "prod_q90": float(np.quantile(prod, .9)),
         "prod_gap_times_logx1_mean": float(prod2.mean()), "prod2_median": float(np.median(prod2)),
         "prod2_q10": float(np.quantile(prod2, .1)), "prod2_q90": float(np.quantile(prod2, .9)),
         "x1_on_prime_(f<1e-9)": int(np.sum(f < 1e-9))}
    log("%s : n=%d ; fraction dans l'écart premier écart max uniforme %.3f ; g·Δlog p médiane %.3f [q10 %.3f, q90 %.3f] ; g·log x1 médiane %.3f"
        % (label, d["n"], d["frac_maxdev_rel"], d["prod_median"], d["prod_q10"], d["prod_q90"], d["prod2_median"]))
    return d
res["raccord"] = {}
for name, m in bands.items():
    mm = m & inlim
    if mm.sum() < 100: continue
    res["raccord"][name] = {"real_primes": raccord(P, x1[mm], g[mm], "réel   " + name), "twin_pseudo": raccord(Q, x1[mm], g[mm], "jumeau " + name)}
res["raccord"]["all"] = {"real_primes": raccord(P, x1[inlim], g[inlim], "réel   toutes"), "twin_pseudo": raccord(Q, x1[inlim], g[inlim], "jumeau toutes")}
json.dump(res, open(os.path.join(OUT, "data", "e426a_results.json"), "w"), indent=1)
log("terminé")
