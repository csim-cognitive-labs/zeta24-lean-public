# -*- coding: utf-8 -*-
"""E417 — limite et fréquences hautes : convergence de Λ̂_H hors et aux événements (depuis E415),
largeur de transition et dépassement de Gibbs du canal brut ψ̂₀_H autour de premiers, contre
l'échelle πx/T_max ; différence brut / intégré."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import *
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e417.log"))
G, sha = load_zeros(log)
res = {}
# 1. transitions brutes autour de p ∈ {101, 1009, 10007} ; troncatures par hauteur
PR = [101, 1009, 10007]
HS = [1000.0, 10000.0, 100000.0, 1000000.0, float(G[-1])]
lam_v, isp_v = sieve_lambda(10100)   # VALIDATION : saut attendu log p et niveau ψ(p−)
res["gibbs"] = {}
for p in PR:
    assert isp_v[p]
    psi_left = float(np.sum(lam_v[:p]))   # ψ(p⁻)  (VALIDATION)
    jump = math.log(p)
    for H in HS:
        n = int(np.searchsorted(G, H, side="right")); gam = G[:n]
        ts = np.linspace(-0.5, 0.5, 2001 if n <= 200000 else 401)
        vals = np.array([psi0_hat(p + t, 0.5, gam) for t in ts])
        # largeur : entre les derniers passages à 10 % et 90 % du saut autour de t = 0
        lvl = (vals - psi_left) / jump
        i0 = np.argmin(np.abs(ts))
        # largeur à 10–90 % mesurée sur la monotonie locale au centre
        left = ts[:i0][lvl[:i0] <= 0.1]; right = ts[i0:][lvl[i0:] >= 0.9]
        width = (right[0] - left[-1]) if (len(left) and len(right)) else float("nan")
        over = float(np.max(lvl[i0:]) - 1.0); under = float(np.min(lvl[:i0]))
        scale = math.pi * p / gam[-1]
        err_far = float(np.sqrt(np.mean(((vals - (psi_left + jump * (ts > 0))) [np.abs(ts) > 3 * scale]) ** 2))) if np.any(np.abs(ts) > 3 * scale) else float("nan")
        r = dict(p=p, H=H, zeros=n, T_max=float(gam[-1]), width_10_90=width, scale_pi_x_over_T=scale,
                 ratio_width_over_scale=(width / scale if width == width else None), overshoot=over, undershoot=under, rms_outside_3scale=err_far)
        res["gibbs"]["%d_%g" % (p, H)] = r
        log("p=%5d H=%9.0f zéros=%7d : largeur 10–90 %% = %.5f ; πp/T = %.5f ; rapport %.3f ; dépassement +%.3f / %.3f ; rms hors 3 échelles %.4f"
            % (p, H, n, width, scale, (width / scale if width == width else float("nan")), over, under, err_far))
        np.save(os.path.join(OUT, "data", "profile_p%d_H%d.npy" % (p, int(H))), np.vstack([ts, vals]))
# 2. convergence hors / aux événements, depuis E415 (fenêtre W1), canaux A et B
E415 = os.path.join(OUT, "..", "E415_RawEventReconstruction", "data")
TRUNC = [3, 10, 40, 100, 300, 1000, 5000, 10000, 100000, 1000000, 2001052]
W = list(range(3, 301)); lamA = np.load(os.path.join(E415, "lamA_W1.npy")); lamB = np.load(os.path.join(E415, "lamB_W1.npy"))
lam, isp = sieve_lambda(302); truth = np.array([lam[n] for n in W]); ev = truth > 0
res["convergence_W1"] = {}
for j, H in enumerate(TRUNC):
    T = float(G[H - 1])
    eA = lamA[:, j] - truth; eB = lamB[:, j] - truth
    r = dict(zeros=H, T_max=T, A_rms_events=float(np.sqrt(np.mean(eA[ev] ** 2))), A_rms_off=float(np.sqrt(np.mean(eA[~ev] ** 2))),
             B_rms_events=float(np.sqrt(np.mean(eB[ev] ** 2))), B_rms_off=float(np.sqrt(np.mean(eB[~ev] ** 2))),
             B_rms_times_T=float(np.sqrt(np.mean(eB ** 2)) * T), A_rms_times_sqrtT=float(np.sqrt(np.mean(eA ** 2)) * math.sqrt(T)))
    res["convergence_W1"][str(H)] = r
    log("zéros=%8d T=%10.1f | A rms événements %.4f, hors %.4f | B rms événements %.3e, hors %.3e | B·T = %.3f | A·√T = %.3f"
        % (H, T, r["A_rms_events"], r["A_rms_off"], r["B_rms_events"], r["B_rms_off"], r["B_rms_times_T"], r["A_rms_times_sqrtT"]))
# 3. précision nécessaire à la localisation : le plus petit nombre de zéros tel que la classification (E416) soit exacte sur W1
E416 = os.path.join(OUT, "..", "E416_PrimeGapReconstruction", "data", "e416_results.json")
if os.path.exists(E416):
    r416 = json.load(open(E416))["W1"]
    for chan in ("A", "B"):
        ok = [H for H in TRUNC if r416["%s_%d" % (chan, H)]["all_gaps_exact"]]
        res["min_zeros_exact_W1_%s" % chan] = (min(ok) if ok else None)
        log("plus petite troncature avec tous les écarts de W1 exacts, canal %s : %s" % (chan, str(min(ok) if ok else "aucune")))
json.dump(res, open(os.path.join(OUT, "data", "e417_results.json"), "w"), indent=1)
log("terminé")
