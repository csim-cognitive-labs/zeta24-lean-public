# -*- coding: utf-8 -*-
"""E420 — valeurs réelles aux contacts, alternance, inversion tangentielle, enroulement. Aucune donnée arithmétique."""
import os, sys, math, json, numpy as np, mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import load_zeros, Logger, phase, contacts_in
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e420.log"))
G, sha = load_zeros(log)
A, X = 2.0, 1e4
def measure(beta, T, label, synthetic):
    k, C = contacts_in(beta, T, A, X)
    rho = beta + 1j * T
    v = np.exp(rho * np.log(C)) / rho
    closed = ((-1.0) ** k) * C ** beta / math.hypot(beta, T)
    mod = np.abs(v)
    r = dict(tour=label, synthetique=synthetic, beta=beta, T=T, n_contacts=int(len(C)), k_min=int(k[0]), k_max=int(k[-1]))
    r["max_im_rel"] = float(np.max(np.abs(v.imag) / mod))
    r["max_re_vs_forme_fermee_rel"] = float(np.max(np.abs(v.real - closed) / mod))
    r["paires_meme_signe"] = int(np.sum(np.sign(v.real[1:]) == np.sign(v.real[:-1])))
    ratio = mod[1:] / mod[:-1]; pred = math.exp(beta * math.pi / T)
    r["rapport_amplitude_attendu"] = pred
    r["max_err_rapport_amplitude_rel"] = float(np.max(np.abs(ratio - pred)) / pred)
    # enroulement : log|v_k| affine en k
    lk = np.log(mod); slope, icpt = np.polyfit(k, lk, 1)
    r["pente_log_amplitude"] = float(slope); r["pente_attendue"] = beta * math.pi / T
    r["residu_affine_max"] = float(np.max(np.abs(lk - (slope * k + icpt))))
    r["contacts_pour_doubler"] = T * math.log(2) / (beta * math.pi)
    r["amplitude_premier_contact"] = float(mod[0]); r["amplitude_dernier_contact"] = float(mod[-1])
    # inversion depuis les contacts seuls
    That = math.pi / np.diff(np.log(C))
    r["max_err_T_inverse_rel"] = float(np.max(np.abs(That - T)) / T)
    bamp = That * np.log(ratio) / math.pi
    r["max_err_beta_amplitude"] = float(np.max(np.abs(bamp - beta)))
    btan = T / np.tan(T * np.log(C) - k * math.pi)
    r["max_err_beta_tangente"] = float(np.max(np.abs(btan - beta)))
    btan_hat = That / np.tan(That * np.log(C[:-1]) - k[:-1] * math.pi)
    r["max_err_beta_tangente_T_estime"] = float(np.max(np.abs(btan_hat - beta)))
    # jumeau mpmath sur 5 contacts
    mp.mp.dps = 30; errs = []
    for kk in k[:5]:
        kk = int(kk); ph = mp.atan(mp.mpf(T) / beta); Ck = mp.exp((ph + kk * mp.pi) / T)
        rr = mp.mpc(beta, T); vv = mp.exp(rr * mp.log(Ck)) / rr
        cl = (-1) ** kk * Ck ** beta / mp.sqrt(beta ** 2 + T ** 2)
        errs.append(float(abs(vv.imag) / abs(vv))); errs.append(float(abs(vv.real - cl) / abs(vv)))
    r["jumeau_mpmath_max_err_rel"] = max(errs)
    log("%s : %d contacts, Im/|v| %.1e, forme fermée %.1e, même signe %d, rapport ampl. %.1e, T̂ %.1e, β̂_amp %.1e, β̂_tan %.1e, mp %.1e"
        % (label, len(C), r["max_im_rel"], r["max_re_vs_forme_fermee_rel"], r["paires_meme_signe"], r["max_err_rapport_amplitude_rel"],
           r["max_err_T_inverse_rel"], r["max_err_beta_amplitude"], r["max_err_beta_tangente"], r["jumeau_mpmath_max_err_rel"]))
    return r
res = []
for rk in [1, 2, 3, 10, 100, 1000, 10000, 100000, 1000000, 2001052]:
    res.append(measure(0.5, float(G[rk - 1]), "rang %d" % rk, False))
syn = []
for (r1, r2) in [(1, 2), (100, 101), (2000, 2001)]:
    T = 0.5 * (float(G[r1 - 1]) + float(G[r2 - 1]))
    for b in (0.3, 0.45, 0.49):
        syn.append(measure(b, T, "synthétique β=%.2f T=%.6f (milieu %d-%d)" % (b, T, r1, r2), True))
json.dump(res, open(os.path.join(OUT, "data", "e420_real_towers.json"), "w"), indent=1)
json.dump(syn, open(os.path.join(OUT, "data", "e420_synthetic.json"), "w"), indent=1)
log("terminé")
