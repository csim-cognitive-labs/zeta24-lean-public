# -*- coding: utf-8 -*-
"""E424 — lecture croisée entre Tours successives aux contacts du successeur (amplitudes, phases relatives)."""
import os, sys, math, json, numpy as np, mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import load_zeros, Logger, CHUNK
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e424.log"))
G, sha = load_zeros(log)
A = 2.0
TWO_PI = 2 * math.pi

def contacts_from(beta, T, a):
    """Deux premiers contacts de la grille (β, T) au-delà de a : indices k, k+1 et positions."""
    ph = np.arctan2(T, beta)
    k = np.ceil((T * np.log(a) - ph) / np.pi)
    C0 = np.exp((ph + k * np.pi) / T); C1 = np.exp((ph + (k + 1) * np.pi) / T)
    return k, C0, C1

def tower(beta, T, x):
    rho = beta + 1j * T
    return np.exp(rho * np.log(x)) / rho

def cross_block(be, Te, bl, Tl):
    """Lectures aux contacts du successeur (bl, Tl) : différence radiale, β_e, T_e."""
    k, C0, C1 = contacts_from(bl, Tl, A)
    ve0, ve1 = tower(be, Te, C0), tower(be, Te, C1)
    vl0, vl1 = tower(bl, Tl, C0), tower(bl, Tl, C1)
    cross_e = np.abs(ve1) / np.abs(ve0); cross_l = np.abs(vl1) / np.abs(vl0)
    Tl_hat = np.pi / (np.log(C1) - np.log(C0))
    dbeta = Tl_hat / np.pi * np.log(cross_e / cross_l)
    beta_e = Tl_hat / np.pi * np.log(cross_e)
    step = np.angle(ve1 / ve0) % TWO_PI
    Te_hat = Tl_hat / np.pi * step
    return k, dbeta, beta_e, Te_hat, Tl_hat

# --- 1. toutes les paires consécutives réelles (ON → ON) ---
N = len(G); n_pairs = N - 1
max_dbeta = 0.0; max_beta_e = 0.0; max_Te_rel = 0.0; max_Tl_rel = 0.0
q_dbeta = []; q_Te = []
per_decade = {}
for s in range(0, n_pairs, CHUNK):
    e = slice(s, min(s + CHUNK, n_pairs))
    Te = G[e]; Tl = G[s + 1:min(s + CHUNK, n_pairs) + 1]
    k, dbeta, beta_e, Te_hat, Tl_hat = cross_block(0.5, Te, 0.5, Tl)
    max_dbeta = max(max_dbeta, float(np.max(np.abs(dbeta))))
    max_beta_e = max(max_beta_e, float(np.max(np.abs(beta_e - 0.5))))
    err_Te = np.abs(Te_hat - Te) / Tl
    max_Te_rel = max(max_Te_rel, float(np.max(err_Te)))
    max_Tl_rel = max(max_Tl_rel, float(np.max(np.abs(Tl_hat - Tl) / Tl)))
    q_dbeta.append(np.abs(dbeta)); q_Te.append(err_Te)
    dec = np.floor(np.log10(Tl)).astype(int)
    for d in np.unique(dec):
        m = dec == d
        per_decade.setdefault(int(d), [0.0, 0.0, 0])
        per_decade[int(d)][0] = max(per_decade[int(d)][0], float(np.max(np.abs(dbeta[m]))))
        per_decade[int(d)][1] = max(per_decade[int(d)][1], float(np.max(err_Te[m])))
        per_decade[int(d)][2] += int(m.sum())
    if s % (CHUNK * 2) == 0:
        log("paires %d..%d : |Δβ̂| max %.2e, |β̂_e−½| max %.2e, |T̂_e−T_e|/T_l max %.2e" % (s, e.stop, max_dbeta, max_beta_e, max_Te_rel))
q_dbeta = np.concatenate(q_dbeta); q_Te = np.concatenate(q_Te)
real = dict(n_paires=int(n_pairs), max_abs_dbeta=max_dbeta, max_abs_beta_e_minus_half=max_beta_e,
            max_Te_err_over_Tl=max_Te_rel, max_Tl_err_rel=max_Tl_rel,
            quantiles_dbeta={q: float(np.quantile(q_dbeta, q)) for q in (0.5, 0.9, 0.99, 0.999)},
            quantiles_Te_err_over_Tl={q: float(np.quantile(q_Te, q)) for q in (0.5, 0.9, 0.99, 0.999)},
            n_Te_err_over_Tl_gt_1e_9=int(np.sum(q_Te > 1e-9)), n_dbeta_gt_1e_9=int(np.sum(q_dbeta > 1e-9)),
            par_decade_de_T_l={str(d): dict(max_abs_dbeta=v[0], max_Te_err_over_Tl=v[1], n=v[2]) for d, v in sorted(per_decade.items())})
log("réel : %s" % json.dumps({k: v for k, v in real.items() if k != "par_decade_de_T_l"}))

# --- 2. jumeau mpmath sur 6 paires réelles ---
mp.mp.dps = 30
def twin(be, Te, bl, Tl):
    be, Te, bl, Tl = map(mp.mpf, (be, Te, bl, Tl))
    ph = mp.atan(Tl / bl); k = mp.ceil((Tl * mp.log(A) - ph) / mp.pi)
    C0 = mp.exp((ph + k * mp.pi) / Tl); C1 = mp.exp((ph + (k + 1) * mp.pi) / Tl)
    re, rl = mp.mpc(be, Te), mp.mpc(bl, Tl)
    ve0, ve1 = mp.exp(re * mp.log(C0)) / re, mp.exp(re * mp.log(C1)) / re
    vl0, vl1 = mp.exp(rl * mp.log(C0)) / rl, mp.exp(rl * mp.log(C1)) / rl
    cross_e = abs(ve1) / abs(ve0); cross_l = abs(vl1) / abs(vl0)
    dbeta = Tl / mp.pi * mp.log(cross_e / cross_l)
    step = mp.arg(ve1 / ve0) % (2 * mp.pi)
    Te_hat = Tl / mp.pi * step
    return dict(k=int(k), dbeta=float(dbeta), dbeta_attendu=float(be - bl), beta_e=float(Tl / mp.pi * mp.log(cross_e)),
                Te_hat=float(Te_hat), Te=float(Te), err_Te_over_Tl=float(abs(Te_hat - Te) / Tl),
                pas_phase_attendu=float((Te * mp.pi / Tl) % (2 * mp.pi)), pas_phase=float(step))
twins = []
for rk in [1, 100, 2000, 100000, 1000000, 2001051]:
    Te, Tl = float(G[rk - 1]), float(G[rk])
    t = twin(0.5, Te, 0.5, Tl); t["rang_e"] = rk
    k, dbeta, beta_e, Te_hat, Tl_hat = cross_block(0.5, np.array([Te]), 0.5, np.array([Tl]))
    t["float64_dbeta"] = float(dbeta[0]); t["float64_Te_err_over_Tl"] = float(abs(Te_hat[0] - Te) / Tl)
    twins.append(t)
    log("jumeau rang %d : Δβ̂ mp %.1e (f64 %.1e), T̂_e err/T_l mp %.1e (f64 %.1e)" % (rk, t["dbeta"], t["float64_dbeta"], t["err_Te_over_Tl"], t["float64_Te_err_over_Tl"]))

# --- 3. synthétique : prédécesseur réel ON, successeur OFF à la hauteur milieu (n+1, n+2) ---
syn = []
for rk in [1, 100, 2000, 100000]:
    Te = float(G[rk - 1]); Tl = 0.5 * (float(G[rk]) + float(G[rk + 1]))
    for bl in (0.3, 0.45, 0.49):
        k, dbeta, beta_e, Te_hat, Tl_hat = cross_block(0.5, np.array([Te]), bl, np.array([Tl]))
        km, dbm, _, _, _ = cross_block(1 - bl, np.array([Tl]), bl, np.array([Tl]))   # miroir lu aux contacts du membre
        t = twin(0.5, Te, bl, Tl)
        r = dict(rang_e=rk, beta_l=bl, T_l=Tl, k=int(k[0]), dbeta_lu=float(dbeta[0]), dbeta_attendu=0.5 - bl,
                 err_dbeta=float(abs(dbeta[0] - (0.5 - bl))), beta_e_lu=float(beta_e[0]),
                 Te_hat=float(Te_hat[0]), err_Te_over_Tl=float(abs(Te_hat[0] - Te) / Tl),
                 miroir_dbeta_lu=float(dbm[0]), miroir_dbeta_attendu=1 - 2 * bl, err_miroir=float(abs(dbm[0] - (1 - 2 * bl))),
                 jumeau_mp_dbeta=t["dbeta"], jumeau_mp_err_Te_over_Tl=t["err_Te_over_Tl"])
        syn.append(r)
        log("synthétique e=rang %d, β_l=%.2f : Δβ̂ %.12f (attendu %.2f), miroir %.12f (attendu %.2f), T̂_e err/T_l %.1e, mp %.1e"
            % (rk, bl, r["dbeta_lu"], r["dbeta_attendu"], r["miroir_dbeta_lu"], r["miroir_dbeta_attendu"], r["err_Te_over_Tl"], t["err_Te_over_Tl"]))
json.dump(dict(sha256=sha, reel=real, jumeaux=twins, synthetique=syn), open(os.path.join(OUT, "data", "e424_results.json"), "w"), indent=1)
log("terminé")
