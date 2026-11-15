# -*- coding: utf-8 -*-
"""E425 — (a) paire miroir aux contacts du membre OFF ; (b) position du premier de même rang dans la grille des contacts."""
import os, sys, math, json, numpy as np, mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import load_zeros, Logger, CHUNK
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e425.log"))
G, sha = load_zeros(log)
A, X = 2.0, 1e4

def contacts_in(beta, T, a, x):
    ph = math.atan2(T, beta)
    k0 = math.ceil((T * math.log(a) - ph) / math.pi); k1 = math.floor((T * math.log(x) - ph) / math.pi)
    k = np.arange(k0, k1 + 1, dtype=np.float64)
    return k, np.exp((ph + k * np.pi) / T)

def tower(beta, T, x):
    rho = beta + 1j * T
    return np.exp(rho * np.log(x)) / rho

# --- (a) paire miroir aux contacts du membre ---
mirror = []
def mirror_case(beta, T, label, synthetic):
    k, C = contacts_in(beta, T, A, X)
    vm = tower(beta, T, C); vmir = tower(1 - beta, T, C)
    pair_im = (vm + vmir).imag
    phrel = math.atan2(T, beta) - math.atan2(T, 1 - beta)
    pred = ((-1.0) ** k) * math.sin(phrel)
    norm = pair_im / np.abs(vmir)
    r = dict(tour=label, synthetique=synthetic, beta=beta, T=T, n_contacts=int(len(C)), phase_relative=phrel,
             sin_phase_relative=math.sin(phrel), approx_1_moins_2beta_sur_T=(1 - 2 * beta) / T,
             max_abs_im_membre_rel=float(np.max(np.abs(vm.imag) / np.abs(vm))),
             min_abs_im_paire_sur_module_miroir=float(np.min(np.abs(norm))),
             max_err_im_paire_vs_prediction=float(np.max(np.abs(norm - pred))),
             n_contacts_im_paire_nulle=int(np.sum(pair_im == 0.0)))
    mp.mp.dps = 30; errs = []
    for kk in k[:5]:
        kk = int(kk); b = mp.mpf(beta); Tm = mp.mpf(T)
        Ck = mp.exp((mp.atan(Tm / b) + kk * mp.pi) / Tm)
        rm, rr = mp.mpc(b, Tm), mp.mpc(1 - b, Tm)
        s = mp.exp(rm * mp.log(Ck)) / rm + mp.exp(rr * mp.log(Ck)) / rr
        p = (-1) ** kk * mp.sin(mp.atan(Tm / b) - mp.atan(Tm / (1 - b)))
        errs.append(float(abs(s.imag / abs(mp.exp(rr * mp.log(Ck)) / rr) - p)))
    r["jumeau_mpmath_max_err"] = max(errs)
    log("%s : %d contacts, sin φ_rel %.3e, min |Im paire|/|miroir| %.3e, écart à la prédiction %.1e, Im membre %.1e, mp %.1e"
        % (label, len(C), r["sin_phase_relative"], r["min_abs_im_paire_sur_module_miroir"], r["max_err_im_paire_vs_prediction"],
           r["max_abs_im_membre_rel"], r["jumeau_mpmath_max_err"]))
    return r
for (r1, r2) in [(1, 2), (100, 101), (2000, 2001), (100000, 100001)]:
    T = 0.5 * (float(G[r1 - 1]) + float(G[r2 - 1]))
    for b in (0.3, 0.45, 0.49):
        mirror.append(mirror_case(b, T, "synthétique β=%.2f T=%.6f (milieu %d-%d)" % (b, T, r1, r2), True))
for rk in [1, 100, 2000, 100000]:
    mirror.append(mirror_case(0.5, float(G[rk - 1]), "contrôle ON rang %d" % rk, False))

# --- (b) position du premier de même rang dans la grille des contacts ---
N = len(G)
LIM = 36_000_000
sieve = np.ones(LIM + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(LIM ** 0.5) + 1):
    if sieve[i]: sieve[i * i::i] = False
P = np.flatnonzero(sieve)
assert len(P) >= N, "crible trop court"
log("crible : %d premiers ≤ %d ; p_1 = %d, p_%d = %d" % (len(P), LIM, P[0], N, P[N - 1]))
P = P[:N].astype(np.float64)
def stage(beta, T, p):
    return (T * np.log(p) - np.arctan2(T, beta)) / np.pi
hist = np.zeros(20, dtype=np.int64); n_even = 0; sum_cos = 0.0; sum_cos2 = 0.0
shift_hist = {}
k_min = None; k_max = None
for s in range(0, N, CHUNK):
    e = slice(s, min(s + CHUNK, N))
    T = G[e]; p = P[e]
    st = stage(0.5, T, p); k = np.floor(st); f = st - k
    hist += np.histogram(f, bins=20, range=(0.0, 1.0))[0]
    n_even += int(np.sum(k % 2 == 0))
    c = np.cos(np.pi * st); sum_cos += float(c.sum()); sum_cos2 += float((c * c).sum())
    k_min = int(k.min()) if k_min is None else min(k_min, int(k.min())); k_max = int(k.max()) if k_max is None else max(k_max, int(k.max()))
    st3 = stage(0.3, T, p); k3 = np.floor(st3)
    for d, c_ in zip(*np.unique(k3 - k, return_counts=True)):
        shift_hist[int(d)] = shift_hist.get(int(d), 0) + int(c_)
    if s % (CHUNK * 2) == 0:
        log("zéros %d..%d : k ∈ [%d, %d], crans %s" % (s, e.stop, k_min, k_max, shift_hist))
prime = dict(n=int(N), histogramme_fraction_20_classes=hist.tolist(), proportion_k_pair=n_even / N,
             moyenne_cos_pi_s=sum_cos / N, moyenne_cos2_pi_s=sum_cos2 / N, k_min=k_min, k_max=k_max,
             crans_k_beta03_moins_k_half=shift_hist,
             cran_dans_moins1_0_a_100pct=bool(set(shift_hist.keys()) <= {-1, 0}),
             ecart_max_histogramme_a_uniforme_rel=float(np.max(np.abs(hist / (N / 20) - 1))))
log("premiers : %s" % json.dumps(prime))
mp.mp.dps = 30; tw = []
for rk in [1, 2, 3, 10, 100, 1000, 10000, 100000, 1000000, 2001052]:
    T = mp.mpf(float(G[rk - 1])); p = mp.mpf(int(P[rk - 1]))
    s_mp = (T * mp.log(p) - mp.atan(T / mp.mpf("0.5"))) / mp.pi
    s64 = float(stage(0.5, np.array([float(G[rk - 1])]), np.array([float(P[rk - 1])]))[0])
    tw.append(dict(rang=rk, p=int(P[rk - 1]), s_mp=float(s_mp), s_f64=s64, ecart=float(abs(s_mp - s64)), k=int(mp.floor(s_mp)), f=float(s_mp - mp.floor(s_mp))))
    log("jumeau rang %d : p = %d, s = %.9f (écart f64 %.1e), k = %d, f = %.6f" % (rk, int(P[rk - 1]), float(s_mp), tw[-1]["ecart"], tw[-1]["k"], tw[-1]["f"]))
json.dump(dict(sha256=sha, miroir=mirror, premiers=prime, jumeaux_premiers=tw), open(os.path.join(OUT, "data", "e425_results.json"), "w"), indent=1)
log("terminé")
