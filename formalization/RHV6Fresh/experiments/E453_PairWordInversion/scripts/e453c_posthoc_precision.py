#!/usr/bin/env python3
"""E453 (c) — contrôle POST-HOC (ajouté après lecture des résultats (a)/(b), consigné comme tel) : l'inversion
tangentielle du miroir est mal conditionnée en flottant (erreur de β ≈ T·log p·ε_machine) ; on la recalcule à 30 et 60
chiffres pour les 24 couples × 3 contacts, et on recalcule le mot du miroir (10 premiers) depuis (β, T) rendus par
l'inversion du mot de la Tour à 60 chiffres (H4). Attendu : erreur divisée d'un facteur ≈ 10^30 entre 30 et 60 chiffres,
H4 sans écart."""
import os, sys, json, math, numpy as np
from mpmath import mp, mpf, log, exp, atan, tan, floor, pi
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
lg = Logger(os.path.join(OUT, "logs", "e453c.log"))
G, sha = load_zeros(lg)
N = 10**7
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
P = np.nonzero(sieve)[0]
Q = [int(P[i]) for i in np.linspace(0, len(P)-1, 10).astype(int)]
def inv(beta, T, k):
    phi = atan(T/beta); C0 = exp((phi + k*pi)/T); C1 = exp((phi + (k+1)*pi)/T)
    T_rec = pi/log(C1/C0); b_rec = T_rec/tan(T_rec*log(C0) - k*pi)
    return T_rec, b_rec
res = []; h4_total = 0
for r_ in [1, 10, 100, 1000, 10000, 100000]:
    Tf = float(G[r_-1])
    for b in ["0.3", "0.4", "0.45", "0.5"]:
        row = dict(rank=r_, beta=b)
        for dps in [30, 60]:
            mp.dps = dps
            T = mpf(repr(Tf)); beta = mpf(b); bm = 1-beta
            ks = [int(floor((T*log(q) - atan(T/bm))/pi)) for q in (Q[0], Q[5], Q[9])]
            err = max(max(abs(Tr-T)/T, abs(br-bm)) for Tr, br in (inv(bm, T, k) for k in ks))
            row[f"H1_err_dps{dps}"] = float(err)
        mp.dps = 60
        T = mpf(repr(Tf)); beta = mpf(b)
        k0 = int(floor((T*log(Q[5]) - atan(T/beta))/pi))
        Tr, br = inv(beta, T, k0)
        mism = sum(int(floor((Tr*log(q) - atan(Tr/(1-br)))/pi)) != int(floor((T*log(q) - atan(T/(1-beta)))/pi)) for q in Q)
        row["H4_mismatch_dps60"] = int(mism); h4_total += mism
        row["ratio_30_over_60"] = row["H1_err_dps30"]/row["H1_err_dps60"] if row["H1_err_dps60"] > 0 else None
        res.append(row)
        lg(f"rang {r_:6d} β={b:4s} | H1 err 30 ch. {row['H1_err_dps30']:.1e} | 60 ch. {row['H1_err_dps60']:.1e} | H4 (60 ch.) {mism}")
lg(f"H4 écarts totaux {h4_total} ; erreur max 60 chiffres {max(r['H1_err_dps60'] for r in res):.1e}")
json.dump(dict(zeros_sha=sha, posthoc=True, results=res, H4_total=h4_total), open(os.path.join(OUT, "data", "e453c_results.json"), "w"), indent=1)
