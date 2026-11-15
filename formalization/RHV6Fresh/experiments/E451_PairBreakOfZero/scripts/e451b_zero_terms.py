#!/usr/bin/env python3
"""E451 (b) — les objets d'E450 au paramètre d'un zéro vrai sont le module du terme du zéro : H3 (cassure = module du
terme × facteur de cellule), H4 (deux mots à ≤ 1 cellule), H5 (produit des modules = x/(‖ρ‖‖ρ*‖)), H6 (rapport =
x^{2β−1}‖ρ*‖/‖ρ‖). Six zéros (β = 1/2, miroir = zéro) et trois paires OFF témoins aux mêmes fréquences. numpy, 10^5 premiers."""
import os, sys, json, math, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
lg = Logger(os.path.join(OUT, "logs", "e451b.log"))
G, sha = load_zeros(lg)
N = 10**7
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
P = np.nonzero(sieve)[0].astype(np.float64)
rng = np.random.default_rng(451)
S = np.sort(rng.choice(P, 100000, replace=False))
lg(f"premiers ≤ 10^7 : {len(P)} ; échantillon {len(S)} (graine 451)")

def word(beta, T, x):
    phi = math.atan2(T, beta)
    s = (T*np.log(x) - phi)/math.pi
    k = np.floor(s); f = s - k
    C = np.exp((phi + k*math.pi)/T)
    nrm = math.hypot(beta, T)
    v = ((-1.0)**k) * C**beta / nrm
    return k, f, v, nrm

def check(beta, T, label):
    kb, fb, vb, nb = word(beta, T, S)
    km, fm, vm, nm = word(1-beta, T, S)
    termb = S**beta / nb                # ‖zeroTerm z x‖
    termm = S**(1-beta) / nm            # ‖zeroTerm (mirrorMember z) x‖
    h3 = np.max(np.abs(np.abs(vb) - termb*np.exp(-beta*math.pi*fb/T)) / termb)
    h4 = int(np.sum(np.abs(km - kb) > 1))
    h5 = np.max(np.abs(termb*termm - S/(nb*nm)) / (S/(nb*nm)))
    ratio = termb/termm; ref = S**(2*beta-1) * (nm/nb)
    h6 = np.max(np.abs(ratio - ref)/ref)
    marks = {int(10**d): float(ratio[np.searchsorted(S, 10**d)]) for d in range(3, 7)}
    ok = (h3 <= 1e-12) and (h4 == 0) and (h5 <= 1e-12) and (h6 <= 1e-12)
    lg(f"{label} β={beta} T={T:.6f}: H3 err={h3:.2e} H4 viol={h4} H5 err={h5:.2e} H6 err={h6:.2e} "
       f"rapport à 10^3..10^6={[f'{v:.4g}' for v in marks.values()]} ok={ok}")
    return dict(label=label, beta=beta, T=T, h3_err=float(h3), h4_viol=h4, h5_err=float(h5), h6_err=float(h6),
                ratio_marks=marks, ok=bool(ok))

ranks = [1, 10, 100, 1000, 10000, 100000]
res = []
for r in ranks:
    T = float(G[r-1])
    res.append(check(0.5, T, f"zéro rang {r} (ligne)"))
    for beta in (0.3, 0.4, 0.45):
        res.append(check(beta, T, f"paire OFF témoin à la fréquence du rang {r}"))
all_ok = all(x["ok"] for x in res)
lg(f"FIN e451b all_ok={all_ok}")
json.dump(dict(zeros=len(G), sha256=sha, sample=len(S), seed=451, results=res, all_ok=all_ok),
          open(os.path.join(OUT, "data", "e451b_results.json"), "w"), indent=1)
