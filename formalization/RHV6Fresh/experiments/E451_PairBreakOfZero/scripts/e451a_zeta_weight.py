#!/usr/bin/env python3
"""E451 (a) — le calcul de zêta décide de l'existence de la Tour : |ζ(1/2 + iγ)| aux six zéros de K0 et aux trois
contrôles de K0 (milieux entre zéros consécutifs). mpmath, 30 chiffres. Aucune somme de Tours."""
import os, sys, json, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
import mpmath as mp
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
lg = Logger(os.path.join(OUT, "logs", "e451a.log"))
G, sha = load_zeros(lg)
mp.mp.dps = 30
ranks = [1, 10, 100, 1000, 10000, 100000]
controls = [(1, 2), (100, 101), (10000, 10001)]
pts = [(f"zéro rang {r}", float(G[r-1]), True) for r in ranks] + \
      [(f"contrôle milieu rangs {a}–{b}", 0.5*(float(G[a-1])+float(G[b-1])), False) for a, b in controls]
res = []
for label, gam, is_zero in pts:
    t0 = time.time()
    s = mp.mpc(mp.mpf(1)/2, mp.mpf(gam))
    z = mp.zeta(s)
    dz = mp.zeta(s, derivative=1)
    az = abs(z); adz = abs(dz)
    # précision des hauteurs lues (~1e-9) : |ζ| attendu ≤ |ζ'|·δγ en un zéro
    bound = adz * mp.mpf("1e-9")
    ok = (az <= 10*bound) if is_zero else (az > mp.mpf("1e-3"))
    lg(f"{label}: γ={gam:.9f} |ζ|={mp.nstr(az,6)} |ζ'|={mp.nstr(adz,6)} |ζ'|·1e-9={mp.nstr(bound,3)} "
       f"{'zéro' if is_zero else 'contrôle'} ok={ok} ({time.time()-t0:.1f}s)")
    res.append(dict(label=label, gamma=gam, abs_zeta=float(az), abs_dzeta=float(adz), is_zero=is_zero, ok=bool(ok)))
all_ok = all(r["ok"] for r in res)
lg(f"FIN e451a all_ok={all_ok}")
json.dump(dict(zeros=len(G), sha256=sha, dps=30, points=res, all_ok=all_ok), open(os.path.join(OUT, "data", "e451a_results.json"), "w"), indent=1)
