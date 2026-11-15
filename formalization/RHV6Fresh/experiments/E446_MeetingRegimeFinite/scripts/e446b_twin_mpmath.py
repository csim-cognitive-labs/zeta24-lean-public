# -*- coding: utf-8 -*-
"""E446(b) — jumeau déterministe à 30 chiffres (mpmath) : recalcule N_obs (dernier rang où deux écarts consécutifs ont
chacun un contact) pour chaque Tour avec des contacts en haute précision et des premiers exacts (sympy), et les rapports
poids/longueur sur 12 cellules par Tour par sommation entière exacte de Λ. Compare à data/e446a_results.json."""
import os, sys, json, math
from mpmath import mp, mpf, atan2, log as mlog, exp as mexp, floor as mfloor, pi as mpi
from sympy import primerange, factorint
mp.dps = 30
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
sys.path.insert(0, os.path.join(OUT, "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
log = Logger(os.path.join(OUT, "logs", "e446b.log"))
G, sha = load_zeros(log)
A = json.load(open(os.path.join(OUT, "data", "e446a_results.json")))
NT = 1_000_000
P = list(primerange(2, NT + 1)); LP = [mlog(mpf(p)) for p in P]
def lam(n):
    f = factorint(n)
    return mlog(mpf(list(f)[0])) if len(f) == 1 else mpf(0)
ok = True; twin = []
for t in A["towers"]:
    T = mpf(G[t["rank"] - 1]); b = mpf(t["beta"]); ph = atan2(T, b)
    m = [int(mfloor((T * lp - ph) / mpi)) for lp in LP]
    both = [n for n in range(len(P) - 2) if m[n] < m[n + 1] and m[n + 1] < m[n + 2]]
    N_obs = both[-1] if both else -1
    # N_obs de (a) n'est comparable que s'il est < len(P)−2 (bornes différentes : 10^7 contre 2·10^6)
    comparable = t["N_obs"] < len(P) - 2
    same = (N_obs == t["N_obs"]) if comparable else None
    viol = sum(1 for n in both if mlog(mpf(P[n + 2]) / P[n]) < mpi / T)
    # rapports poids/longueur sur 12 cellules (C_k entre 10^3 et 10^4)
    cells = []
    k0 = int(mfloor((T * mlog(mpf(1000)) - ph) / mpi)); k1 = int(mfloor((T * mlog(mpf(10000)) - ph) / mpi))
    ks = sorted(set(int(k0 + i * (k1 - k0) / 11) for i in range(12)))
    for k in ks:
        C0 = mexp((ph + k * mpi) / T); C1 = mexp((ph + (k + 1) * mpi) / T)
        a0 = int(mfloor(C0)); a1 = int(mfloor(C1))
        W = sum(lam(n) for n in range(a0 + 1, a1 + 1)) if a1 > a0 else mpf(0)
        cells.append({"k": k, "ratio": float(W / (C1 - C0))})
    twin.append({"rank": t["rank"], "beta": t["beta"], "N_obs_twin": N_obs, "N_obs_a": t["N_obs"], "comparable": comparable,
                 "same": same, "F2_violations_twin": viol, "cells": cells})
    if same is False or viol: ok = False
    log("rang %7d β=%.2f : N_obs jumeau %d, (a) %d, comparable=%s same=%s, F2viol=%d, rapports %s" % (
        t["rank"], t["beta"], N_obs, t["N_obs"], comparable, same, viol, " ".join("%.3f" % c["ratio"] for c in cells)))
json.dump({"sha256": sha, "NT": NT, "all_ok": ok, "twin": twin}, open(os.path.join(OUT, "data", "e446b_twin.json"), "w"), indent=1)
log("all_ok = %s" % ok)
