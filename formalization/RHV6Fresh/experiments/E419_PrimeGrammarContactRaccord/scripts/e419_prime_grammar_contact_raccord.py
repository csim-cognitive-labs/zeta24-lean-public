# -*- coding: utf-8 -*-
"""E419 — raccord avec la grammaire première : accumulation collective sur chaque écart
[p_n, p_{n+1}] (de p_n + ½ à p_{n+1} + ½, demi-entiers), canal brut et intégré ; indépendance du
découpage (deux découpages distincts, même valeur) ; quantité d'information : une valeur complexe
par écart contre 2 001 052 Tours ; sensibilité au remplacement radial d'un membre (quartet OFF au
rang 2000) comparée au résidu de troncature ; question : contrainte nouvelle ou identité connue ?"""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import *
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e419.log"))
G, sha = load_zeros(log)
lam, isp = sieve_lambda(1100); primes = [p for p in range(3, 1001) if isp[p]]   # VALIDATION : seulement pour choisir les bornes d'écart et comparer
res = {"gaps": []}
# 1. accumulation brute par écart avec 2 001 052 zéros : ψ̂₀(q+½) − ψ̂₀(p+½) doit valoir Σ_{p<n≤q} Λ(n)
cache = {}
def p0(x):
    if x not in cache: cache[x] = psi0_hat(x, 0.5, G)
    return cache[x]
errs = []
for p, q in zip(primes, primes[1:]):
    acc = p0(q + 0.5) - p0(p + 0.5)
    expect = float(np.sum(lam[p + 1:q + 1]))      # VALIDATION
    errs.append(acc - expect)
    res["gaps"].append(dict(p=p, q=q, gap=q - p, accumulation_brute=acc, attendu=expect, erreur=acc - expect))
errs = np.array(errs)
log("écarts p ≤ 1000 (%d) : accumulation brute par écart − Σ Λ : rms %.4f, max %.4f" % (len(errs), np.sqrt(np.mean(errs ** 2)), np.max(np.abs(errs))))
res["raw_gap_rms"] = float(np.sqrt(np.mean(errs ** 2))); res["raw_gap_max"] = float(np.max(np.abs(errs)))
# 2. indépendance du découpage : 300 zéros, écart [101, 103] : contacts propres vs contacts d'une autre Tour vs sans contacts
gam = G[:300]; a, x = 101.5, 103.5
tot_own = 0j; tot_other = 0j; tot_none = 0j
for i, g in enumerate(gam):
    rho = 0.5 + 1j * g
    acc_own, _, _ = accumulate_one(rho, tower_value, a, x)
    # découpage par les contacts d'une AUTRE Tour (β', T') = (0.5, γ_{i+1 mod 300})
    g2 = gam[(i + 1) % 300]; k, C = contacts_in(0.5, g2, a, x)
    FC = tower_value(rho, C) if len(C) else np.array([])
    acc_other = (tower_value(rho, x) - tower_value(rho, a)) if len(C) == 0 else ((FC[0] - tower_value(rho, a)) + (FC[1:] - FC[:-1]).sum() + (tower_value(rho, x) - FC[-1]))
    tot_own += acc_own; tot_other += acc_other; tot_none += tower_value(rho, x) - tower_value(rho, a)
log("indépendance du découpage (300 zéros, [101.5, 103.5]) : |propre − direct| = %.3e, |autre Tour − direct| = %.3e (Lean : contact_accumulation_partition_independent)" % (abs(tot_own - tot_none), abs(tot_other - tot_none)))
res["partition_independence"] = dict(own_vs_direct=abs(tot_own - tot_none), other_vs_direct=abs(tot_other - tot_none))
# 3. sensibilité radiale par écart : quartet OFF au rang 2000 (β = 0.3), variation de l'accumulation brute par écart vs résidu de troncature
T = float(G[1999]); rhos = [0.3 + 1j * T, 0.7 + 1j * T]
dv = []
for p, q in zip(primes, primes[1:]):
    d = 0.0
    for xx in (q + 0.5, p + 0.5):
        old = 2 * np.real(xx ** (0.5 + 1j * T) / (0.5 + 1j * T)); new = sum(2 * np.real(xx ** r / r) for r in rhos)
        d += (-(new - old)) * (1 if xx == q + 0.5 else -1)
    dv.append(d)
dv = np.array(dv)
log("quartet OFF rang 2000 (β = 0,3) : variation de l'accumulation brute par écart : rms %.3e, max %.3e ; résidu de troncature par écart : rms %.4f → rapport %.3e" % (np.sqrt(np.mean(dv ** 2)), np.max(np.abs(dv)), np.sqrt(np.mean(errs ** 2)), np.sqrt(np.mean(dv ** 2)) / np.sqrt(np.mean(errs ** 2))))
res["off_gap_sensitivity"] = dict(rms=float(np.sqrt(np.mean(dv ** 2))), max=float(np.max(np.abs(dv))), ratio_to_truncation=float(np.sqrt(np.mean(dv ** 2)) / np.sqrt(np.mean(errs ** 2))))
# 4. information : nombre de valeurs par écart contre nombre de paramètres
res["information"] = dict(valeurs_par_ecart=1, parametres_tours=2 * len(G), ecarts=len(primes) - 1)
json.dump(res, open(os.path.join(OUT, "data", "e419_results.json"), "w"), indent=1)
log("terminé")
