# -*- coding: utf-8 -*-
"""E414 — identité des accumulations : Σ_k [F(C_{k+1}) − F(C_k)] + bords = F(x) − F(a), zéro par zéro
et collectivement, canal brut (x^ρ/ρ) et canal intégré (x^ρ/(ρ(ρ+1))), parties réelle et imaginaire,
avec estimation de l'arrondi (ε·somme des modules) pour séparer arrondi et erreur mathématique."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from contact_common import *
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e414.log"))
G, sha = load_zeros(log)
EPS = np.finfo(float).eps
# intervalle adapté au nombre de contacts (≤ ~3·10⁷) ; [a, x] et N zéros
cases = [(3, 2.0, 50.0), (40, 2.0, 50.0), (300, 2.0, 50.0), (5000, 2.0, 50.0),
         (100000, 100.0, 102.5), (2001052, 1000.0, 1000.085)]
res = {}
for N, a, x in cases:
    gam = G[:N]
    for name, F in (("brut", tower_value), ("intégré", integrated_tower)):
        tot = 0j; direct = 0j; ncont = 0; modsum = 0.0; maxerr = 0.0; maxrel = 0.0
        for g in gam:
            rho = 0.5 + 1j * g
            acc, nc, ms = accumulate_one(rho, F, a, x)
            d = F(rho, x) - F(rho, a)
            e = abs(acc - d); maxerr = max(maxerr, e); maxrel = max(maxrel, e / max(abs(d), 1e-300))
            tot += acc; direct += d; ncont += nc; modsum += ms
        err = tot - direct
        bound = EPS * modsum * 4     # borne d'arrondi grossière : ε × somme des modules (× 4)
        r = dict(N=N, a=a, x=x, canal=name, contacts=int(ncont), somme_complexe=[tot.real, tot.imag],
                 difference_directe=[direct.real, direct.imag], erreur_re=err.real, erreur_im=err.imag,
                 erreur_abs=abs(err), erreur_rel=abs(err) / max(abs(direct), 1e-300),
                 max_erreur_par_zero=maxerr, max_rel_par_zero=maxrel, somme_des_modules=modsum,
                 borne_arrondi=bound, verdict=("ARRONDI" if abs(err) <= bound else "HORS ARRONDI"))
        res["%d_%s" % (N, name)] = r
        log("N=%7d [%g,%g] %-8s contacts=%9d  A=%+.12e%+.12ei  F(x)−F(a)=%+.12e%+.12ei  |err|=%.3e (rel %.1e)  bornearrondi=%.1e  max/zéro=%.1e  %s"
            % (N, a, x, name, ncont, tot.real, tot.imag, direct.real, direct.imag, abs(err),
               r["erreur_rel"], bound, maxerr, r["verdict"]))
# sensibilité à la précision : même calcul en float32 pour N = 300 (brut)
gam = G[:300].astype(np.float32); a, x = 2.0, 50.0
tot32 = 0j; d64 = 0j
for g in gam:
    rho32 = np.complex64(0.5 + 1j * float(g)); rho = 0.5 + 1j * float(g)
    k, C = contacts_in(0.5, float(g), a, x)
    FC = (C.astype(np.float32) ** rho32 / rho32).astype(np.complex64)
    acc = (FC[0] - np.complex64(a) ** rho32 / rho32) + (FC[1:] - FC[:-1]).sum() + (np.complex64(x) ** rho32 / rho32 - FC[-1])
    tot32 += complex(acc); d64 += tower_value(rho, x) - tower_value(rho, a)
log("précision : float32 N=300 brut : |A32 − (F(x)−F(a))64| = %.3e (float64 : %.3e)" % (abs(tot32 - d64), res["300_brut"]["erreur_abs"]))
res["float32_300_brut"] = dict(erreur_abs=abs(tot32 - d64))
json.dump(res, open(os.path.join(OUT, "data", "e414_results.json"), "w"), indent=1)
log("terminé")
