#!/usr/bin/env python3
"""Jumeau déterministe du plan Ψ (E467–E471), pré-enregistré. Sections Ψ1–Ψ5. Aucune sortie fabriquée."""
import json, math, os, time
import numpy as np
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
ZEROS = os.path.join(HERE, "..", "data", "odlyzko_zeros6_2001052.txt")
OUT = {}
t0 = time.time()
mp.mp.dps = 40
allg = np.loadtxt(ZEROS, dtype=np.float64)
print(f"zeros lus : {allg.size}", flush=True)
PI = mp.pi

def K(x, rho):  # noyau intégré x^{rho+1}/(rho(rho+1))
    return mp.power(x, rho + 1) / (rho * (rho + 1))

def share(w, beta, T, x):
    rho = mp.mpc(beta, T)
    return w * (K(x * mp.e**(PI / T), rho) - K(x, rho))

def relerr(a, b):
    return float(abs(a - b) / max(abs(b), mp.mpf(1e-300)))

# ---------------- Ψ1 ----------------
sec = {}
worst_const, worst_closed = 0.0, 0.0
x0 = mp.mpf(10)
for k in range(20):
    T = mp.mpf(allg[k]); beta = mp.mpf(1) / 2
    e = mp.e**(PI / T)
    s0 = share(1, beta, T, x0); r0 = abs(s0) / x0**mp.mpf(1.5)
    f = -mp.e**(PI / T * (1 + beta))
    for n in (1, 10, 100, 1000, 2000):
        xn = x0 * e**n
        sn = share(1, beta, T, xn)
        worst_closed = max(worst_closed, relerr(sn, f**n * s0))
        rn = abs(sn) / xn**mp.mpf(1.5)
        worst_const = max(worst_const, relerr(rn, r0))
sec["ligne_part_relative_constante_err_max"] = worst_const
sec["forme_close_produit_err_max"] = worst_closed
T = mp.mpf(allg[999]); pair = {}
for beta in (mp.mpf("0.3"), mp.mpf("0.4"), mp.mpf("0.45")):
    e = mp.e**(PI / T); worst = 0.0; growth = []
    for b in (beta, 1 - beta):
        s0 = share(1, b, T, x0); r0 = abs(s0) / x0**mp.mpf(1.5)
        for n in (100, 1000, 2000):
            xn = x0 * e**n; rn = abs(share(1, b, T, xn)) / xn**mp.mpf(1.5)
            worst = max(worst, relerr(rn, r0 * mp.e**(n * PI / T * (b - mp.mpf(1) / 2))))
        growth.append(float((abs(share(1, b, T, x0 * e**2000)) / (x0 * e**2000)**mp.mpf(1.5)) / r0))
    pair[str(float(beta))] = dict(forme_close_err_max=worst, rapport_2000_cellules_membre_bas=growth[0],
                                  rapport_2000_cellules_miroir=growth[1], hauteur=float(T))
sec["paire_temoin"] = pair
OUT["psi1"] = sec
print("Ψ1", json.dumps(sec), flush=True)

# ---------------- Ψ2 ----------------
sec = {}
H = 2000
rhos = [mp.mpc(mp.mpf(1) / 2, mp.mpf(g)) for g in allg[:H]]
def total(x, T, rhos_):
    e = mp.e**(PI / T)
    return mp.fsum(2 * mp.re(K(x * e, r) - K(x, r)) for r in rhos_)  # poids 1, paires conjuguées (2 Re)
worst2 = 0.0
for k in (0, 1, 4, 9, 19):
    T = mp.mpf(allg[k]); e = mp.e**(PI / T); beta = mp.mpf(1) / 2
    f = -mp.e**(PI / T * (1 + beta))
    others = [r for i, r in enumerate(rhos) if i != k]
    for n in range(0, 50, 7):
        x = mp.mpf(1000) * e**n
        lhs = total(x * e, T, rhos) - f * total(x, T, rhos)
        rhs = mp.fsum(2 * mp.re(K(x * e * e, r) - K(x * e, r)) - f * 2 * mp.re(K(x * e, r) - K(x, r)) for r in others)
        worst2 = max(worst2, float(abs(lhs - rhs) / max(abs(rhs), mp.mpf(1e-300))))
sec["annulation_une_tour_err_rel_max"] = worst2
# résidu de l'annulateur de la ligne : nul sur une Tour de ligne, forme close sur la paire
T = mp.mpf(allg[999]); e = mp.e**(PI / T); fL = -mp.e**(PI / T * mp.mpf(1.5))
x = mp.mpf(1000)
res_line = abs(share(1, mp.mpf(1) / 2, T, x * e) - fL * share(1, mp.mpf(1) / 2, T, x))
worst3 = 0.0
for beta in (mp.mpf("0.3"), mp.mpf("0.4")):
    fb = -mp.e**(PI / T * (1 + beta))
    for n in (0, 10, 100):
        xn = x * e**n
        lhs = share(1, beta, T, xn * e) - fL * share(1, beta, T, xn)
        rhs = (fb - fL) * fb**n * share(1, beta, T, x)
        worst3 = max(worst3, relerr(abs(lhs), abs(rhs)))
sec["residu_ligne_sur_tour_de_ligne"] = float(res_line)
sec["residu_ligne_paire_forme_close_err_max"] = worst3
OUT["psi2"] = sec
print("Ψ2", json.dumps(sec), flush=True)

# ---------------- Ψ3 ----------------
N = 10**6
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5) + 1):
    if sieve[i]: sieve[i * i::i] = False
primes = np.nonzero(sieve)[0]
logp = np.log(primes.astype(np.float64))
sec = {}
for beta in (0.3, 0.4, 0.45, 0.5):
    asym = np.cumsum((1 - beta) * logp - beta * logp)
    theta = np.cumsum(logp)
    err = float(np.max(np.abs(asym - (1 - 2 * beta) * theta) / np.maximum(np.abs((1 - 2 * beta) * theta), 1e-300))) if beta != 0.5 else float(np.max(np.abs(asym)))
    vals = {}
    for Nk in (10**3, 10**4, 10**5, 10**6):
        idx = np.searchsorted(primes, Nk, side="right") - 1
        vals[str(Nk)] = dict(theta=float(theta[idx]), asymetrie_cumulee=float(asym[idx]), nb_premiers=int(idx + 1))
    sec[str(beta)] = dict(err_identite_max=err, valeurs=vals)
OUT["psi3"] = sec
print("Ψ3", json.dumps(sec), flush=True)

# ---------------- Ψ4 ----------------
sec = {}
worst4, worst_bound = 0.0, 0.0
x0 = mp.mpf(1000)
for k in range(5):
    T = mp.mpf(allg[k]); beta = mp.mpf(1) / 2; e = mp.e**(PI / T)
    E = mp.e**(PI / T * (1 + beta)); s0 = share(1, beta, T, x0)
    acc = mp.mpc(0); bound = abs(s0) / ((E - 1) * x0**mp.mpf(1.5))
    for n in range(500):
        acc += (-1)**n * share(1, beta, T, x0 * e**n)
        if n + 1 in (1, 10, 100, 500):
            Nn = n + 1
            closed = s0 * (E**Nn - 1) / (E - 1)
            worst4 = max(worst4, relerr(abs(acc), abs(closed)))
            rel = abs(acc) / (x0 * e**Nn)**mp.mpf(1.5)
            worst_bound = max(worst_bound, float(rel / bound))
sec["forme_close_err_max"] = worst4
sec["ligne_rapport_a_la_borne_max"] = worst_bound
T = mp.mpf(allg[999]); e = mp.e**(PI / T); pair = {}
for beta in (mp.mpf("0.3"), mp.mpf("0.4")):
    out = {}
    for b in (beta, 1 - beta):
        E = mp.e**(PI / T * (1 + b)); s0 = share(1, b, T, x0)
        rels = {}
        for Nn in (1, 100, 500, 2000):
            closed = s0 * (E**Nn - 1) / (E - 1)
            rels[str(Nn)] = float(abs(closed) / (x0 * e**Nn)**mp.mpf(1.5))
        out["membre_bas" if b == beta else "miroir"] = rels
    pair[str(float(beta))] = out
sec["paire_temoin_somme_alternee_relative"] = pair
OUT["psi4"] = sec
print("Ψ4", json.dumps(sec), flush=True)

# ---------------- Ψ5 ----------------
sec = {}
g = allg; rho_im = g
XMAX = 300000
lam = np.zeros(XMAX + 2)
sv = np.ones(XMAX + 2, dtype=bool); sv[:2] = False
for i in range(2, int((XMAX + 1)**0.5) + 1):
    if sv[i]: sv[i * i::i] = False
for p in np.nonzero(sv)[0]:
    q = p
    while q <= XMAX + 1:
        lam[q] = math.log(p); q *= p
psi_exact = np.cumsum(lam)
coef_c = 2 * 0.5 / (0.25 + g * g); coef_s = 2 * g / (0.25 + g * g)
grid = np.unique(np.round(np.geomspace(1000, XMAX, 60)).astype(int))
res, defect = [], {b: [] for b in (0.3, 0.4, 0.45)}
k1000 = 999; g1 = g[k1000]
for n in grid:
    x = n + 0.5; L = math.log(x); a = g * L
    psi_hat = x - math.sqrt(x) * float(np.dot(coef_c, np.cos(a)) + np.dot(coef_s, np.sin(a))) - math.log(2 * math.pi) - 0.5 * math.log(1 - x**-2)
    res.append(psi_hat - psi_exact[n])
    line_term = 2 * (x**0.5 * complex(math.cos(g1 * L), math.sin(g1 * L)) / complex(0.5, g1)).real
    for b in defect:
        pt = 2 * (x**b * complex(math.cos(g1 * L), math.sin(g1 * L)) / complex(b, g1)).real \
           + 2 * (x**(1 - b) * complex(math.cos(g1 * L), math.sin(g1 * L)) / complex(1 - b, g1)).real
        defect[b].append(pt - line_term)
res = np.array(res); lx = np.log(grid.astype(float))
sec["residu_recomposition"] = dict(max_abs=float(np.max(np.abs(res))), median_abs=float(np.median(np.abs(res))),
                                  cellule_fine_max=float(math.pi * XMAX / g[-1]))
for b in defect:
    d = np.abs(np.array(defect[b])) / np.sqrt(grid)
    # enveloppe par blocs de 10 points, pente log-log
    nb = len(d) // 10
    env_x = np.array([lx[i * 10:(i + 1) * 10].mean() for i in range(nb)])
    env_y = np.array([np.log(d[i * 10:(i + 1) * 10].max()) for i in range(nb)])
    slope = float(np.polyfit(env_x, env_y, 1)[0])
    sec[f"paire_{b}"] = dict(exposant_attendu=0.5 - b, exposant_mesure_enveloppe=slope,
                            defaut_cumule_abs=float(np.sum(np.abs(defect[b]))),
                            defaut_relatif_debut=float(d[0]), defaut_relatif_fin=float(d[-1]),
                            residu_cumule_abs=float(np.sum(np.abs(res))))
OUT["psi5"] = sec
print("Ψ5", json.dumps(sec), flush=True)
OUT["duree_s"] = time.time() - t0
with open(os.path.join(HERE, "twin_results.json"), "w") as fjs:
    json.dump(OUT, fjs, indent=1)
print(f"FIN ; duree {time.time()-t0:.1f} s", flush=True)
