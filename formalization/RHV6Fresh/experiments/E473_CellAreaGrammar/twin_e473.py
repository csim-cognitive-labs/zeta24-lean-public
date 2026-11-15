#!/usr/bin/env python3
"""E473 phase B — jumeau déterministe, pré-enregistré. Grammaire des aires entre contacts consécutifs sur les premiers RÉELS :
identités G1–G3 (sommes de cellule calculées DIRECTEMENT sur les entiers de la cellule, math.fsum), stabilité numérique contre la
formule cumulée d'E472, mesures des termes locaux, des signes et de la transmission. Aucune sortie fabriquée."""
import json, math, os, time, itertools
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ZEROS = os.path.join(HERE, "..", "data", "odlyzko_zeros6_2001052.txt")
OUT = {}
t0 = time.time()
XMAX = 30_000_000
XMIN = 1000.0
TOWERS = [0, 1, 2, 4, 9, 19, 99, 999]      # zéros n° 1, 2, 3, 5, 10, 20, 100, 1000
BETA = 0.5
PI = math.pi

def log(msg):
    print(f"[{time.time()-t0:8.1f}s] {msg}", flush=True)

# ---------------- premiers, Λ, ψ, Σ nΛ ----------------
log(f"crible jusqu'à {XMAX}")
sieve = np.ones(XMAX + 2, dtype=bool); sieve[:2] = False
for i in range(2, int((XMAX + 1) ** 0.5) + 1):
    if sieve[i]:
        sieve[i * i::i] = False
primes = np.nonzero(sieve)[0]
lam = np.zeros(XMAX + 2, dtype=np.float64)
lam[primes] = np.log(primes.astype(np.float64))
for p in primes[primes <= int((XMAX + 1) ** 0.5) + 1]:
    q = int(p) * int(p)
    while q <= XMAX + 1:
        lam[q] = math.log(p); q *= int(p)
del sieve
psi = np.cumsum(lam)                                                   # ψ(n), utilisé pour la demande au contact
nlam = np.cumsum(lam * np.arange(XMAX + 2, dtype=np.float64))         # Σ_{m≤n} m Λ(m) (formule cumulée d'E472, pour la stabilité)
log(f"premiers : {primes.size} ; ψ({XMAX}) = {psi[XMAX]:.6f}")
OUT["premiers"] = dict(XMAX=XMAX, nb_premiers=int(primes.size), psi_XMAX=float(psi[XMAX]))

with open(ZEROS) as f:
    gam = [float(l.split()[0]) for l in itertools.islice(f, 1000)]
log(f"zéros lus (1000 premiers) : γ_1 = {gam[0]:.6f}, γ_1000 = {gam[999]:.6f}")

def demand_area_cumul(a, b):
    """Formule cumulée d'E472 (rawDemand a (b−a) − (b−a)²/2 + b Σ Λ − Σ nΛ) : instable à grand x."""
    fa, fb = int(math.floor(a)), int(math.floor(b))
    raw = psi[fa] - a
    s = b * (psi[fb] - psi[fa]) - (nlam[fb] - nlam[fa])
    return raw * (b - a) - (b - a) ** 2 / 2 + s

towers_out = {}
for k in TOWERS:
    T = gam[k]; g = math.exp(PI / T); phi = math.atan(T / BETA)
    def contact(j):
        return math.exp((phi + j * PI) / T)
    k0 = math.ceil((T * math.log(XMIN) - phi) / PI)
    kmax = math.floor((T * math.log(XMAX) - phi) / PI)       # contact ≤ XMAX
    ks = list(range(k0, kmax))                              # cellules [C_k, C_{k+1}], C_{k+1} ≤ XMAX
    M = len(ks)
    x = np.array([contact(j) for j in range(k0, kmax + 1)])  # contacts C_{k0..kmax}
    ell = x[1:] - x[:-1]
    D = np.array([psi[int(math.floor(c))] - c for c in x])   # rawDemand aux contacts
    W = np.zeros(M); P = np.zeros(M); Q = np.zeros(M)
    for i in range(M):
        fa, fb = int(math.floor(x[i])), int(math.floor(x[i + 1]))
        n = np.arange(fa + 1, fb + 1, dtype=np.float64)
        ln = lam[fa + 1:fb + 1]
        W[i] = math.fsum(ln.tolist())
        P[i] = math.fsum((ln * (x[i + 1] - n)).tolist())
        Q[i] = math.fsum((ln * (n - x[i])).tolist())
    a = D[:-1] * ell - ell ** 2 / 2 + P                      # G1 : cellArea = cellDescentArea + cellExitWeight
    eps = P - ell ** 2 / 2; eta = Q - ell ** 2 / 2
    L = eps[1:] + g * eta[:-1]                                # localGrammarTerm L_k, k = 0..M-2
    # 1. jumeau G1 : P + Q = W ℓ
    g1 = np.max(np.abs(P + Q - W * ell) / np.maximum(W * ell, 1e-300))
    # 2. jumeau G2 : a_{k+1} − g a_k = L_k, rapporté à ℓ_k²
    g2 = np.max(np.abs(a[1:] - g * a[:-1] - L) / ell[:-1] ** 2)
    # 3. jumeau G3 : (1+g) A_{N+1} = a_0 + (−1)^N g a_N − Σ_{n<N} (−1)^n L_n, rapporté à ℓ_N²
    sgn = (-1.0) ** np.arange(M)
    A = np.cumsum(sgn * a)                                    # A_{N+1} = Σ_{n≤N}
    SL = np.concatenate(([0.0], np.cumsum(sgn[:-1] * L)))      # Σ_{n<N} (−1)^n L_n
    res3 = (1 + g) * A - (a[0] + sgn * g * a - SL)
    g3 = np.max(np.abs(res3) / ell ** 2)
    # 4. stabilité : formule de cellule contre formule cumulée
    a_cum = np.array([demand_area_cumul(x[i], x[i + 1]) for i in range(M)])
    stab = np.abs(a_cum - a) / np.maximum(np.abs(a), 1e-300)
    # 5. mesures
    x32 = x[:-1] ** 1.5
    Lrel = np.abs(L) / x32[:-1]
    arel = np.abs(a) / x32
    aell = np.abs(a) / ell ** 2
    signchange = (a[:-1] * a[1:] <= 0)
    Arel = np.abs(A) / x[1:] ** 1.5
    # transmission (G4) sur la plus longue fenêtre initiale d'alternance
    run = 0
    while run < M - 1 and signchange[run]:
        run += 1
    transfer = None
    if run > 0:
        lhs = abs(A[run]); rhs = abs(a[0]) + float(np.sum(np.abs(L[:run])))
        transfer = dict(fenetre_cellules=run + 1, budget_abs=lhs, borne_G4=rhs, rapport=lhs / rhs)
    # clôture conditionnelle G6 : constante mesurée C = max(|L_n|/C_n^{3/2}, |a|/C^{3/2}) et borne compilée résultante
    C = max(float(np.max(Lrel)), float(np.max(arel)))
    r32 = g ** 1.5
    borne_G6 = C * (1 + g + 1 / (r32 - 1)) / (1 + g)
    towers_out[str(k + 1)] = dict(
        T=T, cellules=M, k0=int(k0), x_debut=float(x[0]), x_fin=float(x[-1]), g=g,
        G1_err_rel_max=float(g1), G2_err_sur_ell2_max=float(g2), G3_err_sur_ell2_max=float(g3),
        stabilite_cumul_vs_cellule=dict(max=float(np.max(stab)), mediane=float(np.median(stab)),
                                        derniere=float(stab[-1])),
        L_rel_max=float(np.max(Lrel)), L_rel_dernier=float(Lrel[-1]),
        a_rel_max=float(np.max(arel)), a_rel_dernier=float(arel[-1]),
        a_sur_ell2_max=float(np.max(aell)), a_sur_ell2_dernier=float(aell[-1]),
        fraction_changements_signe=float(np.mean(signchange)), alternance_initiale_cellules=int(run + 1),
        A_rel_max=float(np.max(Arel)), A_rel_dernier=float(Arel[-1]),
        transmission_G4=transfer, C_mesure_G6=C, borne_G6_sur_x32=borne_G6,
        L_signe_negatif_fraction=float(np.mean(L < 0)),
    )
    log(f"Tour {k+1} (T={T:.3f}, {M} cellules) : G1 {g1:.1e} G2 {g2:.1e} G3 {g3:.1e} | stab max {np.max(stab):.1e} "
        f"| |L|/x^1.5 max {np.max(Lrel):.4f} | |a|/x^1.5 max {np.max(arel):.4f} | |a|/ℓ² dernier {aell[-1]:.2e} "
        f"| signes {np.mean(signchange):.2f} | |A|/x^1.5 max {np.max(Arel):.4f} | G6 {borne_G6:.3f}")

OUT["tours"] = towers_out
conf1 = all(v["G1_err_rel_max"] < 1e-10 for v in towers_out.values())
conf2 = all(v["G2_err_sur_ell2_max"] < 1e-9 for v in towers_out.values())
conf3 = all(v["G3_err_sur_ell2_max"] < 1e-9 for v in towers_out.values())
OUT["verdict"] = dict(point1=conf1, point2=conf2, point3=conf3, lettre="A" if (conf1 and conf2 and conf3) else "B")
OUT["duree_s"] = time.time() - t0
with open(os.path.join(HERE, "twin_results.json"), "w") as f:
    json.dump(OUT, f, indent=1)
log(f"verdict {OUT['verdict']} ; écrit twin_results.json")
