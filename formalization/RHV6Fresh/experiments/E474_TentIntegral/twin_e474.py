#!/usr/bin/env python3
"""E474 phase B — jumeau déterministe, pré-enregistré. Quatre hypothèses testées sur les premiers RÉELS, contacts réels (β = 1/2),
formule de cellule (R-Ψ quater), sommes de cellule par math.fsum. Aucune sortie fabriquée.
H1 tente ; H2 mémoire un + autocorrélations ; H3 loi d'échelle en 1/T + inégalité compilée |L_k| ≤ 2gℓ_k M_k ; H4 contrôle intérieur."""
import json, math, os, time, itertools
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ZEROS = os.path.join(HERE, "..", "data", "odlyzko_zeros6_2001052.txt")
OUT = {}
t0 = time.time()
XMAX = 30_000_000
XMIN = 1000.0
TOWERS = [1, 2, 3, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000]   # numéros de zéros
BETA = 0.5
PI = math.pi

def log(msg):
    print(f"[{time.time()-t0:8.1f}s] {msg}", flush=True)

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
psi = np.cumsum(lam)                                   # ψ(n)
Dint = psi - np.arange(XMAX + 2, dtype=np.float64)     # rawDemand aux entiers ; sur [n, n+1) la demande descend de D(n) à D(n)−1
Dsup = np.maximum(np.abs(Dint), np.abs(Dint - 1.0))    # majorant de |rawDemand| sur [n, n+1)
log(f"premiers : {primes.size} ; ψ({XMAX}) = {psi[XMAX]:.6f}")
OUT["premiers"] = dict(XMAX=XMAX, nb_premiers=int(primes.size), psi_XMAX=float(psi[XMAX]))

with open(ZEROS) as f:
    gam = [float(l.split()[0]) for l in itertools.islice(f, 5000)]
log(f"zéros lus (5000) : γ_1 = {gam[0]:.6f}, γ_5000 = {gam[4999]:.6f}")

def sup_abs_D(a, b):
    """majorant de sup |rawDemand| sur (a, b] : max de Dsup sur les entiers ⌊a⌋..⌊b⌋ (chaque entier n couvre [n, n+1))."""
    fa, fb = int(math.floor(a)), int(math.floor(b))
    return float(np.max(Dsup[fa:fb + 1]))

def sup_var_D(a, b, Da):
    """majorant de sup |rawDemand t − rawDemand a| sur (a, b]."""
    fa, fb = int(math.floor(a)), int(math.floor(b))
    seg = Dint[fa:fb + 1] - Da
    return float(max(np.max(np.abs(seg)), np.max(np.abs(seg - 1.0))))

def autocorr(y, j):
    if len(y) <= j + 2:
        return None
    a, b = y[:-j], y[j:]
    if np.std(a) == 0 or np.std(b) == 0:
        return None
    return float(np.corrcoef(a, b)[0, 1])

towers_out = {}
for num in TOWERS:
    T = gam[num - 1]; g = math.exp(PI / T); phi = math.atan(T / BETA)
    def contact(j):
        return math.exp((phi + j * PI) / T)
    k0 = math.ceil((T * math.log(XMIN) - phi) / PI)
    kmax = math.floor((T * math.log(XMAX) - phi) / PI)
    ks = list(range(k0, kmax)); M = len(ks)
    x = np.array([contact(j) for j in range(k0, kmax + 1)])
    ell = x[1:] - x[:-1]
    D = np.array([psi[int(math.floor(c))] - c for c in x])
    W = np.zeros(M); P = np.zeros(M); Q = np.zeros(M)
    for i in range(M):
        fa, fb = int(math.floor(x[i])), int(math.floor(x[i + 1]))
        n = np.arange(fa + 1, fb + 1, dtype=np.float64); ln = lam[fa + 1:fb + 1]
        W[i] = math.fsum(ln.tolist()); P[i] = math.fsum((ln * (x[i + 1] - n)).tolist()); Q[i] = math.fsum((ln * (n - x[i])).tolist())
    a = D[:-1] * ell - ell ** 2 / 2 + P
    eps = P - ell ** 2 / 2; eta = Q - ell ** 2 / 2
    L = eps[1:] + g * eta[:-1]                      # L_k, k = 0..M-2
    Delta = D[1:] - D[:-1]                           # Δ_k = D(C_{k+1}) − D(C_k), k = 0..M-1
    # ---- H1 : tente ----
    tent_res = np.zeros(M - 1)
    for i in range(M - 1):
        fa, fb = int(math.floor(x[i])), int(math.floor(x[i + 2]))
        n = np.arange(fa + 1, fb + 1, dtype=np.float64); ln = lam[fa + 1:fb + 1]
        tent = np.minimum(g * (n - x[i]), x[i + 2] - n)
        S = math.fsum((ln * tent).tolist()) - g * (1 + g) * ell[i] ** 2 / 2
        tent_res[i] = abs(S - L[i]) / ell[i] ** 2
    h1 = float(np.max(tent_res))
    # ---- H2 : mémoire un (identité) + autocorrélations ----
    mem1 = eps[1:] - g * eps[:-1] + g * ell[:-1] * Delta[:-1]
    h2_id = float(np.max(np.abs(mem1 - L) / ell[:-1] ** 2))
    y = L / x[:-2] ** 1.5
    corr = {str(j): autocorr(y, j) for j in range(1, 6)}
    # ---- H3 : loi d'échelle en 1/T ; inégalité compilée ----
    Lrel = np.abs(L) / x[:-2] ** 1.5
    h3_scale = float(np.max(T * Lrel))
    Mk = np.array([sup_abs_D(x[i], x[i + 2]) for i in range(M - 1)])
    bound3 = 2 * g * ell[:-1] * Mk
    h3_ineq_ok = bool(np.all(np.abs(L) <= bound3 * (1 + 1e-12) + 1e-9))
    tight3 = np.abs(L) / bound3
    Mrel = Mk / np.sqrt(x[:-2])
    # ---- H4 : contrôle intérieur ----
    Vk = np.array([sup_var_D(x[i], x[i + 1], D[i]) for i in range(M)])
    h4_ineq_ok = bool(np.all(np.abs(eps) <= ell * Vk * (1 + 1e-12) + 1e-9))
    eps_rel = np.abs(eps) / (ell * np.sqrt(x[:-1]))
    Delta_rel = np.abs(Delta) / np.sqrt(x[:-1])
    V_rel = Vk / np.sqrt(x[:-1])
    partA = eps[1:] - g * eps[:-1]; partB = g * ell[:-1] * Delta[:-1]
    rms_ratio = float(np.sqrt(np.mean(partA ** 2)) / np.sqrt(np.mean(partB ** 2)))
    corr_parts = float(np.corrcoef(partA, partB)[0, 1])
    # ---- budget : borne compilée par la demande (fenêtre entière) ----
    sgn = (-1.0) ** np.arange(M); A = np.cumsum(sgn * a)
    Mwin = sup_abs_D(x[0], x[-1])
    lhs = (1 + g) * abs(A[-1]); rhs = Mwin * (1 + g) ** 2 * x[-2]
    towers_out[str(num)] = dict(
        T=T, cellules=M, x_debut=float(x[0]), x_fin=float(x[-1]), g=g,
        H1_tente_res_max=h1, H2_memoire_un_res_max=h2_id, H2_autocorr=corr,
        H3_T_L_rel_max=h3_scale, H3_L_rel_max=float(np.max(Lrel)), H3_inegalite_compilee_ok=h3_ineq_ok,
        H3_serrage_max=float(np.max(tight3)), H3_serrage_mediane=float(np.median(tight3)),
        H3_M_sur_sqrt_max=float(np.max(Mrel)), H3_M_sur_sqrt_dernier=float(Mrel[-1]),
        H4_inegalite_compilee_ok=h4_ineq_ok, H4_eps_rel_max=float(np.max(eps_rel)), H4_Delta_rel_max=float(np.max(Delta_rel)),
        H4_V_rel_max=float(np.max(V_rel)), H4_rms_ratio_parts=rms_ratio, H4_corr_parts=corr_parts,
        budget_rel_fin=float(abs(A[-1]) / x[-2] ** 1.5), budget_borne_demande_ok=bool(lhs <= rhs),
        budget_sur_borne=float(lhs / rhs), M_fenetre_sur_sqrt=float(Mwin / math.sqrt(x[-1])),
        L_signe_negatif_fraction=float(np.mean(L < 0)),
    )
    log(f"Tour {num} (T={T:.2f}, {M} cell.) : H1 {h1:.1e} H2id {h2_id:.1e} corr1 {corr['1']:+.3f} corr2 {corr['2']:+.3f} "
        f"| T|L|/x^1.5 max {h3_scale:.3f} | ineq3 {h3_ineq_ok} serrage max {np.max(tight3):.3f} | M/√x max {np.max(Mrel):.3f} "
        f"| ineq4 {h4_ineq_ok} ε/(ℓ√x) max {np.max(eps_rel):.3f} Δ/√x max {np.max(Delta_rel):.3f} V/√x max {np.max(V_rel):.3f} "
        f"| rms A/B {rms_ratio:.3f} corr A,B {corr_parts:+.3f} | budget/borne {lhs/rhs:.2e}")

OUT["tours"] = towers_out
tv = towers_out
H1 = all(v["H1_tente_res_max"] < 1e-10 for v in tv.values())
H2id = all(v["H2_memoire_un_res_max"] < 1e-10 for v in tv.values())
c1 = tv["1"]["H2_autocorr"]["1"]; c1000 = tv["1000"]["H2_autocorr"]["1"]
def decroit(c):
    vals = [abs(c[str(j)]) for j in range(1, 6) if c[str(j)] is not None]
    return all(vals[i + 1] <= vals[i] + 0.05 for i in range(len(vals) - 1))
H2 = (c1 is not None and c1 < -0.2) and (c1000 is not None and c1000 > 0.2) and all(decroit(v["H2_autocorr"]) for v in tv.values())
H3 = all(v["H3_T_L_rel_max"] <= 3 for v in tv.values())
ineq = all(v["H3_inegalite_compilee_ok"] and v["H4_inegalite_compilee_ok"] and v["budget_borne_demande_ok"] for v in tv.values())
H4a = all(v["H4_eps_rel_max"] <= 3 and v["H4_Delta_rel_max"] <= 3 for v in tv.values())
H4b = all(1 / 3 <= v["H4_rms_ratio_parts"] <= 3 for v in tv.values())
identites = H1 and H2id and ineq
lettre = "C" if not identites else ("A" if (H2 and H3 and H4a and H4b) else "B")
OUT["verdict"] = dict(H1_identite=H1, H2_identite=H2id, inegalites_compilees=ineq, H2_autocorr=H2, H2_corr1_tour1=c1,
                      H2_corr1_tour1000=c1000, H3_echelle=H3, H4a_echelle_sqrt=H4a, H4b_parts_meme_ordre=H4b, lettre=lettre)
OUT["duree_s"] = time.time() - t0
with open(os.path.join(HERE, "twin_results.json"), "w") as f:
    json.dump(OUT, f, indent=1)
log(f"verdict {OUT['verdict']}")
