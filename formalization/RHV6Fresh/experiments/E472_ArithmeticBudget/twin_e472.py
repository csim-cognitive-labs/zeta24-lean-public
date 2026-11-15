#!/usr/bin/env python3
"""E472 phase B — jumeau déterministe, pré-enregistré. Budget arithmétique alterné sur les premiers RÉELS, séparé du fond,
contre le côté des zéros (formes closes, 1M et 2M zéros), paire artificielle, somme naturelle contre somme à signes rectifiés.
Aucune sortie fabriquée. Tout ce qui est imprimé est calculé."""
import json, math, os, time
import numpy as np
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
ZEROS = os.path.join(HERE, "..", "data", "odlyzko_zeros6_2001052.txt")
OUT = {}
t0 = time.time()
XMAX = 30_000_000
X0 = 1000.0
TOWERS = [0, 1, 2, 4, 9, 19, 99, 999]      # zéros n° 1, 2, 3, 5, 10, 20, 100, 1000
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
psi = np.cumsum(lam)                                   # ψ(n)
nlam = np.cumsum(lam * np.arange(XMAX + 2, dtype=np.float64))   # Σ_{m≤n} m Λ(m)
log(f"premiers : {primes.size} ; ψ({XMAX}) = {psi[XMAX]:.6f}")
OUT["premiers"] = dict(XMAX=XMAX, nb_premiers=int(primes.size), psi_XMAX=float(psi[XMAX]))

def demand_area(a, b):
    """demandArea a b = rawDemand a (b−a) − (b−a)²/2 + Σ_{⌊a⌋<n≤⌊b⌋} Λ(n)(b−n)  (définition compilée, S3)."""
    fa, fb = int(math.floor(a)), int(math.floor(b))
    raw = psi[fa] - a
    s = b * (psi[fb] - psi[fa]) - (nlam[fb] - nlam[fa])
    return raw * (b - a) - (b - a) ** 2 / 2 + s

def demand_area_direct(a, b):
    fa, fb = int(math.floor(a)), int(math.floor(b))
    n = np.arange(fa + 1, fb + 1)
    return (psi[fa] - a) * (b - a) - (b - a) ** 2 / 2 + float(np.sum(lam[n] * (b - n)))

# jumeau de la définition : forme cumulée contre somme directe
chk = []
for (a, b) in ((1000.0, 1234.5), (54321.7, 60000.2), (2.0e6, 2.1e6)):
    d1, d2 = demand_area(a, b), demand_area_direct(a, b)
    chk.append(abs(d1 - d2) / max(abs(d2), 1e-300))
OUT["definition_demandArea_err_rel_max"] = float(max(chk))
# jumeau de demandArea_add
chk = []
for (a, b, c) in ((1000.0, 2000.0, 3000.0), (12345.6, 23456.7, 34567.8), (1.0e6, 2.5e6, 7.0e6)):
    chk.append(abs(demand_area(a, b) + demand_area(b, c) - demand_area(a, c)) / max(abs(demand_area(a, c)), 1e-300))
OUT["demandArea_add_err_rel_max"] = float(max(chk))
log(f"définition {OUT['definition_demandArea_err_rel_max']:.2e} ; additivité {OUT['demandArea_add_err_rel_max']:.2e}")

# ---------------- constante du fond (RawMeetingRemainder.backgroundConstant) ----------------
mp.mp.dps = 30
ld0 = mp.zeta(0, derivative=1) / mp.zeta(0)
ldm1 = mp.zeta(-1, derivative=1) / mp.zeta(-1)
backgroundConstant = float(abs(-ld0) + abs(ldm1) + mp.pi ** 2 / 6)
OUT["backgroundConstant"] = dict(valeur=backgroundConstant, logderiv_zeta_0=float(ld0), logderiv_zeta_m1=float(ldm1))
log(f"backgroundConstant = {backgroundConstant:.6f}")

# ---------------- zéros ----------------
allg = np.loadtxt(ZEROS, dtype=np.float64)
log(f"zéros lus : {allg.size}")
H2, H1 = allg.size, allg.size // 2
rho = 0.5 + 1j * allg                                    # ligne, poids −1 (ψ₁ = x²/2 − Σ x^{ρ+1}/(ρ(ρ+1)) − …)

def K(x, r):
    return np.exp((r + 1) * math.log(x)) / (r * (r + 1))

def zero_side_alternating(T, N, H):
    """−Σ_{j<H} 2 Re[ share_j(x0) ((−q_j)^N − 1)/(−q_j − 1) ],  q_j = e^{π(ρ_j+1)/T}, cellules de la Tour T."""
    r = rho[:H]
    e = math.exp(PI / T)
    share0 = K(X0 * e, r) - K(X0, r)
    q = np.exp(PI * (r + 1) / T)
    mq = -q
    # (−q)^N = (−1)^N e^{1.5 N π/T} e^{i N π γ/T}
    mag = math.exp(1.5 * N * PI / T) * ((-1) ** N)
    ph = np.mod(N * PI * allg[:H] / T, 2 * PI)
    mqN = mag * np.exp(1j * ph)
    s = share0 * (mqN - 1) / (mq - 1)
    return -2.0 * float(np.sum(s.real))

def zero_side_natural(T, N, H):
    """−Σ 2 Re[ K_j(x_N) − K_j(x0) ]  (télescopage, towerNaturalSum_telescope)."""
    r = rho[:H]
    xN = X0 * math.exp(N * PI / T)
    return -2.0 * float(np.sum((K(xN, r) - K(X0, r)).real))

# ---------------- par Tour ----------------
towers_out = {}
for k in TOWERS:
    T = float(allg[k]); e = math.exp(PI / T); g = math.exp(PI / T * 1.5)
    Nmax = int(math.floor(math.log(XMAX / X0) / (PI / T))) - 1
    xs = X0 * e ** np.arange(Nmax + 1)
    a = np.array([demand_area(xs[n], xs[n] * e) for n in range(Nmax)])      # aires de cellule a_n
    sign = (-1.0) ** np.arange(Nmax)
    A = np.cumsum(sign * a)                      # budget arithmétique alterné A_N (N = 1..Nmax)
    Nat = np.cumsum(a)                           # budget naturel
    Rect = np.cumsum(np.abs(a))                  # somme des modules côté premiers
    xN = xs[1:]                                  # x_N pour N = 1..Nmax
    scale = xN ** 1.5
    # jumeau du télescopage côté premiers (naturalCellTotal_eq_telescope, partie arithmétique)
    tel = np.array([demand_area(X0, xs[N]) for N in range(1, Nmax + 1)])
    err_tel = float(np.max(np.abs(Nat - tel) / np.maximum(np.abs(tel), 1e-300)))
    # alternance de signe des aires côté premiers
    alt_frac = float(np.mean(np.sign(a[1:]) == -np.sign(a[:-1]))) if Nmax > 1 else float("nan")
    # points de mesure
    Ns = sorted(set(int(v) for v in np.geomspace(max(2, Nmax // 50), Nmax, 8)))
    rows = []
    for N in Ns:
        xNv = xs[N]; sc = xNv ** 1.5
        Z2 = zero_side_alternating(T, N, H2); Z1 = zero_side_alternating(T, N, H1)
        R = A[N - 1] - Z2
        bg_bound = backgroundConstant * (e + 1) / (e - 1) * xNv
        Znat2 = zero_side_natural(T, N, H2)
        Rnat = Nat[N - 1] - Znat2
        rows.append(dict(N=N, x_N=float(xNv),
                         A_rel=float(A[N - 1] / sc), Nat_rel=float(Nat[N - 1] / sc), Rect_rel=float(Rect[N - 1] / sc),
                         Z2M_rel=float(Z2 / sc), troncature_rel=float((Z2 - Z1) / sc),
                         residu_rel_ligne=float(R / sc), residu_sur_xN=float(R / xNv),
                         borne_fond_sur_xN=float(bg_bound / xNv), borne_fond_rel_ligne=float(bg_bound / sc),
                         residu_naturel_sur_xN=float(Rnat / xNv),
                         cellule_rel=float(a[N - 1] / sc), deux_cellules_rel=float((a[N - 1] + a[N - 2]) / sc)))
    # la Tour elle-même : somme naturelle contre somme à signes rectifiés (B2), bornes compilées
    r0 = rho[k]
    def share_line(x):
        return K(x * e, r0) - K(x, r0)
    ratios = []
    for N in Ns:
        rect = sum(abs(share_line(xs[n])) for n in range(N))          # = ‖towerAlternatingSum‖ (sum_norms)
        natural = abs(K(xs[N], r0) - K(X0, r0))                       # = ‖towerNaturalSum‖ (telescope)
        closed_rect = abs(share_line(X0)) * (g ** N - 1) / (g - 1)
        ratios.append(dict(N=N, naturel_sur_rectifie=float(natural / rect), borne_basse=(g - 1) / (g + 1),
                           rectifie_forme_close_err=float(abs(rect - closed_rect) / closed_rect)))
    towers_out[str(k + 1)] = dict(T=T, cellules=Nmax, x_Nmax=float(xs[Nmax]), telescopage_premiers_err_rel_max=err_tel,
                                 fraction_alternance_signe_aires=alt_frac,
                                 A_rel_max=float(np.max(np.abs(A) / scale)), A_rel_fin=float(A[-1] / scale[-1]),
                                 Nat_rel_max=float(np.max(np.abs(Nat) / scale)), Rect_rel_fin=float(Rect[-1] / scale[-1]),
                                 mesures=rows, tour_naturel_vs_rectifie=ratios)
    log(f"Tour {k+1} (T={T:.3f}) : {Nmax} cellules ; A_rel max {towers_out[str(k+1)]['A_rel_max']:.4f} ; "
        f"résidu/x_N fin {rows[-1]['residu_sur_xN']:.4f} (borne fond {rows[-1]['borne_fond_sur_xN']:.2f}) ; "
        f"troncature rel {rows[-1]['troncature_rel']:.2e}")
OUT["tours"] = towers_out

# ---------------- paire artificielle à la hauteur de la Tour n°1000 (audit §4) ----------------
k = 999; T = float(allg[k]); e = math.exp(PI / T)
Nmax = int(math.floor(math.log(XMAX / X0) / (PI / T))) - 1
Ns = sorted(set(int(v) for v in np.geomspace(max(2, Nmax // 50), Nmax, 8)))
def alt_closed(b, N):
    r = complex(b, T); q = np.exp(PI * (r + 1) / T)
    s0 = K(X0 * e, r) - K(X0, r)
    return s0 * ((-q) ** N - 1) / (-q - 1)
pair_out = {}
for b in (0.3, 0.4, 0.45):
    rows = []
    for N in Ns:
        sc = (X0 * e ** N) ** 1.5
        L = alt_closed(0.5, N)                       # Tour de ligne à cette hauteur (poids −1 ; 2 Re pour la conjuguée)
        Sb, Sm = alt_closed(b, N), alt_closed(1 - b, N)
        pair_complex = -2 * (Sb + Sm).real; line = -2 * L.real
        rows.append(dict(N=N, paire_complexe_rel=float(pair_complex / sc), ligne_rel=float(line / sc),
                         defaut_rel=float((pair_complex - line) / sc),
                         somme_des_normes_rel=float((abs(Sb) + abs(Sm)) / sc), norme_de_la_somme_rel=float(abs(Sb + Sm) / sc)))
    pair_out[str(b)] = rows
OUT["paire_artificielle_T1000"] = dict(T=T, mesures=pair_out)
log("paire artificielle calculée")

OUT["duree_s"] = time.time() - t0
with open(os.path.join(HERE, "twin_results.json"), "w") as f:
    json.dump(OUT, f, indent=1)
log("FIN")
