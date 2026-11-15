#!/usr/bin/env python3
"""E476 — jumeau déterministe pré-enregistré : tente et cassure. H1 poids de tente de la cassure (deux tentes), H2 la cassure lit la
tente, H3 dent de scie du budget alterné (regroupement + loi des signes), H4 obligation de la paire (poids du miroir). Premiers réels,
contacts réels β = 1/2 ; aucune sortie fabriquée."""
import json, math, os, time, itertools
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
ZEROS = os.path.join(HERE, "..", "data", "odlyzko_zeros6_2001052.txt")
t0 = time.time(); OUT = {}
XMAX = 30_000_000; XMIN = 1000.0; PI = math.pi; BETA = 0.5
TOWERS = [1, 2, 3, 5, 10, 20, 100, 1000]
def log(m): print(f"[{time.time()-t0:8.1f}s] {m}", flush=True)
log(f"crible jusqu'à {XMAX}")
sieve = np.ones(XMAX + 2, dtype=bool); sieve[:2] = False
for i in range(2, int((XMAX + 1) ** 0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
primes = np.nonzero(sieve)[0]
lam = np.zeros(XMAX + 2); lam[primes] = np.log(primes.astype(np.float64))
for p in primes[primes <= int((XMAX + 1) ** 0.5) + 1]:
    q = int(p)*int(p)
    while q <= XMAX + 1: lam[q] = math.log(p); q *= int(p)
del sieve
supp = np.nonzero(lam)[0]; supp = supp[supp >= XMIN]        # support de Λ au-dessus de XMIN
LAM = lam[supp]; X = supp.astype(np.float64)
log(f"premiers : {primes.size} ; support Λ ≥ {XMIN:.0f} : {supp.size}")
with open(ZEROS) as f:
    gam = [float(l.split()[0]) for l in itertools.islice(f, 1000)]
OUT["tours"] = {}
for tz in TOWERS:
    T = gam[tz-1]; g = math.exp(PI/T); phi = math.atan(T/BETA); rho = abs(complex(BETA, T))
    stage = (T*np.log(X) - phi)/PI; k = np.floor(stage); f = stage - k
    C = lambda kk: np.exp((phi + kk*PI)/T)
    Ck, Ck1, Ck2 = C(k), C(k+1), C(k+2)
    # H1 : formules compilées contre la tente directe
    w_direct = np.minimum(g*(X - Ck), Ck2 - X)                    # tentKernel k x
    w_prev_direct = np.minimum(g*(X - C(k-1)), Ck1 - X)           # tentKernel (k-1) x
    w = g*X*(1 - np.exp(-PI*f/T)); w_prev = X*(g*np.exp(-PI*f/T) - 1)
    h1 = max(np.max(np.abs(w - w_direct)/X), np.max(np.abs(w_prev - w_prev_direct)/X))
    # H2 : amplitude de la cassure
    v_abs = Ck**BETA/rho; v_tent = X**BETA*(1 - w/(g*X))**BETA/rho
    h2 = float(np.max(np.abs(v_abs - v_tent)/v_abs))
    # H3 : dent de scie
    saw = (1+g)*X - 2*Ck1; h3_id = float(np.max(np.abs((w - w_prev) - saw)/X))
    f0 = (T/PI)*math.log(2*g/(1+g)); frac_pos = float(np.mean(saw > 0)); pred = 1 - f0
    # H3a : regroupement sur la fenêtre k0..k0+N (cellules complètes dans [XMIN, XMAX])
    kmin, kmax = int(k.min()), int(k.max())
    k0 = kmin + 1; N = kmax - k0 - 1                               # tentes k0..k0+N-1, cellules k0..k0+N toutes complètes
    kk = np.arange(k0, k0 + N + 1); Ck0 = C(kk.astype(float)); ell = C(kk+1.0) - Ck0
    # termes locaux L_{k0+n} par la tente (E474) : Σ_{cellules n, n+1} Λ·tente_n − g(1+g)ℓ_n²/2
    cell_idx = (k - k0).astype(int)
    # contributions : w dans sa propre tente (indice j = cell_idx), w_prev dans la tente précédente (indice j-1)
    L = np.zeros(N)
    for j in range(N):
        m_own = cell_idx == j; m_prev = cell_idx == j + 1
        L[j] = math.fsum((LAM[m_own]*w[m_own]).tolist()) + math.fsum((LAM[m_prev]*w_prev[m_prev]).tolist()) - g*(1+g)*ell[j]**2/2
    sgn = (-1.0)**np.arange(N); budget = math.fsum((sgn*L).tolist())
    # regroupement par premiers : cellule 0 → +w ; cellules 1..N-1 → (−1)^j saw ; cellule N → (−1)^{N−1} w_prev
    j = cell_idx; contrib = np.where(j == 0, w, np.where(j == N, (-1.0)**(N-1)*w_prev, (-1.0)**j*saw))
    mask = (j >= 0) & (j <= N)
    regroup = math.fsum((LAM[mask]*contrib[mask]).tolist()) - math.fsum((sgn*g*(1+g)*ell[:N]**2/2).tolist())
    scale = math.fsum((LAM[mask]*np.abs(contrib[mask])).tolist())
    h3a = abs(budget - regroup)/scale
    # contenu premier signé de la dent de scie (cellules intérieures) rapporté à x_N^{3/2}
    inner = (j >= 1) & (j <= N-1)
    saw_sum = math.fsum((LAM[inner]*(-1.0)**j[inner]*saw[inner]).tolist())
    xN = C(float(k0 + N))
    OUT["tours"][str(tz)] = dict(T=T, cellules=N+1, premiers=int(mask.sum()), H1_residu=float(h1), H2_residu=h2,
        H3_identite=h3_id, H3_fraction_positive=frac_pos, H3_prediction=pred, H3_ecart=abs(frac_pos-pred), f0=f0,
        H3a_regroupement=float(h3a), budget=budget, budget_sur_x32=budget/xN**1.5, saw_sum_sur_x32=saw_sum/xN**1.5,
        saw_abs_median_sur_x=float(np.median(np.abs(saw)/X)), w_sur_gx_median=float(np.median(w/(g*X))))
    log(f"Tour {tz} T={T:.3f} cellules {N+1} premiers {mask.sum()} | H1 {h1:.1e} H2 {h2:.1e} H3id {h3_id:.1e} | pos {frac_pos:.4f} préd {pred:.4f} "
        f"| regroup {h3a:.1e} | budget/x^1.5 {budget/xN**1.5:.4f} saw/x^1.5 {saw_sum/xN**1.5:.4f}")
    if tz == 1:   # H4 : paire fictive à T_1
        H4 = {}
        for b in (0.5, 0.45, 0.4, 0.3):
            delta = math.atan(T/b) - math.atan(T/(1-b))
            fs = np.mod(f + delta/PI, 1.0); ws = g*X*(1 - np.exp(-PI*fs/T))
            rel = np.abs(ws - w)/(g*X)
            shift = np.floor(stage + delta/PI) - k
            H4[f"beta_{b:.2f}"] = dict(delta_sur_pi=delta/PI, diff_rel_mediane=float(np.median(rel)), diff_rel_max=float(np.max(rel)),
                                       fraction_mot_decale=float(np.mean(shift != 0)))
        OUT["H4"] = H4
        log(f"H4 : " + " ; ".join(f"β={b}: méd {H4[f'beta_{b:.2f}']['diff_rel_mediane']:.2e}, mot décalé {H4[f'beta_{b:.2f}']['fraction_mot_decale']:.3f}" for b in (0.5,0.45,0.4,0.3)))
tv = OUT["tours"].values()
ok1 = all(v["H1_residu"] < 1e-10 for v in tv); ok2 = all(v["H2_residu"] < 1e-10 for v in tv)
ok3a = all(v["H3a_regroupement"] < 1e-9 for v in tv)
ok3b = all(v["H3_ecart"] < 0.02 for v in tv if v["premiers"] >= 10000)
ok4 = OUT["H4"]["beta_0.50"]["diff_rel_mediane"] < 1e-12 and OUT["H4"]["beta_0.40"]["diff_rel_mediane"] > 1e-3
OUT["verdict_jumeau"] = dict(H1=ok1, H2=ok2, H3a=ok3a, H3b=ok3b, H4=ok4)
OUT["duree_s"] = time.time() - t0
json.dump(OUT, open(os.path.join(HERE, "twin_results.json"), "w"), indent=1, default=float)
log(f"verdict jumeau {OUT['verdict_jumeau']} ; écrit twin_results.json")
