#!/usr/bin/env python3
"""E477 — jumeau déterministe pré-enregistré : poids alternés de la cassure, Tour moins miroir, sur les premiers à mot décalé.
P1 fraction |δ|/π, P2 loi du premier ordre, P3 identité sur les non décalés, P4 ordre en δ (somme désalternée), P5 échelle en x,
P6 décision. Premiers réels, contacts réels ; paire fictive (β, T) / (1−β, T) ; aucune sortie fabriquée."""
import json, math, os, time, itertools
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
ZEROS = os.path.join(HERE, "..", "data", "odlyzko_zeros6_2001052.txt")
t0 = time.time(); OUT = {"tours": {}}
XMAX = 30_000_000; XMIN = 1000.0; PI = math.pi
TOWERS = [1, 10, 100]; BETAS = [0.5, 0.45, 0.40, 0.30]
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
supp = np.nonzero(lam)[0]; supp = supp[supp >= XMIN]
LAM = lam[supp]; X = supp.astype(np.float64)
log(f"premiers : {primes.size} ; support Λ ≥ {XMIN:.0f} : {supp.size}")
with open(ZEROS) as f:
    gam = [float(l.split()[0]) for l in itertools.islice(f, 1000)]
def fit_slope(xs, ys):
    lx, ly = np.log(xs), np.log(ys); A = np.vstack([lx, np.ones_like(lx)]).T
    return float(np.linalg.lstsq(A, ly, rcond=None)[0][0])
for tz in TOWERS:
    T = gam[tz-1]; g = math.exp(PI/T); OUT["tours"][str(tz)] = dict(T=T, betas={})
    for b in BETAS:
        phi, phim = math.atan(T/b), math.atan(T/(1-b)); delta = phi - phim          # δ ≥ 0 pour β ≤ 1/2
        stage = (T*np.log(X) - phi)/PI; k = np.floor(stage); f = stage - k
        stagem = stage + delta/PI; km = np.floor(stagem); fm = stagem - km
        C = lambda kk: np.exp((phi + kk*PI)/T); Cm = lambda kk: np.exp((phim + kk*PI)/T)
        kmin, kmax = int(k.min()), int(k.max()); k0 = kmin + 1; N = kmax - k0        # cellules complètes k0..k0+N−1
        if N % 2 == 1: N -= 1                                                        # nombre pair de cellules
        j = (k - k0).astype(int); jm = (km - k0).astype(int)
        win = (j >= 0) & (j < N)
        sawT = (1+g)*X - 2*C(k+1); sawM = (1+g)*X - 2*Cm(km+1)
        altT = (-1.0)**j*sawT; altM = (-1.0)**jm*sawM; D = altT - altM
        shift = (km != k); sh = win & shift; un = win & ~shift
        massT = math.fsum(LAM[win].tolist()); massS = math.fsum(LAM[sh].tolist())
        res = dict(delta=delta, delta_sur_pi=delta/PI, cellules=int(N), premiers=int(win.sum()), premiers_decales=int(sh.sum()),
                   P1_fraction=massS/massT if massT else 0.0)
        if b == 0.5:
            res["temoin_D_max"] = float(np.max(np.abs(D[win]))) if win.any() else 0.0
            res["temoin_decales"] = int(sh.sum())
            OUT["tours"][str(tz)]["betas"][f"{b:.2f}"] = res
            log(f"Tour {tz} β={b} témoin : décalés {sh.sum()} ; max|D| {res['temoin_D_max']:.1e}"); continue
        res["P1_ecart_relatif"] = abs(res["P1_fraction"] - delta/PI)/(delta/PI)
        # P2 : loi du premier ordre sur les décalés
        u = 1 - f[sh]; Dlin = (-1.0)**j[sh]*(2*X[sh]/T)*(g*delta - (1+g)*PI*u)
        scale = X[sh]*delta/T
        res["P2_residu_median"] = float(np.median(np.abs(D[sh] - Dlin)/scale)) if sh.any() else None
        res["P2_D_median"] = float(np.median(np.abs(D[sh])/scale)) if sh.any() else None
        # P3 : identité sur les non décalés
        ident = (-1.0)**(j[un]+1)*2*C(k[un]+1)*(1 - math.exp(-delta/T))
        res["P3_residu"] = float(np.max(np.abs(D[un] - ident)/(2*C(k[un]+1)*delta/T)))
        # P4 : sommes par cellule (décalés), désalternées ; prédiction second ordre
        Sk = np.zeros(N); SkU = np.zeros(N)
        for c in range(N):
            m = sh & (j == c); Sk[c] = math.fsum((LAM[m]*D[m]).tolist())
            mu = un & (j == c); SkU[c] = math.fsum((LAM[mu]*D[mu]).tolist())
        kk = np.arange(k0, k0+N, dtype=float); ell = C(kk+1) - C(kk); Ck1 = C(kk+1)
        pred_k = (delta**2*(g-1)/(PI*T))*ell*Ck1
        sgn = (-1.0)**np.arange(N)
        R = math.fsum((sgn*Sk).tolist())/math.fsum(pred_k.tolist())
        res["P4_R"] = R; res["P4_R_cellules_median"] = float(np.median(sgn*Sk/pred_k))
        res["P4_R_premier_ordre_equiv"] = R*delta                                   # pour P6
        # non décalés : somme désalternée rapportée à (2δ/T)(g−1)x² (premier ordre)
        predU = (2*delta/T)*(1-delta/PI)*ell*Ck1
        res["nondecales_R"] = -math.fsum((sgn*SkU).tolist())/math.fsum(predU.tolist())
        # P5 : cumul sur un nombre pair de cellules, échelle en x
        cum = np.cumsum(Sk); Xe = C(kk+1)                                            # fin de la cellule c
        ev = np.arange(1, N, 2)                                                      # indices impairs = nombre pair de cellules
        Spair = cum[ev]; Xev = Xe[ev]
        bound = 3*(delta**2*(g-1)**2/(PI*T))*Xev**2
        res["P5_ratio_borne_max"] = float(np.max(np.abs(Spair)/bound))
        nz = np.abs(Spair) > 0
        res["P5_pente"] = fit_slope(Xev[nz], np.abs(Spair[nz])) if nz.sum() >= 3 else None
        res["P5_Spair_sur_x32_dernier"] = float(Spair[-1]/Xev[-1]**1.5)
        res["P5_Spair_sur_x2_dernier"] = float(Spair[-1]/Xev[-1]**2)
        res["somme_abs_cellules_sur_x2"] = float(np.sum(np.abs(Sk))/Xev[-1]**2)
        OUT["tours"][str(tz)]["betas"][f"{b:.2f}"] = res
        log(f"Tour {tz} T={T:.2f} β={b} δ/π={delta/PI:.2e} cellules {N} décalés {sh.sum()} | P1 {res['P1_fraction']:.2e} (écart {res['P1_ecart_relatif']:.3f}) "
            f"| P2 résidu {res['P2_residu_median']:.3f} |D| {res['P2_D_median']:.2f} | P3 {res['P3_residu']:.1e} | P4 R {R:.3f} (non déc. {res['nondecales_R']:.3f}) "
            f"| P5 borne {res['P5_ratio_borne_max']:.2f} pente {res['P5_pente']} S/x^1.5 {res['P5_Spair_sur_x32_dernier']:.2e}")
# verdicts
V = {}
bs = ["0.45", "0.40", "0.30"]
V["P1"] = all(OUT["tours"][t]["betas"][b]["P1_ecart_relatif"] < 0.05 for t in ("1", "10", "100") for b in bs)
V["P2"] = all(OUT["tours"][t]["betas"][b]["P2_residu_median"] <= 0.1 and 0.2 <= OUT["tours"][t]["betas"][b]["P2_D_median"] <= 3 for t in ("1", "10", "100") for b in bs)
V["P3"] = all(OUT["tours"][t]["betas"][b]["P3_residu"] < 1e-10 for t in ("1", "10", "100") for b in bs)
V["P4"] = all(0.5 <= OUT["tours"]["1"]["betas"][b]["P4_R"] <= 2 for b in bs) and all(0.3 <= OUT["tours"]["10"]["betas"][b]["P4_R"] <= 3 for b in bs)
V["P5"] = all(OUT["tours"][t]["betas"][b]["P5_ratio_borne_max"] <= 1 and (OUT["tours"][t]["betas"][b]["P5_pente"] or 0) >= 1.7 for t in ("1", "10", "100") for b in bs)
P6 = {}
for t in ("1", "10"):
    Rs = [OUT["tours"][t]["betas"][b]["P4_R"] for b in bs]; Rd = [OUT["tours"][t]["betas"][b]["P4_R_premier_ordre_equiv"] for b in bs]
    P6[t] = dict(R=Rs, R_delta=Rd, second_ordre=(max(Rs)-min(Rs))/abs(np.mean(Rs)) <= 0.3 if np.mean(Rs) else False,
                 premier_ordre=(max(Rd)-min(Rd))/abs(np.mean(Rd)) <= 0.3 if np.mean(Rd) else False)
V["P6"] = P6; V["temoin"] = all(OUT["tours"][t]["betas"]["0.50"]["temoin_decales"] == 0 and OUT["tours"][t]["betas"]["0.50"]["temoin_D_max"] < 1e-6 for t in ("1", "10", "100"))
OUT["verdict_jumeau"] = V; OUT["duree_s"] = time.time() - t0
json.dump(OUT, open(os.path.join(HERE, "twin_results.json"), "w"), indent=1, default=float)
log(f"verdict jumeau {json.dumps(V, default=float)} ; écrit twin_results.json")
