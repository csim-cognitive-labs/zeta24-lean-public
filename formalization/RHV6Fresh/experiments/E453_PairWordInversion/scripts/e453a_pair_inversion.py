#!/usr/bin/env python3
"""E453 (a) — K3 : inversion d'E449 appliquée au mot du miroir. H1 inversion tangentielle depuis deux contacts du miroir
rend (1−β, T) ; H2 encadrement |k/log x − T/π| ≤ (|φ|+π)/(π log x) pour les deux mots, sur tous les premiers ≤ 10^7 ;
polygone d'E449 sur le mot du miroir (X = 10^4, 10^6) : (T, φ*) dedans ; H4 mot du miroir recalculé depuis (β, T) rendus par
l'inversion du mot de la Tour ; H5/H6 mots distincts par décade. 24 couples d'E452. Deux termes, aucune somme de Tours."""
import os, sys, json, math, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
lg = Logger(os.path.join(OUT, "logs", "e453a.log"))
G, sha = load_zeros(lg)
N = 10**7
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
P = np.nonzero(sieve)[0].astype(np.float64); L = np.log(P)
lg(f"premiers ≤ 10^7 : {len(P)}")

def word(beta, T, Lx):
    phi = math.atan2(T, beta)
    s = (T*Lx - phi)/math.pi
    k = np.floor(s); f = s - k
    return k.astype(np.int64), f, phi

def polygon(Lx, k, T0):
    lo_b = (k + 1) * math.pi; hi_b = k * math.pi
    def phi_lo(T): return np.max(T * Lx - lo_b)
    def phi_hi(T): return np.min(T * Lx - hi_b)
    def g(T): return phi_hi(T) - phi_lo(T)
    def root(a, b):
        for _ in range(80):
            m = 0.5 * (a + b)
            if g(m) >= 0: a = m
            else: b = m
        return a
    step = 1.0
    while g(T0 - step) >= 0: step *= 2
    T_lo = root(T0, T0 - step)
    step = 1.0
    while g(T0 + step) >= 0: step *= 2
    T_hi = root(T0, T0 + step)
    grid = np.linspace(T_lo, T_hi, 2001)
    plo = np.array([phi_lo(t) for t in grid]); phi_ = np.array([phi_hi(t) for t in grid])
    ok = phi_ >= plo
    plo, phi_ = plo[ok], phi_[ok]
    return dict(g_at_true=float(g(T0)), T_lo=float(T_lo), T_hi=float(T_hi), T_width=float(T_hi-T_lo),
                phi_lo=float(np.min(plo)), phi_hi=float(np.max(phi_)))

TOL = 1e-10
def check(beta, T, label):
    kb, fb, phib = word(beta, T, L)
    km, fm, phim = word(1-beta, T, L)
    # H1 : inversion tangentielle sur deux contacts du miroir
    h1 = []
    for kk in [int(km[0]), int(km[len(km)//2]), int(km[-1])]:
        C0 = math.exp((phim + kk*math.pi)/T); C1 = math.exp((phim + (kk+1)*math.pi)/T)
        T_rec = math.pi/math.log(C1/C0); ph_rec = T_rec*math.log(C0) - kk*math.pi; b_rec = T_rec/math.tan(ph_rec)
        h1.append(dict(k=kk, T_rel_err=abs(T_rec-T)/T, phi_err=abs(ph_rec-phim), beta_err=abs(b_rec-(1-beta))))
    h1_max = max(max(e["T_rel_err"], e["beta_err"]) for e in h1)
    # H2 : encadrement pour les deux mots sur tous les premiers
    def bracket_viol(k, phi):
        lhs = np.abs(k/L - T/math.pi); rhs = (abs(phi) + math.pi)/(math.pi*L)
        return int(np.sum(lhs > rhs*(1+1e-12)))
    h2 = bracket_viol(kb, phib) + bracket_viol(km, phim)
    slope_last = float(km[-1]/L[-1]); slope_target = T/math.pi
    # polygone d'E449 sur le mot du miroir
    poly = []
    for X in [10**4, 10**6]:
        sel = P <= X
        r = polygon(L[sel], km[sel], T); r["X"] = X
        r["true_inside"] = bool(r["T_lo"]-1e-9 <= T <= r["T_hi"]+1e-9 and r["phi_lo"]-1e-9 <= phim <= r["phi_hi"]+1e-9)
        poly.append(r)
    poly_ok = all(r["true_inside"] for r in poly)
    # H4 : (β, T) rendus par l'inversion du mot de la Tour (deux contacts), puis mot du miroir recalculé
    kk = int(kb[len(kb)//2])
    C0 = math.exp((phib + kk*math.pi)/T); C1 = math.exp((phib + (kk+1)*math.pi)/T)
    T_r = math.pi/math.log(C1/C0); b_r = T_r/math.tan(T_r*math.log(C0) - kk*math.pi)
    km_r, _, _ = word(1-b_r, T_r, L)
    h4 = int(np.sum(km_r != km))
    # H5/H6 : mots distincts par décade
    diff = km != kb
    decades = {}
    for d in range(1, 8):
        sel = (P >= 10**(d-1)) & (P < 10**d)
        decades[f"1e{d-1}-1e{d}"] = int(np.sum(diff & sel))
    n_diff = int(np.sum(diff)); last_diff = float(P[np.nonzero(diff)[0][-1]]) if n_diff else None
    if beta == 0.5: h56_ok = n_diff == 0
    else: h56_ok = all(v > 0 for v in decades.values())
    ok = h1_max <= TOL and h2 == 0 and poly_ok and h4 == 0 and h56_ok
    r = dict(label=label, beta=beta, T=T, phi_mirror=phim, H1=h1, H1_max=h1_max, H2_violations=h2,
             slope_last=slope_last, slope_target=slope_target, polygon=poly, polygon_ok=poly_ok,
             H4_mismatch=h4, T_recovered=T_r, beta_recovered=b_r, n_diff=n_diff, last_diff_prime=last_diff,
             diff_by_decade=decades, H56_ok=bool(h56_ok), ok=bool(ok))
    lg(f"{label:16s} β={beta:.2f} T={T:.6f} | H1 {h1_max:.1e} | H2 viol {h2} pente {slope_last:.6f}→{slope_target:.6f} "
       f"| polygone {'dedans' if poly_ok else 'HORS'} T largeur 1e6: {poly[1]['T_width']:.1e} | H4 {h4} "
       f"| mots distincts {n_diff} (dernier p={last_diff}) décades {list(decades.values())} | {'OK' if ok else 'ECHEC'}")
    return r

results = []
for r_ in [1, 10, 100, 1000, 10000, 100000]:
    T = float(G[r_-1])
    for beta in [0.3, 0.4, 0.45, 0.5]:
        results.append(check(beta, T, f"rang{r_}_b{beta}"))
allok = all(r["ok"] for r in results)
lg(f"TOTAL : {len(results)} couples ; tous OK : {allok}")
json.dump(dict(zeros_sha=sha, primes=len(P), tol=TOL, results=results, all_ok=allok),
          open(os.path.join(OUT, "data", "e453a_results.json"), "w"), indent=1)
