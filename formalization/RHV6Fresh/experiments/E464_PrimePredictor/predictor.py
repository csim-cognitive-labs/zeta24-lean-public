#!/usr/bin/env python3
"""E464 — prédicteur de premiers par les Tours (méthode fixée dans README.md, pré-enregistrée).
Prédiction : saut de la demande reconstituée entre n-1/2 et n+1/2 > 0.75*log(n). Contrôle par division à la fin seulement."""
import json, math, os, time
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ZEROS = os.path.join(HERE, "..", "data", "odlyzko_zeros6_2001052.txt")
STARTS = [10**3, 10**4, 10**5, 2*10**5, 3*10**5, 5*10**5, 10**6, 10**7, 10**8]
WIDTH = 300
FAMILIES = [2001052, 500000]

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0: return False
        d += 2
    return True

def psi_rec(x, g, coef_c, coef_s):
    L = math.log(x)
    a = g * L
    s = math.sqrt(x) * float(np.dot(coef_c, np.cos(a)) + np.dot(coef_s, np.sin(a)))
    return x - s - math.log(2 * math.pi) - 0.5 * math.log(1.0 - x ** -2.0)

def main():
    t0 = time.time()
    allg = np.loadtxt(ZEROS, dtype=np.float64)
    print(f"zeros lus : {allg.size} ; dernier = {allg[-1]:.9f}", flush=True)
    out = []
    for N in FAMILIES:
        g = allg[:N]
        tmax = float(g[-1])
        w = 1.0 - g / tmax
        den = 0.25 + g * g
        coef_c = 2.0 * w * 0.5 / den
        coef_s = 2.0 * w * g / den
        print(f"\n=== famille de {N} Tours, hauteur max {tmax:.3f}, horizon attendu ~ hauteur/pi = {tmax/math.pi:.0f}", flush=True)
        for x0 in STARTS:
            vals = [psi_rec(x0 - 0.5 + k, g, coef_c, coef_s) for k in range(WIDTH + 1)]
            pred, jumps = [], {}
            for k in range(WIDTH):
                n = x0 + k
                j = (vals[k + 1] - vals[k]) / math.log(n)
                jumps[n] = j
                if j > 0.75:
                    pred.append(n)
            # ---- controle, a la fin seulement ----
            true = [n for n in range(x0, x0 + WIDTH) if is_prime(n)]
            ps, ts = set(pred), set(true)
            rec = dict(tours=N, hauteur_max=tmax, debut=x0, largeur=WIDTH,
                       cellule_tour_haute=math.pi * x0 / tmax,
                       premiers_vrais=len(ts), predits=len(ps), justes=len(ps & ts),
                       manques=len(ts - ps), faux=len(ps - ts),
                       saut_min_sur_premiers=min(jumps[n] for n in ts) if ts else None,
                       saut_max_hors_premiers=max(jumps[n] for n in jumps if n not in ts))
            out.append(rec)
            print(json.dumps(rec), flush=True)
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump(out, f, indent=1)
    print(f"\nFIN ; duree {time.time()-t0:.1f} s", flush=True)

if __name__ == "__main__":
    main()
