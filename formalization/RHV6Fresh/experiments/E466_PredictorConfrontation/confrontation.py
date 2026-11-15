#!/usr/bin/env python3
"""E466 — confrontation de quatre canaux de score (méthode fixée dans README.md, pré-enregistrée).
Canaux : J-F (E464), J-noF, D2-F, D2-noF. Décisions R0/R1/R2. Contrôle exact par division à la fin seulement."""
import json, math, os, time
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ZEROS = os.path.join(HERE, "..", "data", "odlyzko_zeros6_2001052.txt")
REF = [10**3, 10**4, 10**5, 2*10**5, 3*10**5, 5*10**5, 10**6, 10**7, 10**8]
NEW = [5*10**4, 15*10**4, 25*10**4, 4*10**5, 7*10**5]
WIDTH = 300
FAMILIES = [2001052, 500000]
LOG2PI = math.log(2 * math.pi)

def category(n):
    """'p' premier, 'pk' puissance k>=2 d'un premier (retourne k), 'c' composé autre, pour n >= 2."""
    if n % 2 == 0:
        k = 0
        m = n
        while m % 2 == 0: m //= 2; k += 1
        return ('p', 1) if n == 2 else (('pk', k) if m == 1 else ('c', 0))
    d = 3
    while d * d <= n:
        if n % d == 0:
            k, m = 0, n
            while m % d == 0: m //= d; k += 1
            return ('pk', k) if m == 1 else ('c', 0)
        d += 2
    return ('p', 1)

class Family:
    def __init__(self, g):
        self.g = g
        self.tmax = float(g[-1])
        w = 1.0 - g / self.tmax
        rho = 0.5 + 1j * g
        c1 = 1.0 / rho                      # psi : 2 Re[x^rho / rho]
        c2 = 1.0 / (rho * (rho + 1.0))      # integre : 2 Re[x^(rho+1) / (rho(rho+1))]
        self.a1F, self.b1F = 2 * w * c1.real, -2 * w * c1.imag
        self.a1N, self.b1N = 2 * c1.real, -2 * c1.imag
        self.a2F, self.b2F = 2 * w * c2.real, -2 * w * c2.imag
        self.a2N, self.b2N = 2 * c2.real, -2 * c2.imag

    def psi_both(self, x):
        """(psi_F, psi_noF) reconstitues en x (canal E464)."""
        L = math.log(x); a = self.g * L; co, si = np.cos(a), np.sin(a)
        bg = x - LOG2PI - 0.5 * math.log(1.0 - x ** -2.0)
        sF = math.sqrt(x) * float(np.dot(self.a1F, co) + np.dot(self.b1F, si))
        sN = math.sqrt(x) * float(np.dot(self.a1N, co) + np.dot(self.b1N, si))
        return bg - sF, bg - sN

    def integ_both(self, x):
        """(I_F, I_noF) : signal integre reconstitue, fond conserve (x^2/2 - x log 2pi - zeros triviaux)."""
        L = math.log(x); a = self.g * L; co, si = np.cos(a), np.sin(a)
        triv = -sum(x ** (1 - 2 * k) / (2 * k * (2 * k - 1)) for k in range(1, 6))
        bg = 0.5 * x * x - x * LOG2PI + triv
        sF = x ** 1.5 * float(np.dot(self.a2F, co) + np.dot(self.b2F, si))
        sN = x ** 1.5 * float(np.dot(self.a2N, co) + np.dot(self.b2N, si))
        return bg - sF, bg - sN

def window(fam, x0, N):
    ns = list(range(x0, x0 + WIDTH))
    # canal J : saut entre n-1/2 et n+1/2
    pj = [fam.psi_both(x0 - 0.5 + k) for k in range(WIDTH + 1)]
    # canal D2 : seconde difference du signal integre aux entiers n-1, n, n+1
    pi_ = [fam.integ_both(x0 - 1 + k) for k in range(WIDTH + 2)]
    scores = {"J-F": {}, "J-noF": {}, "D2-F": {}, "D2-noF": {}}
    for k, n in enumerate(ns):
        ln = math.log(n)
        scores["J-F"][n] = (pj[k + 1][0] - pj[k][0]) / ln
        scores["J-noF"][n] = (pj[k + 1][1] - pj[k][1]) / ln
        scores["D2-F"][n] = (pi_[k + 2][0] - 2 * pi_[k + 1][0] + pi_[k][0]) / ln
        scores["D2-noF"][n] = (pi_[k + 2][1] - 2 * pi_[k + 1][1] + pi_[k][1]) / ln
    # ---- controle, a la fin seulement ----
    cat = {n: category(n) for n in ns}
    exact = {n: (1.0 if cat[n][0] == 'p' else (1.0 / cat[n][1] if cat[n][0] == 'pk' else 0.0)) for n in ns}
    primes = [n for n in ns if cat[n][0] == 'p']
    powers = [n for n in ns if cat[n][0] == 'pk']
    comps = [n for n in ns if cat[n][0] == 'c']
    cell = math.pi * x0 / fam.tmax
    rec = dict(tours=N, hauteur_max=fam.tmax, debut=x0, largeur=WIDTH, inedite=(x0 in NEW),
               cellule_tour_haute=cell, R2_decidee=(cell <= 1.0),
               premiers_vrais=len(primes), puissances_vraies=len(powers), composes_vrais=len(comps), canaux={})
    for ch, sc in scores.items():
        predR0 = {n for n in ns if sc[n] > 0.75}
        predR1 = {n for n in predR0 if n % 6 in (1, 5)}
        P = set(primes)
        d = dict(
            saut_min_sur_premiers=min(sc[n] for n in primes) if primes else None,
            saut_max_sur_composes=max(sc[n] for n in comps) if comps else None,
            saut_max_sur_puissances=max(sc[n] for n in powers) if powers else None,
            marge=(min(sc[n] for n in primes) - max(sc[n] for n in comps)) if primes and comps else None,
            err_max_premiers=max(abs(sc[n] - exact[n]) for n in primes) if primes else None,
            err_max_composes=max(abs(sc[n] - exact[n]) for n in comps) if comps else None,
            err_max_puissances=max(abs(sc[n] - exact[n]) for n in powers) if powers else None,
            R0=dict(predits=len(predR0), justes=len(predR0 & P), manques=len(P - predR0),
                    faux_composes=len(predR0 & set(comps)), faux_puissances=len(predR0 & set(powers))),
            R1=dict(predits=len(predR1), justes=len(predR1 & P), manques=len(P - predR1),
                    faux_composes=len(predR1 & set(comps)), faux_puissances=len(predR1 & set(powers))),
        )
        rec["canaux"][ch] = d
    return rec

def main():
    t0 = time.time()
    allg = np.loadtxt(ZEROS, dtype=np.float64)
    print(f"zeros lus : {allg.size} ; dernier = {allg[-1]:.9f}", flush=True)
    out = []
    for N in FAMILIES:
        fam = Family(allg[:N])
        print(f"\n=== famille de {N} Tours, hauteur max {fam.tmax:.3f}", flush=True)
        for x0 in sorted(REF + NEW):
            rec = window(fam, x0, N)
            out.append(rec)
            short = {ch: (round(d["saut_min_sur_premiers"], 3), round(d["saut_max_sur_composes"], 3),
                          d["R0"]["justes"], d["R0"]["manques"], d["R0"]["faux_composes"] + d["R0"]["faux_puissances"])
                     for ch, d in rec["canaux"].items()}
            print(f"x0={x0} cell={rec['cellule_tour_haute']:.3f} inedite={rec['inedite']} P={rec['premiers_vrais']} "
                  f"(min_prem, max_comp, justes, manques, faux) : {json.dumps(short)}", flush=True)
            with open(os.path.join(HERE, "results.json"), "w") as f:
                json.dump(out, f, indent=1)
    print(f"\nFIN ; duree {time.time()-t0:.1f} s", flush=True)

if __name__ == "__main__":
    main()
