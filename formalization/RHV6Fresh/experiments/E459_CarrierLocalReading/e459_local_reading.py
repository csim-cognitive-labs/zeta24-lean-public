#!/usr/bin/env python3
"""E459 — volet déterministe (§19.88). Aucun paramètre libre, aucune graine : premiers ≤ 10⁶ par crible, 200 premières hauteurs
d'Odlyzko, Tours de contrôle β ∈ {0,3 ; 0,4 ; 0,45} (non porteuses). (a) fraction de cellule de la ligne aux dix premiers rangs ;
(b) demi-largeur exacte de la fenêtre de même lecture (formule tangentielle), recoupée par test direct ; (c) part des contrôles qui
satisfont H-a ; (d) premier rang de bande (où H-b casse). Mesure, aucune loi, aucune densité."""
import sys, math
import numpy as np

ZFILE = sys.argv[1]
out = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s, flush=True); out.append(s)

N = 10**6
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
primes = np.nonzero(sieve)[0].astype(np.float64)
logp = np.log(primes)
T0 = np.array([float(l.split()[0]) for l in open(ZFILE) if l.strip()])[:200]
P('# E459 volet déterministe — premiers ≤', N, ':', len(primes), '; hauteurs :', len(T0), '(première', T0[0], ', dernière', T0[-1], ')')
K = 10

def stage(beta, T, lp):
    return (T * lp - math.atan(T / beta)) / math.pi

def same(beta, T, lp):
    return np.floor(stage(beta, T, lp)) == np.floor(stage(1.0 - beta, T, lp))

def halfwidth(T, lp):
    """Demi-largeur exacte de la fenêtre de même lecture, côté bas, pour chaque premier de lp (1/2 = tout l'intervalle ]0, 1/2])."""
    s = stage(0.5, T, lp); f = s - np.floor(s)
    a2 = math.atan(2 * T)
    eps = np.full_like(lp, 0.5)
    ua = a2 + math.pi * f                 # arctan(T/β) ≤ ua
    m = ua < math.pi / 2
    eps[m] = np.minimum(eps[m], 0.5 - T / np.tan(ua[m]))
    ub = a2 - math.pi * (1.0 - f)         # arctan(T/(1−β)) > ub
    m = ub > 0
    eps[m] = np.minimum(eps[m], T / np.tan(ub[m]) - 0.5)
    return eps, f

# (a) et (b)
lp10 = logp[:K]
dist_min = 1.0; eps0 = []; eps10 = []; bad_in = 0; bad_out = 0; tested_out = 0
for T in T0:
    eps, f = halfwidth(T, lp10)
    dist_min = min(dist_min, float(np.min(np.minimum(f, 1.0 - f))))
    eps0.append(float(eps[0])); eps10.append(float(eps.min()))
    for j in range(K):
        e = float(eps[j])
        if not same(0.5 - e * (1 - 1e-6), T, lp10[j:j+1])[0]: bad_in += 1
        if e * (1 + 1e-3) < 0.5:
            tested_out += 1
            if same(0.5 - e * (1 + 1e-3), T, lp10[j:j+1])[0]: bad_out += 1
eps0 = np.array(eps0); eps10 = np.array(eps10)
P('\n## (a) ligne, dix premiers rangs, 200 hauteurs')
P('plus petite distance de la fraction de cellule à un contact (0 ou 1) :', '%.6e' % dist_min, '; strictement positive :', dist_min > 0)
P('\n## (b) demi-largeur exacte de la fenêtre de même lecture (0.5 = toute position radiale basse)')
P('rang 0 seul      : min %.6e ; médiane %.6e ; max %.6e ; hauteurs à fenêtre totale : %d' % (eps0.min(), np.median(eps0), eps0.max(), int(np.sum(eps0 >= 0.5))))
P('dix premiers rangs: min %.6e ; médiane %.6e ; max %.6e ; hauteurs à fenêtre totale : %d' % (eps10.min(), np.median(eps10), eps10.max(), int(np.sum(eps10 >= 0.5))))
P('recoupement direct : juste en deçà du bord, lecture différente :', bad_in, '/', 200 * K, '; juste au-delà, même lecture :', bad_out, '/', tested_out)

# (c) et (d)
P('\n## (c) part des Tours de contrôle qui satisfont H-a ; (d) premier rang de bande')
for beta in (0.3, 0.4, 0.45):
    ok0 = 0; ok10 = 0; cons = 0; first = []
    for i, T in enumerate(T0):
        sm = same(beta, T, logp)
        a0 = bool(sm[0]); a10 = bool(np.all(sm[:K]))
        ok0 += a0; ok10 += a10
        cons += int(a0 == (0.5 - beta < eps0[i])) + int(a10 == (0.5 - beta < eps10[i]))
        nz = np.nonzero(~sm)[0]
        first.append(int(nz[0]) if len(nz) else -1)
    first = np.array(first); fin = first[first >= 0]
    P('contrôle β = %s : H-a au rang 0 : %d / 200 ; H-a sur les dix premiers rangs : %d / 200 ; accord avec la fenêtre exacte : %d / 400'
      % (beta, ok0, ok10, cons))
    P('   premier rang de bande : fini pour %d / 200 Tours ; min %d ; médiane %.1f ; max %d (premier correspondant au max : %d)'
      % (len(fin), int(fin.min()), float(np.median(fin)), int(fin.max()), int(primes[int(fin.max())])))
open(sys.argv[2], 'w').write('\n'.join(out) + '\n')
