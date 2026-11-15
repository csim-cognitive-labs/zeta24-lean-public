#!/usr/bin/env python3
"""E458 — recontrôle en précision étendue (mpmath, 40 chiffres) du ou des cas écartés par le jumeau (marge au bord < 1e-9 en double),
contrôle β = 0,45. Les hauteurs du fichier d'Odlyzko n'ont que 9 décimales : la Tour recontrôlée est celle de la hauteur TELLE QUE LUE."""
import sys, math
import numpy as np
from mpmath import mp, mpf, atan, log, floor, pi
mp.dps = 40
N = 10**6
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
primes = np.nonzero(sieve)[0]
logp = np.log(primes.astype(np.float64))
lines = [l.split()[0] for l in open(sys.argv[1]) if l.strip()][:200]
beta = 0.45
found = 0
for Ts in lines:
    T = float(Ts)
    s = (T * logp - math.atan(T / beta)) / math.pi; sm = (T * logp - math.atan(T / (1 - beta))) / math.pi
    marg = np.minimum(np.abs(s - np.round(s)), np.abs(sm - np.round(sm)))
    for j in np.nonzero(marg < 1e-9)[0]:
        found += 1
        p = int(primes[j]); Tm = mpf(Ts); b = mpf('0.45')
        S = (Tm * log(p) - atan(Tm / b)) / pi; Sm = (Tm * log(p) - atan(Tm / (1 - b))) / pi
        w, wm = floor(S), floor(Sm); d = int(wm - w)
        k = wm
        b0 = d in (0, 1)
        b4 = ((d == 1) == (k <= Sm and S < k)) and ((w + 1 <= Sm) == (d == 1))
        print('hauteur', Ts, 'premier', p, ': marge double', float(marg[j]), '; position Tour', mp.nstr(S, 25), '; position miroir', mp.nstr(Sm, 25),
              '; écart des mots', d, '; B0 conforme', b0, '; B4 conforme', b4)
print('cas recontrôlés :', found)
