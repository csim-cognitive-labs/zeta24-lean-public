#!/usr/bin/env python3
"""E457 — recontrôle en précision étendue (mpmath, 40 chiffres) des 9 cas signalés : la marge relative 10⁻⁶ du test « en deçà »
vaut (1−f)·10⁻⁶ ≤ 1,6·10⁻¹³ en valeur absolue, sous le bruit de la double précision (|s|·2,2·10⁻¹⁶ ≈ 3·10⁻¹³). On refait, pour
chaque cas, les quatre tests sur TOUS les premiers ≤ 10⁶ en précision étendue."""
import sys, math
import numpy as np, mpmath as mp
mp.mp.dps = 40
ZFILE = sys.argv[1]
cases = [(0.5, 82.910381), (0.5, 276.452050), (0.3, 395.582870), (0.4, 258.610439), (0.4, 282.465115), (0.4, 373.864874),
         (0.45, 244.070898), (0.45, 283.211186), (0.45, 384.956117)]
heights = [float(l.split()[0]) for l in open(ZFILE) if l.strip()][:200]
N = 10**6
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
primes = [int(p) for p in np.nonzero(sieve)[0]]
logs = [mp.log(p) for p in primes]
def stages(beta, T):
    a = mp.atan(T / beta)
    return [(T * l - a) / mp.pi for l in logs]
def floors(beta, T): return [mp.floor(s) for s in stages(beta, T)]
ok_all = 0
for beta0, Tapprox in cases:
    T = mp.mpf(min(heights, key=lambda h: abs(h - Tapprox)))
    beta = mp.mpf(beta0)
    S = stages(beta, T); F = [mp.floor(s) for s in S]
    g = [1 - (s - f) for s, f in zip(S, F)]               # 1 − fraction de cellule
    # marge radiale exacte : arctan(T/β') = arctan(T/β) − π(1−f)
    a = mp.atan(T / beta)
    cand = []
    for gi in g:
        th = a - mp.pi * gi
        cand.append(min(T / mp.tan(th) - beta, 1 - beta) if th > 0 else 1 - beta)
    db = min(cand)
    # marge en hauteur : résolution monotone par bissection sur chaque premier (borne sup. via dérivée)
    # ΔT_q ≥ π g_q / log q (dérivée ≤ log q) : seuls les 200 plus petits π g/log q peuvent réaliser le minimum,
    # car pour les autres la borne inférieure dépasse déjà la valeur exacte d'un candidat (vérifié ci-dessous)
    ratio = sorted(range(len(primes)), key=lambda i: g[i] / logs[i])[:200]
    dts = []
    for i in ratio:
        l, f = logs[i], F[i]; target = mp.pi * (f + 1)
        lo, hi = T, T + 1
        for _ in range(140):
            mid = (lo + hi) / 2
            if mid * l - mp.atan(mid / beta) < target: lo = mid
            else: hi = mid
        dts.append(lo - T)
    dt = min(dts)
    rset = set(ratio)
    excluded_lower_bound = min(mp.pi * g[i] / logs[i] for i in range(len(primes)) if i not in rset)
    assert excluded_lower_bound > dt, 'un premier exclu pourrait réaliser le minimum'
    t = {'β_in': floors(beta + db * (1 - mp.mpf('1e-6')), T) == F,
         'T_in': floors(beta, T + dt * (1 - mp.mpf('1e-6'))) == F,
         'β_out': (floors(beta + db * (1 + mp.mpf('1e-3')), T) != F) if beta + db * (1 + mp.mpf('1e-3')) < 1 else True,
         'T_out': floors(beta, T + dt * (1 + mp.mpf('1e-3'))) != F}
    ok = all(t.values()); ok_all += ok
    print('β=%.2f T=%s : Δβ_max=%s ΔT_max=%s ; tests %s ; %s' % (beta0, mp.nstr(T, 12), mp.nstr(db, 6), mp.nstr(dt, 6),
          {k: ('OK' if v else 'ÉCHEC') for k, v in t.items()}, 'CONFORME' if ok else 'NON CONFORME'))
print('cas recontrôlés en précision étendue :', len(cases), '; conformes :', ok_all)
