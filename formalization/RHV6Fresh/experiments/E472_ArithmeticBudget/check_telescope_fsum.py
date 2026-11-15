#!/usr/bin/env python3
"""Contrôle a posteriori (E472, point 2) : le dépassement du seuil 1e-8 du télescopage côté premiers pour les Tours 20 et 1000
est-il une accumulation flottante de np.cumsum ? Recalcul avec math.fsum (sommation exacte) sur les mêmes aires."""
import math, json, time
import numpy as np
XMAX = 30_000_000; X0 = 1000.0; PI = math.pi
sieve = np.ones(XMAX + 2, dtype=bool); sieve[:2] = False
for i in range(2, int((XMAX + 1) ** 0.5) + 1):
    if sieve[i]: sieve[i * i::i] = False
primes = np.nonzero(sieve)[0]
lam = np.zeros(XMAX + 2); lam[primes] = np.log(primes.astype(np.float64))
for p in primes[primes <= int((XMAX + 1) ** 0.5) + 1]:
    q = int(p) * int(p)
    while q <= XMAX + 1:
        lam[q] = math.log(p); q *= int(p)
psi = np.cumsum(lam); nlam = np.cumsum(lam * np.arange(XMAX + 2, dtype=np.float64))
def demand_area(a, b):
    fa, fb = int(math.floor(a)), int(math.floor(b))
    return (psi[fa] - a) * (b - a) - (b - a) ** 2 / 2 + b * (psi[fb] - psi[fa]) - (nlam[fb] - nlam[fa])
allg = np.loadtxt("../data/odlyzko_zeros6_2001052.txt", dtype=np.float64)
out = {}
for k in (19, 999):
    T = float(allg[k]); e = math.exp(PI / T)
    Nmax = int(math.floor(math.log(XMAX / X0) / (PI / T))) - 1
    xs = X0 * e ** np.arange(Nmax + 1)
    a = [demand_area(xs[n], xs[n] * e) for n in range(Nmax)]
    worst_cumsum, worst_fsum = 0.0, 0.0
    cs = np.cumsum(np.array(a))
    for N in range(1, Nmax + 1):
        tel = demand_area(X0, xs[N])
        worst_cumsum = max(worst_cumsum, abs(cs[N - 1] - tel) / abs(tel))
        worst_fsum = max(worst_fsum, abs(math.fsum(a[:N]) - tel) / abs(tel))
    out[str(k + 1)] = dict(T=T, cellules=Nmax, err_rel_max_cumsum=worst_cumsum, err_rel_max_fsum=worst_fsum)
    print(f"Tour {k+1} : cumsum {worst_cumsum:.2e} ; fsum {worst_fsum:.2e}", flush=True)
json.dump(out, open("check_telescope_fsum.json", "w"), indent=1)
