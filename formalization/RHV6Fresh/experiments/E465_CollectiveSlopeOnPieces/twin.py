#!/usr/bin/env python3
"""E465 — jumeau déterministe : identités S1–S3, S5, S7, S8, S12 à 50 chiffres. Aucun seuil ajusté après coup."""
import json, time
from mpmath import mp, mpf, log, exp, pi, floor, ceil
mp.dps = 50
N = 2000
t0 = time.time()
sieve = [True] * (N + 1); sieve[0] = sieve[1] = False
for i in range(2, int(N ** 0.5) + 1):
    if sieve[i]:
        for j in range(i * i, N + 1, i): sieve[j] = False
primes = [i for i in range(N + 1) if sieve[i]]
Lam = [mpf(0)] * (N + 1)
for p in primes:
    q = p
    while q <= N:
        Lam[q] = log(mpf(p)); q *= p
def psi(x): return sum(Lam[n] for n in range(1, int(floor(x)) + 1))
def raw(x): return psi(x) - x
def smoothed(x): return sum(Lam[n] * (1 - mpf(n) / x) for n in range(0, int(ceil(x))))
def integ(x): return sum(Lam[n] * (x - n) for n in range(1, int(floor(x)) + 1))
def area(a, b):
    return raw(a) * (b - a) - (b - a) ** 2 / 2 + sum(Lam[n] * (b - n) for n in range(int(floor(a)) + 1, int(floor(b)) + 1))
def exact_area(a, b):
    """Intégrale exacte de la demande brute sur [a,b], morceau par morceau entre entiers."""
    pts = [a] + [mpf(n) for n in range(int(floor(a)) + 1, int(floor(b)) + 1) if a < n < b] + [b]
    tot = mpf(0)
    for u, v in zip(pts[:-1], pts[1:]):
        lvl = psi(u)
        tot += lvl * (v - u) - (v * v - u * u) / 2
    return tot
def rel(u, v): return abs(u - v) / max(mpf(1), abs(u), abs(v))
worst = {k: mpf(0) for k in ["S1", "S3", "S3_integrale", "S5", "S7", "S8", "S12"]}
heights = [mpf("14.134725141734693790457251983562"), mpf("21.022039638771554992628479593897"),
           mpf("25.010857580145688763213790992563"), mpf("30.424876125859513210311897530584"),
           mpf("32.935061587739189690662368964075")]
ncells = 0
for T in heights:
    step = exp(pi / T); c = mpf("1.5")
    while c * step * step < N - 1:
        a, b, d = c, c * step, c * step * step
        worst["S1"] = max(worst["S1"], rel(a * smoothed(a), integ(a)))
        worst["S3"] = max(worst["S3"], rel(integ(b) - integ(a) - (b * b - a * a) / 2, area(a, b)))
        worst["S3_integrale"] = max(worst["S3_integrale"], rel(exact_area(a, b), area(a, b)))
        worst["S5"] = max(worst["S5"], rel(area(a, b) + area(b, d), area(a, d)))
        c = b; ncells += 1
ngaps = 0
T = heights[0]; step = exp(pi / T)
for pn, pn1 in zip(primes[:200], primes[1:201]):
    lo, up = mpf(pn), mpf(pn1)
    full = area(lo, up)
    nonprime = raw(lo) * (up - lo) - (up - lo) ** 2 / 2 + sum(Lam[n] * (up - n) for n in range(pn + 1, pn1 + 1) if not sieve[n])
    worst["S7"] = max(worst["S7"], rel(full, nonprime))
    a = up - mpf("0.25"); b = up + mpf("0.5")
    if pn1 - pn >= 1:
        worst["S8"] = max(worst["S8"], rel(area(a, b), raw(a) * (b - a) - (b - a) ** 2 / 2 + log(up) * (b - up)))
    k = ceil(log(lo) * T / pi); cuts = [lo]
    while exp(k * pi / T) < up:
        c = exp(k * pi / T)
        if c > lo: cuts.append(c)
        k += 1
    cuts.append(up)
    worst["S12"] = max(worst["S12"], rel(sum(area(u, v) for u, v in zip(cuts[:-1], cuts[1:])), full))
    ngaps += 1
tol = mpf(10) ** -30
out = {"cells": ncells, "gaps": ngaps, "tolerance": "1e-30", "worst": {k: mp.nstr(v, 5) for k, v in worst.items()},
       "conform": all(v <= tol for v in worst.values()), "seconds": round(time.time() - t0, 2)}
print(json.dumps(out, indent=1))
json.dump(out, open(__file__.replace("twin.py", "twin_results.json"), "w"), indent=1)
