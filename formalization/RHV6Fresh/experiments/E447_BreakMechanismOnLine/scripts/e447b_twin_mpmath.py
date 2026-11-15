# -*- coding: utf-8 -*-
"""E447(b) — jumeau déterministe (mpmath 30 chiffres, sympy pour les premiers ≤ 10^6) de e447a : identité d'Abel sur des
blocs de 10 cellules, amplitude exacte à la cassure sur 200 premiers, cassure puis descente sur les cellules à un poids,
pour trois hauteurs. Tout recalculé indépendamment de numpy."""
import os, sys, json, math
from mpmath import mp, mpf, exp, log, sqrt, floor, atan2, pi
import sympy
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
lg = Logger(os.path.join(OUT, "logs", "e447b.log"))
mp.dps = 30
G, sha = load_zeros(lg)
NT = 1_000_000; XMIN = 1000
primes = list(sympy.primerange(2, NT + 1)); pset = set(primes)
psi = [mpf(0)] * (NT + 1); lamz = [False] * (NT + 1)
for p in primes:
    q = p
    while q <= NT:
        lamz[q] = True; q *= p
acc = mpf(0); fac = sympy.factorint
for n in range(1, NT + 1):
    if lamz[n]:
        f = fac(n); acc += log(mpf(list(f.keys())[0]))
    psi[n] = acc
lg("ψ aux entiers ≤ %d prêt" % NT)
def rawd(x): return psi[int(floor(x))] - x
res = {"dps": mp.dps, "towers": [], "all_ok": True}
for rank in [1, 100, 10000]:
    T = mpf(G[rank - 1]); ph = atan2(T, mpf("0.5")); norm = sqrt(mpf("0.25") + T * T); rho = exp(pi / (2 * T))
    def contact(k): return exp((ph + k * pi) / T)
    def val(k): return (-1) ** (k % 2) * sqrt(contact(k)) / norm
    out = {"rank": rank, "T": float(T)}
    kmin = int(math.ceil(float((T * log(mpf(XMIN)) - ph) / pi)))
    # Abel : blocs de 10 cellules à 10^3 et 10^4
    ab = []
    for x0 in [1000, 10000]:
        k0 = int(math.ceil(float((T * log(mpf(x0)) - ph) / pi))); M = 10
        if float(contact(k0 + M + 1)) > NT: continue
        R = [rawd(contact(k0 + i)) for i in range(M + 1)]; V = [val(k0 + i) for i in range(M + 1)]
        lhs = sum(V[i] * (R[i + 1] - R[i]) for i in range(M))
        rhs = V[M] * R[M] - V[0] * R[0] + (1 + rho) * sum(V[i] * R[i + 1] for i in range(M))
        scale = max(abs(V[i] * R[i]) for i in range(M + 1))
        ab.append({"x0": x0, "k0": k0, "rel_residual": float(abs(lhs - rhs) / scale)})
    out["abel"] = ab
    # amplitude exacte sur 200 premiers entre 10^3 et 10^4
    ps = [p for p in primes if XMIN <= p <= 10000][::max(1, len([p for p in primes if XMIN <= p <= 10000]) // 200)][:200]
    errs = []; viol = 0
    for q in ps:
        s = (T * log(mpf(q)) - ph) / pi; k = int(floor(s)); f = s - k
        vdir = abs(val(k)); vex = sqrt(mpf(q)) * exp(-pi * f / (2 * T)) / norm
        errs.append(float(abs(vdir - vex) / vex))
        if not (sqrt(mpf(q)) * exp(-pi / (2 * T)) / norm < vdir <= sqrt(mpf(q)) / norm): viol += 1
    out["amp_max_rel_err"] = max(errs); out["amp_bounds_violations"] = viol; out["amp_sample"] = len(ps)
    # cassure puis descente : premières 300 cellules ≥ 10^3 à exactement un poids (premier)
    cnt = 0; maxerr = mpf(0); k = kmin
    while cnt < 300 and float(contact(k + 1)) < NT:
        a = int(floor(contact(k))); b = int(floor(contact(k + 1)))
        ws = [n for n in range(a + 1, b + 1) if lamz[n]]
        if len(ws) == 1 and ws[0] in pset:
            q = ws[0]; lhs = rawd(mpf(q)) - rawd(contact(k)); rhs = log(mpf(q)) - (mpf(q) - contact(k))
            maxerr = max(maxerr, abs(lhs - rhs)); cnt += 1
        k += 1
    out["solo_checked"] = cnt; out["solo_max_abs_err"] = float(maxerr)
    ok = all(a["rel_residual"] < 1e-20 for a in ab) and out["amp_max_rel_err"] < 1e-25 and viol == 0 and float(maxerr) < 1e-25
    out["ok"] = bool(ok); res["all_ok"] = bool(res["all_ok"] and ok)
    res["towers"].append(out)
    lg("rang %d : Abel %s | amp err %.1e viol %d | solo %d err %.1e | ok=%s" % (rank, [a["rel_residual"] for a in ab],
        out["amp_max_rel_err"], viol, cnt, float(maxerr), ok))
json.dump(res, open(os.path.join(OUT, "data", "e447b_twin.json"), "w"), indent=1)
lg("FIN e447b all_ok=%s" % res["all_ok"])
