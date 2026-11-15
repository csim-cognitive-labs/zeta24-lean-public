# -*- coding: utf-8 -*-
"""E449(b) — jumeau déterministe (mpmath 30 chiffres, sympy premiers ≤ 10^6) : (d) formule tangentielle exacte depuis deux
contacts ; (a) intervalle de T et plage de φ, β du polygone du mot pour les rangs 1 et 100 avec les premiers ≤ 10^6
(bissection 60 pas, grille 41 points), à comparer aux valeurs X = 10^6 de e449a. Tout recalculé indépendamment de numpy."""
import os, sys, json, math
from mpmath import mp, mpf, exp, log, floor, atan2, pi, tan
import sympy
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
lg = Logger(os.path.join(OUT, "logs", "e449b.log"))
mp.dps = 30
G, sha = load_zeros(lg)
primes = list(sympy.primerange(2, 1_000_001)); lg("premiers ≤ 10^6 : %d" % len(primes))
Ls = [log(mpf(p)) for p in primes]
try: A = json.load(open(os.path.join(OUT, "data", "e449a_results.json")))
except Exception: A = None
res = {"dps": mp.dps, "towers": [], "all_ok": True}
for rank in [1, 100]:
    T = mpf(G[rank - 1]); ph = atan2(T, mpf("0.5"))
    ks = [int(floor((T * l - ph) / pi)) for l in Ls]
    lo_b = [(k + 1) * pi for k in ks]; hi_b = [k * pi for k in ks]
    def phi_lo(t): return max(t * l - b for l, b in zip(Ls, lo_b))
    def phi_hi(t): return min(t * l - b for l, b in zip(Ls, hi_b))
    def g(t): return phi_hi(t) - phi_lo(t)
    def root(a, b):
        for _ in range(60):
            m = (a + b) / 2
            if g(m) >= 0: a = m
            else: b = m
        return a
    T_lo = root(T, T - 1); T_hi = root(T, T + 1)
    grid = [T_lo + (T_hi - T_lo) * i / 40 for i in range(41)]
    pl = [phi_lo(t) for t in grid]; phh = [phi_hi(t) for t in grid]
    pts = [(t, a, b) for t, a, b in zip(grid, pl, phh) if b >= a]
    phi_min = min(a for _, a, _ in pts); phi_max = max(b for _, _, b in pts)
    beta_lo = min(t / tan(b) for t, _, b in pts); beta_hi = max(t / tan(a) for t, a, _ in pts)
    # (d) tangentielle
    kk = ks[len(ks) // 2]; C0 = exp((ph + kk * pi) / T); C1 = exp((ph + (kk + 1) * pi) / T)
    T_rec = pi / log(C1 / C0); ph_rec = T_rec * log(C0) - kk * pi; b_rec = T_rec / tan(ph_rec)
    out = {"rank": rank, "T": float(T), "T_lo": float(T_lo), "T_hi": float(T_hi), "phi_lo": float(phi_min), "phi_hi": float(phi_max),
           "beta_lo": float(beta_lo), "beta_hi": float(beta_hi), "g_at_true": float(g(T)),
           "tangential_T_err": float(abs(T_rec - T)), "tangential_phi_err": float(abs(ph_rec - ph)), "tangential_beta_err": float(abs(b_rec - mpf("0.5")))}
    ok = out["tangential_beta_err"] < 1e-24 and T_lo <= T <= T_hi and phi_min <= ph <= phi_max and beta_lo <= mpf("0.5") <= beta_hi
    if A is not None:
        ref = [t for t in A["towers"] if t["label"] == "zéro rang %d" % rank]
        if ref:
            r6 = [r for r in ref[0]["by_X"] if r["X"] == 10 ** 6][0]
            cmp = {"T_lo": abs(r6["T_lo"] - out["T_lo"]), "T_hi": abs(r6["T_hi"] - out["T_hi"]),
                   "phi_lo": abs(r6["phi_lo"] - out["phi_lo"]), "phi_hi": abs(r6["phi_hi"] - out["phi_hi"])}
            out["diff_vs_e449a"] = cmp
            ok = ok and cmp["T_lo"] < 1e-8 and cmp["T_hi"] < 1e-8 and cmp["phi_lo"] < 1e-6 and cmp["phi_hi"] < 1e-6
    out["ok"] = bool(ok); res["all_ok"] = res["all_ok"] and bool(ok); res["towers"].append(out)
    lg("rang %d : T∈[%.12f, %.12f] φ∈[%.10f, %.10f] β∈[%.8f, %.8f] tangentielle β err %.1e ok=%s diff=%s" % (
        rank, T_lo, T_hi, phi_min, phi_max, beta_lo, beta_hi, out["tangential_beta_err"], ok, out.get("diff_vs_e449a")))
json.dump(res, open(os.path.join(OUT, "data", "e449b_twin.json"), "w"), indent=1)
lg("FIN e449b all_ok=%s" % res["all_ok"])
