# -*- coding: utf-8 -*-
"""E448(b) — jumeau déterministe (mpmath 30 chiffres, sympy pour les premiers) de e448a : orbite de la fraction, deux
formes du rapport des amplitudes, monotonie, paires dans une même cellule par décade (entiers à comparer à e448a),
pour trois hauteurs, premiers p_n < 10^6. Tout recalculé indépendamment de numpy."""
import os, sys, json, math
from mpmath import mp, mpf, exp, log, sqrt, floor, atan2, pi
import sympy
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
lg = Logger(os.path.join(OUT, "logs", "e448b.log"))
mp.dps = 30
G, sha = load_zeros(lg)
primes = list(sympy.primerange(2, 1_000_100)); lg("premiers : %d" % len(primes))
def frac(x): return x - floor(x)
res = {"dps": mp.dps, "towers": [], "all_ok": True}
try:
    A_ref = json.load(open(os.path.join(OUT, "data", "e448a_results.json")))
except Exception:
    A_ref = None
for rank in [1, 100, 10000]:
    T = mpf(G[rank - 1]); ph = atan2(T, mpf("0.5")); norm = sqrt(mpf("0.25") + T * T)
    out = {"rank": rank, "T": float(T)}
    same = [0] * 6; pairs = [0] * 6; worst_orbit = mpf(0); worst_rc = mpf(0); worst_re = mpf(0); mono_viol = 0
    prev = None
    for p in primes:
        s = (T * log(mpf(p)) - ph) / pi; k = int(floor(s)); f = s - k
        A = sqrt(exp((ph + k * pi) / T)) / norm
        if prev is not None and prev[0] < 1_000_000:
            p0, s0, k0, f0, A0 = prev
            d = T * log(mpf(p) / p0) / pi
            e = abs(f - frac(f0 + d)); e = min(e, 1 - e); worst_orbit = max(worst_orbit, e)
            ratio = A / A0
            worst_rc = max(worst_rc, abs(ratio - exp(pi * (k - k0) / (2 * T))) / ratio)
            worst_re = max(worst_re, abs(ratio - sqrt(mpf(p) / p0) * exp(-pi * (f - f0) / (2 * T))) / ratio)
            if A < A0: mono_viol += 1
            dd = int(math.floor(math.log10(p0))); pairs[dd] += 1
            if k == k0: same[dd] += 1
        prev = (p, s, k, f, A)
    out.update({"orbit_max_circ_residual": float(worst_orbit), "ratio_cells_max_rel_err": float(worst_rc),
                "ratio_exact_max_rel_err": float(worst_re), "mono_violations": mono_viol,
                "same_cell_by_decade": [{"decade": dd, "pairs": pairs[dd], "same_cell": same[dd]} for dd in range(6)]})
    ok = worst_orbit < mpf("1e-20") and worst_rc < mpf("1e-25") and worst_re < mpf("1e-25") and mono_viol == 0
    if A_ref is not None:
        ref = [t for t in A_ref["towers"] if t["rank"] == rank]
        if ref:
            refsc = {x["decade"]: x for x in ref[0]["same_cell_by_decade"]}
            match = all(refsc.get(dd, {}).get("same_cell") == same[dd] and refsc.get(dd, {}).get("pairs") == pairs[dd] for dd in range(6))
            out["same_cell_matches_e448a"] = match; ok = ok and match
    out["ok"] = ok; res["all_ok"] = res["all_ok"] and ok
    res["towers"].append(out)
    lg("rang %d : orbite=%.2e cells=%.2e exact=%.2e mono=%d même cellule=%s ok=%s" % (rank, out["orbit_max_circ_residual"],
        out["ratio_cells_max_rel_err"], out["ratio_exact_max_rel_err"], mono_viol, same, ok))
json.dump(res, open(os.path.join(OUT, "data", "e448b_twin.json"), "w"), indent=1)
lg("FIN e448b all_ok=%s" % res["all_ok"])
