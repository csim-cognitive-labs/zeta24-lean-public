# -*- coding: utf-8 -*-
"""E426(b) — rencontres brutes (parties réelles égales) de Tours consécutives par localisation de racines, par bande de hauteur ;
comparaison aux réseaux unitaires compilés ; valeurs portées ; contacts encadrant ; jumeau mpmath."""
import os, sys, math, json, numpy as np, mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import load_zeros, Logger
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e426b.log"))
G, sha = load_zeros(log)
BETA = 0.5; TWO_PI = 2 * math.pi; CH = 4_000_000; MAXN = 3e7
BANDS = {"low(1..101)": range(0, 100), "mid(1e5..)": range(100000, 100100), "high(2M-100..)": range(len(G) - 101, len(G) - 1)}
def roots(T1, T2, umax):
    """racines de D(u) = cos(T1 u − φ1)/r1 − cos(T2 u − φ2)/r2 sur [0, umax] (grille 8 points par période rapide + bissection)."""
    p1, p2 = math.atan2(T1, BETA), math.atan2(T2, BETA); r1, r2 = math.hypot(BETA, T1), math.hypot(BETA, T2)
    D = lambda u: np.cos(T1 * u - p1) / r1 - np.cos(T2 * u - p2) / r2
    h = (TWO_PI / (T1 + T2)) / 8; n = int(umax / h) + 2
    out = []
    for a in range(0, n, CH):
        u = a * h + h * np.arange(min(CH, n - a) + 1); d = D(u)
        sc = np.flatnonzero(np.sign(d[:-1]) * np.sign(d[1:]) < 0)
        lo, hi = u[sc], u[sc + 1]; dlo = d[sc]
        for _ in range(48):
            mid = 0.5 * (lo + hi); dm = D(mid); left = np.sign(dm) == np.sign(dlo)
            lo = np.where(left, mid, lo); dlo = np.where(left, dm, dlo); hi = np.where(left, hi, mid)
        out.append(0.5 * (lo + hi))
    return np.concatenate(out) if out else np.zeros(0), (p1, p2, r1, r2)
res = {"zeros": int(len(G)), "sha256": sha, "bands": {}}
twin_cases = []
for bname, rr in BANDS.items():
    rows = []; skipped = 0
    for n in rr:
        T1, T2 = G[n], G[n + 1]; g = T2 - T1; p1, p2 = math.atan2(T1, BETA), math.atan2(T2, BETA)
        u1 = (p2 - p1 + TWO_PI) / g; fs = TWO_PI / (T1 + T2); umax = u1 + 3 * fs
        if umax / fs > MAXN: skipped += 1; continue
        R, (p1, p2, r1, r2) = roots(T1, T2, umax)
        # réseaux unitaires dans la fenêtre
        mf = np.arange(math.ceil((-(p1 + p2)) / TWO_PI), math.floor(((T1 + T2) * umax - (p1 + p2)) / TWO_PI) + 1)
        vf = (p1 + p2 + TWO_PI * mf) / (T1 + T2); vs = np.array([(p2 - p1) / g, u1])
        lattice = np.sort(np.concatenate([vf, vs]))
        nf = len(vf); ns = 2
        # déplacement de chaque racine brute au point de réseau le plus proche, en unités du pas rapide
        j = np.clip(np.searchsorted(lattice, R), 1, len(lattice) - 1)
        disp = np.minimum(np.abs(R - lattice[j - 1]), np.abs(R - lattice[j])) / fs
        # racine brute la plus proche de la rencontre lente u1, valeur réelle brute (x^β cos/r), contacts encadrant
        i1 = int(np.argmin(np.abs(R - u1))) if len(R) else -1
        if i1 >= 0:
            ru = R[i1]; x = math.exp(ru); val1 = x ** BETA * math.cos(T1 * ru - p1) / r1; val2 = x ** BETA * math.cos(T2 * ru - p2) / r2
            s1 = (T1 * ru - p1) / math.pi; s2 = (T2 * ru - p2) / math.pi
            near = {"u": ru, "disp_from_u1_in_fast_steps": (ru - u1) / fs, "x": x, "value_T1": val1, "value_T2": val2,
                    "contact_k_before_T1": math.floor(s1), "frac_T1": s1 - math.floor(s1), "contact_k_before_T2": math.floor(s2), "frac_T2": s2 - math.floor(s2),
                    "unit_cos_at_root": math.cos(T1 * ru - p1), "unit_cos_at_u1": math.cos(T1 * u1 - p1)}
        else: near = None
        # ordre : nombre de racines brutes entre u0 et u1 contre nombre de points rapides entre u0 et u1
        n_between = int(np.sum((R > vs[0]) & (R < u1))); f_between = int(np.sum((vf > vs[0]) & (vf < u1)))
        vals = np.exp(R * BETA) * np.cos(T1 * R - p1) / r1
        rows.append({"rank": n + 1, "T1": T1, "T2": T2, "gap": g, "u1": u1, "n_raw": int(len(R)), "n_unit_fast": int(nf), "n_unit_slow": ns,
                     "disp_max": float(disp.max()) if len(R) else None, "disp_rms": float(np.sqrt(np.mean(disp ** 2))) if len(R) else None,
                     "raw_between_u0_u1": n_between, "fast_between_u0_u1": f_between, "value_abs_max": float(np.abs(vals).max()) if len(R) else None,
                     "value_abs_mean": float(np.abs(vals).mean()) if len(R) else None, "near_slow1": near})
        if n in (0, 1, 100000, len(G) - 2) and len(R): twin_cases.append((n, T1, T2, R[:20].tolist(), near["u"] if near else None))
    dm = [r["disp_max"] for r in rows if r["disp_max"] is not None]; dq = [r["n_raw"] - r["n_unit_fast"] - r["n_unit_slow"] for r in rows]
    bet = [r["raw_between_u0_u1"] - r["fast_between_u0_u1"] for r in rows]
    summ = {"pairs": len(rows), "skipped_too_many_roots": skipped, "count_diff_raw_minus_unit_hist": {str(k): dq.count(k) for k in sorted(set(dq))},
            "between_u0_u1_diff_hist": {str(k): bet.count(k) for k in sorted(set(bet))},
            "disp_max_median": float(np.median(dm)) if dm else None, "disp_max_max": float(np.max(dm)) if dm else None,
            "disp_rms_median": float(np.median([r["disp_rms"] for r in rows if r["disp_rms"] is not None])) if dm else None,
            "near_slow1_disp_median_fast_steps": float(np.median([abs(r["near_slow1"]["disp_from_u1_in_fast_steps"]) for r in rows if r["near_slow1"]])) if rows else None,
            "near_slow1_disp_max_fast_steps": float(np.max([abs(r["near_slow1"]["disp_from_u1_in_fast_steps"]) for r in rows if r["near_slow1"]])) if rows else None,
            "near_slow1_unit_cos_abs_median": float(np.median([abs(r["near_slow1"]["unit_cos_at_root"]) for r in rows if r["near_slow1"]])) if rows else None}
    res["bands"][bname] = {"summary": summ, "pairs": rows}
    log("bande %s : %d paires (%d sautées) ; n_brut − n_unitaire : %s ; déplacement max médian %.3g pas rapides (max %.3g) ; "
        "racine proche de la rencontre lente 1 : déplacement médian %.3g pas rapides, |cos| médian %.3f"
        % (bname, len(rows), skipped, summ["count_diff_raw_minus_unit_hist"], summ["disp_max_median"] or 0, summ["disp_max_max"] or 0,
           summ["near_slow1_disp_median_fast_steps"] or 0, summ["near_slow1_unit_cos_abs_median"] or 0))
# jumeau déterministe mpmath (30 chiffres) : raffinement des 20 premières racines et de la racine proche de u1
mp.mp.dps = 30; tw = []
for n, T1, T2, R20, ru in twin_cases:
    t1, t2 = mp.mpf(T1), mp.mpf(T2); p1, p2 = mp.atan2(t1, mp.mpf(BETA)), mp.atan2(t2, mp.mpf(BETA)); r1, r2 = mp.hypot(BETA, t1), mp.hypot(BETA, t2)
    D = lambda u: mp.cos(t1 * u - p1) / r1 - mp.cos(t2 * u - p2) / r2
    errs = []
    for r0 in R20 + ([ru] if ru is not None else []):
        try: errs.append(float(abs(mp.findroot(D, mp.mpf(r0)) - r0)))
        except Exception as e: errs.append(None)
    tw.append({"rank": n + 1, "max_abs_err_vs_float": max(e for e in errs if e is not None), "n": len(errs)})
    log("jumeau mpmath rang %d : écart max float/mpmath %.2e sur %d racines" % (n + 1, tw[-1]["max_abs_err_vs_float"], len(errs)))
res["twin_mpmath"] = tw
json.dump(res, open(os.path.join(OUT, "data", "e426b_results.json"), "w"), indent=1)
log("terminé")
