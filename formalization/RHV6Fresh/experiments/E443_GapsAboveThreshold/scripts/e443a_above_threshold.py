# -*- coding: utf-8 -*-
"""E443(a) — les écarts au-dessus du seuil d'UNE Tour (β = ½, T = hauteur d'Odlyzko de rang donné). Objets : contacts,
cellules, signes, écarts, Λ exact, demande brute. Contrôles compilés (0 violation attendue) : A1 (Bertrand), A2–A3
(cellules par écart, déplacement), A4 (écart sans contact dans une cellule), A5 (pente d'un écart entier), A6 (poids non
premier ≤ 2√C log C), A7 (second seuil : la cellule de rencontre descend). Mesures sans théorème étiquetées."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e443a.log"))
G, sha = load_zeros(log)
BETA = 0.5; RANKS = [1, 100, 1000, 10000, 100000]; N = 1000000
lam = np.zeros(N + 1); isp = np.zeros(N + 1, dtype=bool)
sieve = np.ones(N + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(N ** 0.5) + 1):
    if sieve[i]: sieve[i * i::i] = False
P = np.flatnonzero(sieve).astype(np.int64)
for p in P:
    q = p
    while q <= N:
        lam[q] = math.log(p); q *= p
isp[P] = True
PS = np.cumsum(lam); TH = np.cumsum(np.where(isp, lam, 0.0))
log("crible : %d premiers ≤ %d" % (len(P), N))
PR = P[P >= 3]; LOGP = np.log(PR.astype(np.float64)); GAP = np.diff(P).astype(np.float64)   # GAP[j] = PR[j] - P[j] (écart ⟨j+1⟩)
def stage(T, x): return (T * np.log(x) - math.atan2(T, BETA)) / math.pi
def contact(T, k): return np.exp((math.atan2(T, BETA) + k * math.pi) / T)
def solve(fn, lo, hi):
    for _ in range(300):
        mid = 0.5 * (lo + hi)
        if fn(mid) > 0: hi = mid
        else: lo = mid
    return 0.5 * (lo + hi)
res = {"zeros": int(len(G)), "sha256": sha, "N": N, "beta": BETA, "towers": {}}
for rank in RANKS:
    T = float(G[rank - 1]); r = math.exp(math.pi / T)
    s = stage(T, PR.astype(np.float64)); m = np.floor(s).astype(np.int64)
    kmin = int(np.floor(stage(T, 2.0))) - 1; kmax = int(m[-1]) + 2
    K = np.arange(kmin, kmax + 1, dtype=np.int64); C = contact(T, K.astype(np.float64))
    FL = np.minimum(np.floor(C).astype(np.int64), N)
    cellW = PS[FL[1:]] - PS[FL[:-1]]; cellPW = TH[FL[1:]] - TH[FL[:-1]]; cellNPW = cellW - cellPW
    cellL = C[1:] - C[:-1]; cellD = (PS[FL[1:]] - C[1:]) - (PS[FL[:-1]] - C[:-1])
    idx = m - kmin
    viol = {}
    # A1 Bertrand
    viol["A1_bertrand"] = int(np.sum(PR > 2 * P[:-1]))
    # A2–A3 : cellules entières par écart et déplacement
    mlow = np.floor(stage(T, P[:-1].astype(np.float64))).astype(np.int64)      # dernier contact avant p_n
    has_contact = m > mlow
    whole = np.where(has_contact, m - (mlow + 1), 0)
    viol["A2_wholeCellCount"] = int(np.sum(whole[has_contact] >= T * math.log(2) / math.pi))
    dk = m[1:] - m[:-1]
    viol["A3_displacement"] = int(np.sum(dk >= T * math.log(2) / math.pi + 1))
    # A4 : écart sans contact dans la cellule de sa rencontre
    nc = ~has_contact
    viol["A4_gap_in_cell"] = int(np.sum(~((C[idx[nc]] <= P[:-1][nc]) & (PR[nc] < C[idx[nc] + 1]))))
    # A5 : pente d'un écart entier
    lhs = (PS[PR] - PR) - (PS[P[:-1]] - P[:-1]); npw_gap = (PS[PR] - TH[PR]) - (PS[P[:-1]] - TH[P[:-1]])
    viol["A5_gap_demand"] = int(np.sum(np.abs(lhs - (LOGP + npw_gap - GAP)) > 1e-6 * (1 + np.abs(lhs))))
    # A6 : poids non premier ≤ 2√C log C (toutes les cellules avec C_{k+1} ≤ N)
    okc = FL[1:] < N
    bound6 = 2 * np.sqrt(C[1:]) * np.log(C[1:])
    viol["A6_nonprime_bound"] = int(np.sum(cellNPW[okc] > bound6[okc] * (1 + 1e-12)))
    ratio6 = cellNPW[okc] / bound6[okc]
    # A7 : second seuil
    both = np.zeros(len(PR), dtype=bool); both[:-1] = has_contact[:-1] & has_contact[1:]   # écart I (avant p) et J (après p) avec contact
    far = LOGP + 2 * np.sqrt(PR * r) * np.log(PR * r) < PR * (1 - 1 / r)
    viol["A7_second_threshold"] = int(np.sum(both & far & (cellD[idx] >= 0)))
    xstar = solve(lambda x: x * (r - 1) - math.log(x), 2.0, 1e12)
    xstar2 = solve(lambda x: x * (1 - 1 / r) - (math.log(x) + 2 * math.sqrt(x * r) * math.log(x * r)), 2.0, 1e14)
    # mesures
    desc = cellD[idx] < 0
    between = both & (PR > xstar) & (PR <= xstar2)
    above2 = both & (PR > xstar2)
    smallest_all_desc = None
    if both.any():
        nd = PR[both & ~desc]
        smallest_all_desc = int(nd.max()) if len(nd) else int(PR[both].min())
    # part des écarts avec contact par décade, contre moyenne(min(1, g/L)) (L = longueur de la cellule de p_n)
    Lcell = cellL[np.floor(stage(T, P[:-1].astype(np.float64))).astype(np.int64) - kmin]
    rule = np.minimum(1.0, GAP / Lcell)
    decades = {}
    for d in range(1, 7):
        sel = (P[:-1] >= 10 ** (d - 1)) & (P[:-1] < 10 ** d)
        if sel.any():
            decades["1e%d" % d] = {"n": int(sel.sum()), "contact_fraction": float(np.mean(has_contact[sel])),
                                   "rule_mean_min1_g_over_L": float(np.mean(rule[sel])),
                                   "primes_per_cell_over_L_logp": float(np.mean((Lcell[sel] / np.log(P[:-1][sel].astype(np.float64)))))}
    # premiers par cellule et signe des pentes au-dessus de x* (mesure)
    cellC = C[:-1]; above = (cellC > xstar) & okc
    ppc = (np.searchsorted(P, FL[1:]) - np.searchsorted(P, FL[:-1]))[above] if above.any() else np.array([])
    meas = {"cells_above_xstar": int(above.sum()),
            "primes_per_cell_mean": float(ppc.mean()) if above.any() else None,
            "L_over_logC_mean": float(np.mean(cellL[above] / np.log(cellC[above]))) if above.any() else None,
            "positive_slope_fraction_above_xstar": float(np.mean(cellD[above] > 0)) if above.any() else None,
            "abs_slope_over_L_mean_above_xstar": float(np.mean(np.abs(cellD[above]) / cellL[above])) if above.any() else None}
    tw = {"T": T, "r": r, "violations": viol, "xstar": xstar, "xstar2": xstar2,
          "gaps": int(len(PR)), "contact_fraction": float(np.mean(has_contact)),
          "A6_ratio_max": float(ratio6.max()), "A6_ratio_mean": float(ratio6.mean()),
          "meeting_cells_both_contacts": int(both.sum()),
          "descending_fraction_below_xstar": float(np.mean(desc[both & (PR <= xstar)])) if (both & (PR <= xstar)).any() else None,
          "descending_fraction_between": float(np.mean(desc[between])) if between.any() else None, "n_between": int(between.sum()),
          "descending_fraction_above_xstar2": float(np.mean(desc[above2])) if above2.any() else None, "n_above2": int(above2.sum()),
          "largest_nondescending_p_both": smallest_all_desc, "decades": decades, "measures_no_theorem": meas,
          "max_displacement": int(dk.max()), "bertrand_bound": T * math.log(2) / math.pi + 1}
    res["towers"]["rank%d" % rank] = tw
    log("rang %d T=%.3f : viol %s ; x*=%.1f x**=%.3g ; contact %.3f ; A6 max %.3f ; descente sous x* %s, entre %s (n=%d), au-dessus x** %s (n=%d) ; plus grand p non descendant %s ; déplacement max %d < %.1f ; décades %s ; mesures %s" % (
        rank, T, viol, xstar, xstar2, tw["contact_fraction"], tw["A6_ratio_max"], tw["descending_fraction_below_xstar"],
        tw["descending_fraction_between"], tw["n_between"], tw["descending_fraction_above_xstar2"], tw["n_above2"],
        smallest_all_desc, tw["max_displacement"], tw["bertrand_bound"], json.dumps(decades), json.dumps(meas)))
json.dump(res, open(os.path.join(OUT, "data", "e443a_results.json"), "w"), indent=1)
log("terminé")
