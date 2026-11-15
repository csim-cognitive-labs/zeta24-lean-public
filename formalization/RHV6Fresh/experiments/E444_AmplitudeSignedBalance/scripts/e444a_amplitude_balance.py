# -*- coding: utf-8 -*-
"""E444(a) — le bilan signé porté par la fréquence ET l'amplitude d'UNE Tour (β = ½, T = hauteur d'Odlyzko de rang donné).
Objets : contacts C_k = exp((arctan(T/β)+kπ)/T), cellules, valeurs réelles aux contacts v_k = (−1)^k C_k^β/|β+iT|,
écarts, Λ exact, demande brute. Contrôles compilés (0 violation attendu, tolérances float64 explicites) : B2 (β lu à
chaque rencontre depuis la fraction de cellule), B3 (T et β lus sur chaque cellule), B4 (forme close pondérée), B6
(identité de bloc et de série), B7 (rapport des valeurs entre rencontres, borne de Bertrand). Mesures : R9 (signes qui
changent avec β), R10 (croissance de la somme pondérée), R11 (rencontres par cellule et changements de signe au-dessus
de x*). Jumeau à 30 chiffres : e444b_twin_mpmath.py."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e444a.log"))
G, sha = load_zeros(log)
BETA = 0.5; RANKS = [1, 10, 100, 1000, 10000, 100000, 2000000]; N = 1000000
BETAS_ALT = [0.1, 0.3, 0.7, 0.9, 1.0]
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
PR = P[P >= 3]; LOGP = np.log(PR.astype(np.float64))
def phase(T, b): return math.atan2(T, b)
def stage(T, x, b=BETA): return (T * np.log(x) - phase(T, b)) / math.pi
def contact(T, k, b=BETA): return np.exp((phase(T, b) + k * math.pi) / T)
def solve(fn, lo, hi):
    for _ in range(300):
        mid = 0.5 * (lo + hi)
        if fn(mid) > 0: hi = mid
        else: lo = mid
    return 0.5 * (lo + hi)
res = {"zeros": int(len(G)), "sha256": sha, "N": N, "beta": BETA, "betas_alt": BETAS_ALT, "towers": {}}
for rank in RANKS:
    T = float(G[rank - 1]); r = math.exp(math.pi / T); rb = math.exp(BETA * math.pi / T); nrm = math.hypot(BETA, T)
    s = stage(T, PR.astype(np.float64)); m = np.floor(s).astype(np.int64); frac = s - m
    kmin = int(np.floor(stage(T, 2.0))) - 1; kmax = int(m[-1]) + 2
    K = np.arange(kmin, kmax + 1, dtype=np.int64); C = contact(T, K.astype(np.float64))
    V = np.where(K % 2 == 0, 1.0, -1.0) * np.sqrt(C) / nrm          # v_k (β = ½ : C^β = √C)
    FL = np.minimum(np.floor(C).astype(np.int64), N)
    cellW = PS[FL[1:]] - PS[FL[:-1]]; cellPW = TH[FL[1:]] - TH[FL[:-1]]
    cellL = C[1:] - C[:-1]; cellD = (PS[FL[1:]] - C[1:]) - (PS[FL[:-1]] - C[:-1])
    idx = m - kmin
    viol = {}; meas = {}
    # B2 : β lu à chaque rencontre depuis (T, p, cellule + fraction) ; budget d'erreur float64 explicite
    ang = T * LOGP - math.pi * s
    beta_read = T / np.tan(ang)
    err2 = np.abs(beta_read - BETA) / BETA
    budget2 = 64 * np.finfo(float).eps * np.abs(T * LOGP) * (T / BETA)   # perte par annulation × sensibilité de tan près de π/2
    viol["B2_radial_from_fraction"] = int(np.sum(err2 > np.maximum(budget2, 1e-9)))
    meas["B2_max_rel_dev"] = float(err2.max()); meas["B2_median_rel_dev"] = float(np.median(err2))
    # B3 : T et β lus sur chaque cellule (rapport des longueurs, rapport des amplitudes)
    lr = np.log(cellL[1:] / cellL[:-1]); vr = np.log(np.abs(V[2:]) / np.abs(V[1:-1]))
    T_read = math.pi / lr; b_read = vr / lr
    # budget float64 : erreur relative d'une longueur ≈ eps·C/L, amplifiée par 1/log(rapport) = T/π
    budget3 = 256 * np.finfo(float).eps * (C[1:-1] / cellL[:-1]) * (T / math.pi)
    viol["B3_height_from_lengths"] = int(np.sum(np.abs(T_read - T) / T > np.maximum(budget3, 1e-10)))
    viol["B3_radial_from_ratios"] = int(np.sum(np.abs(b_read - BETA) / BETA > np.maximum(budget3, 1e-10)))
    meas["B3_budget_max"] = float(budget3.max())
    meas["B3_max_rel_dev_T"] = float(np.max(np.abs(T_read - T) / T)); meas["B3_max_rel_dev_beta"] = float(np.max(np.abs(b_read - BETA) / BETA))
    # B4 : forme close du bilan des longueurs pondéré par l'amplitude
    q4 = math.exp((BETA + 1) * math.pi / T); nb4 = 0; worst4 = 0.0
    for M in (1, 2, 3, 7, 50, 200):
        if M > len(cellL): continue
        for k0i in np.linspace(0, len(cellL) - M, 20).astype(int):
            direct = float(np.sum(V[k0i:k0i + M] * cellL[k0i:k0i + M]))
            closed = V[k0i] * cellL[k0i] * (1 - (-q4) ** M) / (1 + q4)
            d = abs(direct - closed) / (abs(direct) + abs(V[k0i] * cellL[k0i]))
            budget4 = max(1e-10, 256 * np.finfo(float).eps * float(np.max(C[k0i:k0i + M] / cellL[k0i:k0i + M])))
            worst4 = max(worst4, d); nb4 += d > budget4
    viol["B4_closed_form"] = int(nb4); meas["B4_max_rel_dev"] = worst4
    # B6 : identité de bloc (plusieurs rencontres par cellule) : Σ_i v_{a+i} W^prime_{a+i} = Σ_{q premier du bloc} v_{m(q)} log q
    nb6 = 0; worst6 = 0.0
    for M in (1, 5, 50, 400):
        if M > len(cellL): continue
        for a_i in np.linspace(0, len(cellL) - M, 25).astype(int):
            lhs = float(np.sum(V[a_i:a_i + M] * cellPW[a_i:a_i + M]))
            sel = (PR > C[a_i]) & (PR <= C[a_i + M]) & (PR <= N)
            # Λ(2) : la cellule contenant 2 n'est jamais dans un bloc commençant à a_i ≥ 0 si C[a_i] ≥ 2 ; on exclut p = 2 par PR ≥ 3 et on vérifie
            if C[a_i] < 2: continue
            rhs = float(np.sum(V[idx[sel]] * LOGP[sel]))
            d = abs(lhs - rhs) / (1 + abs(lhs)); worst6 = max(worst6, d); nb6 += d > 1e-9
    viol["B6_block_identity"] = int(nb6); meas["B6_max_rel_dev"] = worst6
    # B6' : série de rencontres : toutes les cellules entre deux rencontres consécutives avec contact ; Σ_j v_{m_j} log p_{j+1} = Σ_i v_{k0+i} W^prime
    mlow = np.floor(stage(T, P[:-1].astype(np.float64))).astype(np.int64); has_contact = m > mlow
    runs = []; j = 0
    while j < len(PR):
        if has_contact[j]:
            k = j
            while k + 1 < len(PR) and has_contact[k + 1]: k += 1
            if k - j >= 3: runs.append((j, k))
            j = k + 1
        else: j += 1
    nb6b = 0; worst6b = 0.0; nruns = 0
    for (j0, j1) in runs[:200]:
        nruns += 1
        a = idx[j0]; b = idx[j1]
        lhs = float(np.sum(V[a:b] * cellPW[a:b])); rhs = float(np.sum(V[idx[j0:j1]] * LOGP[j0:j1]))
        d = abs(lhs - rhs) / (1 + abs(lhs)); worst6b = max(worst6b, d); nb6b += d > 1e-9
    viol["B6_series_identity"] = int(nb6b); meas["B6_series_count"] = nruns; meas["B6_series_max_rel_dev"] = worst6b
    # B7 : entre rencontres consécutives : rapport des valeurs = (−e^{βπ/T})^Δ, β lu, Δ < T log 2/π + 1
    dk = m[1:] - m[:-1]
    ratio = V[idx[1:]] / V[idx[:-1]]
    pred = np.where(dk % 2 == 0, 1.0, -1.0) * rb ** dk
    viol["B7_value_ratio"] = int(np.sum(np.abs(ratio - pred) / np.abs(pred) > 1e-9))
    pos = dk > 0
    b7 = T * np.log(np.abs(ratio[pos])) / (dk[pos] * math.pi)
    viol["B7_radial_from_meetings"] = int(np.sum(np.abs(b7 - BETA) / BETA > 1e-8))
    viol["B7_bertrand"] = int(np.sum(dk >= T * math.log(2) / math.pi + 1))
    meas["B7_max_displacement"] = int(dk.max()); meas["B7_bertrand_bound"] = T * math.log(2) / math.pi + 1
    # R9 : part des rencontres dont le signe change quand β passe de ½ à β'
    r9 = {}
    for b2 in BETAS_ALT:
        m2 = np.floor(stage(T, PR.astype(np.float64), b2)).astype(np.int64)
        flips = float(np.mean((m2 - m) % 2 != 0))
        shift = abs(phase(T, BETA) - phase(T, b2)) / math.pi
        r9[str(b2)] = {"flip_fraction": flips, "phase_shift_cells": shift, "ratio": (flips / shift if shift > 0 else None)}
    meas["R9_sign_flips_vs_phase_shift"] = r9
    # R10 : croissance de la somme des rencontres pesées par l'amplitude A_J = Σ_{j<J} v_{m_j} log p_{j+1}
    A = np.cumsum(V[idx] * LOGP); S = np.cumsum(np.where(m % 2 == 0, 1.0, -1.0) * LOGP)
    r10 = {}
    for J in (10, 100, 1000, 10000, len(PR)):
        if J > len(PR): continue
        lastv = abs(V[idx[J - 1]]) * LOGP[J - 1]
        r10[str(J)] = {"p_J": int(PR[J - 1]), "abs_A": float(abs(A[J - 1])), "A_over_last_term": float(abs(A[J - 1]) / lastv),
                       "A_over_last_amp_sqrtJ": float(abs(A[J - 1]) / (abs(V[idx[J - 1]]) * math.sqrt(J))),
                       "abs_S_signed_only": float(abs(S[J - 1]))}
    # exposant mesuré de |A_J| en p_J sur la seconde moitié (log-log, moindres carrés) : mesure sans théorème
    Jh = np.arange(len(PR) // 2, len(PR)); x = np.log(PR[Jh].astype(np.float64)); y = np.log(np.abs(A[Jh]) + 1e-300)
    r10["loglog_exponent_second_half"] = float(np.polyfit(x, y, 1)[0])
    meas["R10_amplitude_weighted_sum"] = r10
    # R11 : au-dessus de x* : rencontres par cellule, et changements de signe entre rencontres consécutives contre Bertrand
    xstar = solve(lambda x: x * (r - 1) - math.log(x), 2.0, 1e12)
    above = PR[:-1] > xstar
    r11 = {"x_star": xstar, "meetings_above": int(above.sum())}
    if above.sum() > 0:
        cnt = np.bincount(idx[PR > xstar]); cnt = cnt[cnt > 0]
        d = dk[above]
        r11.update({"primes_per_cell_mean": float(cnt.mean()), "primes_per_cell_max": int(cnt.max()),
                    "frac_same_cell": float(np.mean(d == 0)), "frac_odd_displacement": float(np.mean(d % 2 == 1)),
                    "frac_even_positive": float(np.mean((d > 0) & (d % 2 == 0))), "max_displacement": int(d.max()),
                    "bertrand_bound": T * math.log(2) / math.pi + 1})
    meas["R11_above_threshold"] = r11
    res["towers"][str(rank)] = {"T": T, "r": r, "n_meetings": int(len(PR)), "violations": viol, "measures": meas}
    log("rang %d T=%.6f : violations %s" % (rank, T, viol))
    log("  B2 max/med dev %.2e/%.2e ; B3 dev T %.1e β %.1e ; B4 %.1e ; B6 %.1e (séries %d, %.1e) ; Δmax %d < %.2f" % (
        meas["B2_max_rel_dev"], meas["B2_median_rel_dev"], meas["B3_max_rel_dev_T"], meas["B3_max_rel_dev_beta"], meas["B4_max_rel_dev"],
        meas["B6_max_rel_dev"], nruns, worst6b, meas["B7_max_displacement"], meas["B7_bertrand_bound"]))
    log("  R9 " + " ; ".join("β'=%s : flips %.5f / shift %.5f" % (b, v["flip_fraction"], v["phase_shift_cells"]) for b, v in r9.items()))
    log("  R10 " + " ; ".join("J=%s : |A|/dernier %.3g, |A|/(amp√J) %.3g" % (J, v["A_over_last_term"], v["A_over_last_amp_sqrtJ"]) for J, v in r10.items() if isinstance(v, dict)) + " ; exposant %.3f" % r10["loglog_exponent_second_half"])
    log("  R11 " + json.dumps(r11))
tot = sum(sum(t["violations"].values()) for t in res["towers"].values())
res["total_violations"] = int(tot)
json.dump(res, open(os.path.join(OUT, "data", "e444a_results.json"), "w"), indent=1)
log("TOTAL violations = %d" % tot)
