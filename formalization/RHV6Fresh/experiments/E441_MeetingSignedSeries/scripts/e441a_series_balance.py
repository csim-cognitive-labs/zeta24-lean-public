# -*- coding: utf-8 -*-
"""E441(a) — bilan signé des rencontres le long de la série d'UNE Tour (β = ½ fixé, hauteur T = hauteur d'Odlyzko
de rang donné, données). Objets autorisés seulement : contacts C_k = exp((arctan(T/β) + kπ)/T), cellules [C_k, C_{k+1}),
signes (−1)^k, écarts entre premiers consécutifs, Λ exact par crible, demande brute ψ(x) − x.
Contrôles compilés (0 violation attendue) : lastContact_le / lt_contact_succ (encadrement), meetingCell_series_read_by_frequency
(|Δm − T log(p'/p)/π| < 1), cellDemand_eq, signedPrimeSum_eq_meetings (M3), series_signed_balance (M4),
signedLengthSum_closed_form / signedLengthSum_first_last (M5), cellLength_lt_of_lt_meeting / meeting_mul_lt_cellLength (M6),
series_balance_near_meetings (M7). Mesures sans théorème : (d) règle de signe, (e) règle de montée, (f) croissance de S_J."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e441a.log"))
G, sha = load_zeros(log)
BETA = 0.5
RANKS = [1, 100, 1000, 10000, 100000, 1000000, 2001052]
N = 200000
# Λ exact par crible (VALIDATION arithmétique) : Λ(n) = log p si n = p^a
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
PS = np.cumsum(lam)                       # ψ(x) pour x entier
TH = np.cumsum(np.where(isp, lam, 0.0))   # θ(x) : poids premier seulement
log("crible : %d premiers ≤ %d, ψ(N) = %.6f, θ(N) = %.6f" % (len(P), N, PS[N], TH[N]))
PR = P[P >= 3]                            # rencontres p_{n+1}, n ≥ 1 (p_1 = 2 est une borne inférieure seulement)
LOGP = np.log(PR.astype(np.float64))
def stage(T, x): return (T * np.log(x) - math.atan2(T, BETA)) / math.pi
def contact(T, k): return np.exp((math.atan2(T, BETA) + k * math.pi) / T)
res = {"zeros": int(len(G)), "sha256": sha, "N": N, "primes": int(len(P)), "beta": BETA, "towers": {}}
for rank in RANKS:
    T = float(G[rank - 1]); r = math.exp(math.pi / T)
    s = stage(T, PR.astype(np.float64)); m = np.floor(s).astype(np.int64); f = s - m
    kmin = int(m[0]) - 1; kmax = int(m[-1]) + 2
    K = np.arange(kmin, kmax + 1, dtype=np.int64)
    C = contact(T, K.astype(np.float64))               # C[idx] pour k = kmin + idx
    FL = np.floor(C).astype(np.int64); FL = np.minimum(FL, N)
    cellW = PS[FL[1:]] - PS[FL[:-1]]; cellPW = TH[FL[1:]] - TH[FL[:-1]]; cellNPW = cellW - cellPW
    cellL = C[1:] - C[:-1]
    cellD = (PS[FL[1:]] - C[1:]) - (PS[FL[:-1]] - C[:-1])
    idx = m - kmin
    viol = {}
    viol["bracket"] = int(np.sum(~((C[idx] <= PR) & (PR < C[idx + 1]))))
    ambiguous = int(np.sum(np.abs(s - np.round(s)) < 1e-9))
    dk = m[1:] - m[:-1]; pred = T * np.log(PR[1:] / PR[:-1]) / math.pi
    viol["read_by_frequency"] = int(np.sum(np.abs(dk - pred) >= 1))
    # règle exacte de déplacement : Δm = ⌊pred⌋ + [f + {pred} ≥ 1]
    rule_dm = np.floor(pred).astype(np.int64) + ((f[:-1] + (pred - np.floor(pred))) >= 1).astype(np.int64)
    viol["displacement_rule"] = int(np.sum(rule_dm != dk))
    viol["cellDemand_eq"] = int(np.sum(np.abs(cellD - (cellW - cellL)) > 1e-7 * (1 + np.abs(cellW) + np.abs(cellL))))
    has_contact = dk > 0                                  # l'écart (p_j, p_{j+1}) a un contact
    gaps = len(dk)
    # (b) séries maximales où chaque écart a un contact ; identité M3 et M4, M7
    runs = []; j = 0
    while j < gaps:
        if has_contact[j]:
            k = j
            while k < gaps and has_contact[k]: k += 1
            runs.append((j, k)); j = k
        else: j += 1
    m3_maxabs = 0.0; m7_viol = 0; m4_viol = 0; m6_viol = 0; cf_relerr = 0.0; fl_relerr = 0.0; ratios = []; nseries = 0
    m3_general_viol = 0; longest = (0, 0)
    for (a0, b) in runs:                                  # gaps a0..b-1 ont un contact (gap j = (PR[j], PR[j+1]))
        # Lean : ⟨n⟩ = gap a0 = (p_n, p_{n+1}) avec p_{n+1} = PR[a0+1] ; m_n = m[a0+1] ; ⟨n+J⟩ = gap b-1, m_{n+J} = m[b] ;
        # cellules [m[a0+1], m[b]) ; rencontres p_{n+1..n+J} = PR[a0+1 .. b-1], J = b - a0 - 1 ≥ 1
        a = a0 + 1; J = b - a0 - 1
        if J < 1: continue
        b = b + 1                                         # PR[b-1] = p_{n+J+1} (rencontre de ⟨n+J⟩)
        k0 = m[a]; M = m[b - 1] - k0
        if M < 1: continue
        nseries += 1
        if J > longest[1] - longest[0]: longest = (a, b)
        i0 = k0 - kmin; sg = (-1.0) ** np.arange(M)
        spw = np.sum(sg * cellPW[i0:i0 + M]); snpw = np.sum(sg * cellNPW[i0:i0 + M]); sl = np.sum(sg * cellL[i0:i0 + M])
        sd = np.sum(sg * cellD[i0:i0 + M])
        off = m[a:b - 1] - k0; msum = np.sum((-1.0) ** off * LOGP[a:b - 1])
        m3_maxabs = max(m3_maxabs, abs(spw - msum))
        if abs(sd - (spw + snpw - sl)) > 1e-6 * (1 + abs(sd) + abs(sl)): m4_viol += 1
        cf = cellL[i0] * (1 - (-r) ** M) / (1 + r)
        cf_relerr = max(cf_relerr, abs(sl - cf) / max(abs(sl), 1e-300))
        fl = (cellL[i0] - (-1.0) ** M * r * cellL[i0 + M - 1]) / (1 + r)
        fl_relerr = max(fl_relerr, abs(sl - fl) / max(abs(sl), 1e-300))
        ratios.append(abs(sl) / cellL[i0 + M - 1])
        bound = PR[b - 1] * (r - 1)
        if not (abs(sd - msum - snpw) < bound): m7_viol += 1
        if not (cellL[i0 + M - 1] < bound and PR[a] * (1 - 1 / r) < cellL[i0]): m6_viol += 1
    # (b') cas général : cellules [m[a], m[b]) d'une série quelconque (y compris écarts sans contact) :
    # poids premier signé = Σ sur les premiers q avec C_{m[a]} ≤ q < C_{m[b]} de (−1)^{m(q)−m[a]} log q
    rng = np.random.RandomState(441); gen_maxabs = 0.0; extra_terms = 0; ngen = 0
    for _ in range(2000):
        a = int(rng.randint(0, len(PR) - 2)); b = int(min(len(PR) - 1, a + 1 + rng.randint(1, 50)))
        k0 = m[a]; M = m[b] - k0
        if M < 1: continue
        ngen += 1; i0 = k0 - kmin; sg = (-1.0) ** np.arange(M)
        spw = np.sum(sg * cellPW[i0:i0 + M])
        sel = (C[i0] < PR) & (PR <= FL[i0 + M])             # Ioc en entiers : C_{m[a]} < q ≤ ⌊C_{m[b]}⌋
        qs = np.sum((-1.0) ** (m[sel] - k0) * LOGP[sel])
        gen_maxabs = max(gen_maxabs, abs(spw - qs))
        extra_terms += int(np.sum(sel)) - (b - a)
    # (d) règle de signe entre rencontres consécutives (mesure)
    flip = (dk % 2 == 1)
    par_round = (np.round(pred).astype(np.int64) % 2 == 1)
    par_floor = (np.floor(pred).astype(np.int64) % 2 == 1)
    # (e) règle de montée : L_m ≤ log p
    Lm = cellL[idx]; rising = Lm <= LOGP
    sure_rise = PR * (r - 1) <= LOGP
    both = np.zeros(len(PR), dtype=bool); both[1:-1] = has_contact[:-1] & has_contact[1:]   # écarts I et J avec contact
    sure_fall = both & (PR * (1 - 1 / r) > LOGP + cellNPW[idx])
    e_viol = int(np.sum(sure_rise & ~rising)) + int(np.sum(sure_fall & (cellD[idx] >= 0)))
    e_sure_fall_n = int(np.sum(sure_fall)); e_sure_rise_n = int(np.sum(sure_rise))
    meet_rise_both = float(np.mean(cellD[idx][both] >= 0)) if both.any() else None
    xs = 2.0
    for _ in range(200):                                   # seuil x* : x(r−1) = log x
        xs2 = math.log(xs) / (r - 1); 
        if abs(xs2 - xs) < 1e-9 * xs: break
        xs = 0.5 * (xs + xs2)
    # (f) croissance de S_J sur la plus longue série
    growth = {}
    if longest[1] - longest[0] >= 3:
        a, b = longest; off = m[a:b - 1] - m[a]
        S = np.cumsum((-1.0) ** off * LOGP[a:b - 1]); Jv = np.arange(1, len(S) + 1)
        bound = PR[a + 1:b] * (r - 1)
        growth = {"J_max": int(len(S)), "p_start": int(PR[a]), "p_end": int(PR[b - 1]),
                  "abs_S_over_sqrtJ_logp_max": float(np.max(np.abs(S) / (np.sqrt(Jv) * LOGP[a:b - 1]))),
                  "abs_S_over_sqrtJ_logp_final": float(abs(S[-1]) / (math.sqrt(len(S)) * LOGP[b - 2])),
                  "abs_S_final": float(abs(S[-1])), "abs_S_max": float(np.max(np.abs(S))),
                  "bound_final": float(bound[-1]), "abs_S_over_bound_final": float(abs(S[-1]) / bound[-1]),
                  "abs_S_over_bound_max": float(np.max(np.abs(S) / bound)),
                  "fraction_J_where_S_exceeds_bound": float(np.mean(np.abs(S) > bound))}
    tw = {"T": T, "r_minus_1": r - 1, "ambiguous_stage": ambiguous, "violations": viol,
          "gaps": int(gaps), "gaps_with_contact_fraction": float(np.mean(has_contact)),
          "mean_contacts_per_gap": float(dk.mean()), "runs_with_contact": len(runs), "series_J_ge_1": nseries,
          "longest_run_gaps": int(longest[1] - longest[0]),
          "M3_max_abs_diff": m3_maxabs, "M4_violations": m4_viol, "M5_closed_form_relerr": cf_relerr,
          "M5_first_last_relerr": fl_relerr, "M6_violations": m6_viol, "M7_violations": m7_viol,
          "signed_descent_over_last_cell": {"n": len(ratios), "min": float(min(ratios)) if ratios else None,
                                            "max": float(max(ratios)) if ratios else None,
                                            "mean": float(np.mean(ratios)) if ratios else None, "r_over_1_plus_r": r / (1 + r)},
          "general_prime_sum_max_abs_diff": gen_maxabs, "general_series": ngen, "general_extra_or_missing_terms": extra_terms,
          "sign_flip_fraction": float(np.mean(flip)), "flip_pred_round_agree": float(np.mean(flip == par_round)),
          "flip_pred_floor_agree": float(np.mean(flip == par_floor)),
          "rising_fraction": float(np.mean(rising)), "rising_threshold_xstar": xs,
          "rising_fraction_below_xstar": float(np.mean(rising[PR <= xs])) if np.any(PR <= xs) else None,
          "rising_fraction_above_xstar_r": float(np.mean(rising[PR > xs * r])) if np.any(PR > xs * r) else None,
          "rising_rule_violations": e_viol, "sure_rise_n": e_sure_rise_n, "sure_fall_n": e_sure_fall_n, "meeting_cells_rising_fraction_both_contacts": meet_rise_both, "both_contacts_fraction": float(np.mean(both)), "largest_rising_p": int(PR[rising].max()) if rising.any() else None,
          "smallest_nonrising_p": int(PR[~rising].min()) if (~rising).any() else None,
          "growth": growth}
    res["towers"]["rank%d" % rank] = tw
    log("rang %d T=%.4f : contacts/écart %.3f, écarts avec contact %.3f, viol %s, M3 %.2e, M4 %d, M5 %.1e/%.1e, M6 %d, M7 %d, "
        "descente/dernière cellule [%s, %s] (r/(1+r)=%.4f), général %.2e (%d séries, termes ± %d), "
        "flips %.3f (round %.3f, floor %.3f), montée %.3f x*=%.1f viol %d, croissance %s" % (
        rank, T, tw["mean_contacts_per_gap"], tw["gaps_with_contact_fraction"], viol, m3_maxabs, m4_viol, cf_relerr, fl_relerr,
        m6_viol, m7_viol, tw["signed_descent_over_last_cell"]["min"], tw["signed_descent_over_last_cell"]["max"], r / (1 + r),
        gen_maxabs, ngen, extra_terms, tw["sign_flip_fraction"], tw["flip_pred_round_agree"], tw["flip_pred_floor_agree"],
        tw["rising_fraction"], xs, e_viol, json.dumps(growth)))
json.dump(res, open(os.path.join(OUT, "data", "e441a_results.json"), "w"), indent=1)
log("terminé")
