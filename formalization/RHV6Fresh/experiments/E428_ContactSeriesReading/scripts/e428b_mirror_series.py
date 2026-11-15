# -*- coding: utf-8 -*-
"""E428(b) — (1) indices de la Tour et de son miroir (mirror_contact_log_ratio, mirror_stagePosition_difference,
mirror_series_shift_difference_le_one, mirrorMode_add_norm / mirrorMode_sub_norm) ; (2) raccord individuel–collectif
(truncatedStep_eq_sum_individual, collective_eq_individual_add_rest) ; (3) recherche d'une loi sur série : candidats
contre le mot de 12 transitions. Jumeau mpmath."""
import os, sys, math, json, numpy as np, mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros, background_psi1
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e428b.log"))
G, sha = load_zeros(log)
RANKS = [1, 10, 100, 1000, 10000, 100000, 1000000, 2001052]
sieve = np.ones(20000, dtype=bool); sieve[:2] = False
for i in range(2, 142):
    if sieve[i]: sieve[i * i::i] = False
Pall = np.flatnonzero(sieve); Pi = Pall[2:2003]; P = Pi.astype(np.float64)   # p = 5 .. 17393 (2001 événements)
s = (Pi % 6 == 1); src, dst = s[:-1], s[1:]; orient = src.astype(int) - dst.astype(int)
code = np.where(src & dst, 0, np.where(src & ~dst, 1, np.where(~src & dst, 2, 3))).astype(np.int64)
NW = len(code) - 11; W = np.zeros(NW, dtype=np.int64)
for l in range(12): W |= code[l:l + NW] << (2 * l)
def cell_index(beta, T, q): return np.ceil((T * np.log(q) - math.atan2(T, beta)) / math.pi) - 1
def contact_value(beta, T, k):
    ph = math.atan2(T, beta); C = np.exp((ph + k * math.pi) / T)
    return np.where(k % 2 == 0, 1.0, -1.0) * C ** beta / math.hypot(beta, T)
def law_test(cand, tol=1e-9):
    """Critère pré-enregistré : à mot identique (groupes ≥ 2 fenêtres), étendue du candidat ≤ tol pour tous."""
    groups = {}
    for w, c in zip(W, cand): groups.setdefault(int(w), []).append(float(c))
    rng = np.array([np.ptp(v) for v in groups.values() if len(v) >= 2])
    return {"groups_ge2": int(len(rng)), "max_range": float(rng.max()), "fraction_groups_constant": float(np.mean(rng <= tol)),
            "law": bool(np.all(rng <= tol))}
res = {"zeros": int(len(G)), "sha256": sha, "events": int(len(orient)), "windows12": int(NW), "distinct_words": int(len(np.unique(W))), "pairs": {}}
for rank in RANKS:
    T = float(G[rank - 1])
    for beta in (0.3, 0.5):
        bm = 1 - beta; key = "rank%d_pair%.1f_%.1f" % (rank, beta, bm); r = {"T": T, "beta": beta, "mirror": bm}
        shift = math.atan2(T, beta) - math.atan2(T, bm); sp = shift / math.pi
        kb = cell_index(beta, T, P).astype(np.int64); km = cell_index(bm, T, P).astype(np.int64)
        d = km - kb
        # mirror_stagePosition_difference : s_β − s_{1−β} = −shift/π ⇒ k_{1−β} − k_β ∈ {⌊shift/π⌋, ⌈shift/π⌉}
        ok_abs = bool(np.all((d == math.floor(sp)) | (d == math.ceil(sp))))
        # séries depuis chaque ancrage : (Δk_m − Δk_β) = d_j − d_a ∈ {−1,0,1}
        D = d[None, :] - d[:, None]; iu = np.triu_indices(len(d), 1); Dv = D[iu]
        # mirror_contact_log_ratio au contact 0
        lr = (math.atan2(T, beta) / T) - (math.atan2(T, bm) / T)
        # normes miroir aux abscisses t = log p, d = β − ½ (modes normalisés)
        dd = beta - 0.5; t = np.log(P); v_plus = np.exp((dd + 1j * T) * t); v_minus = np.exp((-dd + 1j * T) * t)
        n_add = np.abs(v_plus + v_minus); n_sub = np.abs(v_plus - v_minus)
        r["C"] = {"phase_shift_over_pi": sp, "phase_shift_zero": bool(abs(shift) < 1e-15),
                  "abs_index_fraction_differs": float(np.mean(d != 0)), "abs_index_in_floor_ceil": ok_abs,
                  "series_shift_diff_values": sorted(set(int(x) for x in np.unique(Dv))), "series_shift_diff_violations": int(np.sum(np.abs(Dv) > 1)),
                  "series_shift_diff_fraction_nonzero": float(np.mean(Dv != 0)), "series_pairs": int(len(Dv)),
                  "contact_log_ratio_formula_abs_err": float(abs(lr - shift / T)),
                  "mirror_add_norm_vs_2cosh_max_err": float(np.max(np.abs(n_add - 2 * np.cosh(dd * t)))),
                  "mirror_sub_norm_vs_2sinh_max_err": float(np.max(np.abs(n_sub - 2 * np.abs(np.sinh(dd * t))))),
                  "mirror_add_norm_min": float(n_add.min()), "mirror_sub_norm_min": float(n_sub.min()), "mirror_sub_norm_max": float(n_sub.max())}
        # A4 : candidats sur fenêtres de 12 événements (p_i .. p_{i+12})
        i0 = np.arange(NW); p_start = P[i0]; p_end = P[i0 + 12]
        kmeet = cell_index(beta, T, P[1:]); v = contact_value(beta, T, kmeet)
        cs_v = np.concatenate([[0.0], np.cumsum(v)]); cs_ov = np.concatenate([[0.0], np.cumsum(orient * v)])
        nz = (d[1:] - d[:-1]) != 0; cs_nz = np.concatenate([[0], np.cumsum(nz)])
        cands = {"amplitude_total": beta * np.log(p_end / p_start), "signed_contact_sum": cs_v[i0 + 12] - cs_v[i0],
                 "oriented_weighted_sum": cs_ov[i0 + 12] - cs_ov[i0], "mirror_shift_discrepancies": (cs_nz[i0 + 12] - cs_nz[i0]).astype(float),
                 "mirror_amplitude_difference": (1 - 2 * beta) * np.log(p_end / p_start)}
        r["A4"] = {k: law_test(c) for k, c in cands.items()}
        res["pairs"][key] = r
        log("rang %d paire (%.1f, %.1f) : décalage/π %.4f ; indices absolus ≠ %.3f ; écarts de série %s (viol. %d, non nuls %.3f) ; lois %s"
            % (rank, beta, bm, sp, r["C"]["abs_index_fraction_differs"], r["C"]["series_shift_diff_values"], r["C"]["series_shift_diff_violations"],
               r["C"]["series_shift_diff_fraction_nonzero"], {k: v["law"] for k, v in r["A4"].items()}))
# (2) A0 : H = 1000, canal intégré, zéros authentiques
H = 1000.0; g = G[G <= H]; rho = 0.5 + 1j * g
def F(x): return -2.0 * np.real(np.exp(rho * math.log(x)) / (rho * (rho + 1)))   # −m(ρ)·x^ρ/(ρ(ρ+1)) + conjugué, m = 1
a0 = {"H": H, "zeros_le_H": int(len(g)), "N": {}}
for N in (5, 7, 11, 101, 1009):
    indiv = (N + 1) * F(N + 1) - N * F(N)                       # individualStepContribution ρ N (chaque Tour)
    collective = indiv.sum()
    direct = (N + 1) * F(N + 1).sum() - N * F(N).sum()          # truncatedStep_eq (somme puis pas)
    bg = background_psi1(N + 1) - background_psi1(N)
    a0["N"][str(N)] = {"sum_individual": float(collective), "direct": float(direct), "abs_err": float(abs(collective - direct)),
                       "single_tower_rank1_over_collective": float(indiv[0] / collective) if collective != 0 else None,
                       "max_single_over_collective": float(np.max(np.abs(indiv)) / abs(collective)) if collective != 0 else None,
                       "background_plus_collective": float(bg + collective), "log_N": float(math.log(N))}
    log("A0 N = %d : somme des contributions %.9f, directe %.9f (écart %.2e) ; une Tour / collectif max %.3f ; fond + collectif %.4f (log N = %.4f)"
        % (N, collective, direct, abs(collective - direct), a0["N"][str(N)]["max_single_over_collective"], bg + collective, math.log(N)))
res["A0"] = a0
# jumeau mpmath : paire (0,3 ; 0,7) à la hauteur du zéro 1, 10 événements
mp.mp.dps = 30; T = mp.mpf(repr(float(G[0]))); tw = {}
for b in (mp.mpf("0.3"), mp.mpf("0.7")):
    ph = mp.atan(T / b); tw[str(b)] = [int(mp.ceil((T * mp.log(int(q)) - ph) / mp.pi)) - 1 for q in Pi[:10]]
dm = [a - c for a, c in zip(tw["0.7"], tw["0.3"])]
npd = (cell_index(0.7, float(G[0]), P[:10]) - cell_index(0.3, float(G[0]), P[:10])).astype(int)
res["twin_mpmath"] = {"indices_0.3": tw["0.3"], "indices_0.7": tw["0.7"], "diff": dm, "numpy_diff": [int(x) for x in npd], "agree": bool(list(npd) == dm)}
log("jumeau mpmath (zéro 1, 10 événements) : écarts miroir %s ; accord numpy %s" % (dm, res["twin_mpmath"]["agree"]))
json.dump(res, open(os.path.join(OUT, "data", "e428b_results.json"), "w"), indent=1, ensure_ascii=False, default=str)
log("terminé")
