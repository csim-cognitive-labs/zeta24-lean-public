# -*- coding: utf-8 -*-
"""E427(a) — grammaire de référence exacte des écarts premiers (entiers, aucune donnée spectrale).
États (p mod 6 = 1 ou 5), quatre transitions, conformité classe/états, bilan orienté cumulé (confinement),
retour après croisements inverses, N11 − N55 (mesure), dénombrement des 8 192 mots de douze transitions,
mots réalisés par les premiers. Jumeau : second crible indépendant en entiers Python purs jusqu'à 10⁶."""
import os, sys, json, time, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e427a.log"))
LIM = 10 ** 8
res = {"limit": LIM}

def grammar_arrays(P):
    """P : premiers > 3 croissants (entiers). Retourne états, orientation, classe, conformité."""
    s = (P % 6 == 1)                      # True = état 1, False = état 5
    src, dst = s[:-1], s[1:]
    cls = (P[1:] - P[:-1]) % 6
    expected = np.where(src == dst, 0, np.where(src, 4, 2))
    orient = src.astype(np.int64) - dst.astype(np.int64)   # +1 : 1→5 (t15), −1 : 5→1 (t51), 0 : maintien
    return s, src, dst, cls, expected, orient

t0 = time.time()
sieve = np.ones(LIM + 1, dtype=bool); sieve[:2] = False
for i in range(2, int(LIM ** 0.5) + 1):
    if sieve[i]: sieve[i * i::i] = False
P = np.flatnonzero(sieve).astype(np.int64); del sieve
P = P[P > 3]
log("crible : %d premiers > 3 jusqu'à %d (%.1f s)" % (len(P), LIM, time.time() - t0))
res["primes_gt3"] = int(len(P))
s, src, dst, cls, expected, orient = grammar_arrays(P)
# (1) deux états, conformité des quatre transitions
res["all_in_two_states"] = bool(np.all((P % 6 == 1) | (P % 6 == 5)))
viol = int(np.sum(cls != expected))
res["class_state_violations"] = viol
counts = {"t11": int(np.sum(src & dst)), "t15": int(np.sum(src & ~dst)), "t51": int(np.sum(~src & dst)), "t55": int(np.sum(~src & ~dst))}
res["transition_counts"] = counts
log("conformité classe/états : %d violation(s) ; transitions %s" % (viol, counts))
# (2) bilan orienté cumulé : télescopage et confinement
B = np.cumsum(orient)
ind = s.astype(np.int64)
tele = B - (ind[0] - ind[1:])
res["balance_telescoping_violations"] = int(np.sum(tele != 0))
res["balance_min"], res["balance_max"] = int(B.min()), int(B.max())
res["balance_hist"] = {str(v): int(np.sum(B == v)) for v in (-1, 0, 1)}
log("bilan cumulé : télescopage %d violation(s) ; min %d max %d ; histogramme %s"
    % (res["balance_telescoping_violations"], B.min(), B.max(), res["balance_hist"]))
# (3) retour après croisements inverses
i15 = np.flatnonzero(orient == 1); i51 = np.flatnonzero(orient == -1)
# alternance : les croisements, dans l'ordre, alternent +1/−1
cross_idx = np.flatnonzero(orient != 0); cross_val = orient[cross_idx]
res["crossings"] = int(len(cross_idx))
res["alternation_violations"] = int(np.sum(cross_val[1:] == cross_val[:-1]))
# bilan entre un croisement et le croisement inverse suivant : B[b] − B[a−1]
Bprev = np.concatenate([[0], B])
seg = Bprev[cross_idx[1:] + 1] - Bprev[cross_idx[:-1]]
res["return_violations"] = int(np.sum(seg != 0))
dw = cross_idx[1:] - cross_idx[:-1] - 1          # nombre de maintiens entre deux croisements inverses
res["dwell_between_inverse_crossings"] = {"min": int(dw.min()), "median": float(np.median(dw)), "q90": float(np.quantile(dw, .9)),
                                          "q99": float(np.quantile(dw, .99)), "max": int(dw.max()), "mean": float(dw.mean())}
log("croisements %d, alternance %d violation(s), retour %d violation(s) ; séjours entre croisements inverses : médiane %.0f, q99 %.0f, max %d"
    % (len(cross_idx), res["alternation_violations"], res["return_violations"], np.median(dw), np.quantile(dw, .99), dw.max()))
# (4) séjours : N11 − N55 cumulé (mesure ; aucune loi)
D = np.cumsum((src & dst).astype(np.int64) - (~src & ~dst).astype(np.int64))
res["dwell_balance_N11_minus_N55"] = {"final": int(D[-1]), "min": int(D.min()), "max": int(D.max()), "argmin_rank": int(np.argmin(D)), "argmax_rank": int(np.argmax(D))}
occ = np.cumsum(ind[:-1]) - np.cumsum(1 - ind[:-1])  # N1• − N5•
res["occupancy_minus_dwell_abs_max"] = int(np.max(np.abs((occ - D) - (np.cumsum(orient)))))  # identité D = occ − (N15 − N51) ⇒ 0 attendu
log("N11 − N55 : final %d, min %d, max %d (mesure) ; identité séjours/occupation : écart max %d"
    % (D[-1], D.min(), D.max(), res["occupancy_minus_dwell_abs_max"]))
# (5) dénombrement : mots valides de douze transitions parmi 4^12 (codes 0=t11 1=t15 2=t51 3=t55)
t0 = time.time()
idx = np.arange(4 ** 12, dtype=np.int64); valid = np.ones(len(idx), dtype=bool); prev = None
for l in range(12):
    d = ((idx >> (2 * l)) & 3).astype(np.int8)
    src_l = d <= 1; dst_l = (d == 0) | (d == 2)
    if prev is not None: valid &= (prev == src_l)
    prev = dst_l
res["valid_words_12_transitions"] = int(valid.sum()); del idx, valid
log("mots valides de 12 transitions : %d (attendu 8192 = 2^13 ; %.1f s)" % (res["valid_words_12_transitions"], time.time() - t0))
code = np.where(src & dst, 0, np.where(src & ~dst, 1, np.where(~src & dst, 2, 3))).astype(np.int64)
N = len(code) - 11; W = np.zeros(N, dtype=np.int64)
for l in range(12): W |= code[l:l + N] << (2 * l)
uniq = np.unique(W)
res["realized_words_12_transitions_primes_le_limit"] = int(len(uniq))
res["realized_fraction_of_valid"] = float(len(uniq) / 8192)
log("mots de 12 transitions réalisés par les premiers ≤ %d : %d / 8192 (mesure)" % (LIM, len(uniq)))
# ---- jumeau déterministe : crible indépendant en entiers purs jusqu'à 10^6 ----
TW = 10 ** 6
flags = bytearray([1]) * (TW + 1); flags[0] = flags[1] = 0
for i in range(2, int(TW ** 0.5) + 1):
    if flags[i]:
        for j in range(i * i, TW + 1, i): flags[j] = 0
Pt = [i for i in range(5, TW + 1) if flags[i]]
tw = {"primes_gt3": len(Pt), "class_state_violations": 0, "balance_min": 0, "balance_max": 0, "return_violations": 0, "crossings": 0}
b = 0; last_cross = None; bal_at_last = 0; prev_sign = 0
for a, c in zip(Pt, Pt[1:]):
    sa, sc = a % 6 == 1, c % 6 == 1
    cl = (c - a) % 6
    exp = 0 if sa == sc else (4 if sa else 2)
    if cl != exp: tw["class_state_violations"] += 1
    o = int(sa) - int(sc); b += o
    tw["balance_min"] = min(tw["balance_min"], b); tw["balance_max"] = max(tw["balance_max"], b)
    if o != 0:
        tw["crossings"] += 1
        if last_cross is not None and b - bal_at_last != 0: tw["return_violations"] += 1
        last_cross = a; bal_at_last = b - o  # bilan juste avant ce croisement
# comparaison avec numpy restreint à 10^6
m = P <= TW; Pm = P[m]; _, src_m, dst_m, cls_m, exp_m, or_m = grammar_arrays(Pm); Bm = np.cumsum(or_m)
ref = {"primes_gt3": int(len(Pm)), "class_state_violations": int(np.sum(cls_m != exp_m)), "balance_min": int(Bm.min()),
       "balance_max": int(Bm.max()), "crossings": int(np.sum(or_m != 0))}
ci = np.flatnonzero(or_m != 0); Bp = np.concatenate([[0], Bm]); ref["return_violations"] = int(np.sum((Bp[ci[1:] + 1] - Bp[ci[:-1]]) != 0))
res["twin_pure_python_1e6"] = tw; res["numpy_restricted_1e6"] = ref
res["twin_agreement"] = all(tw[k] == ref[k] for k in tw)
log("jumeau (entiers purs ≤ 10^6) : %s ; numpy ≤ 10^6 : %s ; accord %s" % (tw, ref, res["twin_agreement"]))
json.dump(res, open(os.path.join(OUT, "data", "e427a_results.json"), "w"), indent=1, ensure_ascii=False)
log("terminé")
