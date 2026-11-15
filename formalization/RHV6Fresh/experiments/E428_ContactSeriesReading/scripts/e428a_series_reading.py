# -*- coding: utf-8 -*-
"""E428(a) — lecture certifiée des premiers d'une série depuis un ancrage et la progression des indices de contact
d'une Tour (compilé : cellIndex_difference_bounds, estimate_brackets, certified_rounding, certified_unique_integer,
true_threshold_also_certifies). Validation après coup contre les vrais premiers. Jumeau mpmath 30 chiffres."""
import os, sys, math, json, numpy as np, mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e428a.log"))
G, sha = load_zeros(log)
RANKS = [1, 10, 100, 1000, 10000, 100000, 1000000, 2001052]
ANCHORS = [5, 541, 7919]; SERIES = [12, 120, 1200]
sieve = np.ones(30000, dtype=bool); sieve[:2] = False
for i in range(2, 174):
    if sieve[i]: sieve[i * i::i] = False
P = np.flatnonzero(sieve).astype(np.int64)
def cell_index(beta, T, q): return np.ceil((T * np.log(q) - math.atan2(T, beta)) / math.pi) - 1
def classes(seq): return (seq[1:] - seq[:-1]) % 6
res = {"zeros": int(len(G)), "sha256": sha, "anchors": ANCHORS, "series": SERIES, "towers": {}}
for rank in RANKS:
    T = float(G[rank - 1]); h = math.pi / T; eh1 = math.expm1(h)
    ref_dk = {}
    for beta, kind in ((0.5, "authentic"), (0.3, "synthetic"), (0.7, "synthetic")):
        key = "rank%d_beta%.1f" % (rank, beta); r = {"kind": kind, "T": T, "beta": beta, "h": h, "readings": {}}
        for a in ANCHORS:
            ia = int(np.searchsorted(P, a)); assert P[ia] == a
            for m in SERIES:
                seg = P[ia:ia + m + 1].astype(np.float64); true = P[ia:ia + m + 1]
                k = cell_index(beta, T, seg); dk = (k - k[0]).astype(np.int64)
                qhat = a * np.exp(h * dk)                     # seriesEstimate : ne lit que (p_a, T, Δk)
                cert = qhat * eh1 < 0.5                       # seuil corrigé (lisible)
                old = true * eh1 < 0.5                        # ancien seuil (lit le q inconnu) : comparaison seulement
                read = np.rint(qhat).astype(np.int64)
                right = read == true
                brk = np.all((qhat * math.exp(-h) < true) & (true < qhat * math.exp(h)))   # estimate_brackets
                # mot lu : classes mod 6 des écarts lus, sur les paires certifiées consécutives
                both = cert[1:] & cert[:-1]
                word_mismatch = int(np.sum((classes(read) != classes(true)) & both))
                ref_dk.setdefault((a, m), {})[beta] = dk
                r["readings"]["a%d_m%d" % (a, m)] = {
                    "members": int(m + 1), "brackets_hold": bool(brk),
                    "certified": int(cert.sum()), "certified_wrong": int(np.sum(cert & ~right)),
                    "uncertified_right": int(np.sum(~cert & right)), "uncertified": int(np.sum(~cert)),
                    "old_threshold_pass": int(old.sum()), "old_pass_new_fail": int(np.sum(old & ~cert)),
                    "new_pass_old_fail": int(np.sum(cert & ~old)), "old_pass_wrong": int(np.sum(old & ~right)),
                    "word_pairs_certified": int(both.sum()), "word_mismatch_certified": word_mismatch,
                    "max_abs_error_certified": float(np.max(np.abs(qhat - true)[cert])) if cert.any() else None,
                    "first_uncertified_prime": int(true[np.argmin(cert)]) if (~cert).any() else None}
        res["towers"][key] = r
    # information radiale des indices : Δk à β = 0,3 / 0,7 contre β = ½, même fréquence
    for (a, m), d in ref_dk.items():
        for beta in (0.3, 0.7):
            diff = d[beta] - d[0.5]
            res["towers"]["rank%d_beta%.1f" % (rank, beta)]["readings"]["a%d_m%d" % (a, m)]["dk_vs_half"] = {
                "fraction_differs": float(np.mean(diff != 0)), "values": sorted(set(int(x) for x in np.unique(diff)))}
    tot = res["towers"]["rank%d_beta0.5" % rank]["readings"]
    log("rang %d (T = %.6g, h = %.3g) : certifiés %s ; certifiés faux %d ; ancien seuil mais pas nouveau %d"
        % (rank, T, h, {k: v["certified"] for k, v in tot.items()}, sum(v["certified_wrong"] for v in tot.values()),
           sum(v["old_pass_new_fail"] for v in tot.values())))
# synthèse
allr = [v for t in res["towers"].values() for v in t["readings"].values()]
res["summary"] = {"total_readings": int(sum(v["members"] for v in allr)), "certified": int(sum(v["certified"] for v in allr)),
                  "certified_wrong": int(sum(v["certified_wrong"] for v in allr)), "brackets_all_hold": bool(all(v["brackets_hold"] for v in allr)),
                  "word_mismatch_certified": int(sum(v["word_mismatch_certified"] for v in allr)),
                  "uncertified_right": int(sum(v["uncertified_right"] for v in allr)),
                  "old_pass_new_fail": int(sum(v["old_pass_new_fail"] for v in allr)), "new_pass_old_fail": int(sum(v["new_pass_old_fail"] for v in allr)),
                  "old_pass_wrong": int(sum(v["old_pass_wrong"] for v in allr))}
log("synthèse : %s" % res["summary"])
# jumeau mpmath 30 chiffres : rangs 1 et 2001052, ancrage 5, j ≤ 12, β ∈ {0,5 ; 0,3}
mp.mp.dps = 30; tw = {}
for rank in (1, 2001052):
    T = mp.mpf(repr(float(G[rank - 1])))
    for beta in (0.5, 0.3):
        b = mp.mpf(beta); ph = mp.atan(T / b); h = mp.pi / T
        seg = P[np.searchsorted(P, 5):np.searchsorted(P, 5) + 13]
        k = [int(mp.ceil((T * mp.log(int(q)) - ph) / mp.pi)) - 1 for q in seg]
        dk = [x - k[0] for x in k]; qh = [5 * mp.exp(h * d) for d in dk]
        cert = [bool(q * (mp.exp(h) - 1) < mp.mpf(1) / 2) for q in qh]; read = [int(mp.nint(q)) for q in qh]
        npk = cell_index(beta, float(G[rank - 1]), seg.astype(np.float64)); npdk = (npk - npk[0]).astype(int)
        tw["rank%d_beta%.1f" % (rank, beta)] = {"dk_equal": bool(list(npdk) == dk), "cert": cert, "read": read, "true": [int(x) for x in seg],
                                                "read_eq_true_where_cert": bool(all(r == t for r, t, c in zip(read, seg, cert) if c)),
                                                "max_rel_diff_qhat": float(max(abs(float(q) - 5 * math.exp(math.pi / float(G[rank - 1]) * d)) / float(q) for q, d in zip(qh, dk)))}
res["twin_mpmath"] = tw; res["twin_agreement"] = bool(all(v["dk_equal"] and v["read_eq_true_where_cert"] for v in tw.values()))
log("jumeau mpmath : %s ; accord %s" % ({k: (v["dk_equal"], sum(v["cert"]), v["max_rel_diff_qhat"]) for k, v in tw.items()}, res["twin_agreement"]))
json.dump(res, open(os.path.join(OUT, "data", "e428a_results.json"), "w"), indent=1, ensure_ascii=False, default=str)
log("terminé")
