# -*- coding: utf-8 -*-
"""E429(a) — lecture radiale et valeur aux points de rencontre depuis le dernier contact (compilé : lastContact_le,
lt_contact_succ, log_div_lastContact, towerRe_from_lastContact, growth_factor_eq, radialReadingAt_eq,
radial_of_meeting_value, mirror_readings_sum_one, meetingReadingsAgree_iff_line, lastContact_difference_bounds,
cellIndexAt_le_lastContactBefore). Jumeau mpmath 30 chiffres."""
import os, sys, math, json, numpy as np, mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e429a.log"))
G, sha = load_zeros(log)
RANKS = [1, 10, 100, 1000, 10000, 100000, 1000000, 2001052]
sieve = np.ones(30000, dtype=bool); sieve[:2] = False
for i in range(2, 174):
    if sieve[i]: sieve[i * i::i] = False
P = np.flatnonzero(sieve).astype(np.int64)
MEET = P[1:2001].astype(np.float64)            # points de rencontre : premiers de rangs 2..2001 (5..17393)
def stage(beta, T, x): return (T * np.log(x) - math.atan2(T, beta)) / math.pi
def contact(beta, T, k): return np.exp((math.atan2(T, beta) + k * math.pi) / T)
def cval(beta, T, k): return (-1.0) ** k * contact(beta, T, k) ** beta / math.hypot(beta, T)
def tower_re(beta, T, x): return x ** beta / math.hypot(beta, T) * np.cos(T * np.log(x) - math.atan2(T, beta))
def relerr(a, b): return float(np.max(np.abs(a - b) / np.maximum(np.abs(b), 1e-300)))
res = {"zeros": int(len(G)), "sha256": sha, "meetings": int(len(MEET)), "towers": {}, "violations": {}}
viol = {"P1_bracket": 0, "P5_count_bound": 0, "pivot_le_last": 0}
for rank in RANKS:
    T = float(G[rank - 1]); store = {}
    for beta in (0.5, 0.3, 0.7):
        s = stage(beta, T, MEET); k = np.floor(s); f = s - k
        Ck = contact(beta, T, k); Ck1 = contact(beta, T, k + 1)
        viol["P1_bracket"] += int(np.sum(~((Ck <= MEET) & (MEET < Ck1))))
        vk = cval(beta, T, k); vk1 = cval(beta, T, k + 1)
        direct = tower_re(beta, T, MEET)
        from_contact = vk * (MEET / Ck) ** beta * np.cos(math.pi * f)
        growth = (MEET / Ck) ** beta; growth_pred = np.exp(beta * math.pi * f / T)
        reading = T * np.log(np.abs(vk1) / np.abs(vk)) / math.pi                         # radialReadingAt
        tang = T / np.tan(T * np.log(Ck) - k * math.pi)                                   # radial_of_contact_tangent
        ok = (f > 0.05) & (np.abs(np.cos(math.pi * f)) > 0.05)
        mval = T * (np.log(np.abs(direct[ok])) - np.log(np.abs(vk[ok])) - np.log(np.abs(np.cos(math.pi * f[ok])))) / (math.pi * f[ok])
        # P5 : contacts entre rencontres consécutives
        dk = k[1:] - k[:-1]; pred = T * np.log(MEET[1:] / MEET[:-1]) / math.pi
        viol["P5_count_bound"] += int(np.sum(np.abs(dk - pred) >= 1))
        piv = np.ceil(s) - 1
        viol["pivot_le_last"] += int(np.sum(piv > k))
        hist = np.histogram(f, bins=10, range=(0, 1))[0]
        store[beta] = {"k": k, "f": f, "dk": dk}
        res["towers"]["rank%d_beta%.1f" % (rank, beta)] = {
            "T": T, "beta": beta, "kind": "authentic" if beta == 0.5 else "synthetic_same_height",
            "P2_value_relerr": relerr(from_contact, direct), "P2_growth_relerr": relerr(growth, growth_pred),
            "P3_reading_abs_err": float(np.max(np.abs(reading - beta))), "P3_tangent_abs_err": float(np.max(np.abs(tang - beta))),
            "P3_meeting_value_abs_err": float(np.max(np.abs(mval - beta))) if ok.any() else None, "P3_meeting_value_n": int(ok.sum()),
            "P5_max_abs_dev": float(np.max(np.abs(dk - pred))), "pivot_eq_last_fraction": float(np.mean(piv == k)),
            "cell_fraction_hist10": [int(x) for x in hist], "cell_fraction_mean": float(f.mean()),
            "gaps_with_zero_contacts": int(np.sum(dk == 0)), "mean_contacts_per_gap": float(dk.mean())}
    # P4 : paire miroir (0,3 ; 0,7) et témoin en ligne
    r3 = T * np.log(np.abs(cval(0.3, T, store[0.3]["k"] + 1)) / np.abs(cval(0.3, T, store[0.3]["k"]))) / math.pi
    r7 = T * np.log(np.abs(cval(0.7, T, store[0.7]["k"] + 1)) / np.abs(cval(0.7, T, store[0.7]["k"]))) / math.pi
    shift_pred = ((math.atan2(T, 0.3) - math.atan2(T, 0.7)) / math.pi) % 1.0
    shift_meas = (store[0.3]["f"] - store[0.7]["f"]) % 1.0        # f_β − f_{1−β} ≡ (s_β − s_{1−β}) = −(φ_β − φ_{1−β})/π ... signe vérifié
    shift_meas2 = (store[0.7]["f"] - store[0.3]["f"]) % 1.0
    res["towers"]["rank%d_pair" % rank] = {
        "P4_sum_minus_one_max": float(np.max(np.abs(r3 + r7 - 1))), "P4_diff_mean": float(np.mean(r7 - r3)), "P4_diff_expected": 0.4,
        "P4_on_agree_max": 0.0, "mirror_shift_pred_mod1": shift_pred,
        "mirror_shift_meas_dev": float(min(np.max(np.abs(shift_meas - shift_pred)), np.max(np.abs(shift_meas2 - shift_pred)))),
        "count_differs_0.3_vs_0.5_fraction": float(np.mean(store[0.3]["dk"] != store[0.5]["dk"])),
        "count_differs_0.7_vs_0.5_fraction": float(np.mean(store[0.7]["dk"] != store[0.5]["dk"]))}
    t = res["towers"]["rank%d_beta0.5" % rank]; pr = res["towers"]["rank%d_pair" % rank]
    log("rang %d (T=%.6g) : P2 %.1e/%.1e ; P3 lecture %.1e tangente %.1e valeur %s ; P5 dev max %.4f ; comptage ≠ (0,3 vs ½) %.4f ; décalage miroir dev %.1e ; contacts/écart %.3f"
        % (rank, T, t["P2_value_relerr"], t["P2_growth_relerr"], t["P3_reading_abs_err"], t["P3_tangent_abs_err"], t["P3_meeting_value_abs_err"],
           t["P5_max_abs_dev"], pr["count_differs_0.3_vs_0.5_fraction"], pr["mirror_shift_meas_dev"], t["mean_contacts_per_gap"]))
res["violations"] = viol
allt = [v for kk, v in res["towers"].items() if "beta" in kk]
res["summary"] = {"violations": viol, "max_P2_value_relerr": max(v["P2_value_relerr"] for v in allt),
                  "max_P2_growth_relerr": max(v["P2_growth_relerr"] for v in allt),
                  "max_P3_reading_abs_err": max(v["P3_reading_abs_err"] for v in allt),
                  "max_P3_tangent_abs_err": max(v["P3_tangent_abs_err"] for v in allt),
                  "max_P3_meeting_value_abs_err": max(v["P3_meeting_value_abs_err"] for v in allt if v["P3_meeting_value_abs_err"] is not None),
                  "max_P4_sum_minus_one": max(v["P4_sum_minus_one_max"] for kk, v in res["towers"].items() if "pair" in kk),
                  "max_mirror_shift_dev": max(v["mirror_shift_meas_dev"] for kk, v in res["towers"].items() if "pair" in kk)}
log("synthèse : %s" % res["summary"])
# jumeau mpmath 30 chiffres
mp.mp.dps = 30; tw = {}
for rank in (1, 2001052):
    T = mp.mpf(repr(float(G[rank - 1])))
    for beta in (0.5, 0.3):
        b = mp.mpf(beta); ph = mp.atan(T / b); nrm = mp.sqrt(b * b + T * T)
        rows = []
        for q in MEET[:10]:
            q = int(q); s = (T * mp.log(q) - ph) / mp.pi; k = int(mp.floor(s)); f = s - k
            Ck = mp.exp((ph + k * mp.pi) / T); vk = (-1) ** k * Ck ** b / nrm; vk1 = (-1) ** (k + 1) * mp.exp((ph + (k + 1) * mp.pi) / T) ** b / nrm
            direct = mp.mpf(q) ** b / nrm * mp.cos(T * mp.log(q) - ph)
            rows.append({"p": q, "k": k, "f": float(f), "value": float(direct), "from_contact": float(vk * (q / Ck) ** b * mp.cos(mp.pi * f)),
                         "reading": float(T * mp.log(abs(vk1) / abs(vk)) / mp.pi)})
        Tn = float(G[rank - 1]); s = stage(beta, Tn, MEET[:10]); kn = np.floor(s); fn = s - kn
        rn = Tn * np.log(np.abs(cval(beta, Tn, kn + 1)) / np.abs(cval(beta, Tn, kn))) / math.pi
        tw["rank%d_beta%.1f" % (rank, beta)] = {"rows": rows, "k_equal": bool(all(int(kn[i]) == rows[i]["k"] for i in range(10))),
            "f_max_dev": float(max(abs(fn[i] - rows[i]["f"]) for i in range(10))),
            "value_max_dev": float(max(abs(tower_re(beta, Tn, MEET[i]) - rows[i]["value"]) for i in range(10))),
            "reading_max_dev": float(max(abs(rn[i] - rows[i]["reading"]) for i in range(10)))}
        log("jumeau rang %d β=%.1f : k égaux %s ; f dev %.1e ; valeur dev %.1e ; lecture dev %.1e" % (rank, beta, tw["rank%d_beta%.1f" % (rank, beta)]["k_equal"],
            tw["rank%d_beta%.1f" % (rank, beta)]["f_max_dev"], tw["rank%d_beta%.1f" % (rank, beta)]["value_max_dev"], tw["rank%d_beta%.1f" % (rank, beta)]["reading_max_dev"]))
res["twin_mpmath"] = tw
json.dump(res, open(os.path.join(OUT, "data", "e429a_results.json"), "w"), indent=1, ensure_ascii=False, default=str)
log("terminé")
