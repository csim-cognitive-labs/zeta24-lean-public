# -*- coding: utf-8 -*-
"""E427(c) — niveau 2 : transport de l'équilibre grammatical vers les contacts authentiques des Tours.
Événements premiers de rangs 2..2001 ; Tours authentiques (zéros de rangs 1, 10, 100, 1 000, 10 000, 100 000, 1 000 000,
2 001 052, β = ½) et Tours de séparation (mêmes hauteurs, β = 0,3 et 0,7, synthétiques).
Mesures : bilan pondéré par les valeurs aux contacts contre la borne d'Abel compilée ; candidats de transport (décalage
d'indice de contact, variation de log-amplitude) contre l'orientation ; dérive d'amplitude relative sur segments de bilan
nul contre segments de bilan non nul ; jumeau mpmath 30 chiffres."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e427c.log"))
G, sha = load_zeros(log)
RANKS = [1, 10, 100, 1000, 10000, 100000, 1000000, 2001052]
# premiers de rangs 2..2002 (p_2 = 5) : événements r = 2..2001, point de rencontre de r = p_{r+1}
sieve = np.ones(20000, dtype=bool); sieve[:2] = False
for i in range(2, 142):
    if sieve[i]: sieve[i * i::i] = False
Pall = np.flatnonzero(sieve); P = Pall[2:2003].astype(np.float64)       # p_2 .. p_2002
s = (Pall[2:2003] % 6 == 1); src, dst = s[:-1], s[1:]
orient = src.astype(int) - dst.astype(int)                             # orientation de l'événement r (r = 2..2001)
gap = (Pall[3:2003] - Pall[2:2002]).astype(np.float64)
NE = len(orient)
res = {"zeros": int(len(G)), "sha256": sha, "events": int(NE), "p_first": int(Pall[2]), "p_last": int(Pall[2002]), "towers": {}}

def cell_index(beta, T, q):  return np.ceil((T * np.log(q) - math.atan2(T, beta)) / math.pi) - 1
def contact_value(beta, T, k):
    ph = math.atan2(T, beta); C = np.exp((ph + k * math.pi) / T)
    return np.where(k % 2 == 0, 1.0, -1.0) * C ** beta / math.hypot(beta, T)

def entropy(c):
    p = c[c > 0] / c.sum(); return float(-(p * np.log2(p)).sum())
def mutual_info(o, v, bins=20):
    """Information mutuelle (bits) entre l'orientation (3 valeurs) et un candidat continu discrétisé."""
    vb = np.digitize(v, np.quantile(v, np.linspace(0, 1, bins + 1)[1:-1]))
    joint = np.zeros((3, bins));
    for a, b in zip(o + 1, vb): joint[a, b] += 1
    return entropy(joint.sum(1)) + entropy(joint.sum(0)) - entropy(joint.ravel())

def transport_criterion(o, v, tol=1e-9):
    """Un transport exact exigerait v = f(o) : pour chaque orientation, étendue des valeurs du candidat."""
    return {str(k): {"count": int(np.sum(o == k)), "min": float(v[o == k].min()), "max": float(v[o == k].max()),
                     "range": float(np.ptp(v[o == k])), "constant_at_tol": bool(np.ptp(v[o == k]) <= tol)} for k in (-1, 0, 1)}

# segments : d'un croisement au croisement inverse suivant (bilan 0) et au maintien précédant ce dernier (bilan ±1)
ci = np.flatnonzero(orient != 0)
seg0 = [(a, b) for a, b in zip(ci[:-1], ci[1:])]                       # événements a..b, bilan 0
seg1 = [(a, b - 1) for a, b in zip(ci[:-1], ci[1:]) if b - 1 > a]      # événements a..b−1, bilan ±1
mi_orient_gap = mutual_info(orient, gap)
res["mutual_info_orientation_gap_bits"] = mi_orient_gap
res["mutual_info_orientation_gapmod6_bits"] = mutual_info(orient, gap % 6, bins=3)
for rank in RANKS:
    T = float(G[rank - 1])
    for beta, kind in ((0.5, "authentic"), (0.3, "synthetic"), (0.7, "synthetic")):
        key = "rank%d_beta%.1f" % (rank, beta); r = {"kind": kind, "T": T, "beta": beta}
        k_meet = cell_index(beta, T, P[1:])          # cellule du point de rencontre p_{r+1}, r = 2..2001
        k_start = cell_index(beta, T, P[:-1])        # cellule du départ p_r
        v = contact_value(beta, T, k_meet)           # meetingContactValue
        # (1) bilan pondéré contre la borne d'Abel compilée, fenêtres glissantes
        r["abel"] = {}
        for n in (12, 120):
            viol = 0; ratios = []
            for i in range(0, NE - n + 1):
                o = orient[i:i + n]; w = v[i:i + n]
                S = float(np.dot(o, w)); bound = (abs(w[0]) + abs(w[-1]) + np.abs(np.diff(w)).sum()) / 2
                if abs(S) > bound * (1 + 1e-9) + 1e-12: viol += 1
                ratios.append(abs(S) / bound if bound > 0 else 0.0)
            ratios = np.array(ratios)
            r["abel"][str(n)] = {"windows": int(len(ratios)), "violations": int(viol), "ratio_median": float(np.median(ratios)),
                                 "ratio_max": float(ratios.max())}
        # (2) candidats de transport
        dk = k_meet - k_start                        # décalage d'indice de contact à travers l'événement r
        dlog = beta * np.log(P[1:] / P[:-1])         # variation de log-amplitude x^β à travers l'événement r
        r["candidates"] = {"cell_shift": {"transport": transport_criterion(orient, dk.astype(float)), "mutual_info_bits": mutual_info(orient, dk.astype(float))},
                           "log_amplitude": {"transport": transport_criterion(orient, dlog), "mutual_info_bits": mutual_info(orient, dlog)},
                           "contact_value": {"transport": transport_criterion(orient, v), "mutual_info_bits": mutual_info(orient, v)}}
        # (3) dérive d'amplitude relative sur segments (bilan 0 contre bilan ±1) : (p_{b+1}/p_a)^(β−½)
        d0 = np.array([(P[b + 1] / P[a]) ** (beta - 0.5) for a, b in seg0]); d1 = np.array([(P[b + 1] / P[a]) ** (beta - 0.5) for a, b in seg1])
        r["drift"] = {"segments_balance0": int(len(d0)), "segments_balance_pm1": int(len(d1)),
                      "neutral_fraction_balance0": float(np.mean(np.abs(d0 - 1) < 1e-9)), "neutral_fraction_balance_pm1": float(np.mean(np.abs(d1 - 1) < 1e-9)),
                      "drift_median_balance0": float(np.median(d0)), "drift_median_balance_pm1": float(np.median(d1))}
        res["towers"][key] = r
        log("%s (T=%.3f, β=%.1f, %s) : Abel violations 12/120 = %d/%d (ratio médian %.3f/%.3f) ; IM(orient; Δk)=%.3f, IM(orient; Δlog)=%.3f, IM(orient; v)=%.3f bits [IM(orient; écart)=%.3f] ; transport exact : Δk %s, Δlog %s ; dérive neutre : bilan 0 %.3f, bilan ±1 %.3f"
            % (key, T, beta, kind, r["abel"]["12"]["violations"], r["abel"]["120"]["violations"], r["abel"]["12"]["ratio_median"], r["abel"]["120"]["ratio_median"],
               r["candidates"]["cell_shift"]["mutual_info_bits"], r["candidates"]["log_amplitude"]["mutual_info_bits"], r["candidates"]["contact_value"]["mutual_info_bits"], mi_orient_gap,
               all(t["constant_at_tol"] for t in r["candidates"]["cell_shift"]["transport"].values()),
               all(t["constant_at_tol"] for t in r["candidates"]["log_amplitude"]["transport"].values()),
               r["drift"]["neutral_fraction_balance0"], r["drift"]["neutral_fraction_balance_pm1"]))
# --- jumeau mpmath : valeurs aux contacts, Tour du zéro 1, dix événements ---
import mpmath as mp
mp.mp.dps = 30
T = float(G[0]); beta = 0.5; tw = []
for r_ in range(10):
    q = mp.mpf(int(P[r_ + 1])); Tm = mp.mpf(T); ph = mp.atan2(Tm, mp.mpf(beta))
    k = mp.ceil((Tm * mp.log(q) - ph) / mp.pi) - 1
    C = mp.exp((ph + k * mp.pi) / Tm); vm = (-1) ** int(k) * C ** beta / mp.sqrt(beta ** 2 + Tm ** 2)
    kn = cell_index(beta, T, P[r_ + 1]); vn = contact_value(beta, T, kn)
    tw.append({"p": int(P[r_ + 1]), "k_mp": int(k), "k_np": int(kn), "v_mp": float(vm), "v_np": float(vn), "abs_diff": abs(float(vm) - float(vn))})
res["twin_mpmath_rank1"] = tw; res["twin_max_abs_diff"] = max(t["abs_diff"] for t in tw); res["twin_cell_index_agree"] = all(t["k_mp"] == t["k_np"] for t in tw)
log("jumeau mpmath (zéro 1, 10 événements) : indices de cellule identiques %s, écart max des valeurs %.2e" % (res["twin_cell_index_agree"], res["twin_max_abs_diff"]))
json.dump(res, open(os.path.join(OUT, "data", "e427c_results.json"), "w"), indent=1, ensure_ascii=False)
log("terminé")
