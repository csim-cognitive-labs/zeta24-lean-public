# -*- coding: utf-8 -*-
"""E445(a) — le prix radial au point de rencontre contre le budget. (1) Sur les sept Tours réelles (β = ½, T d'Odlyzko) :
contrôles P4 (amplitude à la cellule de rencontre encadrée) et P5 (bilan pondéré borné par la dernière cellule), 0
violation attendu. (2) Pour une paire témoin (β, 1−β) à la même fréquence, β ∈ {0,3 ; 0,4 ; 0,45} : prix offPrice =
cosh((β−½) log p) aux rencontres, prix du miroir p^{1−β}/‖ρ'‖ contre le budget d'UNE rencontre (log p, P6) et contre le
budget cumulé (θ(p) ≤ log 4 · p, T2) : mesure des deux directions. Jumeau : e445b_twin_mpmath.py."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e445a.log"))
G, sha = load_zeros(log)
RANKS = [1, 10, 100, 1000, 10000, 100000, 2000000]; N = 1000000; WITNESS = [0.3, 0.4, 0.45]
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
PR = P[P >= 3]; LOGP = np.log(PR.astype(np.float64))
def phase(T, b): return math.atan2(T, b)
def stage(T, x, b): return (T * np.log(x) - phase(T, b)) / math.pi
def contact(T, k, b): return np.exp((phase(T, b) + k * math.pi) / T)
res = {"zeros": int(len(G)), "sha256": sha, "N": N, "towers": {}}
for rank in RANKS:
    T = float(G[rank - 1]); out = {"T": T}
    # (1) Tours réelles : P4 et P5 à β = ½
    b = 0.5; nrm = math.hypot(b, T); q = math.exp(b * math.pi / T)
    s = stage(T, PR.astype(np.float64), b); m = np.floor(s).astype(np.int64)
    kmin = int(np.floor(stage(T, 2.0, b))) - 1; kmax = int(m[-1]) + 2
    K = np.arange(kmin, kmax + 1); C = contact(T, K.astype(np.float64), b)
    V = np.where(K % 2 == 0, 1.0, -1.0) * C ** b / nrm
    FL = np.minimum(np.floor(C).astype(np.int64), N)
    cellD = (PS[FL[1:]] - C[1:]) - (PS[FL[:-1]] - C[:-1])
    idx = m - kmin; absV = np.abs(V[idx])
    lo = PR ** b * math.exp(-b * math.pi / T) / nrm; hi = PR ** b / nrm
    viol = {"P4_lower": int(np.sum(absV <= lo * (1 - 1e-12))), "P4_upper": int(np.sum(absV > hi * (1 + 1e-12)))}
    nb5 = 0; worst5 = 0.0; n5 = 0
    for k0 in np.linspace(0, len(cellD) - 2, 30).astype(int):
        for mm in (0, 1, 3, 10, 50):
            if k0 + mm >= len(cellD): continue
            vs = float(np.sum(V[k0:k0 + mm + 1] * cellD[k0:k0 + mm + 1]))
            D = float(np.max(np.abs(cellD[k0:k0 + mm + 1])))
            bound = abs(V[k0 + mm]) * D * q / (q - 1)
            n5 += 1; ratio = abs(vs) / bound if bound > 0 else 0.0; worst5 = max(worst5, ratio); nb5 += ratio > 1 + 1e-12
    viol["P5_bound"] = int(nb5); out["violations"] = viol
    out["P5_checks"] = n5; out["P5_max_ratio_to_bound"] = worst5; out["P5_factor_q_over_q_minus_1"] = q / (q - 1)
    # (2) paire témoin à la même fréquence
    wit = {}
    for bw in WITNESS:
        gw = 1 - bw; nrm_m = math.hypot(gw, T)
        price = np.cosh((bw - 0.5) * LOGP)                       # offPrice β p
        mirror_amp = PR ** gw / nrm_m                             # amplitude du miroir à p (P4, à e^{γπ/T} près)
        per_meeting = LOGP                                        # budget d'une rencontre
        cumulative = TH[PR]                                       # budget cumulé θ(p)
        beats_one = mirror_amp > per_meeting
        first_beats = int(PR[np.argmax(beats_one)]) if beats_one.any() else None
        all_after = bool(np.all(beats_one[np.argmax(beats_one):])) if beats_one.any() else False
        beats_cum = mirror_amp > cumulative
        wit[str(bw)] = {"price_at_1e6": float(price[-1]), "price_at_1e3": float(price[np.searchsorted(PR, 1000)]),
                        "mirror_amp_at_1e6": float(mirror_amp[-1]), "log_p_at_1e6": float(per_meeting[-1]),
                        "first_prime_where_mirror_beats_log_p": first_beats, "beats_log_p_for_all_after": all_after,
                        "frac_meetings_mirror_beats_cumulative_theta": float(np.mean(beats_cum)),
                        "theta_over_mirror_amp_at_1e6": float(cumulative[-1] / mirror_amp[-1]),
                        "pair_identity_max_rel_dev": float(np.max(np.abs(PR ** bw + PR ** gw - 2 * np.sqrt(PR) * price) / (PR ** bw + PR ** gw)))}
    out["witness_pairs"] = wit
    res["towers"][str(rank)] = out
    log("rang %d T=%.4f : violations %s ; P5 ratio max %.3f (facteur q/(q−1) = %.1f)" % (rank, T, viol, worst5, q / (q - 1)))
    for bw, w in wit.items():
        log("  β=%s : prix(10⁶)=%.3g, miroir bat log p dès p=%s (et après : %s), bat θ(p) sur %.4f des rencontres, θ/miroir(10⁶)=%.3g, identité paire %.1e" % (
            bw, w["price_at_1e6"], w["first_prime_where_mirror_beats_log_p"], w["beats_log_p_for_all_after"], w["frac_meetings_mirror_beats_cumulative_theta"], w["theta_over_mirror_amp_at_1e6"], w["pair_identity_max_rel_dev"]))
tot = sum(sum(t["violations"].values()) for t in res["towers"].values()); res["total_violations"] = int(tot)
json.dump(res, open(os.path.join(OUT, "data", "e445a_results.json"), "w"), indent=1)
log("TOTAL violations = %d" % tot)
