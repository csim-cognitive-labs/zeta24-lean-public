# -*- coding: utf-8 -*-
"""E429(b) — résidu de cassure sur une série de rencontres (canal lissé exact), lecture radiale aux rencontres sur
le canal lissé (meetingDeposit_norm), insertion de paires hors ligne à hauteurs synthétiques, coût d'absorption par la
famille authentique (obligation Deux, version locale, ill-posé déclaré), paiement mutuel de deux paires (obligation
Trois). Identités : breakResidual_erase, breakResidual_erase_pair. Jumeau mpmath 30 chiffres."""
import os, sys, math, json, numpy as np, mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros, background_psi1, sieve_lambda
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e429b.log"))
G, sha = load_zeros(log)
H = 1000.0; g = G[G <= H]; RHO = 0.5 + 1j * g
lam, isp = sieve_lambda(20000)
P = np.flatnonzero(isp).astype(np.int64); MEET = P[1:2001].astype(np.float64)       # 5..17393
S0 = np.cumsum(lam); S1 = np.cumsum(np.arange(len(lam)) * lam)
def psi1_exact(x):                      # Σ_{n≤x} Λ(n)(x − n), x entier
    xi = x.astype(np.int64); return x * S0[xi] - S1[xi]
def contrib(rho, x):                    # −2Re[x^{ρ+1}/(ρ(ρ+1))], matrice (len(rho), len(x))
    lx = np.log(x)[None, :]; r = rho[:, None]
    return -2.0 * np.real(np.exp((r + 1) * lx) / (r * (r + 1)))
def cmod(rho, x):                        # |x^{ρ+1}/(ρ(ρ+1))|
    lx = np.log(x)[None, :]; r = rho[:, None]
    return np.abs(np.exp((r + 1) * lx) / (r * (r + 1)))
TS, TS2 = 17.5, 23.0
assert np.min(np.abs(G[:10] - TS)) > 1.0 and np.min(np.abs(G[:10] - TS2)) > 1.0, "hauteur synthétique trop proche d'un zéro réel"
res = {"zeros_le_H": int(len(g)), "H": H, "sha256": sha, "meetings": int(len(MEET)), "T_synth": [TS, TS2]}
# 1. résidu de troncature par écart, identité breakResidual_erase
C = contrib(RHO, MEET)                                # (N_H, 2001)
bg = np.array([background_psi1(x) for x in MEET])
psi_hat = bg + C.sum(axis=0); psi_ex = psi1_exact(MEET)
break_ex = np.diff(psi_ex); break_hat = np.diff(psi_hat); eps = break_ex - break_hat
resid_pt = psi_ex - psi_hat                            # breakResidual (famille F_H, cible ψ₁ exact) aux rencontres
resid_wo1 = psi_ex - (bg + C[1:].sum(axis=0))
res["1_truncation"] = {"gap_residual_abs_mean": float(np.mean(np.abs(eps))), "gap_residual_abs_max": float(np.max(np.abs(eps))),
                       "gap_residual_rel_mean": float(np.mean(np.abs(eps) / np.maximum(np.abs(break_ex), 1e-300))),
                       "break_exact_abs_mean": float(np.mean(np.abs(break_ex))),
                       "breakResidual_erase_identity_err": float(np.max(np.abs(resid_wo1 - (resid_pt + C[0]))))}
log("1. résidu de troncature par écart : moyen %.4g, max %.4g (cassure moyenne %.4g) ; identité erase %.1e"
    % (res["1_truncation"]["gap_residual_abs_mean"], res["1_truncation"]["gap_residual_abs_max"], res["1_truncation"]["break_exact_abs_mean"],
       res["1_truncation"]["breakResidual_erase_identity_err"]))
# 2. lecture radiale aux rencontres sur le canal lissé (meetingDeposit_norm)
M = cmod(RHO, MEET); ratio = M[:, 1:] / M[:, :-1]; lr = np.log(MEET[1:] / MEET[:-1])[None, :]
beta_read = np.log(ratio) / lr - 1.0
res["2_radial_reading_smoothed"] = {"towers": int(len(g)), "gaps": int(len(MEET) - 1), "max_abs_err_vs_half": float(np.max(np.abs(beta_read - 0.5)))}
log("2. lecture radiale aux rencontres (canal lissé, %d Tours × %d écarts) : erreur max %.1e" % (len(g), len(MEET) - 1, res["2_radial_reading_smoothed"]["max_abs_err_vs_half"]))
# 3. insertion des paires
pairs = {"off_17.5": np.array([0.3 + 1j * TS, 0.7 + 1j * TS]), "off_23.0": np.array([0.3 + 1j * TS2, 0.7 + 1j * TS2]),
         "on_control_17.5": np.array([0.5 + 1j * TS, 0.5 + 1j * TS]), "on_control_23.0": np.array([0.5 + 1j * TS2, 0.5 + 1j * TS2])}
D = np.diff(C, axis=1)                                 # dépôts par écart de F_H (N_H, 2000)
absD_sum = np.abs(D).sum(axis=0)
PV = {}; PD = {}
res["3_pairs"] = {}
for name, rho in pairs.items():
    cp = contrib(rho, MEET); PV[name] = cp.sum(axis=0); d = np.diff(PV[name]); PD[name] = d
    # identité breakResidual_erase_pair : résidu sans la paire = résidu avec + somme des deux valeurs (famille F_H ∪ paire)
    with_pair = psi_ex - (bg + C.sum(axis=0) + PV[name]); ident = float(np.max(np.abs(resid_pt - (with_pair + PV[name]))))
    res["3_pairs"][name] = {"share_vs_exact_break_mean": float(np.mean(np.abs(d) / np.maximum(np.abs(break_ex), 1e-300))),
                            "share_vs_family_absdeposits_mean": float(np.mean(np.abs(d) / absD_sum)),
                            "fraction_gaps_pair_exceeds_break": float(np.mean(np.abs(d) > np.abs(break_ex))),
                            "abs_deposit_first12_mean": float(np.mean(np.abs(d[:12]))), "abs_deposit_last12_mean": float(np.mean(np.abs(d[-12:]))),
                            "erase_pair_identity_err": ident}
    log("3. %s : part/cassure %.3f ; part/Σ|dépôts F_H| %.4f ; dépasse la cassure sur %.3f des écarts ; |dépôt| 12 premiers %.3g, 12 derniers %.3g ; identité %.1e"
        % (name, res["3_pairs"][name]["share_vs_exact_break_mean"], res["3_pairs"][name]["share_vs_family_absdeposits_mean"],
           res["3_pairs"][name]["fraction_gaps_pair_exceeds_break"], res["3_pairs"][name]["abs_deposit_first12_mean"], res["3_pairs"][name]["abs_deposit_last12_mean"], ident))
# 4. coût d'absorption par F_H (pondérations réelles libres), solution de norme minimale
res["4_absorption"] = {}
for name in pairs:
    res["4_absorption"][name] = {}
    for m in (12, 120, 600, 1200, 2000):
        A = D[:, :m].T; d = PD[name][:m]
        a, _, rk, sv = np.linalg.lstsq(A, d, rcond=None)
        r = A @ a - d
        res["4_absorption"][name][str(m)] = {"a_norm2": float(np.linalg.norm(a)), "a_max_abs": float(np.max(np.abs(a))), "rank": int(rk),
                                            "residual_rel": float(np.linalg.norm(r) / np.linalg.norm(d)), "d_norm2": float(np.linalg.norm(d))}
    log("4. %s : %s" % (name, {m: (round(v["a_norm2"], 4), round(v["residual_rel"], 4), v["rank"]) for m, v in res["4_absorption"][name].items()}))
def ratio_growth(off, on):
    return {m: res["4_absorption"][off][m]["a_norm2"] / res["4_absorption"][on][m]["a_norm2"] for m in ("12", "120", "600")}
res["4_absorption"]["criterion_Deux"] = {}
for off, on in (("off_17.5", "on_control_17.5"), ("off_23.0", "on_control_23.0")):
    rg = ratio_growth(off, on); grows = rg["600"] > rg["12"]
    res["4_absorption"]["criterion_Deux"][off] = {"ratio_norm_off_over_on": rg, "grows_12_to_600": bool(grows)}
    log("4. critère Deux (%s / %s) : rapport ‖a‖ OFF/témoin m=12 %.4f, 120 %.4f, 600 %.4f → croît : %s" % (off, on, rg["12"], rg["120"], rg["600"], grows))
# 5. obligation Trois : deux paires hors ligne
A_ = PV["off_17.5"]; B_ = PV["off_23.0"]
c = np.abs(A_ + B_) / (np.abs(A_) + np.abs(B_))
low = c < 0.1; runs = []; cur = 0
for v in low:
    cur = cur + 1 if v else 0; runs.append(cur)
s = float(np.dot(A_, B_) / np.dot(B_, B_)); mutual_res = float(np.linalg.norm(A_ - s * B_) / np.linalg.norm(A_))
# réseaux d'annulation prédits (membres dominants β = 0,7, canal lissé : phase φ' = arctan(T/β) + arctan(T/(β+1)))
def ph_s(beta, T): return math.atan2(T, beta) + math.atan2(T, beta + 1)
p1, p2 = ph_s(0.7, TS), ph_s(0.7, TS2); u = np.log(MEET)
def net_dist(u, T1, T2, f1, f2):
    slow = ((T1 - T2) * u - (f1 - f2) - math.pi) / (2 * math.pi); fast = ((T1 + T2) * u - (f1 + f2) - math.pi) / (2 * math.pi)
    ds = np.abs(slow - np.round(slow)) * 2 * math.pi / abs(T1 - T2); df = np.abs(fast - np.round(fast)) * 2 * math.pi / (T1 + T2)
    return np.minimum(ds, df) / (math.pi / max(T1, T2))     # en fraction de cellule de la Tour la plus haute
dist = net_dist(u, TS, TS2, p1, p2)
res["5_mutual_payment"] = {"fraction_c_lt_0.1": float(np.mean(low)), "longest_run_c_lt_0.1": int(max(runs)), "c_mean": float(c.mean()),
                           "single_scalar_absorption_residual_rel": mutual_res, "scalar": s,
                           "net_dist_mean_all": float(dist.mean()), "net_dist_mean_cancelled": float(dist[low].mean()) if low.any() else None,
                           "net_dist_median_cancelled": float(np.median(dist[low])) if low.any() else None}
log("5. Trois : c<0,1 sur %.3f des rencontres, plus longue suite %d, c moyen %.3f ; absorption A par B (un scalaire) résidu relatif %.3f ; distance au réseau : toutes %.3f, annulées %s"
    % (res["5_mutual_payment"]["fraction_c_lt_0.1"], res["5_mutual_payment"]["longest_run_c_lt_0.1"], c.mean(), mutual_res,
       res["5_mutual_payment"]["net_dist_mean_all"], res["5_mutual_payment"]["net_dist_mean_cancelled"]))
# jumeau mpmath 30 chiffres : 10 premiers écarts
mp.mp.dps = 30
def contrib_mp(rho, x): return -2 * mp.re(mp.power(x, rho + 1) / (rho * (rho + 1)))
tw = {"pair_deposit_max_reldev": {}, "psi1_exact_max_dev": 0.0}
for name, rho in pairs.items():
    vals = [sum(contrib_mp(mp.mpc(r.real, r.imag), int(x)) for r in rho) for x in MEET[:11]]
    dm = [float(vals[i + 1] - vals[i]) for i in range(10)]
    tw["pair_deposit_max_reldev"][name] = float(max(abs(dm[i] - PD[name][i]) / max(abs(dm[i]), 1e-300) for i in range(10)))
lam_mp = {int(p): mp.log(int(p)) for p in P if p <= 20000}
def psi1_mp(x):
    s = mp.mpf(0)
    for n in range(2, x + 1):
        if lam[n] != 0:
            pr = int(round(math.exp(lam[n]))); s += mp.log(pr) * (x - n)
    return s
pe = [psi1_mp(int(x)) for x in MEET[:11]]
tw["psi1_exact_max_dev"] = float(max(abs(float(pe[i]) - psi_ex[i]) for i in range(11)))
g100 = G[G <= 100.0]; rho100 = 0.5 + 1j * g100
C100 = contrib(rho100, MEET[:11]); hat100 = bg[:11] + C100.sum(axis=0); eps100 = np.diff(psi_ex[:11]) - np.diff(hat100)
hat_mp = []
for x in MEET[:11]:
    xi = int(x); s = mp.mpf(repr(float(background_psi1(x))))
    for gg in g100: s += contrib_mp(mp.mpc(0.5, repr(float(gg))), xi)
    hat_mp.append(s)
eps_mp = [float(pe[i + 1] - pe[i] - (hat_mp[i + 1] - hat_mp[i])) for i in range(10)]
tw["eps_H100_numpy"] = [float(v) for v in eps100]; tw["eps_H100_mpmath"] = eps_mp
tw["eps_H100_max_absdev"] = float(max(abs(eps100[i] - eps_mp[i]) for i in range(10)))
res["twin_mpmath"] = tw
log("jumeau : dépôts des paires dev rel max %s ; ψ₁ exact dev %.1e ; ε (H=100) dev max %.1e" % (tw["pair_deposit_max_reldev"], tw["psi1_exact_max_dev"], tw["eps_H100_max_absdev"]))
json.dump(res, open(os.path.join(OUT, "data", "e429b_results.json"), "w"), indent=1, ensure_ascii=False, default=str)
log("terminé")
