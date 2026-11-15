# -*- coding: utf-8 -*-
"""E429(c) — POST-HOC (non pré-enregistré, déclaré comme tel). (1) Les écarts P2/P3 au-delà de 10⁻⁹ aux rangs ≥ 10⁵
(T ≥ 7·10⁴) : localisation. Aux points les plus mauvais, recalcul à 30 chiffres de l'identité towerRe_from_lastContact,
de la lecture tangentielle et de la lecture sur la valeur à la rencontre : si l'identité tient à 10⁻²⁰, l'écart en
double précision vient du conditionnement (argument du cosinus ~ 10⁷, tangente ~ 10⁶), pas de l'énoncé.
(2) Témoin supplémentaire pour le coût d'absorption : une Tour AUTHENTIQUE (zéro de rang 1) retirée de F_H, absorbée
par les 648 autres — le témoin pré-enregistré (paire en ligne à hauteur synthétique) est lui aussi étranger à la
famille ; ce témoin-ci mesure le coût d'absorber un membre légitime."""
import os, sys, math, json, numpy as np, mpmath as mp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import Logger, load_zeros, sieve_lambda
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e429c.log"))
G, sha = load_zeros(log)
lam, isp = sieve_lambda(20000); P = np.flatnonzero(isp).astype(np.int64); MEET = P[1:2001].astype(np.float64)
res = {"posthoc": True}
# (1) localisation
def stage(beta, T, x): return (T * np.log(x) - math.atan2(T, beta)) / math.pi
def contact(beta, T, k): return np.exp((math.atan2(T, beta) + k * math.pi) / T)
def cval(beta, T, k): return (-1.0) ** k * contact(beta, T, k) ** beta / math.hypot(beta, T)
def tower_re(beta, T, x): return x ** beta / math.hypot(beta, T) * np.cos(T * np.log(x) - math.atan2(T, beta))
mp.mp.dps = 30; res["1_localisation"] = {}
for rank in (100000, 1000000, 2001052):
    T = float(G[rank - 1]); beta = 0.5
    s = stage(beta, T, MEET); k = np.floor(s); f = s - k; Ck = contact(beta, T, k); vk = cval(beta, T, k)
    direct = tower_re(beta, T, MEET); fc = vk * (MEET / Ck) ** beta * np.cos(math.pi * f)
    rel = np.abs(fc - direct) / np.abs(direct); j = int(np.argmax(rel))
    tang = T / np.tan(T * np.log(Ck) - k * math.pi); jt = int(np.argmax(np.abs(tang - beta)))
    Tm = mp.mpf(repr(T)); b = mp.mpf(beta); ph = mp.atan(Tm / b); nrm = mp.sqrt(b * b + Tm * Tm)
    out = {"worst_P2_prime": int(MEET[j]), "worst_P2_relerr_double": float(rel[j]), "cos_pi_f_double": float(np.cos(math.pi * f[j]))}
    q = int(MEET[j]); sm = (Tm * mp.log(q) - ph) / mp.pi; km = int(mp.floor(sm)); fm = sm - km
    Cm = mp.exp((ph + km * mp.pi) / Tm); vm = (-1) ** km * Cm ** b / nrm
    dm = mp.mpf(q) ** b / nrm * mp.cos(Tm * mp.log(q) - ph); fcm = vm * (q / Cm) ** b * mp.cos(mp.pi * fm)
    out["identity_relerr_mpmath30"] = float(abs(fcm - dm) / abs(dm)); out["k_double_eq_mp"] = bool(int(k[j]) == km)
    out["direct_double_vs_mp_relerr"] = float(abs(direct[j] - dm) / abs(dm)); out["from_contact_double_vs_mp_relerr"] = float(abs(fc[j] - dm) / abs(dm))
    q2 = int(MEET[jt]); sm2 = (Tm * mp.log(q2) - ph) / mp.pi; km2 = int(mp.floor(sm2)); Cm2 = mp.exp((ph + km2 * mp.pi) / Tm)
    out["worst_tangent_prime"] = q2; out["tangent_abs_err_double"] = float(abs(tang[jt] - beta))
    out["tangent_abs_err_mpmath30"] = float(abs(Tm / mp.tan(Tm * mp.log(Cm2) - km2 * mp.pi) - b))
    res["1_localisation"]["rank%d" % rank] = out
    log("post-hoc (1) rang %d : P2 pire premier %d, erreur double %.1e (cos πf = %.1e), identité à 30 chiffres %.1e, direct double/mp %.1e, depuis contact double/mp %.1e ; tangente pire erreur double %.1e, à 30 chiffres %.1e"
        % (rank, out["worst_P2_prime"], out["worst_P2_relerr_double"], out["cos_pi_f_double"], out["identity_relerr_mpmath30"],
           out["direct_double_vs_mp_relerr"], out["from_contact_double_vs_mp_relerr"], out["tangent_abs_err_double"], out["tangent_abs_err_mpmath30"]))
# (2) absorption d'un membre authentique par les autres
H = 1000.0; g = G[G <= H]; RHO = 0.5 + 1j * g
def contrib(rho, x):
    lx = np.log(x)[None, :]; r = rho[:, None]; return -2.0 * np.real(np.exp((r + 1) * lx) / (r * (r + 1)))
C = contrib(RHO, MEET); D = np.diff(C, axis=1)
res["2_authentic_member_absorption"] = {}
for idx, label in ((0, "zero_rank1"), (9, "zero_rank10"), (99, "zero_rank100")):
    others = np.delete(D, idx, axis=0); d = D[idx]; row = {}
    for m in (12, 120, 600, 1200, 2000):
        A = others[:, :m].T; a, _, rk, _ = np.linalg.lstsq(A, d[:m], rcond=None); r = A @ a - d[:m]
        row[str(m)] = {"a_norm2": float(np.linalg.norm(a)), "a_max_abs": float(np.max(np.abs(a))), "rank": int(rk), "residual_rel": float(np.linalg.norm(r) / np.linalg.norm(d[:m]))}
    res["2_authentic_member_absorption"][label] = row
    log("post-hoc (2) %s absorbé par les autres : %s" % (label, {m: (round(v["a_norm2"], 3), round(v["residual_rel"], 4)) for m, v in row.items()}))
json.dump(res, open(os.path.join(OUT, "data", "e429c_posthoc.json"), "w"), indent=1, ensure_ascii=False, default=str)
log("terminé")
