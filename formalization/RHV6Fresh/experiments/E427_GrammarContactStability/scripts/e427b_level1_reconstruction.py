# -*- coding: utf-8 -*-
"""E427(b) — niveau 1 : la grammaire des écarts premiers reconstruite depuis les Tours des zéros authentiques.
Chaîne sans donnée arithmétique : Tours (β = ½, hauteurs du fichier) → somme collective des valeurs signées
(canal brut A aux demi-entiers, canal intégré B) → Λ̂(n) → règle pré-enregistrée d'E416 → premiers reconstruits →
états reconstruits (résidu mod 6) → transitions reconstruites → raccord, alternance, bilan, retour.
Les vrais premiers ne sont consultés qu'APRÈS, pour la validation. Contrôles de séparation : famille déplacée (β = 0,3),
famille pseudo-aléatoire de même densité (graine 20261104). Jumeau : mpmath 30 chiffres."""
import os, sys, math, json, hashlib, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import *
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
E415 = os.path.join(OUT, "..", "E415_RawEventReconstruction", "data")
log = Logger(os.path.join(OUT, "logs", "e427b.log"))
G, sha = load_zeros(log)
TRUNC = [1000, 5000, 100000, 1000000, 2001052]
E415_TRUNC = [3, 10, 40, 100, 300, 1000, 5000, 10000, 100000, 1000000, 2001052]
WINDOWS = {"W1": list(range(3, 301)), "W2": list(range(10000, 10061)), "W3": list(range(100000, 100031))}
res = {"zeros": int(len(G)), "sha256": sha, "truncations": TRUNC}

def grammar_from_sequence(primes):
    """Grammaire lue sur une suite croissante d'entiers (reconstruite ou vraie) : états, transitions (codes 0..3),
    classes, orientation, bilan cumulé, et vérifications internes (identités : raccord, alternance, confinement)."""
    p = np.array(primes, dtype=np.int64)
    if len(p) < 2:
        return {"n": int(len(p)), "states": (p % 6 == 1).astype(int).tolist(), "trans": [], "cls": [], "orient": [], "balance": [],
                "in_two_states": bool(np.all((p % 6 == 1) | (p % 6 == 5))) if len(p) else True, "class_conform": True,
                "alternation_ok": True, "balance_bounded": True, "return_ok": True}
    s = (p % 6 == 1); src, dst = s[:-1], s[1:]
    cls = (p[1:] - p[:-1]) % 6
    expected = np.where(src == dst, 0, np.where(src, 4, 2))
    orient = src.astype(int) - dst.astype(int)
    B = np.cumsum(orient)
    code = np.where(src & dst, 0, np.where(src & ~dst, 1, np.where(~src & dst, 2, 3)))
    ci = np.flatnonzero(orient != 0); cv = orient[ci]
    Bp = np.concatenate([[0], B])
    return {"n": int(len(p)), "states": s.astype(int).tolist(), "trans": code.tolist(), "cls": cls.tolist(), "orient": orient.tolist(),
            "balance": B.tolist(), "in_two_states": bool(np.all((p % 6 == 1) | (p % 6 == 5))),
            "class_conform": bool(np.all(cls == expected)),
            "alternation_ok": bool(np.all(cv[1:] != cv[:-1])) if len(ci) > 1 else True,
            "balance_bounded": bool(np.all(np.abs(B) <= 1)),
            "return_ok": bool(np.all((Bp[ci[1:] + 1] - Bp[ci[:-1]]) == 0)) if len(ci) > 1 else True}

def compare(rec, tru):
    """Validation après coup : désaccords état par état, transition par transition, bilan par bilan (sur le préfixe commun)
    et différence de longueur."""
    m = min(len(rec["states"]), len(tru["states"])); mt = min(len(rec["trans"]), len(tru["trans"]))
    return {"len_rec": rec["n"], "len_true": tru["n"],
            "state_mismatches_prefix": int(sum(a != b for a, b in zip(rec["states"][:m], tru["states"][:m]))),
            "transition_mismatches_prefix": int(sum(a != b for a, b in zip(rec["trans"][:mt], tru["trans"][:mt]))),
            "balance_mismatches_prefix": int(sum(a != b for a, b in zip(rec["balance"][:mt], tru["balance"][:mt]))),
            "exact": rec["states"] == tru["states"] and rec["trans"] == tru["trans"]}

def reconstruct(W, lam):
    labels = [classify(n, lam[i])[1] for i, n in enumerate(W)]
    return [n for n, l in zip(W, labels) if l == "prime"], [n for n, l in zip(W, labels) if l != "none"]

def lam_channels(W, beta, gam, idx):
    """Λ̂A (brut, demi-entiers) et Λ̂B (intégré) aux troncatures idx, depuis les Tours (β, γ)."""
    P0 = {m: background_raw(m - 0.5) - sum_raw(m - 0.5, beta, gam, cumulative=True)[idx] for m in range(W[0], W[-1] + 2)}
    P1 = {m: background_psi1(float(m)) - m * sum_integrated(float(m), beta, gam, cumulative=True)[idx] for m in range(W[0] - 1, W[-1] + 2)}
    lamA = np.array([P0[n + 1] - P0[n] for n in W]); lamB = np.array([P1[n + 1] - 2 * P1[n] + P1[n - 1] for n in W])
    return lamA, lamB

IDX = np.array(TRUNC) - 1
# empreintes des fichiers E415 réutilisés pour l'échelle de troncature
res["e415_npy_sha256"] = {f: hashlib.sha256(open(os.path.join(E415, f), "rb").read()).hexdigest()[:16]
                          for f in sorted(os.listdir(E415)) if f.endswith(".npy")}
res["authentic"] = {}
for wname, W in WINDOWS.items():
    log("fenêtre %s : recalcul des canaux A et B depuis les zéros (toutes troncatures %s)" % (wname, TRUNC))
    lamA, lamB = lam_channels(W, 0.5, G, IDX)
    e415A = np.load(os.path.join(E415, "lamA_%s.npy" % wname)); e415B = np.load(os.path.join(E415, "lamB_%s.npy" % wname))
    sel = [E415_TRUNC.index(h) for h in TRUNC]
    res["authentic"][wname] = {"max_abs_diff_vs_E415_A": float(np.max(np.abs(lamA - e415A[:, sel]))),
                               "max_abs_diff_vs_E415_B": float(np.max(np.abs(lamB - e415B[:, sel])))}
    log("  cohérence avec E415 : A %.2e, B %.2e" % (res["authentic"][wname]["max_abs_diff_vs_E415_A"], res["authentic"][wname]["max_abs_diff_vs_E415_B"]))
    # --- reconstruction (aucune donnée arithmétique) ---
    recs = {}
    for chan, L in (("A", lamA), ("B", lamB)):
        for j, H in enumerate(TRUNC):
            primes_rec, events_rec = reconstruct(W, L[:, j])
            recs["%s_%d" % (chan, H)] = (primes_rec, events_rec, grammar_from_sequence(primes_rec))
    # --- VALIDATION (après) ---
    lam, isp = sieve_lambda(W[-1] + 2)
    true_primes = [n for n in W if isp[n]]; tru = grammar_from_sequence(true_primes)
    res["authentic"][wname]["true_primes"] = len(true_primes); res["authentic"][wname]["true_grammar"] = {k: tru[k] for k in ("states", "trans", "balance")}
    for key, (pr, ev, rec) in recs.items():
        c = compare(rec, tru)
        c.update({k: rec[k] for k in ("in_two_states", "class_conform", "alternation_ok", "balance_bounded", "return_ok")})
        c["reconstructed_primes"] = pr; c["reconstructed_states"] = rec["states"]; c["reconstructed_trans"] = rec["trans"]
        res["authentic"][wname][key] = c
        log("  %s zéros=%8s : premiers reconstruits %d / vrais %d ; deux états %s ; désaccords états %d, transitions %d, bilans %d ; exact %s"
            % (key[0], key[2:], c["len_rec"], c["len_true"], c["in_two_states"], c["state_mismatches_prefix"],
               c["transition_mismatches_prefix"], c["balance_mismatches_prefix"], c["exact"]))
# --- route par contacts authentiques : W1, H = 1000, canal brut, accumulation de chaque Tour sur ses propres contacts ---
log("route par contacts : W1, 1000 zéros, canal brut, accumulation contact par contact dans [n−½, n+½]")
gam = G[:1000]; W = WINDOWS["W1"]; lam_contact = np.empty(len(W)); ncont = 0
for i, n in enumerate(W):
    a, x = n - 0.5, n + 0.5; acc = 0.0
    for g in gam:
        rho = 0.5 + 1j * g
        v, nc, _ = accumulate_one(rho, tower_value, a, x); acc += 2.0 * v.real; ncont += nc
    lam_contact[i] = (background_raw(x) - background_raw(a)) - acc
lamA1 = lam_channels(W, 0.5, G[:1000], np.array([999]))[0][:, 0]
res["contact_route_W1_H1000"] = {"contacts_total": int(ncont), "max_abs_diff_vs_endpoint": float(np.max(np.abs(lam_contact - lamA1))),
                                 "max_rel_diff": float(np.max(np.abs(lam_contact - lamA1) / np.maximum(np.abs(lamA1), 1e-12)))}
pr_c, _ = reconstruct(W, lam_contact); rec_c = grammar_from_sequence(pr_c)
lam, isp = sieve_lambda(302); tru1 = grammar_from_sequence([n for n in W if isp[n]])
res["contact_route_W1_H1000"]["grammar_compare"] = compare(rec_c, tru1)
log("  %d contacts ; écart max contact/bords %.2e (rel %.2e) ; grammaire reconstruite : %s"
    % (ncont, res["contact_route_W1_H1000"]["max_abs_diff_vs_endpoint"], res["contact_route_W1_H1000"]["max_rel_diff"], res["contact_route_W1_H1000"]["grammar_compare"]))
# --- contrôles de séparation ---
res["separation"] = {}
# (i) famille déplacée : mêmes hauteurs, β = 0,3
for wname in ("W1",):
    W = WINDOWS[wname]; lam, isp = sieve_lambda(W[-1] + 2); tru = grammar_from_sequence([n for n in W if isp[n]])
    for H in (1000, 2001052):
        lamA = lam_channels(W, 0.3, G[:H], np.array([H - 1]))[0][:, 0]
        pr, ev = reconstruct(W, lamA); rec = grammar_from_sequence(pr); c = compare(rec, tru)
        c.update({k: rec[k] for k in ("in_two_states", "class_conform", "alternation_ok", "balance_bounded", "return_ok")}); c["reconstructed_primes"] = pr
        res["separation"]["shifted_beta0.3_%s_H%d" % (wname, H)] = c
        log("séparation (i) β=0,3 %s H=%d : premiers reconstruits %d / vrais %d ; deux états %s ; désaccords états %d ; exact %s"
            % (wname, H, c["len_rec"], c["len_true"], c["in_two_states"], c["state_mismatches_prefix"], c["exact"]))
# (ii) hauteurs pseudo-aléatoires de même densité (Riemann–von Mangoldt), β = ½, jamais aux hauteurs réelles
rng = np.random.default_rng(20261104)
def Ncount(T): return T / (2 * math.pi) * np.log(T / (2 * math.pi * math.e)) + 7 / 8
grid = np.linspace(14.0, float(G[-1]), 2_000_000); Ng = Ncount(grid)
for H in (1000, 2001052):
    u = np.sort(rng.uniform(Ng[0], Ncount(float(G[H - 1])), H)); Gs = np.interp(u, Ng, grid)
    j = np.searchsorted(G, Gs); near = np.minimum(np.abs(G[np.minimum(j, len(G) - 1)] - Gs), np.abs(G[np.maximum(j - 1, 0)] - Gs))
    assert near.min() > 1e-9, "hauteur synthétique coïncidant avec un zéro réel"
    W = WINDOWS["W1"]; lam, isp = sieve_lambda(W[-1] + 2); tru = grammar_from_sequence([n for n in W if isp[n]])
    lamA = lam_channels(W, 0.5, Gs, np.array([H - 1]))[0][:, 0]
    pr, ev = reconstruct(W, lamA); rec = grammar_from_sequence(pr); c = compare(rec, tru)
    c.update({k: rec[k] for k in ("in_two_states", "class_conform", "alternation_ok", "balance_bounded", "return_ok")})
    c["reconstructed_primes"] = pr; c["min_distance_to_real_zero"] = float(near.min())
    res["separation"]["pseudo_density_W1_H%d" % H] = c
    log("séparation (ii) densité seule H=%d : premiers reconstruits %d / vrais %d ; deux états %s ; désaccords états %d ; exact %s ; distance min aux zéros réels %.2e"
        % (H, c["len_rec"], c["len_true"], c["in_two_states"], c["state_mismatches_prefix"], c["exact"], near.min()))
# --- jumeau déterministe : mpmath 30 chiffres, H = 1000, canal brut ---
import mpmath as mp
mp.mp.dps = 30
tw = {}
for n in (3, 5, 7, 97, 101):
    vals = []
    for x in (n - 0.5, n + 0.5):
        xx = mp.mpf(x); S = mp.mpf(0)
        for g in G[:1000]:
            rho = mp.mpc(0.5, float(g)); S += 2 * mp.re(mp.power(xx, rho) / rho)
        vals.append(xx - mp.log(2 * mp.pi) - mp.log(1 - xx ** -2) / 2 - S)
    lam_mp = float(vals[1] - vals[0])
    lam_np = float(lam_channels([n], 0.5, G[:1000], np.array([999]))[0][0, 0])
    tw[str(n)] = {"mpmath": lam_mp, "numpy": lam_np, "abs_diff": abs(lam_mp - lam_np)}
res["twin_mpmath_H1000"] = tw; res["twin_max_abs_diff"] = max(v["abs_diff"] for v in tw.values())
log("jumeau mpmath (H=1000) : écart max %.2e" % res["twin_max_abs_diff"])
json.dump(res, open(os.path.join(OUT, "data", "e427b_results.json"), "w"), indent=1, ensure_ascii=False)
log("terminé")
