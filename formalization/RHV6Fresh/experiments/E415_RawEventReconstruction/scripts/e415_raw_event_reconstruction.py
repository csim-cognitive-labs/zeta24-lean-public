# -*- coding: utf-8 -*-
"""E415 — reconstruction des poids Λ(n) depuis les zéros, quatre approches, toutes troncatures.
A : canal brut, Λ̂^A_H(n) = ψ̂₀_H(n+½) − ψ̂₀_H(n−½)
B : canal intégré, Λ̂^B_H(n) = ψ̂₁_H(n+1) − 2ψ̂₁_H(n) + ψ̂₁_H(n−1)  (seconde différence exacte, Lean)
C : accumulation par contacts à valeurs complexes (= D par télescopage ; vérifié sur une sous-famille)
D : calcul spectral direct (= B, même somme).
Aucune donnée arithmétique n'entre dans A–D ; Λ(n) n'est consulté qu'en VALIDATION, après calcul."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import *
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e415.log"))
G, sha = load_zeros(log)
TRUNC = [3, 10, 40, 100, 300, 1000, 5000, 10000, 100000, 1000000, 2001052]
IDX = np.array(TRUNC) - 1
WINDOWS = {"W1": list(range(3, 301)), "W2": list(range(10000, 10061)), "W3": list(range(100000, 100031))}
beta = 0.5
def psi1_all(x): return background_psi1(x) - x * sum_integrated(x, beta, G, cumulative=True)[IDX]
def psi0_all(x): return background_raw(x) - sum_raw(x, beta, G, cumulative=True)[IDX]
results = {}
for wname, W in WINDOWS.items():
    log("fenêtre %s : n ∈ [%d, %d]" % (wname, W[0], W[-1]))
    # ψ̂₁ aux entiers n−1..n+1, ψ̂₀ aux demi-entiers
    ints = list(range(W[0] - 1, W[-1] + 2))
    P1 = {m: psi1_all(float(m)) for m in ints}
    P0 = {m: psi0_all(m - 0.5) for m in range(W[0], W[-1] + 2)}
    lamA = np.array([[P0[n + 1][j] - P0[n][j] for j in range(len(TRUNC))] for n in W])
    lamB = np.array([[P1[n + 1][j] - 2 * P1[n][j] + P1[n - 1][j] for j in range(len(TRUNC))] for n in W])
    np.save(os.path.join(OUT, "data", "lamA_%s.npy" % wname), lamA)
    np.save(os.path.join(OUT, "data", "lamB_%s.npy" % wname), lamB)
    log("  calcul spectral terminé (A et B=D) ; validation seulement maintenant")
    # ---- VALIDATION ----
    lam, isp = sieve_lambda(W[-1] + 2)
    truth = np.array([lam[n] for n in W])
    cls = np.array(["prime" if isp[n] else ("power" if lam[n] > 0 else "none") for n in W])
    results[wname] = {}
    for j, H in enumerate(TRUNC):
        eA = lamA[:, j] - truth; eB = lamB[:, j] - truth
        r = dict(zeros=H, gamma_max=float(G[H - 1]),
                 A_rms=float(np.sqrt(np.mean(eA ** 2))), A_max=float(np.max(np.abs(eA))),
                 B_rms=float(np.sqrt(np.mean(eB ** 2))), B_max=float(np.max(np.abs(eB))),
                 B_rms_prime=float(np.sqrt(np.mean(eB[cls == "prime"] ** 2))),
                 B_rms_none=float(np.sqrt(np.mean(eB[cls == "none"] ** 2))),
                 A_rms_prime=float(np.sqrt(np.mean(eA[cls == "prime"] ** 2))),
                 A_rms_none=float(np.sqrt(np.mean(eA[cls == "none"] ** 2))))
        results[wname][str(H)] = r
        log("  zéros=%8d γ_max=%11.2f | A: rms %.4f max %.4f (premiers %.4f, vides %.4f) | B: rms %.3e max %.3e (premiers %.3e, vides %.3e)"
            % (H, r["gamma_max"], r["A_rms"], r["A_max"], r["A_rms_prime"], r["A_rms_none"], r["B_rms"], r["B_max"], r["B_rms_prime"], r["B_rms_none"]))
    # tableau par entier, troncature complète
    with open(os.path.join(OUT, "data", "e415_%s_full.txt" % wname), "w") as f:
        f.write("# n  classe  Λ(n)  Λ̂A(2001052)  E_A  Λ̂B(2001052)  E_B\n")
        for i, n in enumerate(W):
            f.write("%d %s %.6f %.6f %+.6f %.6f %+.3e\n" % (n, cls[i], truth[i], lamA[i, -1], lamA[i, -1] - truth[i], lamB[i, -1], lamB[i, -1] - truth[i]))
# ---- C = D : accumulation par contacts (valeurs complexes) sur [n−1, n+1], 5000 zéros, fenêtre 3..60 ----
log("C vs D : accumulation par contacts (5000 zéros) sur les cellules [n−1,n], [n,n+1], n = 3..60")
gam = G[:5000]; maxdiff = 0.0; cnt = 0
for n in range(3, 61):
    accC = 0j; accD = 0j
    for g in gam:
        rho = 0.5 + 1j * g
        a1, c1_, _ = accumulate_one(rho, integrated_tower, n - 1.0, float(n))
        a2, c2_, _ = accumulate_one(rho, integrated_tower, float(n), n + 1.0)
        # seconde différence de x·F : (n+1)F(n+1) − 2nF(n) + (n−1)F(n−1) = (n+1)(a2) − (n−1)(a1) + ... exact :
        Fn = integrated_tower(rho, float(n)); Fm = integrated_tower(rho, n - 1.0); Fp = integrated_tower(rho, n + 1.0)
        accC += (n + 1) * (Fn + a2) - 2 * n * Fn + (n - 1) * (Fn - a1)
        accD += (n + 1) * Fp - 2 * n * Fn + (n - 1) * Fm
        cnt += c1_ + c2_
    maxdiff = max(maxdiff, abs(accC - accD))
log("  C vs D : max |C − D| = %.3e sur %d contacts (identité télescopique, Lean : contact_accumulation_eq_endpoint_difference)" % (maxdiff, cnt))
results["C_vs_D"] = dict(max_abs_diff=maxdiff, contacts=int(cnt), zeros=5000, window=[3, 60])
json.dump(results, open(os.path.join(OUT, "data", "e415_results.json"), "w"), indent=1)
log("terminé")
