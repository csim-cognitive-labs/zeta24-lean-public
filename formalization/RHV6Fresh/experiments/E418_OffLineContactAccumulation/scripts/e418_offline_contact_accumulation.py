# -*- coding: utf-8 -*-
"""E418 — sensibilité radiale : on remplace, à une hauteur T = γ_r réelle, le membre de ligne
ρ = ½ + iT par (1) une Tour seule β + iT (avec sa conjuguée, sans miroir : brise la symétrie
s ↔ 1−s, scénario de contrôle), (2) la paire miroir β + iT, 1−β + iT (avec conjuguées = quartet
complet, symétries de ζ respectées). SCÉNARIO SYNTHÉTIQUE : jamais une constellation de vrais zéros.
Mesures : déplacement des contacts, phase, amplitude, contributions, accumulations, lecture des
cassures, écarts reconstruits, complément nécessaire, et borne démontrable du défaut."""
import os, sys, math, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "E414_ContactValueAccumulation", "scripts"))
from contact_common import *
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
log = Logger(os.path.join(OUT, "logs", "e418.log"))
G, sha = load_zeros(log)
W = list(range(3, 301)); lam, isp = sieve_lambda(302); truth = np.array([lam[n] for n in W])
RANKS = [1, 100, 2000]; BETAS = [0.3, 0.45, 0.49]
# base : ligne complète (2 001 052 zéros), ψ̂₁ aux entiers 2..301, ψ̂₀ aux demi-entiers
P1 = {m: psi1_hat(float(m), 0.5, G) for m in range(2, 302)}
P0 = {m: psi0_hat(m - 0.5, 0.5, G) for m in range(3, 302)}
lamB0 = np.array([P1[n + 1] - 2 * P1[n] + P1[n - 1] for n in W]); lamA0 = np.array([P0[n + 1] - P0[n] for n in W])
labB0 = [classify(n, v)[1] for n, v in zip(W, lamB0)]; labA0 = [classify(n, v)[1] for n, v in zip(W, lamA0)]
log("ligne : rms Λ̂B − Λ = %.3e, rms Λ̂A − Λ = %.4f" % (np.sqrt(np.mean((lamB0 - truth) ** 2)), np.sqrt(np.mean((lamA0 - truth) ** 2))))
def delta_terms(T, rhos_new):
    """Variation des contributions (brut, intégré) quand ½+iT est remplacé par la famille rhos_new."""
    dB = {}; dA = {}
    for m in range(2, 302):
        x = float(m); old = 2 * np.real(x ** (0.5 + 1j * T) / ((0.5 + 1j * T) * (1.5 + 1j * T)))
        new = sum(2 * np.real(x ** r / (r * (r + 1))) for r in rhos_new)
        dB[m] = -x * (new - old)          # ψ̂₁ change de −x·ΔS
    for m in range(3, 302):
        x = m - 0.5; old = 2 * np.real(x ** (0.5 + 1j * T) / (0.5 + 1j * T))
        new = sum(2 * np.real(x ** r / r) for r in rhos_new)
        dA[m] = -(new - old)
    return dB, dA
res = {}
for r in RANKS:
    T = float(G[r - 1])
    for b in BETAS:
        for scen, rhos in (("tour_seule", [b + 1j * T]), ("paire_miroir", [b + 1j * T, (1 - b) + 1j * T])):
            dB, dA = delta_terms(T, rhos)
            lamB = lamB0 + np.array([dB[n + 1] - 2 * dB[n] + dB[n - 1] for n in W])
            lamA = lamA0 + np.array([dA[n + 1] - dA[n] for n in W])
            labB = [classify(n, v)[1] for n, v in zip(W, lamB)]; labA = [classify(n, v)[1] for n, v in zip(W, lamA)]
            dlam = lamB - lamB0; dlamA = lamA - lamA0
            # borne démontrable (accroissements finis sur la seconde différence de x^{s+1}/(s(s+1)) : |Δ²| ≤ max x^{Re s − 1}) :
            bound = np.array([2 * ((n - 1) ** (-0.5) + sum((n - 1) ** (rr.real - 1) for rr in rhos)) for n in W])
            # géométrie : contacts, phase, amplitude (à x = 100)
            geo = {}
            for rr in rhos:
                geo["%.2f" % rr.real] = dict(phase=phase(rr.real, T), phase_ligne=phase(0.5, T),
                    deplacement_log_contact=(phase(rr.real, T) - phase(0.5, T)) / T,
                    rapport_amplitude_x100=100 ** (rr.real - 0.5), module_1_sur_rho=1 / abs(rr), module_1_sur_rho_ligne=1 / abs(0.5 + 1j * T))
            rec = dict(rang=r, T=T, beta=b, scenario=scen, geometrie=geo,
                       max_abs_delta_lamB=float(np.max(np.abs(dlam))), max_abs_delta_lamA=float(np.max(np.abs(dlamA))),
                       rms_delta_lamB=float(np.sqrt(np.mean(dlam ** 2))),
                       borne_max=float(np.max(bound)), delta_dans_borne=bool(np.all(np.abs(dlam) <= bound + 1e-12)),
                       rapport_delta_sur_borne_max=float(np.max(np.abs(dlam) / bound)),
                       changements_classification_B=int(sum(1 for u, v in zip(labB, labB0) if u != v)),
                       changements_classification_A=int(sum(1 for u, v in zip(labA, labA0) if u != v)),
                       erreurs_B_vs_verite=int(sum(1 for n, l in zip(W, labB) if (l == "prime") != bool(isp[n]))),
                       erreurs_A_vs_verite=int(sum(1 for n, l in zip(W, labA) if (l == "prime") != bool(isp[n]))),
                       complement_necessaire_rms=float(np.sqrt(np.mean(dlam ** 2))),
                       residu_troncature_rms_ligne=float(np.sqrt(np.mean((lamB0 - truth) ** 2))))
            res["r%d_b%.2f_%s" % (r, b, scen)] = rec
            log("rang %4d T=%9.3f β=%.2f %-12s | ΔΛ̂B max %.3e rms %.3e (borne max %.3e, dans la borne : %s, Δ/borne max %.3f) | ΔΛ̂A max %.3e | reclassements B %d A %d | erreurs B %d A %d | résidu troncature ligne %.3e"
                % (r, T, b, scen, rec["max_abs_delta_lamB"], rec["rms_delta_lamB"], rec["borne_max"], rec["delta_dans_borne"], rec["rapport_delta_sur_borne_max"],
                   rec["max_abs_delta_lamA"], rec["changements_classification_B"], rec["changements_classification_A"], rec["erreurs_B_vs_verite"], rec["erreurs_A_vs_verite"], rec["residu_troncature_rms_ligne"]))
# réponse collective : le quartet peut-il être compensé par les autres zéros sans bouger leurs hauteurs ?
# test déterministe : moindres carrés sur les amplitudes (multiplicités réelles) des 1000 premiers zéros pour annuler ΔΛ̂B sur W1
T = float(G[1999]); rhos = [0.3 + 1j * T, 0.7 + 1j * T]; dB, dA = delta_terms(T, rhos)
target = -np.array([dB[n + 1] - 2 * dB[n] + dB[n - 1] for n in W])
M = np.zeros((len(W), 1000))
for j in range(1000):
    g = G[j]; rho = 0.5 + 1j * g
    col = {m: -m * 2 * np.real(float(m) ** rho / (rho * (rho + 1))) for m in range(2, 302)}
    M[:, j] = [col[n + 1] - 2 * col[n] + col[n - 1] for n in W]
coef, *_ = np.linalg.lstsq(M, target, rcond=None)
resid = np.linalg.norm(M @ coef - target) / np.linalg.norm(target)
log("compensation par réglage des amplitudes de 1000 zéros de ligne (hauteurs conservées) : résidu relatif %.3e ; |coef| max %.3e (une multiplicité réelle est un entier ≥ 0 : ces coefficients ne sont pas des multiplicités)" % (resid, np.max(np.abs(coef))))
res["compensation_lstsq"] = dict(residu_relatif=float(resid), coef_max=float(np.max(np.abs(coef))), coef_non_entiers=True)
json.dump(res, open(os.path.join(OUT, "data", "e418_results.json"), "w"), indent=1)
log("terminé")
