#!/usr/bin/env python3
"""E477 post-hoc (après lecture du jumeau) : prédiction P1 corrigée en mesure x, (1−e^{−δ/T})/(1−e^{−π/T}), contre la fraction mesurée ;
et estimation de la fluctuation du premier ordre par premier (écart-type de la somme restreinte) contre la mesure. Lit twin_results.json."""
import json, math, os
HERE = os.path.dirname(os.path.abspath(__file__)); R = json.load(open(os.path.join(HERE, "twin_results.json")))
XMAX = 3e7
for t, d in R["tours"].items():
    T = d["T"]
    for b, r in d["betas"].items():
        if b == "0.50": continue
        delta = r["delta"]; corr = (1 - math.exp(-delta/T))/(1 - math.exp(-math.pi/T))
        # fluctuation : Σ Λ² x² (δ/T)² sur la bande ≈ (δ/π)·(log X)·X³/3·(δ/T)²  → écart-type / X^{3/2}
        std = math.sqrt((delta/math.pi)*math.log(XMAX)/3)*delta/T
        print(f"Tour {t} β={b}: fraction mesurée {r['P1_fraction']:.4e} ; δ/π {delta/math.pi:.4e} ; corrigée {corr:.4e} ; écart relatif corrigé "
              f"{abs(r['P1_fraction']-corr)/corr:.3f} | S_pair/x^1.5 mesuré {r['P5_Spair_sur_x32_dernier']:.2e} ; écart-type estimé {std:.2e} ; "
              f"moyenne second ordre d'une cellule /x^1.5 à X : {delta**2*(math.exp(math.pi/T)-1)**2/(math.pi*T)*math.sqrt(XMAX):.2e}")
