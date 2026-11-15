# E414 — protocole (pré-enregistré 2026-11-03)

1. Pour N ∈ {3, 40, 300, 5000, 100000, 2001052} zéros, intervalle [a, x] choisi AVANT exécution pour borner le nombre
   total de contacts (≈ Σ_ρ T log(x/a)/π ≤ 3·10⁷) : [2, 50] pour N ≤ 5000 ; [100, 102,5] pour 100000 ; [1000, 1000,085]
   pour 2001052.
2. Pour chaque zéro : contacts C_k = exp((arctan(T/β)+kπ)/T) dans [a, x] ; A_ρ = (F(C_min) − F(a)) + Σ_k (F(C_{k+1}) − F(C_k))
   + (F(x) − F(C_max)) en complexe ; comparaison à F(x) − F(a). Deux canaux F : brut, intégré.
3. Mesures : somme complexe collective, parties réelle et imaginaire, erreur absolue et relative, erreur maximale par
   zéro, somme des modules des variations, borne d'arrondi 4·ε·Σ|V| ; verdict ARRONDI / HORS ARRONDI.
4. Sensibilité à la précision : recalcul en float32 pour N = 300 (brut).
5. Critère de succès déclaré : toutes les erreurs ≤ borne d'arrondi ET théorème Lean compilé.
6. Durée bornée : < 10 min, `nohup`, aucun sondage en boucle.
