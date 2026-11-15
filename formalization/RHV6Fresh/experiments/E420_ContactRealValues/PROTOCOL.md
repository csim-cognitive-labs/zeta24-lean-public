# E420 — protocole (pré-enregistré 2026-11-03)
1. Tours réelles : rangs {1, 2, 3, 10, 100, 1 000, 10 000, 100 000, 1 000 000, 2 001 052}, β = ½ (hypothèse de données),
   contacts dans [2, 10⁴] (≤ 3,1·10⁶ contacts pour la Tour la plus haute). Tours synthétiques séparées : β ∈ {0,3, 0,45, 0,49}
   aux hauteurs milieu des zéros (1,2), (100,101), (2000,2001) — jamais la hauteur d'un zéro réel.
2. Pour chaque Tour : v_k = x^ρ/ρ évalué en complexe à x = C_k ; mesures : max |Im v_k|/|v_k|, max |Re v_k − forme fermée|/|v_k|,
   nombre de paires consécutives de même signe (attendu 0), max |(|v_{k+1}|/|v_k|) − e^{βπ/T}|, résidu de l'ajustement affine
   de log|v_k| en k, pente estimée − βπ/T.
3. Inversion depuis les contacts seuls : T̂ = π/Δlog C (chaque paire), β̂_amp = T̂·log|v_{k+1}/v_k|/π, β̂_tan = T̂/tan(T̂ log C_k − kπ) ;
   erreurs maximales. Précision float64 ; jumeau mpmath (30 chiffres) sur 5 contacts par Tour, écart reporté.
4. Critère : toutes les identités à l'arrondi (erreur relative ≤ 10⁻¹⁰ en float64 pour T ≤ 10⁶ ; seuil déclaré avant exécution) ;
   sinon le résultat est consigné tel quel.
5. Durée bornée < 5 min, nohup, pas de sondage.
