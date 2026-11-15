# E422 — protocole (pré-enregistré 2026-11-03)
1. Contacts des Tours de rang {1, 2, 3, 100, 1000} dans [100, 1000] (≈ 10, 15, 18, 173, 1 040 contacts) ; positions exactes.
2. Pour N ∈ {10, 100, 1 000, 10⁴, 10⁵, 2 001 052} : S_N(x) = Σ_{j ≤ N} 2Re(x^{ρ_j}/ρ_j) à chaque contact x (évaluation par blocs
   numpy, float64) ; valeur propre 2v_k ; reste = S_N − 2v_k.
3. Mesures par Tour et par N : médiane et max de |2v_k|/|S_N| ; fraction de contacts où sign(v_k) = sign(S_N) ; rms du reste ;
   rms de S_N ; rms(S_N − S_{N précédent}) ; histogramme (10 classes) de la phase des autres Tours à x.
4. Jumeau déterministe : mpmath 25 chiffres pour N = 100 sur 3 contacts de la Tour 1 ; écart reporté.
5. Durée < 10 min, nohup, pas de sondage. Aucun critère de « succès » arithmétique : résultats descriptifs, consignés tels quels.
