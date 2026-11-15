# E471 (Ψ5) — résultats (2026-11-13) — appui conforme à l'attente écrite

Exécution : `../E467_MemberConstancySeries/logs_twin_run.txt` (section Ψ5, 2 001 052 zéros, coupure nette sans Fejér, grille
géométrique de 60 abscisses de 10^3 à 3·10^5, poids de von Mangoldt exacts par crible). Résultats `twin_results.json` section `psi5`.

* Résidu de recomposition (zéros réels, tous sur la ligne) : médiane 0,0077, maximum 0,99 (atteint vers 3·10^5 où la cellule la plus
  fine vaut 0,83 pas : limite de résolution d'E466). Résidu cumulé en valeur absolue sur la grille : 4,5.
* Paire insérée à la hauteur du zéro de rang 1 000 (hauteur 1 419,42), défaut exigé des autres hauteurs rapporté à l'échelle de la
  ligne, pente de l'enveloppe en coordonnées logarithmiques :

| β de la paire | exposant attendu 1/2 − β | exposant mesuré | défaut cumulé | résidu cumulé réel |
|---|---|---|---|---|
| 0,3 | 0,20 | 0,223 | 81,2 | 4,5 |
| 0,4 | 0,10 | 0,112 | 22,8 | 4,5 |
| 0,45 | 0,05 | 0,039 | 12,7 | 4,5 |

Les trois exposants sont dans la tolérance pré-écrite de ±0,05. Le défaut cumulé exigé par une paire est 3 à 18 fois le résidu cumulé
réel sur la même grille : au cumul, la paire est visible là où un point ne la sépare pas (E402). Ceci est une mesure d'appui : elle ne
démontre rien sur les vrais zéros, elle étalonne les formes closes de Ψ1 et Ψ4 sur la collectivité réelle.
