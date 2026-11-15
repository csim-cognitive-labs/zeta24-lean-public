# E463 — résultats (2026-11-09) — verdict A

* Module `RHV6Fresh/Terminal/RecompositionOnCells.lean` (isolé) : 2 définitions, 14 théorèmes ; compilé à la PREMIÈRE tentative
  (`attempts/build_attempt1.txt`, EXIT=0) ; 9 `#print axioms`, tous `[propext, Classical.choice, Quot.sound]` ; aucun `sorry`.
  Build complet vert (`logs/lake_build_full.txt`, 9064 jobs, EXIT=0). K1–K8 dans la forme pré-écrite.

## Acquis
* La part d'une Tour dans la recomposition des premiers, lue sur ses propres cellules, est exacte : d'une cellule à la suivante elle
  change de signe et son amplitude est multipliée par un facteur fixe, fonction de la fréquence et de la position radiale seulement.
* Ce facteur lit la position radiale (à fréquence donnée il la détermine).
* La part est non nulle sur chaque cellule si et seulement si la Tour est porteuse : première lecture LOCALE du poids, cellule par
  cellule (l'audit d'E460 n'en avait trouvé aucune).
* Bilan collectif : sur toute pièce, la somme des parts de tous les membres égale la variation du signal lissé des premiers.

## Non acquis (dit tel quel)
* Aucune exclusion hors ligne : le facteur d'une Tour hors ligne est simplement un autre nombre.
* La part d'UNE Tour sur une cellule n'est pas lue sur les premiers de cette cellule : seul le total de tous les membres l'est (K7).
  Isoler une Tour dans le total demande toute la recomposition (unicité d'E462), pas une cellule.
* Le membre arithmétique de K7 n'est pas encore écrit en pentes de la demande brute sur les pièces d'E438.
