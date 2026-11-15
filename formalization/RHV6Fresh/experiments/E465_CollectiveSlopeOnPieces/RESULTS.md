# E465 — résultats (2026-11-09) — verdict A

* Module `RHV6Fresh/Terminal/CollectiveSlopeOnPieces.lean` (isolé) : 4 définitions, 19 théorèmes ; compilé à la PREMIÈRE tentative
  (`attempts/build_attempt1.txt`, EXIT=0, aucune erreur ; avertissements de style seulement) ; 14 `#print axioms`, tous
  `[propext, Classical.choice, Quot.sound]` ; aucun `sorry`. Build complet vert (`logs/lake_build_full.txt`, 9064 jobs, EXIT=0).
  S1–S12 dans la forme pré-écrite (S7 sans l'hypothèse d'ordre, inutile).
* Jumeau déterministe (`twin.py`, `logs/twin_run.txt`, `twin_results.json`, 7 s, 50 chiffres) : 276 cellules de contacts des cinq
  premières Tours de la ligne, 200 écarts ; pire écart relatif 1,4·10^-46 (S3) ; S7 et S8 exacts ; conforme (tolérance pré-écrite 10^-30).

## Acquis
* Le total des parts de toutes les Tours sur une pièce se lit maintenant sur la demande brute elle-même : c'est l'AIRE de la demande
  sur la pièce (niveau au départ fois longueur, moins le demi-carré de la longueur, plus chaque poids franchi multiplié par sa distance
  à la fin de la pièce), moins la variation d'un fond résiduel explicite.
* Une rencontre n'y fait pas un saut : le poids du premier entre par sa distance à la fin de la pièce, nulle à la rencontre même.
  Aucun poids premier n'entre dans l'aire de son propre écart ; il entre par le niveau de départ de l'écart suivant.
* Sur une cellule entre deux contacts consécutifs d'une Tour : le terme de cette Tour dans le total est exactement sa part d'E463
  (signe alterné, facteur fixe lisant la position radiale) ; le total est l'aire de la demande sur la cellule.
* L'aire de la demande sur un écart se découpe par les contacts d'une Tour (reste initial, cellules entières, reste final), chaque
  morceau étant lui-même une aire ; les aires s'ajoutent.
* Une pièce plus courte qu'un pas d'entier franchit au plus un entier (seuil géométrique mesuré par E464).

## Non acquis (dit tel quel)
* Aucune exclusion hors ligne : toutes les identités valent pour toute recomposition, sur la ligne comme hors ligne.
* La part d'UNE Tour reste non lue sur les premiers de sa cellule : S11 juxtapose la part et l'aire, il ne les compare pas. Ne JAMAIS
  en tirer « amplitude d'une Tour contre variation de la demande sur la cellule » (obligation retirée par l'auteur, R-E446).
* Le fond résiduel garde les deux constantes de zêta et la série des zéros triviaux (version à constantes libres non faite).

## Leçons d'E464 effectivement utilisées
L1 échelle (S9) ; L2 la rencontre est un changement de pente, pas un saut, dans le signal recomposé sans reste (S7, S8) ; L3 aucun
seuil numérique annoncé, jumeau sur identités exactes seulement.
