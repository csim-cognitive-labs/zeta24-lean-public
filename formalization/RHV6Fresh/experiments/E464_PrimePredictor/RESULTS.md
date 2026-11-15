# E464 — résultats (2026-11-09) — verdict C au sens littéral du pré-enregistrement, loi d'échelle confirmée

Exécution réelle : `logs/run.txt` (365,8 s), `results.json`. Méthode et seuil exactement ceux du pré-enregistrement ; aucun réglage après coup.

| Tours | début | cellule de la Tour la plus haute | premiers vrais | prédits | justes | manqués | faux | saut min sur premiers | saut max hors premiers |
|---|---|---|---|---|---|---|---|---|---|
| 2 001 052 | 10^3 | 0,003 | 43 | 43 | 43 | 0 | 0 | 0,999 | 0,100 |
| 2 001 052 | 10^4 | 0,028 | 33 | 33 | 33 | 0 | 0 | 0,989 | 0,494 |
| 2 001 052 | 10^5 | 0,277 | 23 | 23 | 23 | 0 | 0 | 0,902 | 0,063 |
| 2 001 052 | 2·10^5 | 0,555 | 25 | 0 | 0 | 25 | 0 | 0,730 | 0,104 |
| 2 001 052 | 3·10^5 | 0,832 | 22 | 0 | 0 | 22 | 0 | 0,546 | 0,359 |
| 2 001 052 | 5·10^5 | 1,387 | 25 | 0 | 0 | 25 | 0 | 0,349 | 0,467 |
| 2 001 052 | 10^6 | 2,774 | 24 | 0 | 0 | 24 | 0 | 0,181 | 0,329 |
| 2 001 052 | 10^7 | 27,7 | 14 | 0 | 0 | 14 | 0 | 0,033 | 0,086 |
| 2 001 052 | 10^8 | 277 | 17 | 0 | 0 | 17 | 0 | 0,049 | 0,054 |
| 500 000 | 10^3 | 0,010 | 43 | 43 | 43 | 0 | 0 | 0,995 | 0,100 |
| 500 000 | 10^4 | 0,098 | 33 | 33 | 33 | 0 | 0 | 0,959 | 0,480 |
| 500 000 | 10^5 | 0,984 | 23 | 0 | 0 | 23 | 0 | 0,474 | 0,419 |
| 500 000 | 2·10^5 | 1,967 | 25 | 0 | 0 | 25 | 0 | 0,251 | 0,233 |
| 500 000 | 3·10^5 | 2,951 | 22 | 0 | 0 | 22 | 0 | 0,171 | 0,313 |
| 500 000 | 5·10^5 | 4,918 | 25 | 0 | 0 | 25 | 0 | 0,104 | 0,300 |
| 500 000 | 10^6 | 9,836 | 24 | 0 | 0 | 24 | 0 | 0,056 | 0,158 |
| 500 000 | 10^7 | 98,4 | 14 | 0 | 0 | 14 | 0 | 0,044 | 0,059 |
| 500 000 | 10^8 | 984 | 17 | 0 | 0 | 17 | 0 | 0,053 | 0,053 |

(Sauts exprimés en fraction de `log n`. Le 0,49 hors premiers à 10^4 est un carré de premier, comme prévu.)

## Lecture
* Le prédicteur EXISTE et est exact : 198 premiers prédits sur 198, aucun faux, dans les 5 fenêtres où la cellule de la Tour la plus
  haute est au plus 0,28 pas d'entier (jusqu'à 10^5 avec 2 millions de Tours, jusqu'à 10^4 avec 500 000). Contrôle fait à la fin seulement.
* Verdict littéral C : j'avais annoncé un horizon à cellule ≈ 1 (hauteur max / π). La fenêtre 2·10^5 (cellule 0,555) est sous cet
  horizon et la règle pré-écrite y manque tout (saut 0,73 pour un seuil de 0,75). Mon horizon annoncé était trop optimiste d'un facteur
  2 à 3. Aucune fenêtre n'a été mesurée entre cellule 0,28 et 0,55 : l'horizon réel de la règle est dans cet intervalle.
* La variable de la loi d'échelle est bien la cellule : dans les deux familles, la séparation premiers / non-premiers tient encore à
  cellule 0,55–0,83 (0,73 contre 0,10 ; 0,55 contre 0,36) et disparaît dès cellule ≈ 1 (0,47 contre 0,42 ; 0,35 contre 0,47). L'horizon
  est proportionnel à la hauteur maximale : quatre fois moins de Tours en hauteur, horizon divisé d'autant.
* Au-delà (10^6 à 10^8) : aucun premier prédit, aucune séparation. Les Tours disponibles ne distinguent plus deux entiers voisins.

## Le million de chiffres
Pour séparer deux entiers voisins près de `x`, il faut des Tours de hauteur plusieurs fois `x`. Près de `10^(10^6)`, cela demande un
nombre de zéros qui a lui-même environ un million de chiffres : impossible, et sans rapport avec la puissance de calcul. Contrôler les
30 derniers chiffres ne vérifie rien : la primalité dépend du nombre entier. Les grands premiers connus viennent de formes spéciales
avec un test dédié, pas d'une prédiction. Cette voie ne mène pas à un premier d'un million de chiffres.

## Limites
Fenêtres de 300 entiers ; zéros tous sur la ligne dans cette plage ; poids de Fejér fixés ; aucune fenêtre entre cellule 0,28 et 0,55.
