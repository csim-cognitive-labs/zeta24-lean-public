# E443 — Résultats (exécutée 2026-11-07, après le pré-enregistrement 4522c8d1)

Pièces : `logs/probe_attempt{1,2,3}.txt` (sonde : positivité d'un quotient, côté d'une multiplication, argument
implicite), `logs/lean_attempt1.txt` (module définitif, EXIT=0, **une seule tentative**, 12 `#print axioms`
standards), `logs/lake_build_full_trimmed.txt` (« Build completed successfully (9064 jobs) »), `logs/e443a_log.txt`,
`logs/e443a.stdout`, `data/e443a_results.json` (expérience, 1 s), `logs/e443b_log.txt`, `data/e443b_twin.json`
(jumeau mpmath : seuils `x*`, `x**` à 10⁻¹² relatif). Aucune sortie fabriquée. Une correction de script avant la
course définitive, consignée : l'indexation « les deux écarts voisins ont un contact » était décalée d'un rang (la
première course comptait des cellules à deux rencontres comme cellules de rencontre) ; la course définitive est
celle rapportée ici.

## Module `Terminal/GapsAboveThreshold.lean` (isolé, 12 énoncés)
| bloc | énoncés | contenu |
|---|---|---|
| A1 | `upper_le_two_lower`, `gap_le_lower` | Bertrand sur l'écart (réutilise `primeSuccessor_le_two_mul`) |
| A2–A3 | `log_ratio_le_log_two`, `wholeCellCount_lt_log_two`, `meetingCell_displacement_lt` | moins de `T log 2/π` cellules entières par écart ; déplacement de la cellule de rencontre `< T log 2/π + 1` |
| A4 | `gap_in_cell_of_no_contact` | un écart sans contact tient dans la cellule (signée) de sa rencontre |
| A5 | `gap_primes_singleton`, `gap_demand_variation` | pente d'un écart entier = `log p_{n+1}` + poids non premiers − longueur, sans hypothèse de contact |
| A6 | `cellNonPrimeWeight_le_psi_sub_theta`, `cellNonPrimeWeight_le_sqrt` | poids non premier d'une cellule `≤ 2√C_{k+1} log C_{k+1}` (Tchebychev, Mathlib) |
| A7 | `contact_succ_meeting_le`, `meeting_falls_above_second_threshold` | si `log p + 2√(pr) log(pr) < p(1 − 1/r)`, la cellule de rencontre descend |

## Contrôles compilés sur les données (5 Tours : rangs 1, 10², 10³, 10⁴, 10⁵ ; β = ½ ; 78 497 écarts ≤ 10⁶)
A1–A7 : **0 violation** pour les cinq Tours (Bertrand sur 78 497 écarts ; déplacement maximal 2 / 38 / 231 / 1 606 /
12 182 contre les bornes 4,1 / 53,2 / 314,2 / 2 180 / 16 531 ; A4 sur tous les écarts sans contact ; A5 sur tous les
écarts ; A6 sur toutes les cellules, rapport au plus 0,125 de la borne, moyenne au plus 0,012 (rang 1) et inférieure à 10⁻³ ensuite ; A7 : aucune
rencontre ≤ 10⁶ n'est au-delà de `x**`, zone vide, 0 violation par construction). Seuils (mpmath) :
`x*` = 8,68 / 458,3 / 3 709 / 32 677 / 300 819 ; `x**` = 1,16·10⁴ / 5,64·10⁶ / 3,14·10⁸ / 2,25·10¹⁰ / 1,81·10¹².

## Règles lues des journaux
**R6 — entre `x*` et `x**`, les cellules de rencontre descendent sauf appui d'une puissance de premier (mesure
rattachée à A6–A7).** Sur les cellules de rencontre dont les deux écarts voisins ont un contact et dont la rencontre
est au-dessus de `x*` : part descendante 1,000 (rang 10², 37 cellules), 0,978 (10³, 178), 0,998 (10⁴, 1 270), 0,9993
(10⁵, 8 769) ; sous `x*` : 0 descente (cohérent R4). Les rares cellules de rencontre qui montent au-dessus de `x*`
contiennent une puissance de premier : plus grand `p` non descendant 5 333 (cellule contenant 73² = 5 329) au rang
10³, 49 727 au rang 10⁴, 466 483 (cellule contenant 683² = 466 489) au rang 10⁵. La borne de Tchebychev A6 est
lâche d'un facteur ≥ 8 : `x**` est très au-delà de la hauteur réelle où toute montée cesse.

**R7 — part des écarts avec contact (mesure, aucun théorème).** Par décade de `p_n`, la part des écarts contenant un
contact coïncide avec la moyenne de `min(1, écart/longueur de la cellule de p_n)` à 1 % près (par exemple rang 10³ :
0,644 contre 0,642 pour `p_n ∈ [10⁴, 10⁵)`, 0,124 contre 0,124, 0,0151 contre 0,0151) : sous `x*` tous les écarts ont
un contact, au-dessus la part décroît comme `T log p/(π p)`.

**R8 — ce que les cellules voient au-dessus de `x*` (mesure, aucun théorème ; non utilisé dans la route).** Premiers
par cellule = `L/log C` à 0,1–1 % près (1 342 / 135 / 31 / 7,0 / 1,83) ; part des cellules de pente positive 0,45–0,49
; |pente|/longueur moyenne 0,07 / 0,14 / 0,21 / 0,31 / 0,50 (croît quand les cellules ne contiennent plus qu'un ou
deux premiers).

## Lecture (contacts, intervalles, signes)
Au-dessus de `x*`, un écart n'a plus, le plus souvent, aucun contact : il tient tout entier dans une cellule signée,
et sa pente, écrite sans aucune hypothèse de contact, est son poids de rencontre plus ses puissances de premiers
moins sa longueur. Quand il a un contact, la cellule de rencontre descend sûrement dès que le poids de la rencontre
et la borne de Tchebychev des puissances de premiers restent sous la longueur de la cellule ; en pratique dès `x*`
sauf appui d'une puissance de premier. Le nombre de contacts par écart, et le déplacement de la cellule de rencontre,
restent bornés par la fréquence seule (Bertrand).

## Verdict
**B** : tout compile en une tentative, build complet vert, 0 violation. Rien n'est déclaré manquant. R7 et R8 sont des
mesures sans théorème, étiquetées, non réinjectées dans la route.
