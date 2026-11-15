> Version française conservée à titre de référence. Main language: English, see README.md.

# E443 — Les écarts au-dessus du seuil : ce que les contacts et leurs signes seuls en disent

Pré-enregistrement (2026-11-07), avant toute compilation et toute exécution. Suite d'E442 (§19.61), sous l'ordre
« poursuis le plus possible ». Interdiction spectrale en vigueur (§19.55) ; ordre de travail §19.53.

## Vérification des neuf erreurs
1. Aucune hypothèse nouvelle (Bertrand et les bornes de Tchebychev `ψ − θ ≤ 2√x log x` sont des théorèmes de
   Mathlib / du corpus, aucune asymptotique, aucun PNT, aucune théorie spectrale). 2. Le compilateur décide. 3. Noms
   vérifiés par grep (`primeSuccessor_le_two_mul` réutilisé de `ContinuousProgression` ; `gap_le_lower`,
   `wholeCellCount_lt_log_two`, `meetingCell_displacement_lt`, `gap_in_cell_of_no_contact`, `gap_demand_variation`,
   `gap_primes_singleton`, `cellNonPrimeWeight_le_sqrt`, `meeting_falls_above_second_threshold` libres). 4. `lake
   build RHV6Fresh` après tout changement. 5. Aucun premier ni OFF testé directement. 6. Aucune position radiale.
   7. Aucune famille. 8. Module isolé. 9. Intervalles = restes partiels.

## Question
Au-dessus du seuil `x*` d'une Tour (`x*(r−1) = log x*`), ses cellules sont plus longues que les poids des
rencontres ; la plupart des écarts n'ont plus de contact et tiennent dans une seule cellule signée. Que disent
alors les contacts, les intervalles et leurs signes : combien de contacts au plus par écart (Bertrand), où tient
un écart sans contact, quelle est la pente d'un écart entier, et à partir de quelle hauteur (second seuil `x**`)
toute cellule de rencontre descend sûrement, le poids non premier étant borné par Tchebychev.

## Énoncés visés (module isolé `Terminal/GapsAboveThreshold.lean`, importe `ExactDisplacementAndThreshold` et `ContinuousProgression`)
- A1 `gap_le_lower`, `upper_le_two_lower` : Bertrand sur l'écart (`p_{n+1} − p_n ≤ p_n`).
- A2 `wholeCellCount_lt_log_two` : moins de `T log 2/π` cellules entières dans tout écart.
- A3 `meetingCell_displacement_lt` : le déplacement de la cellule de rencontre entre deux écarts consécutifs est
  `< T log 2/π + 1`.
- A4 `gap_in_cell_of_no_contact` : un écart sans contact tient dans la cellule de sa rencontre.
- A5 `gap_primes_singleton`, `gap_demand_variation` : la pente d'un écart entier = `log p_{n+1}` + poids non
  premiers − longueur de l'écart (aucune hypothèse de contact).
- A6 `cellNonPrimeWeight_le_sqrt` : poids non premier d'une cellule `≤ 2√C_{k+1} log C_{k+1}` (Tchebychev,
  Mathlib `psi_sub_theta_le`).
- A7 `meeting_falls_above_second_threshold` : si `log p + 2√(p r) log(p r) < p(1 − 1/r)`, la cellule de
  rencontre descend (condition en `p` et `T` seuls).

## Expérience chiffrée (`scripts/e443a_above_threshold.py`, jumeau `scripts/e443b_twin_mpmath.py`)
Tours de rangs 1, 100, 10³, 10⁴, 10⁵ (β = ½), premiers ≤ 10⁶, Λ exact. Contrôles (0 violation attendue) : A1–A7.
Mesures : part des écarts avec contact par décade contre la règle `moyenne(min(1, g/L))` ; second seuil `x**`
(résolu) contre le plus petit `p` au-delà duquel toute cellule de rencontre descend ; entre `x*` et `x**`, part
des cellules de rencontre qui descendent ; premiers par cellule contre `L/log p` ; part des cellules de pente
positive au-dessus de `x*` (mesure sans théorème, étiquetée comme telle).

## Protocole et critères
Sonde non versionnée, deux tentatives au plus pour le module définitif, journaux, `#print axioms`, build complet ;
scripts bornés (< 10 min), `nohup`, aucune sortie fabriquée. A : contradiction ; B : tout compile et 0 violation ;
C : échec en deux tentatives. Attendu : B.
