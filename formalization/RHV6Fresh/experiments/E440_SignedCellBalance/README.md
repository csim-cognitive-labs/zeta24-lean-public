# E440 — Le bilan signé des cellules le long de la série : la descente s'annule à une cellule près, les poids des rencontres restent avec leur signe

Pré-enregistrement (2026-11-07), avant toute compilation. Ordre de l'auteur : « OUI CONTINUES. FEU VERT. CONTINUE LA
MÊME DÉMARCHE » après E439 (§19.57). Interdiction spectrale en vigueur (§19.55).

## Vérification des neuf erreurs
1. Aucune hypothèse nouvelle. 2. Le compilateur décide. 3. Noms vérifiés par grep (`cellDemand`, `cellWeight`,
`cellPrimeWeight`, `signedCellSum`, `cellLength` libres ; `rawDemand_variation`, `cell_linear_length`,
`signed_cells_bounded_by_last`, `no_prime_crossed_inside_gap`, `meeting_cell_primes`, `meetingCell` réutilisés).
4. `lake build RHV6Fresh` après tout changement. 5. Aucun premier ni OFF testé directement. 6. Aucune position
radiale. 7. Aucune famille de Tours, aucune somme de contributions. 8. Module isolé. 9. Intervalles = restes partiels.

## Question
Chaque cellule porte un signe `(−1)^k` et une pente (poids franchis − longueur). Que vaut la somme SIGNÉE des pentes
des cellules consécutives le long de la série ? La descente, dont les longueurs croissent, s'annule-t-elle par
alternance ? Que reste-t-il : les poids des rencontres avec le signe de leur cellule ?

## Énoncés visés (module isolé `Terminal/SignedCellBalance.lean`)
- B1 `cellDemand`, `cellLength`, `cellWeight`, `cellDemand_eq` : pente d'une cellule = poids franchis − longueur.
- B2 `cellLength_nonneg`, `cellLength_mono` : longueurs positives et croissantes avec l'indice.
- B3 `inner_cell_demand_le`, `cellDemand_eq_neg_length_of_no_weight` : une cellule intérieure à un écart a une pente
  au plus égale aux poids non premiers moins sa longueur ; sans poids, descente pure strictement négative.
- B4 `signedCellSum`, `signedCellSum_eq` : somme signée des pentes = somme signée des poids − somme signée des longueurs.
- B5 `signed_lengths_bounded`, `signedCellSum_near_signed_weights` : la somme signée des longueurs est bornée par la
  dernière cellule ; la somme signée des pentes est à une cellule près la somme signée des poids.
- B6 `cellPrimeWeight`, `cellWeight_eq_prime_add_nonprime`, `cellPrimeWeight_inner_eq_zero`,
  `cellPrimeWeight_meeting` : le poids d'une cellule se sépare en poids premier et poids non premier ; nul en poids
  premier sur une cellule intérieure ; égal à `log p_{n+1}` sur la cellule de rencontre.
- B7 `meeting_cell_demand_nonneg_of_short` : la cellule de rencontre monte dès qu'elle est plus courte que le poids
  de la rencontre.

## Protocole et critères
Sonde non versionnée, deux tentatives au plus pour le module définitif, journaux, `#print axioms`, build complet.
A : contradiction ; B : tout compile ; C : échec en deux tentatives. Attendu : B.
