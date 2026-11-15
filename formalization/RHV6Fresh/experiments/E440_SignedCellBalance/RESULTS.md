# E440 — Résultats : le bilan signé des cellules le long de la série

Exécutée le 2026-11-07 après pré-enregistrement (commit f0b83fdf). Module isolé
`RHV6Fresh/Terminal/SignedCellBalance.lean`. Sonde non versionnée : une passe (`logs/probe_attempt1.txt`, EXIT=0, un
avertissement de variable inutilisée corrigé), supprimée après capture. Module définitif : **une seule tentative**
(`logs/lean_attempt1.txt`, EXIT=0), quatorze énoncés, axiomes standards. Build complet :
`logs/lake_build_full_trimmed.txt`.

| # | Énoncé | Statut |
|---|--------|--------|
| B1 | `cellDemand_eq` : pente = poids franchis − longueur | compilé |
| B2 | `cellLength_pos`, `cellLength_mono` | compilé |
| B3 | `inner_cell_demand_le`, `cellDemand_eq_neg_length_of_no_weight`, `cellDemand_neg_of_no_weight` | compilé |
| B4 | `signedCellSum_eq` | compilé |
| B5 | `signed_lengths_bounded`, `signedCellSum_near_signed_weights` | compilé |
| B6 | `cellWeight_eq_prime_add_nonprime`, `cellPrimeWeight_inner_eq_zero`, `cellPrimeWeight_meeting`, `meeting_cellDemand` | compilé |
| B7 | `meeting_cell_demand_nonneg_of_short` | compilé |

## En mots
Chaque cellule a une pente : poids des entiers franchis moins sa longueur. Les longueurs sont positives et croissent
avec l'indice. Une cellule intérieure à un écart ne porte aucun poids premier ; sans aucun poids, elle descend
strictement. La somme signée des pentes de cellules consécutives est la somme signée des poids moins la somme signée
des longueurs, et cette dernière est bornée par la dernière cellule : **la descente s'annule par alternance à une
cellule près, et ce qui reste de la somme signée est, à une cellule près, la somme signée des poids**, dont le poids
premier n'est porté que par les cellules de rencontre, chacune avec son signe. La cellule de rencontre monte dès
qu'elle est plus courte que le poids de la rencontre.

## Verdict : B
Tout compile ; rien n'est déclaré manquant ; aucune hypothèse, aucune famille, aucune position radiale.
