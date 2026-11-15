# E438 — Résultats : la pente de l'écart reconstituée par les contacts, les intervalles et leurs signes

Exécutée le 2026-11-07 après pré-enregistrement (commit 28fdbe35). Module isolé
`RHV6Fresh/Terminal/GapSlopeByContacts.lean` (non importé par `RHV6Fresh.lean`). Sonde non versionnée : trois passes
(`logs/probe_attempt1..3.txt` : une erreur omega sur le successeur de premier, un trou comblé par l'hypothèse « l'écart
contient un contact », une réécriture de signe et une positivité), supprimée après capture. Module définitif : **une
seule tentative** (`logs/lean_attempt1.txt`, EXIT=0), quinze énoncés, axiomes standards. Build complet :
`logs/lake_build_full_trimmed.txt` (« Build completed successfully (9064 jobs) »).

## Tableau

| # | Énoncé | Statut |
|---|--------|--------|
| R1 | `rawDemand_variation` : sur toute pièce, variation = poids des entiers franchis − longueur | compilé |
| R2 | `rawDemand_pure_descent` : sans poids franchi, descente pure | compilé |
| R3 | `gap_length_eq_pieces`, `gap_demand_eq_pieces` : longueur et demande de l'écart découpées par les mêmes contacts | compilé |
| R4 | `no_prime_crossed_inside_gap`, `inner_piece_variation` : aucune pièce intérieure ne franchit un premier | compilé |
| R4 | `finalRemainder_carries_meeting` : le poids de la rencontre est dans le reste final (dernier contact strictement avant la rencontre) | compilé |
| R5 | `contactRealValue_add_nat`, `gap_edge_contacts_sign` : signe du dernier contact = signe du premier × parité des cellules entières | compilé |
| R6 | `cell_linear_length`, `finalRemainder_shorter_than_cell`, `initialRemainder_shorter_than_cell` | compilé |
| R7 | `wholeCellCount_bounds` : nombre de cellules entières encadré par la fréquence et le rapport des bords | compilé |
| R8 | `alternating_sum_bounds`, `signed_cells_bounded_by_last` : somme signée des cellules bornée par la dernière | compilé |

## Ce que cela dit, en mots

La demande brute descend d'une unité par unité de longueur sur toute pièce et reçoit le poids de chaque entier franchi.
Les contacts d'une Tour découpent l'écart en reste initial, cellules entières, reste final ; la longueur et la demande
de l'écart se découpent par les mêmes contacts. Aucune pièce strictement intérieure à l'écart ne franchit un premier :
sur ces pièces la pente est la descente de leur longueur, corrigée seulement par des poids non premiers. Le poids de la
rencontre tombe dans le reste final, et seulement là. Les contacts qui bordent l'écart ont des signes liés par la
parité du nombre de cellules entières ; chaque cellule mesure son contact gauche fois un facteur fixé par la fréquence ;
les restes partiels sont plus courts que leur cellule ; le nombre de cellules entières est lu par la fréquence et le
rapport des bords ; la somme signée des longueurs de cellules consécutives a le signe de la dernière et ne dépasse pas
la dernière cellule.

## Non-circularité
Aucune hypothèse, aucune famille de Tours, aucune somme de contributions, aucun canal de zéros, aucune position
radiale. Seules dépendances : définitions de Tchebychev (Mathlib), contacts d'une Tour, restes partiels (E436), demande
brute (E437), absence de premier entre deux premiers consécutifs (grammaire).

## Verdict : B
Tout compile ; rien n'est déclaré manquant. L'hypothèse « dernier contact strictement avant la rencontre » est le
complémentaire du dépôt en ligne (vrai au plus une fois sur la série, §19.46) ; dans ce cas limite la rencontre est un
contact et le reste final est vide.
