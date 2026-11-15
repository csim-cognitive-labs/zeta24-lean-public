# E439 — Résultats : le signe de la cellule de rencontre le long d'une série d'écarts

Exécutée le 2026-11-07 après pré-enregistrement (commit e1774249). Module isolé
`RHV6Fresh/Terminal/MeetingCellSigns.lean` (non importé par `RHV6Fresh.lean`). Sonde non versionnée : deux passes
(`logs/probe_attempt1.txt` : trois erreurs — une monotonie mal typée, un omega, une réécriture qui touchait aussi
l'exposant ; `logs/probe_attempt2.txt` : EXIT=0), supprimée après capture. Module définitif : **une seule tentative**
(`logs/lean_attempt1.txt`, EXIT=0), seize énoncés, axiomes standards. Build complet :
`logs/lake_build_full_trimmed.txt` (« Build completed successfully (9064 jobs) »).

## Tableau

| # | Énoncé | Statut |
|---|--------|--------|
| S1 | `contactRealValue_eq_sign_mul`, `contactRealValue_sign_shift` | compilé |
| S2 | `meetingCell_eq_next_lower` : la cellule de rencontre de l'écart n ouvre l'écart n+1 | compilé |
| S3 | `lastContactBefore_mono`, `meetingCell_step`, `meetingCell_eq_of_no_contact` | compilé |
| S4 | `meeting_sign_step`, `meeting_sign_same_of_no_contact` | compilé |
| S5 | `meetingCell_telescope`, `meetingCell_mono_rank`, `meeting_sign_series`, `meetingCell_series_read_by_frequency` | compilé |
| S6 | `inner_cell_variation`, `meeting_cell_primes`, `meeting_cell_demand`, `meeting_cell_demand_ge` | compilé |

## En mots
La cellule qui contient une rencontre est la cellule qui ouvre l'écart suivant : le signe se transmet. D'une rencontre
à la suivante, l'indice de cellule avance du nombre de contacts franchis (cellules entières plus un) si l'écart contient
un contact, et ne bouge pas sinon (les deux rencontres partagent alors la cellule). Le signe de la cellule de rencontre
change donc selon la parité du nombre de contacts franchis ; sur une série, le signe au rang n+J est celui du rang n
fois la parité du déplacement total, et ce déplacement est lu à moins d'une unité près par la fréquence fois le
logarithme du rapport des deux rencontres. Toute cellule entière strictement intérieure à un écart est une descente
pure (poids non premiers seulement). La cellule de rencontre, recomposée par le reste final de l'écart et le reste
initial du suivant, franchit exactement un premier : sa pente est le poids de la rencontre, plus des poids non
premiers, moins sa longueur.

## Non-circularité
Aucune hypothèse, aucune famille, aucune somme de contributions, aucune position radiale. Les hypothèses des énoncés
S6 (chaque écart contient un contact ; dernier contact strictement avant la rencontre) excluent seulement le dépôt en
ligne (au plus une fois sur la série, §19.46) et les écarts plus courts qu'une cellule, traités par
`meetingCell_eq_of_no_contact`.

## Verdict : B
Tout compile ; rien n'est déclaré manquant.
