# E439 — Le signe de la cellule qui contient la rencontre, le long d'une série d'écarts

Pré-enregistrement (2026-11-07), avant toute compilation. Ordre de l'auteur : « continues oui » après E438 (§19.56) ;
interdiction spectrale en vigueur (CLAUDE.md « INTERDICTION SPECTRALE », §19.55).

## Vérification des neuf erreurs
1. Aucune hypothèse nouvelle. 2. Le compilateur décide. 3. Noms vérifiés par grep (`meetingCell`, `cellSign`,
`lastContactBefore_mono`, `contactRealValue_sign_shift` libres ; `lastContactBefore`, `wholeCellCount`,
`firstContact_add_count`, `contactRealValue_add_nat`, `rawDemand_variation`, `no_prime_crossed_inside_gap`,
`lastContact_difference_bounds`, `thm_noPrimeStrictlyBetweenSuccessivePrimes` réutilisés). 4. `lake build RHV6Fresh`
après tout changement. 5. Aucun premier ni OFF testé directement. 6. Aucune position radiale. 7. Aucune famille de
Tours, aucune somme de contributions : UNE Tour, SES contacts, les cellules, leurs signes, la série des écarts.
8. Module isolé, non ajouté à `RHV6Fresh.lean`. 9. Les intervalles de contacts sont des restes partiels d'écart.

## Question
Chaque rencontre `p_{n+1}` est dans la cellule ouverte par le dernier contact avant elle (E438). Quel est le signe de
cette cellule le long de la série des écarts, comment la parité se transmet-elle d'une rencontre à la suivante, et que
les restes partiels de part et d'autre d'une rencontre imposent-ils à la pente de cette cellule ?

## Objets
Nouveaux (définitions seulement) : `meetingCell β T I = lastContactBefore β T I.upper` (indice de la cellule qui
contient la rencontre), `cellSign k = (−1)^k`. Tous les autres existent.

## Énoncés visés (module isolé `Terminal/MeetingCellSigns.lean`)
- S1 `contactRealValue_eq_sign_mul`, `contactRealValue_sign_shift` : la valeur au contact porte le signe `(−1)^k` ; le
  contact `m` rangs plus loin a le signe multiplié par `(−1)^m`.
- S2 `meetingCell_eq_next_lower` : la cellule de la rencontre de l'écart `n` est la cellule qui ouvre l'écart `n+1`
  (le signe se transmet à l'écart suivant).
- S3 `lastContactBefore_mono`, `meetingCell_step` : si l'écart `n+1` contient un contact, l'indice de la cellule de
  rencontre avance du nombre de contacts franchis (cellules entières + 1) ; `meetingCell_eq_of_no_contact` : sinon les
  deux rencontres sont dans la même cellule.
- S4 `meeting_sign_step` : le signe de la cellule de rencontre change selon la parité (cellules entières + 1) de
  l'écart franchi ; `meeting_sign_same_of_no_contact`.
- S5 `meetingCell_telescope`, `meeting_sign_series`, `meetingCell_series_read_by_frequency` : sur une série, le
  déplacement de l'indice télescope, le signe est la parité du déplacement total, et ce déplacement est lu par la
  fréquence et le rapport des deux rencontres à moins d'une unité près.
- S6 `inner_cell_variation` : toute cellule entière strictement intérieure à un écart est une descente pure (poids
  non premiers seulement) ; `meeting_cell_demand` : la cellule de rencontre, recomposée par le reste final de l'écart
  et le reste initial du suivant, porte exactement UN poids premier, celui de la rencontre, plus des poids non
  premiers, moins sa longueur ; `meeting_cell_demand_ge`.

## Protocole et critères
Sonde `*_SCRATCH.lean` non versionnée, deux tentatives au plus pour le module définitif, journaux dans `logs/`,
`#print axioms`, puis build complet. A : contradiction avec un fait compilé ; B : tout compile, rien déclaré manquant ;
C : un énoncé ne compile pas en deux tentatives. Attendu : B.
