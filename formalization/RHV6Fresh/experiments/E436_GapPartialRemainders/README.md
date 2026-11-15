# E436 — Restes partiels d'écart aux contacts : la part d'une Tour sur un écart découpée par ses propres contacts (2026-11-06)

Expérience de compilation seule (aucune mesure numérique ; aucun jumeau requis). Plan de redressement §19.51, étapes 1 à 4.
Cadre (auteur, 2026-11-06) : les intervalles définis par les contacts d'une Tour sont des RESTES PARTIELS des écarts des
premiers ; ils appartiennent à la reconstitution collective des écarts et ne sont pas liés directement aux premiers.

## Vérification écrite des neuf points (CLAUDE.md, liste des erreurs)
(1) la synchronisation (`all_signals_meet`) n'est pas mise en cause ; (2) aucun « critère échoué » sur la structure ;
(3) rien n'est lu sur un signal mélangé : chaque part est l'incrément du terme lissé du membre entre les deux bornes de
l'écart ; (4) aucune définition demandée à l'auteur ; (5) aucun mot prêté ; (6) action livrée (module, commit) ; (7) la
paire est traitée comme somme de deux parts à la même fréquence, et la cible porte sur la somme de toutes les parts ;
(8) les écarts ne sont jamais liés à la hauteur ; (9) aucune Tour ne « touche » un premier : les contacts découpent la
part de la Tour sur l'écart, les bornes de l'écart sont les premiers, les deux morceaux de bord sont des fractions de cellule.

## Question posée (avant toute compilation)
Comment la part exacte d'une Tour sur un écart (`smoothedLocalContribution`) se décompose-t-elle sur les cellules de
contact de cette Tour, et que devient cette décomposition (a) pour deux membres de même fréquence, (b) sur une série
d'écarts consécutifs, (c) face à la reconstitution collective et à la prémisse unique en fréquence ?

## Hypothèses admises
Aucune. Les sondes S4 posent un porteur `C : OffCarrier` et le gel compilé (`outgoing_same_height`) seulement.

## Acquis réutilisés (forme Lean vérifiée avant usage)
`accumulationFrom`, `contact_accumulation_eq_endpoint_difference`, `contactAccumulation`, `contactVariation`,
`contact_partition_exact`, `contactAt_eq`, `contactAt_ratio`, `lastContactBefore`, `cellFraction`, `lastContact_le`,
`lt_contact_succ`, `log_div_lastContact`, `height_mul_log_eq`, `stagePosition`, `residueTerm_gap_eq`,
`smoothedLocalContribution`, `localArithmeticTarget`, `all_signals_meet`, `imposedShare_eq`, `meetingPoint`,
`contactAt_eq_contactMinusAt`, `contact_eq_line_mul_radial`, `mirror_contacts_coincide_iff`, `outgoing_same_height`,
`ExpectedFrequencyRisesAtMeetings`, `expectedFrequency_iff_no_shared_frequency`. Aucune démonstration refaite.

## Protocole
1. Pré-enregistrer (ce fichier, commit) avant la première compilation.
2. Sondes TDD dans `GapPartialRemainders_SCRATCH.lean` (non versionné, supprimé après capture ; sorties exactes dans
   `logs/probe_attempt*.txt`).
3. Module isolé `Terminal/GapPartialRemainders.lean` (non ajouté à `RHV6Fresh.lean`), deux tentatives au plus
   (`logs/lean_attempt{1,2}.txt`), aucune hypothèse posée, aucun `sorry`, axiomes affichés ; `lake build RHV6Fresh` vert.

## Sondes prévues et attendus (écrits avant exécution)
- **S1 — Découpage.** Part d'une Tour `(β, T)` sur un écart = reste partiel initial (de `p_n` au premier contact dans
  l'écart) + cellules entières + reste partiel final (du dernier contact à `p_{n+1}`), dès que l'écart contient un
  contact ; sinon la part est un seul reste partiel, de longueur logarithmique < π/T. Chaque reste de bord couvre une
  fraction de cellule lue par `cellFraction` aux bornes. Attendu : compile par `accumulationFrom` et `log_div_lastContact`.
- **S2 — Fréquence partagée.** Deux Tours de même fréquence ont des positions d'étage décalées d'une constante (part
  radiale seule) ; leurs nombres de contacts dans tout écart diffèrent d'au plus un. Attendu : compile par `Int.floor`.
- **S3 — Série d'écarts.** Les deux restes partiels de part et d'autre d'un point de rencontre recomposent exactement une
  cellule de la Tour ; sur `J` écarts consécutifs, la somme des parts est cellules entières + deux restes de bord.
  Attendu : compile par télescopage.
- **S4 — Cible.** Depuis la reconstitution collective sur chaque écart, S1–S3 et le gel du porteur, tenter la prémisse
  unique en fréquence (`ExpectedFrequencyRisesAtMeetings`) puis `False`. Attendu (écrit avant exécution) : but laissé ;
  reproduit intégralement, sans être renommé « ce qui manque ».

## Critères (une seule catégorie)
A fermeture compilée ; B réduction inconditionnelle nouvelle (la part d'une Tour sur un écart et sur une série lue
entièrement en restes partiels de cellule, compilée) ; C équivalence à RH compilée ; D rien de compilable. Attendu : B.

## Addendum avant toute compilation (2026-11-06, second message de l'auteur)
La somme infinie n'est pas un appui et ne comble aucun écart ; aucun retour à l'analyse spectrale. `all_signals_meet`
et `imposedShare_eq` sont retirés de la liste des acquis utilisés. Objets : contact `contactAt`, valeur au contact
`contactRealValue`, contribution de cellule brute `towerValue ρ p_{n+1} − towerValue ρ p_n` (et sa partie réelle
`towerRe`), bilan au point de rencontre avec reste explicite pour une famille finie `breakResidual`, `breakResidual_erase`.
Sondes reposées : S1 découpage de la contribution de cellule brute par les contacts de la Tour (restes de bord = fractions
de cellule) ; S2 fréquence partagée (nombre de contacts dans tout écart : différence ≤ 1) ; S3 série (les restes de part
et d'autre d'un point de rencontre recomposent une cellule) ; S4 bilan avec reste pour la famille finie contenant la paire,
valeurs aux contacts du miroir en `C_k^{1/2+δ}` (`contactRealValue`), tentative de `False` ; attendu : but laissé,
reproduit intégralement. Critère attendu : B (découpage et série compilés en canal brut).
