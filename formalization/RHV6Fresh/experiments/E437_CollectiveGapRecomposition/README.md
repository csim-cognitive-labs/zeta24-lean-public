# E437 — Recomposition collective d'un écart par les restes partiels de plusieurs Tours, canal brut (2026-11-07)

Expérience de compilation seule (aucune mesure numérique). Ordre de l'auteur (§19.53) : connaissance et maîtrise des
écarts et des contacts AVANT toute chasse radiale. Aucune position radiale n'entre dans une conclusion ; aucun zéro OFF ;
aucune somme infinie ; aucun retour à l'analyse spectrale.

## Vérification écrite des neuf points (CLAUDE.md)
(1) rien sur la synchronisation ; (2) aucun critère sur la structure ; (3) rien lu sur un signal mélangé : chaque part
est la variation de la Tour entre les deux bornes de l'écart ; (4) aucune définition demandée ; (5) aucun mot prêté ;
(6) action livrée ; (7) aucune paire traitée ; (8) écarts jamais liés à la hauteur ; (9) aucune Tour ne touche un premier :
les bornes de l'écart sont les premiers, les contacts découpent la part de chaque Tour.

## Question posée (avant compilation)
Dans le canal brut (demande `ψ(x) − x` sur l'axe réel), comment une famille FINIE de Tours recompose-t-elle un écart par
les restes partiels de chacune, que porte le reste explicite, et comment le bilan passe-t-il à l'écart suivant ? Et, point
de l'auteur : le reste est-il nécessaire (une famille finie peut-elle recomposer l'écart seule) ?

## Hypothèses admises
Aucune.

## Acquis réutilisés (forme Lean vérifiée avant usage)
`Chebyshev.psi` (Mathlib), `massA`, `massA_succ`, `massA_eq_psi`, `psiRemainder`, `towerRe`, `breakResidual`,
`breakResidual_erase`, `PrimeGapInterval` (`lower`, `upper`, `one_lt_lower`, `lower_lt_upper`), `meetingPoint`,
`thm_primeAtRank_isPrime`, `GapHasContact`, `gap_variation_eq_remainders`, `initialEdgeRemainder`, `wholeCellSum`,
`finalEdgeRemainder`, `consecutive_lower_eq_upper`, `ArithmeticFunction.vonMangoldt_apply_prime`.

## Protocole
1. Pré-enregistrement (ce fichier, commit) avant toute compilation.
2. Sondes de noms dans `CollectiveGapRecomposition_SCRATCH.lean` (non versionné, supprimé après capture ; sorties dans
   `logs/probe_attempt*.txt`).
3. Module isolé `Terminal/CollectiveGapRecomposition.lean` (non ajouté à `RHV6Fresh.lean`), deux tentatives au plus,
   journalisées (`logs/lean_attempt{1,2}.txt`), aucun `sorry`, axiomes affichés, `lake build RHV6Fresh` vert.

## Énoncés visés et attendus (écrits avant exécution)
- **R1 Recomposition collective.** Pour une famille finie dont chaque membre a un contact dans l'écart, la somme des
  parts = somme sur les membres de (reste partiel initial + cellules entières + reste partiel final). Attendu : compile
  (somme de `gap_variation_eq_remainders`).
- **R2 Bilan d'un écart avec reste explicite.** Demande de l'écart = parts de la famille + variation du reste explicite
  sur l'écart. Attendu : identité, compile.
- **R3 Passage à l'écart suivant.** Sur une série d'écarts, les variations du reste et les demandes télescopent.
  Attendu : compile.
- **R4 Descente entre rencontres.** Entre deux entiers consécutifs la demande brute descend linéairement ; au passage
  de l'entier elle saute du poids de l'entier. Attendu : compile (`massA_succ`, plancher).
- **R5 Continuité de la famille.** Toute famille finie de Tours est continue en toute abscisse positive. Attendu : compile.
- **R6 Le reste porte le saut.** Pour toute famille finie, la variation du reste explicite au passage d'une rencontre
  tend vers le poids du premier (tout le saut). Attendu : compile.
- **R7 Aucune famille finie ne recompose la rencontre.** Le reste explicite ne peut pas être constant à gauche d'un
  premier. Attendu : compile par R6 (unicité de la limite, poids d'un premier > 0).
Si R6/R7 échouent, buts reproduits intégralement, jamais renommés « ce qui manque ».

## Critères
A fermeture compilée ; B réduction inconditionnelle nouvelle (recomposition collective d'un écart par les restes partiels,
reste explicite portant tout le saut, compilés) ; C équivalence à RH ; D rien de compilable. Attendu : B.
