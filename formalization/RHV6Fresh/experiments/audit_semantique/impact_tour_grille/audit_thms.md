# Impact du fait « la Tour est une grille infinie ; un zéro = un premier est une étiquette de rang » sur les théorèmes compilés

Date : 2026-10-01. Lecture seule : aucun fichier du dépôt n'a été modifié.
Fait nouveau : `RHV6Fresh/RHV6Fresh/Terminal/OneZeroOnePrime.lean` (`occurrence_is_rank_label`, `every_prime_in_every_tower`,
`tower_offset_rigid`, `onLine_iff_entry_at_point`, `onLine_iff_no_grid_translation`, `entry_arrow_point_irrelevant`).

## 1. Méthode

- Sources : `AUDIT_SEMANTIQUE_CUMULE_TOUS_REPERTOIRES.md` (Conclusions, §2, §5.1–5.4, §7, §8.7, §8.8, §8.16 lus en entier),
  `RHV6Fresh/AUDIT_DIFFERENCES_ON_OFF.md` (entier), jsonl de `RHV6Fresh/experiments/audit_semantique/data/` (commit 003f31fc).
- RHV6Fresh au code actuel : 742 théorèmes du jsonl, dont **214 retirés du code depuis 003f31fc** (148 dans les 13 fichiers
  du ménage du 2026-09-29, 66 prémisses et caractérisations retirées dans les fichiers conservés), **528 encore présents**,
  plus **473 théorèmes nouveaux** trouvés par grep `^theorem` (31 fichiers `Terminal/*` absents du jsonl : EntryPositionArrow,
  CanonicalTransition, ChangePredictor, PointedPrimeComparison, OneZeroOnePrime, EngagedClosureVerdict, SpontaneousRegimeBreak,
  PrimeWeightResponse, GrammarKinematics, PrimalEventRaccord, RegimeCell, RegimeTower, …). Total courant : 1001.
- Sélection (`select_thms.py`) : thèmes par regex sur nom, type ou fichier (Tower/tour, contact, cell, pivot, occurrence,
  expectedMinimum, raccord, countedPrime/lastPrime/reached, mirror, regime, translation, pitch, radial, changeResidue, entry,
  ledger, fibre/charge, terme d'Euler local). Priorité : RHV6Fresh entier sur les thèmes (818), rhv3_lean (396, sans
  `Certification/Solution.lean` qui rejoue `Challenge.lean`), puis 45 candidats S des autres bases (grappe T1), puis RHV5Fresh
  (41). Plafond atteint : 1300. rhv4_lean, rh_gap_criterion et le reste de rhv2_fresh/RHV5Fresh sont hors plafond (voir §4bis).
- Classement (`classify_thms.py`) : heuristique sur le type, puis décisions manuelles ; **les 289 énoncés RHV6Fresh qui
  mentionnent occurrence / M / pivot / expectedMinimum / countedPrime / reached ont été lus un par un** (liste dans
  `rhv6_manual_dump.txt`) ; les surcharges sont dans `MANUAL` du script. Les prédicats descriptifs (`PIsOffCriticalLine`,
  `PZeroMembersConsecutive`, `PZeroMemberPrecedes`, …) ne sont pas comptés comme prémisses.
- Classes : **G** invariant de grille (∀ q, ∀ k, ou aucun premier particulier) ; **E** évaluation en une étiquette
  (Occ, p_min, M, cellule choisie ; sous-classes E-Tour et E-grammaire = étiquette de rang pure) ; **S** Tour qui sélectionne un
  premier / cellule à un seul premier / Tour à deux contacts (sous-classes S-prémisse, S-structure, S-définition, S-nom,
  S-fenêtre) ; **R** caractérisation de régime ; **X** ⟺ RH ou sous prémisse non déchargée.
- Fichiers : `audit_thms.csv` (une ligne par théorème : base, nom, fichier, ligne, classe, sous-classe, anticipe, note, type).

## 2. Comptes par base et par classe (sélection de 1300)

| base | G | E | S | R | X | total |
|---|---:|---:|---:|---:|---:|---:|
| RHV6Fresh | 341 | 176 | 8 | 271 | 22 | 818 |
| rhv3_lean | 234 | 73 | 20 | 20 | 49 | 396 |
| RHV5Fresh | 17 | 24 | 0 | 3 | 4 | 48 |
| rhv2_fresh | 3 | 0 | 35 | 0 | 0 | 38 |
| **total** | **595** | **273** | **63** | **294** | **75** | **1300** |

Sous-classes : RHV5Fresh E-Tour = 12 ; RHV5Fresh E-grammaire = 12 ; RHV5Fresh G-heur = 17 ; RHV5Fresh R-heur = 3 ; RHV5Fresh X-RH = 1 ; RHV5Fresh X-prémisse = 3 ; RHV6Fresh E-Tour = 102 ; RHV6Fresh E-grammaire = 74 ; RHV6Fresh G-comptage = 24 ; RHV6Fresh G-grille = 56 ; RHV6Fresh G-heur = 261 ; RHV6Fresh R-cinématique = 12 ; RHV6Fresh R-flèche = 5 ; RHV6Fresh R-heur = 241 ; RHV6Fresh R-raccord = 7 ; RHV6Fresh R-translation = 6 ; RHV6Fresh S-définition = 4 ; RHV6Fresh S-nom = 2 ; RHV6Fresh S-structure = 2 ; RHV6Fresh X-RH = 19 ; RHV6Fresh X-prémisse = 3 ; rhv2_fresh G-heur = 3 ; rhv2_fresh S-fenêtre = 2 ; rhv2_fresh S-prémisse = 33 ; rhv3_lean E-Tour = 63 ; rhv3_lean E-grammaire = 10 ; rhv3_lean G-heur = 234 ; rhv3_lean R-heur = 20 ; rhv3_lean S-prémisse = 20 ; rhv3_lean X-RH = 7 ; rhv3_lean X-prémisse = 42

## 3. Théorème compilé contredisant le fait nouveau : AUCUN

Aucun type compilé, dans les six bases, n'affirme qu'une Tour d'un vrai zéro a un nombre fini de contacts, qu'un premier n'a
pas de cellule, que la cellule de la Tour ne contient qu'un premier sans prémisse, ni que l'occurrence est lue par la
géométrie. Les énoncés « exactement un premier » sont tous sous une prémisse de type T1 (§4), ou portent sur une fenêtre
construite (`thm_anchorState_terminalPrimeCountOne`, rhv2), ou sur des intervalles témoins (`thm_counterexample_*`, rhv3).

**Conflits de prose seulement (à corriger dans les docstrings et les maîtres, pas dans les types) :**

1. `RHV6Fresh/RHV6Fresh/Tower/TrueTowerStructure.lean:10-12`, en-tête : « la Tour d'un vrai zéro a **deux** contacts, et deux
   seulement […] ; l'agrégat de cellules n'existe pas ». Contredit `every_prime_in_every_tower` et `zeroTerm_real_iff_ray`
   (le terme est réel exactement aux `C_k`, pour tout `k ∈ ℤ`). Origine : décision de l'auteur du 2026-09-22, commit a4076a04
   (« deux contacts, jamais une infinité de rencontres, agrégat de cellules inexistant, question close »).
2. `RHV6Fresh/RHV6Fresh/Tower/ProperTower.lean` l. 48 (docstring de `AnalyticContactPair`) et §6 l. 240–247 (avant `analyticPairAt`) : « ces valeurs ne sont pas des
   contacts […] La Tour n'a que deux contacts ». Les paires `analyticPairAt z k` sont exactement les cellules de la grille.
3. `RHV6Fresh/RHV6Fresh/Terminal/EnergyIdentity.lean:36`, nom et docstring de `geometry_selects_raccord_prime` (« la géométrie
   sélectionne le raccord ») : le type sélectionne par la grammaire (`occurrence l = expectedMinimumPrime e`) et localise par la
   géométrie un `q` arbitraire.
4. `RHV6Fresh/RHV6Fresh/Direct/PairTowers.lean` en-tête et `firstTowerOf` / `secondTowerOf` / `lineTowerOf` : « la Tour de tout
   zéro par la règle du pivot sur son minimum attendu » : la Tour (`TrueTower`) = grille + une cellule choisie par l'étiquette.
5. Hors bases RHV6 : rhv2_fresh, structures non habitées `TRHV2MasterCore.t1`, `TMemberLocalization.windowSatisfiesT1`,
   `TRHV2AcquiredInput.t1`, `TCollisionRouteAcquiredInput.t1` (champs qui posent T1 ; incident 8.5 de l'audit cumulé) :
   aucun habitant, donc aucune contradiction compilée.

## 4. Liste complète des S (requalification)

| nom | base | fichier:ligne | sous-classe | pourquoi |
|---|---|---|---|---|
| `firstTower_contactPair_unique` | RHV6Fresh | RHV6Fresh/Direct/PairTowers.lean:109 | S-nom | « la paire de contacts de la première Tour est unique » : type = unicité de la coordonnée k dont la cellule contient p_min(z), vraie pour tout q (pivotCoordinate_unique) ; la Tour n'est pas cette paire |
| `geometry_selects_raccord_prime` | RHV6Fresh | RHV6Fresh/Terminal/EnergyIdentity.lean:36 | S-nom | nom et docstring « la géométrie sélectionne le raccord » ; le type dit : occurrence l = p_min e (grammaire) ∧ la cellule pivot de q existe et est unique pour tout q ; la géométrie localise n'importe quel q, c'est le rang qui sélectionne |
| `firstTowerOf_properState` | RHV6Fresh | RHV6Fresh/Direct/PairTowers.lean:65 | S-définition | état propre de la Tour défini comme la cellule de p_min(z) : la sélection du premier est faite par l'étiquette de rang dans la définition, pas par la géométrie ; type vrai (rfl) |
| `firstTowerOf_eq_lineTowerOf` | RHV6Fresh | RHV6Fresh/Direct/PairTowers.lean:68 | S-définition | état propre de la Tour défini comme la cellule de p_min(z) : la sélection du premier est faite par l'étiquette de rang dans la définition, pas par la géométrie ; type vrai (rfl) |
| `secondTowerOf_properState` | RHV6Fresh | RHV6Fresh/Direct/PairTowers.lean:137 | S-définition | état propre de la Tour défini comme la cellule de p_min(z) : la sélection du premier est faite par l'étiquette de rang dans la définition, pas par la géométrie ; type vrai (rfl) |
| `lineTowerOf_properState` | RHV6Fresh | RHV6Fresh/Direct/PivotCell.lean:281 | S-définition | état propre de la Tour défini comme la cellule de p_min(z) : la sélection du premier est faite par l'étiquette de rang dans la définition, pas par la géométrie ; type vrai (rfl) |
| `TrueTower.ext_pair` | RHV6Fresh | RHV6Fresh/Tower/TrueTowerStructure.lean:61 | S-structure | TrueTower z = mouvement (grille) + UNE paire de contacts distinguée ; module TrueTowerStructure : « deux contacts, et deux seulement, l'agrégat de cellules n'existe pas » ; type vrai, lecture à requalifier : la paire est une cellule de la grille, la Tour est la grille |
| `TrueTower.readings_injective` | RHV6Fresh | RHV6Fresh/Tower/TrueTowerStructure.lean:71 | S-structure | TrueTower z = mouvement (grille) + UNE paire de contacts distinguée ; module TrueTowerStructure : « deux contacts, et deux seulement, l'agrégat de cellules n'existe pas » ; type vrai, lecture à requalifier : la paire est une cellule de la grille, la Tour est la grille |
| `TTrueTowerCarrier.thm_T1_existsUniquePrime` | rhv3_lean | RHV3Lean/Objects/CanonicalT1.lean:178 | S-prémisse | prémisse/objet de type T1 : PUniqueCenterRegime |
| `TTrueTowerCarrier.thm_T1_T2_heightRecoveredAtSuccessorCell` | rhv3_lean | RHV3Lean/Objects/CanonicalT2.lean:158 | S-prémisse | prémisse/objet de type T1 : PUniqueCenterRegime |
| `thm_memberCanonicalOccurrence_incident_ownEvent_iff` | rhv3_lean | RHV3Lean/Research/SameHeightPrimeStability.lean:29 | S-prémisse | prémisse/objet de type T1 : PMemberAnchorLandsInOwnCell |
| `thm_memberCanonicalAnchor_mem_ownCell_iff_sourceIndex_rankWindow` | rhv3_lean | RHV3Lean/Research/SameHeightPrimeStability.lean:40 | S-prémisse | prémisse/objet de type T1 : PMemberAnchorLandsInOwnCell |
| `TTrueTowerCarrier.thm_T1_iff_rightEdgeRank_eq_leftEdgeRank_succ` | rhv3_lean | RHV3Lean/Objects/CanonicalT1.lean:92 | S-prémisse | prémisse/objet de type T1 : PUniqueCenterRegime |
| `TTrueTowerCarrier.thm_T1_iff_existsUniqueGrammarLanding` | rhv3_lean | RHV3Lean/Objects/CanonicalT1.lean:143 | S-prémisse | prémisse/objet de type T1 : PUniqueCenterRegime |
| `TTrueTowerCarrier.thm_T1_centralPrime_eq_C3` | rhv3_lean | RHV3Lean/Objects/CanonicalT1.lean:191 | S-prémisse | prémisse/objet de type T1 : PUniqueCenterRegime |
| `TTrueTowerCarrier.thm_T1_centralPrime_unique` | rhv3_lean | RHV3Lean/Objects/CanonicalT1.lean:206 | S-prémisse | prémisse/objet de type T1 : PUniqueCenterRegime |
| `TTrueTowerCarrier.thm_centralPrime_countRank_eq_rightEdgeRank` | rhv3_lean | RHV3Lean/Objects/CanonicalT2.lean:272 | S-prémisse | prémisse/objet de type T1 : PUniqueCenterRegime |
| `TTrueTowerCarrier.thm_off_impossible_of_mirrorCollision_and_t2Off` | rhv3_lean | RHV3Lean/Objects/OffGrammarSuccessionContradiction.lean:90 | S-prémisse | prémisse/objet de type T1 : PMirrorCollision |
| `TTrueTowerCarrier.thm_leftBand_count_le_one_of_T1` | rhv3_lean | RHV3Lean/Objects/OffMirrorChebyshevChannel.lean:293 | S-prémisse | prémisse/objet de type T1 : PUniqueCenterRegime |
| `TTrueTowerCarrier.thm_rightBand_count_le_one_of_T1` | rhv3_lean | RHV3Lean/Objects/OffMirrorChebyshevChannel.lean:304 | S-prémisse | prémisse/objet de type T1 : PUniqueCenterRegime |
| `TTrueTowerCarrier.thm_mirrorBand_count_mem_zeroOne_of_T1` | rhv3_lean | RHV3Lean/Objects/OffMirrorChebyshevChannel.lean:313 | S-prémisse | prémisse/objet de type T1 : PUniqueCenterRegime |
| `TTrueTowerCarrier.thm_mirrorBand_Dpi_one_imp_Dtheta_strict_of_T1` | rhv3_lean | RHV3Lean/Objects/OffMirrorChebyshevChannel.lean:345 | S-prémisse | prémisse/objet de type T1 : PUniqueCenterRegime |
| `TTrueTowerCarrier.thm_off_impossible_of_T2_and_mirrorCollision` | rhv3_lean | RHV3Lean/Objects/OffMirrorCollisionViaCanonicalSuccession.lean:214 | S-prémisse | prémisse/objet de type T1 : PMirrorCollision |
| `thm_riemannHypothesis_of_T1_T2_mirrorCollision` | rhv3_lean | RHV3Lean/Objects/OffMirrorCollisionViaCanonicalSuccession.lean:255 | S-prémisse | prémisse/objet de type T1 : PMirrorCollision,PUniqueCenterRegime |
| `TTrueTowerCarrier.thm_mirrorCollision_of_stageAndBandsPrimeFree` | rhv3_lean | RHV3Lean/Objects/OffMirrorDifferenceBands.lean:309 | S-prémisse | prémisse/objet de type T1 : PMirrorCollision |
| `TTrueTowerCarrier.thm_mirrorBands_sameCount_of_T1` | rhv3_lean | RHV3Lean/Objects/OffMirrorOverlapReduction.lean:99 | S-prémisse | prémisse/objet de type T1 : PUniqueCenterRegime |
| `TTrueTowerCarrier.thm_mirrorCollision_iff_leftBandEmpty_of_T1` | rhv3_lean | RHV3Lean/Objects/OffMirrorOverlapReduction.lean:153 | S-prémisse | prémisse/objet de type T1 : PUniqueCenterRegime |
| `thm_riemannHypothesis_of_named_mirrorCollision` | rhv3_lean | RHV3Lean/Objects/SamePrimeCollision.lean:139 | S-prémisse | prémisse/objet de type T1 : PCentralPrimeInjective,PMirrorCollision |
| `CertificationSemanticFinal.comparator_semantic_terminalCell_uniquePrime_contract` | rhv2_fresh | Certification/SemanticChallenge.lean:57 | S-prémisse | prémisse/objet de type T1 : PEveryTerminalCellHasUniqueCanonicalPrime |
| `thm_anchorState_terminalPrimeCountOne` | rhv2_fresh | RHV2Fresh/Master/CanonicalOccurrenceCandidateA.lean:226 | S-fenêtre | affirme qu'une fenêtre construite (ancrée) contient exactement un premier : compatible avec la grille (une cellule peut contenir 0, 1 ou plusieurs premiers) ; à requalifier seulement si on la lit comme « la » cellule de la Tour |
| `thm_anchoredTowerState_terminalPrimeCountOne` | rhv2_fresh | RHV2Fresh/Master/CanonicalTerminalCellProducer.lean:225 | S-fenêtre | affirme qu'une fenêtre construite (ancrée) contient exactement un premier : compatible avec la grille (une cellule peut contenir 0, 1 ou plusieurs premiers) ; à requalifier seulement si on la lit comme « la » cellule de la Tour |
| `TCanonicalStateProducer.PT1_iff_toOperator_PCanonicalT1` | rhv2_fresh | RHV2Fresh/Master/CanonicalTerminalChain.lean:58 | S-prémisse | prémisse/objet de type T1 : PCanonicalT1,PT1 |
| `RHV2Definitive.TCollisionRouteAcquiredInput.t1` | rhv2_fresh | RHV2Fresh/Master/Definitive/CollisionRoute.lean:153 | S-prémisse | prémisse/objet de type T1 : PCanonicalT1 |
| `RHV2Definitive.TRHV2AcquiredInput.t1` | rhv2_fresh | RHV2Fresh/Master/Definitive/RiemannHypothesis.lean:142 | S-prémisse | prémisse/objet de type T1 : PCanonicalT1 |
| `TRHV2MasterCore.t1` | rhv2_fresh | RHV2Fresh/Master/DirectTranscription.lean:113 | S-prémisse | prémisse/objet de type T1 : PCanonicalTerminalPrimeCountOne |
| `TRHV2MasterCore.rhv2T1_uniquePrimeLocalization` | rhv2_fresh | RHV2Fresh/Master/DirectTranscription.lean:134 | S-prémisse | prémisse/objet de type T1 : PCanonicalTerminalPrimeCountOne |
| `RHV2Definitive.thm_centrality_of_countOne` | rhv2_fresh | RHV2Fresh/Master/LocalLawAndCentrality.lean:96 | S-prémisse | prémisse/objet de type T1 : PCanonicalCentralityT1,PCanonicalT1 |
| `TMemberLocalization.windowSatisfiesT1` | rhv2_fresh | RHV2Fresh/Master/MemberLocalization.lean:61 | S-prémisse | prémisse/objet de type T1 : PCanonicalTerminalPrimeCountOne |
| `thm_uniquePrimeLocalizationAt_iff_existsUnique` | rhv2_fresh | RHV2Fresh/Master/PrimeLocalization.lean:120 | S-prémisse | prémisse/objet de type T1 : PUniquePrimeLocalizationAt |
| `thm_canonicalTerminalPrimeCountOne_iff_existsUnique` | rhv2_fresh | RHV2Fresh/Master/PrimeLocalization.lean:205 | S-prémisse | prémisse/objet de type T1 : PCanonicalTerminalPrimeCountOne |
| `SixBlockE2.terminalPrimeCountOne` | rhv2_fresh | RHV2Fresh/Master/SixBlockMaterialization.lean:130 | S-prémisse | prémisse/objet de type T1 : PCanonicalTerminalPrimeCountOne,PT1 |
| `CertificationSemanticFinal.comparator_semantic_centralPrime_in_terminalCell` | rhv2_fresh | Certification/SemanticChallenge.lean:75 | S-prémisse | prémisse/objet de type T1 : PEveryTerminalCellHasUniqueCanonicalPrime |
| `TCanonicalStateProducer.prime_lt_c3_le_contactMinus` | rhv2_fresh | RHV2Fresh/Master/CanonicalCellPrimeIsolation.lean:34 | S-prémisse | prémisse/objet de type T1 : PT1 |
| `TCanonicalStateProducer.contactPlus_lt_of_c3_lt_prime` | rhv2_fresh | RHV2Fresh/Master/CanonicalCellPrimeIsolation.lean:46 | S-prémisse | prémisse/objet de type T1 : PT1 |
| `TCanonicalStateProducer.c3_eq_of_mem_other_cell` | rhv2_fresh | RHV2Fresh/Master/CanonicalCellPrimeIsolation.lean:123 | S-prémisse | prémisse/objet de type T1 : PT1 |
| `thm_T1_forces_contactPlus_ge_two` | rhv2_fresh | RHV2Fresh/Master/CanonicalOccurrenceConstraints.lean:46 | S-prémisse | prémisse/objet de type T1 : PCanonicalTerminalPrimeCountOne |
| `TZetaCanonicalTowerOperator.prov_occurrence` | rhv2_fresh | RHV2Fresh/Master/CanonicalProvenance.lean:110 | S-prémisse | prémisse/objet de type T1 : PCanonicalT1 |
| `TZetaCanonicalTowerOperator.prov_absence_outside_cell` | rhv2_fresh | RHV2Fresh/Master/CanonicalProvenance.lean:130 | S-prémisse | prémisse/objet de type T1 : PCanonicalT1 |
| `TCanonicalStateProducer.c3_mem_cell` | rhv2_fresh | RHV2Fresh/Master/CanonicalStateProducer.lean:150 | S-prémisse | prémisse/objet de type T1 : PT1 |
| `TZetaCanonicalTowerOperator.c3_in_cell` | rhv2_fresh | RHV2Fresh/Master/CanonicalT1.lean:88 | S-prémisse | prémisse/objet de type T1 : PCanonicalT1 |
| `TZetaCanonicalTowerOperator.prime_in_cell_eq_c3` | rhv2_fresh | RHV2Fresh/Master/CanonicalT1.lean:98 | S-prémisse | prémisse/objet de type T1 : PCanonicalT1 |
| `TZetaCanonicalTowerOperator.sameC3_of_common_prime_in_cells` | rhv2_fresh | RHV2Fresh/Master/CanonicalT1.lean:107 | S-prémisse | prémisse/objet de type T1 : PCanonicalT1 |
| `TZetaCanonicalTowerOperator.cell_neighbourhood_empty` | rhv2_fresh | RHV2Fresh/Master/CanonicalT1.lean:131 | S-prémisse | prémisse/objet de type T1 : PCanonicalT1 |
| `RHV2Definitive.offMirror_no_common_prime_in_both_cells_of_placeIndex` | rhv2_fresh | RHV2Fresh/Master/Definitive/LocalSuccession.lean:220 | S-prémisse | prémisse/objet de type T1 : PCanonicalT1 |
| `RHV2Definitive.thm_C3_existsUnique_prime_in_cell` | rhv2_fresh | RHV2Fresh/Master/Definitive/Localization.lean:33 | S-prémisse | prémisse/objet de type T1 : PCanonicalT1 |
| `RHV2Definitive.thm_C3_centralPrime_in_cell` | rhv2_fresh | RHV2Fresh/Master/Definitive/Localization.lean:51 | S-prémisse | prémisse/objet de type T1 : PCanonicalT1 |
| `RHV2Definitive.thm_centralRoute_supersedes_definitive_C3_in_cell` | rhv2_fresh | RHV2Fresh/Master/DefinitiveCentralAlignment.lean:424 | S-prémisse | prémisse/objet de type T1 : PCanonicalT1 |
| `localPrimeLocalization_uses_same_axis_cell` | rhv2_fresh | RHV2Fresh/Master/PrimeLocalization.lean:187 | S-prémisse | prémisse/objet de type T1 : PUniquePrimeLocalizationAt |
| `thm_centralPrimeOfZetaZero_mem_terminalCell` | rhv2_fresh | RHV2Fresh/Master/SemanticProofChain.lean:70 | S-prémisse | prémisse/objet de type T1 : PEveryTerminalCellHasUniqueCanonicalPrime |
| `thm_centralPrimeStrictOrder_forces_contactPlus_strictOrder` | rhv2_fresh | RHV2Fresh/Master/SemanticProofChain.lean:519 | S-prémisse | prémisse/objet de type T1 : PEveryTerminalCellHasUniqueCanonicalPrime |
| `thm_centralPrimeOrder_forces_contactPlus_strictOrder` | rhv2_fresh | RHV2Fresh/Master/SemanticProofChain.lean:574 | S-prémisse | prémisse/objet de type T1 : PEveryTerminalCellHasUniqueCanonicalPrime |
| `thm_monotoneContactMinus_forces_centralPrime_monotone` | rhv2_fresh | RHV2Fresh/Master/SemanticProofChain.lean:719 | S-prémisse | prémisse/objet de type T1 : PEveryTerminalCellHasUniqueCanonicalPrime |
| `thm_centralPrimeOrder_of_entryContactMonotone_and_placesDistinct` | rhv2_fresh | RHV2Fresh/Master/SemanticProofChain.lean:801 | S-prémisse | prémisse/objet de type T1 : PEveryTerminalCellHasUniqueCanonicalPrime |

### 4bis. Grappe T1 hors plafond

Le même motif de prémisse (T1, « une cellule, un seul premier ») porte, au total des jsonl, **248 théorèmes de rhv2_fresh**
(dont 38 retenus ci-dessus ; les plus gros fichiers : `Master/SemanticProofChain.lean` 21, `Master/CanonicalProvenance.lean` 18,
`Master/DirectMasterTranscription.lean` 13, `Master/CanonicalT1.lean` 12, `Certification/SemanticChallenge.lean` 12 et sa
copie `SemanticSolution.lean` 12, `Master/TripleEventGrammar.lean` 11, détail dans `t1_cluster_all.txt`) et **19 de rhv3_lean**
(tous retenus). RHV5Fresh, rhv4_lean, rh_gap_criterion : 0 (les 5 occurrences « .t1 » de rh_gap sont des bornes de rectangle).
Toutes sont `CONFIRMÉE SOUS CONDITION` ou `IMPLIQUE RH SOUS PRÉMISSE` : la prémisse est réfutée sur la Tour propre
(`thm_PCanonicalCellFoundCountOne_is_false`, V151), elles ne sont pas fausses, elles sont vides pour la Tour.
RHV5Fresh `PCellExitLaw` (« la cellule du suivant sort de celle du précédent ») est de la même famille : cellule choisie par
l'occurrence ; X (prémisse non déchargée), à relire comme une loi sur deux grilles, ce qui est exactement « la Tour d'arrivée
n'est pas translatée » plus une part de hauteur.

**Lecture des S de RHV6Fresh (8)** : les types restent vrais. Ce qui change est le vocabulaire : `TrueTower z` n'est pas « la
Tour », c'est « la grille de z (mouvement, unique par zéro) + une cellule distinguée » ; la cellule distinguée est choisie
par l'étiquette de rang `p_min(z)` dans la définition (`pivotCell z := pivotPair z (expectedMinimumPrime z)`), jamais par la
géométrie. `towerMotion_subsingleton` (la grille est unique par zéro) reste l'énoncé d'unicité correct.

## 5. Les 30 E les plus importants pour la stratégie

Tous restent vrais (ce sont des théorèmes compilés). Pour chacun : le contenu radial, c'est-à-dire ce qui dépend de `β`, et le
rôle de l'étiquette. Règle commune : sur la grille, le décalage d'un point `q` par rapport à la Tour de ligne vaut `D/π`
pour tout `q` (`tower_offset_rigid`) ; donc dès qu'un énoncé est évalué en `M = Occ(l) = p_min(e)`, sa part radiale est la
même en tout point, et `M` ne contribue que par `log M` dans la part de hauteur ou par une non-dégénérescence.

| # | théorème (RHV6Fresh) | fichier:ligne | phrase |
|---|---|---|---|
| 1 | `towerRaccord_eq` | Terminal/TowerRaccord.lean:55 | Reste vrai, contenu radial = `(β_l − β_e)·log M` dans le transport ; même forme `(β_l − β_e)·log q` en tout `q > 0`, l'unicité du raccord vient de l'étiquette `M = p_min(e)`, pas de la grille. |
| 2 | `TowerRaccord.oriented_iff_transport_le_one` (classé R) | Terminal/TowerRaccord.lean:91 | Reste vrai, contenu radial = signe de `(β_l − β_e)·log M + log(‖ρ_e‖/‖ρ_l‖)` ; identique en tout `q ≥ 1` à la place de `M` à la valeur de `log q` près. |
| 3 | `canonicalTransition_of_passage` | Terminal/CanonicalTransition.lean:56 | Reste vrai, contenu radial = aucun (existence de l'objet : départ en ligne, rang + 1, `M` partagé) ; `M` est une étiquette. |
| 4 | `exit_position_fixed_by_departure` | Terminal/CanonicalTransition.lean:76 | Reste vrai, contenu radial = `D_e = 0` ; vrai en tout point de la grille du départ (départ en ligne ⟹ aucune translation). |
| 5 | `transition_shared_prime_shift` | Terminal/CanonicalTransition.lean:155 | Reste vrai, contenu radial = `D_l` ; le déplacement de tout point `q` d'une Tour à l'autre vaut part de hauteur(`q`) + `D_l`, `D_l` indépendant de `q`. |
| 6 | `transition_conserves_iff_entry_position` (classé R) | Terminal/CanonicalTransition.lean:174 | Reste vrai, contenu radial = `D_l/π` à l'entrée de `M` ; équivaut à « aucune translation de la grille d'arrivée » (`entry_arrow_point_irrelevant`). |
| 7 | `entry_arrow_iff_local_euler_modulus` | Terminal/EntryPositionArrow.lean:112 | Reste vrai, contenu radial = `‖M^{−ρ_l}‖ = M^{−β_l}` ; pour tout entier `n ≥ 2`, `‖n^{−ρ}‖ = n^{−1/2}` ⟺ `β = 1/2` (`rpow_exponent_injective`) : le terme d'Euler du premier partagé n'a aucun rôle propre. |
| 8 | `passage_ledger` | Terminal/GrammarKinematics.lean:133 | Reste vrai, contenu radial = `−Δφ` radial dans `raccordShift` ; `M` n'entre que par `ΔT·log M` (hauteur) et `T_e·log(p_{n+1}/p_n)` (grammaire). |
| 9 | `passage_ledger_radial` | Terminal/GrammarKinematics.lean:152 | Reste vrai, contenu radial = `T_e log r_e − T_l log r_l`, sans aucun `log M`. |
| 10 | `deltaT_from_ledger` | Terminal/GrammarKinematics.lean:143 | Reste vrai, contenu radial = `Δφ` (phases), `M` porte seulement `ΔT·log M` ; c'est une équation, pas une borne. |
| 11 | `chain_ledger` | Terminal/GrammarKinematics.lean:232 | Reste vrai, contenu radial = somme télescopique des parts radiales, indépendante des premiers de la chaîne. |
| 12 | `grammar_kinematics_abel` | Terminal/GrammarKinematics.lean:255 | Reste vrai, contenu radial = aucun (identité d'Abel sur hauteurs et `log p_j`) ; les premiers sont les étiquettes de rang. |
| 13 | `required_eq_realised` | Terminal/GrammarKinematics.lean:407 | Reste vrai, contenu radial = libre : identité vraie pour toute position radiale. |
| 14 | `transitionExcess_eq` | Terminal/GrammarKinematics.lean:540 | Reste vrai, contenu radial = `T_e log r_e − T_l log r_l`, indépendant de `M`. |
| 15 | `diagonal_radial_from_ledger` | Terminal/GrammarKinematics.lean:370 | Reste vrai, contenu radial = `T_l log r_l` exprimé par le registre ; le même en tout point (le registre en `q` donne la même valeur). |
| 16 | `changeResidue_ledger` | Terminal/ChangePredictor.lean:170 | Reste vrai, contenu radial = `D_l − D_e` ; `D` est une constante de grille. |
| 17 | `engaged_changeResidue_from_ledger` | Terminal/ChangePredictor.lean:179 | Reste vrai, contenu radial = `D_l` ; « une formule arithmétique de `D̂` par passage » n'a pas à être cherchée en `M` plutôt qu'ailleurs. |
| 18 | `occurrencePosition_decomposed` | Terminal/GrammarKinematics.lean:83 | Reste vrai, contenu radial = `−T log r` ; même terme pour `towerPosition z q` en tout `q`. |
| 19 | `raccordShift_eq` | Terminal/GrammarKinematics.lean:106 | Reste vrai, contenu radial = `−(φ_l − φ_e)` radial ; `log Occ(l)` n'est multiplié que par `ΔT`. |
| 20 | `fibre_transport_product` | Terminal/RaccordDetector.lean:159 | Reste vrai, contenu radial = `d·log(M₂²/(M₁M₃))` ; même forme pour trois points quelconques, neutre ⟺ `d = 0` dès que `q₂² ≠ q₁q₃` (automatique pour trois premiers distincts, `prime_sq_ne_mul`). |
| 21 | `fibre_charge_eq_one_iff` | Terminal/RaccordDetector.lean:211 | Reste vrai, contenu radial = `d` ; les premiers n'assurent que la non-dégénérescence `M₂² ≠ M₁M₃`. |
| 22 | `transport_product` (RegimeCell) | Terminal/RegimeCell.lean:413 | Reste vrai, contenu radial = charge `(M₂²/(M₁M₃))^d` ; la cellule V→H→V lit `d` en n'importe quel triplet non dégénéré. |
| 23 | `charge_reads_translation` | Terminal/RegimeCell.lean:431 | Reste vrai, contenu radial = `sin(−T log c)` (translation rigide `c` de la grille) ; le triplet de premiers est une base de lecture. |
| 24 | `two_raccord_transport_memberStep` | Terminal/PrimalEventRaccord.lean:387 | Reste vrai, contenu radial = `(β − 1/2)·log(Occ/p_min)` (pas de membre) ; vrai pour tout couple de points distincts. |
| 25 | `firstTower_cell_contains_expected` | Direct/PairTowers.lean:99 | Reste vrai, contenu radial = aucun ; cas particulier de `every_prime_in_every_tower` en `p_min(z)`. |
| 26 | `reaches_occurrence_iff` | Direct/InvertedCount.lean:98 | Reste vrai, contenu radial = `D/π` via le bord `C⁺` ; c'est un comptage `n(z) < countedRank S`, la même loi vaut pour tout premier (`reaches_primeAtRank_iff`). |
| 27 | `secondTower_reads_occurrence_iff_coordinate_lt` | Direct/PairTowers.lean:244 | Reste vrai, contenu radial = nul (comparaison de deux cellules dans la même grille : la translation s'annule) ; la lecture est un écart de hauteur `T·log(p_min/Occ) ≥ π`. |
| 28 | `horizontalRaccords_amplitude_brackets` | Terminal/GeometricEnergyRaccord.lean:96 | Reste vrai, contenu radial = `q^β` aux bords de cellule ; cas `q = Occ(l)` de `pivotCell_amplitude_brackets` (∀ q). |
| 29 | `passage_span_eq_log_occurrences` | Terminal/TwoClocks.lean:56 | Reste vrai, contenu radial = nul (`T/π·log(Occ_l/Occ_e)`, hauteur seule). |
| 30 | `expectedMinimum_le_stateReadout_iff` / `countedPrime_lt_expected_of_lastRay` | Terminal/IndependentContactComparison.lean:16 ; Direct/StateCount.lean:86 | Restent vrais, contenu radial = position de `C⁺` (translatée de `D/π`) ; seuil `p_min(a)` arbitraire (∀ a, y compris a ≠ b). |

Hors classe E mais à citer avec ces 30 : `countedPrime_eq_vonMangoldt` (Direct/StateCount.lean:40) est **G** : le comptage de
Tchebychev au dernier rayon vaut pour toute paire de la grille ; contenu radial = `⌊C⁺⌋` déplacé d'un facteur `r` avec
`|log r| < 1/T²` (différence 4.7 de l'audit ON/OFF). `zeroTerm_real_iff_ray` (Terminal/ExplicitFormulaLink.lean:172) est **G**
et anticipe directement le fait : le terme est réel exactement aux `C_k`, pour tout `k`.

## 6. Les R et leur relecture sur la grille

Verdict global : **aucun R n'est invalidé.** Toutes les caractérisations de régime de RHV6Fresh sont soit déjà des énoncés de grille (∀ k, ∀ q), soit des énoncés sur (β,T) sans cellule ; celles qui sont posées en un premier (Occ, p_min, M) se relisent en un point quelconque, avec le même contenu.

### a. facteur radial, contacts, résidu D (30)

Relecture : déjà des énoncés de grille : un seul facteur r (resp. un seul D) pour tous les k ; relecture : D/π = amplitude de la translation de la grille en unités de cellule. VALIDES sans changement.

`contact_eq_line_mul_radial`, `contacts_height_determined_iff_onLine`, `towerPosition_shift_abs_lt_half`, `towerPosition_eq_line_add_residue`, `changeResidueAt_eq_zero_iff`, `changeResidueAt_neg_iff`, `changeResidueAt_pos_iff`, `changeResidueAt_window`, `changeResidue_eq_zero_iff`, `changeResidue_eq_phase`, `changeResidue_eq_position_sub`, `changeResidue_eq_radial`, `changeResidue_enclosed_by_remainder_growth`, `changeResidue_zero_of_remainder_sqrt_growth`, `changeResidue_vanishes_iff_remainder_sqrt_growth`, `radialFactor_pos`, `radialFactor_gt_one_iff`, `radialFactor_lt_one_iff`, `radialFactor_eq_one_iff`, `one_le_radialFactor_of_le_half`, `phase_eq_line_add_radial`, `tower_offset_rigid`, `offset_eq_translation`, `phase_eq_linePhase_of_onLine`, `change_detector`, `passage_change_detector`, `lineValue_zero_of_onLine`, `linePhase_lt_phase_iff`, `phase_lt_linePhase_iff`, `offset_lt_half`

### b. pas, translation, grille (41)

Relecture : énoncés natifs de la grille (pas π/T, translation rigide, dichotomie de cellule ∀ q). VALIDES ; ils sont la forme compilée du fait nouveau (tower_offset_rigid en est le corollaire ∀ q).

`sameHeight_pivotCoordinate_dichotomy`, `horizontal_cell_dichotomy_at_raccords`, `pivotCoordinate_mirror_mem`, `gridTranslation_contacts`, `horizontal_pivot_shift`, `central_cell_shift`, `towerPitch_eq_contacts`, `mirror_translation_over_next_progression_lt`, `mirror_translation_factor_eq_one_iff`, `sameHeight_grid_rigid_translation`, `sameHeight_pitch_invariant`, `sameRadial_height_changes_pitch`, `onLine_iff_entry_at_point`, `onLine_iff_no_grid_translation`, `gridTranslation_pos`, `log_gridTranslation`, `gridTranslation_lt_one`, `pitch_signature`, `translation_bounds`, `towerPitch_pos`, `towerPitch_radial_blind`, `towerPitch_lt_iff`, `towerPitch_eq_iff`, `rigid_translation_of_sameHeight_radial_lt`, `no_rigid_translation_of_height_ne`, `horizontal_iff_pitch_kept`, `vertical_iff_pitch_contracts`, `horizontal_tower_translation`, `horizontal_iff_tower_translation`, `vertical_iff_no_tower_translation`, `passage_grid_translation_of_sameHeight`, `tower_grid_normal_form`, `competing_regime_at_any_point`, `engaged_passage_translation`, `mirror_translation_lt`, `mirror_translation_lt_inv_pi_height`, `span_eq_on_sameHeight_fiber`, `phase_increment_eq_of_sameHeight`, `onLine_grid_height_only`, `onLine_grid_eq_iff_height_eq`, `passage_grid_decomposition`

### c. miroir (39)

Relecture : le miroir a la même grille translatée (même hauteur) ; « contacts confondus ⟺ en ligne », « intercalés hors ligne » se lisent comme « translation nulle / non nulle » de la grille miroir. VALIDES.

`mirror_contact_eq_iff_onLine`, `mirror_contacts_never_coincide`, `mirror_contacts_eq_of_onLine`, `onLine_of_mirror_contact_eq`, `mirror_all_contacts_shift_of_offLine`, `mirror_contacts_interlace`, `mirrorMember_eq_self_of_onLine`, `mirror_radial_gt`, `mirror_precedes`, `sourceIndex_lt_mirror`, `mirrorMember_ne`, `fiberSuccessor_eq_mirror_or_precedes`, `fiberSuccessor_eq_mirror_of_noInterposition`, `radial_le_mirror_of_consecutive_lowerSide`, `mirror_annulled_iff_onLine`, `mirror_amplitude_exponent_dominates`, `on_packet_mirror_collapses`, `off_packet_mirror_distinct`, `mirror_radial_shift_eq_zero_iff`, `mirror_phase_shift_eq_zero_of_onLine`, `mirror_zeroTerm_eq_of_onLine`, `mirror_degeneracy_of_onLine`, `onLine_of_mirror_phase_shift_eq_zero`, `mirror_degeneracy_tfae`, `mirror_consumes_member_index`, `mirror_sameHeightEvent`, `mirror_sameHeightIndex`, `mirror_event_identity_refuted`, `mirror_transport_refuted`, `off_member_index_lt_mirror`, `off_mirror_same_frequency`, `onLine_mirror_trivial`, `mirror_phase_lt`, `mirror_phase_gap_lt`, `mirror_net_horizontal_force_zero`, `mirror_horizontal_tension_eq_zero_iff`, `mirror_verticalEnergy_eq_zero_iff`, `mirror_verticalEnergy_pos`, `fiberSuccessor_radial_le_mirror`

### d. raccord, transport, amplitude, énergie, pas de membre (28)

Relecture : le transport en M vaut q^{β_l−β_e}·‖ρ_e‖/‖ρ_l‖ en tout q ; orientation, renversement, pas de membre (Occ/p_min)^{β−1/2} et charge (M₂²/(M₁M₃))^d ne dépendent des premiers que par une non-dégénérescence (q₁ ≠ q₂, q₂² ≠ q₁q₃). VALIDES ; M, Occ, p_min sont des points d'évaluation.

`raccordShift_decomposed`, `chain_raccordShift_eq`, `horizontal_raccordShift`, `off_grammaticalRaccord_complete_and_reversed`, `towerRaccord_oriented_iff_window_separates`, `grammaticalRaccord_environment`, `towerRaccord_oriented_of_height_lt`, `towerRaccord_oriented_iff_height_lt`, `TowerRaccord.oriented_iff_transport_le_one`, `towerRaccord_oriented_of_vertical`, `towerRaccord_reverses_of_sameHeight`, `off_towerRaccord_reverses`, `sameHeight_amplitude_inverts_at_raccords`, `onLine_amplitude_exponents_equal`, `amplitude_exponents_eq_iff_onLine`, `amplitude_ratio_sameHeight`, `horizontal_energy_action`, `horizontal_energy_action_zero_of_onLine`, `pair_transport_false`, `memberStep_eq_one_iff`, `memberStep_gt_one_iff`, `memberStep_lt_one_iff`, `off_pair_density_norm`, `off_pair_density_exceeds_line`, `energyRatio_lt_one_of_vertical`, `engaged_transport_flat_iff_arrival_onLine`, `onLine_amplitude_lt_of_height_lt`, `sameHeight_amplitude_inverts_at_primes`

### e. flèche, conservation, persistance, prédicteur (35)

Relecture : « M entre à sa position de ligne » = « un point quelconque y entre » = « la Tour d'arrivée n'est pas translatée » (entry_arrow_point_irrelevant). VALIDES ; le verrou est inchangé.

`transition_conserves_iff_entry_position`, `vertical_arrival_onLine_iff_no_regime_change`, `entry_arrow_iff_upper_conservation`, `arrival_onLine_iff_ledger_height_determined`, `arrival_radial_ge_one`, `arrival_radial_le_one_iff_regime_kept`, `entry_arrow_point_irrelevant`, `engaged_regime_kept`, `vertical_arrival_onLine_iff_fibre_singleton`, `arrival_radial_readings`, `radial_generator_test`, `line_invariant_of_radial_preserving_law`, `transition_conserves_iff_shared_prime_shift`, `predictor_exists`, `predictor_closes`, `engaged_persists_of_predictor`, `predictor_pair_iff_heightOnly`, `change_bit_iff_race`, `vertical_exhausts_iff_arrival_onLine`, `engaged_passage_height_only`, `conservation_not_structural`, `heightOnly_step`, `engaged_persists_to_infinity`, `engagedState_iff_onLine`, `engaged_successor_determined_by_height`, `engaged_progression`, `engaged_propagates`, `vertical_arrival_written_in_arithmetic`, `engaged_linked_production`, `engaged_member_reflection_response`, `vertical_arrival_characterizes`, `engaged_successor_function`, `engaged_persists_of_generator_fixes_line`, `heightOnly_of_remainder_sqrt_growth`, `engaged_persists_of_remainder_sqrt_growth`

### f. cinématique grammaire × Tour (11)

Relecture : registre : la part radiale (T_e log r_e − T_l log r_l) ne contient aucun log M ; M n'entre que dans la part de hauteur ΔT·log M et la part grammaire. VALIDES.

`regime_entry_diagonal_ledger`, `horizontal_ledger_exceeds_grammar`, `onLine_pair_ledger`, `chain_from_line_radial_content`, `transitionExcess_onLine`, `transitionExcess_diagonal_lt`, `transitionExcess_horizontal`, `transition_kinematics_by_configuration`, `chain_transitionExcess_sum`, `first_off_configuration_two_transitions`, `first_off_configuration_alternation_floor`

### g. régimes de passage, jonctions, fibres, cellule V→H→V (58)

Relecture : aucune cellule ni premier particulier dans le type : la dichotomie vertical/horizontal, les jonctions VV/VH/HV, les fibres et la cellule de régime sont des énoncés sur (β,T). VALIDES sans relecture.

`contact_signature`, `radial_gt_of_consecutive_lowerSide`, `regime_entry_recorded`, `regime_change_creates_radial_motion`, `regime_change_requires_radial`, `regimes`, `radial_e`, `radial_e_eq`, `passage_regime_dichotomy`, `horizontalPassage_radial_lt`, `vertical_regime`, `horizontal_regime`, `regimeChange_offLine`, `onLine_keeps_regime`, `off_forces_regime_entry`, `passage_split_by_regime`, `regime_entry_read_on_towers`, `onLine_entry`, `vertical_radial_step`, `regime_entry_diagonal`, `regime_entry_from_line`, `fibre_onLine_unique`, `fibre_multiple_iff_off`, `vertical_departure_onLine_iff_fibre_singleton`, `fibre_has_onLine_member_iff`, `lineValue_ne_zero_fibre_off`, `off_lowerSide`, `sameHeight_horizontal_dominates`, `passage_height_lt_of_onLine`, `off_pair_vs_onLine_pair`, `nullPassage_horizontal`, `horizontal_nullPassage`, `heightProgression_of_horizontalExclusion`, `onLine_passage_shares_grammar_context`, `member_index_lt_of_lowerSide`, `heights_constant_of_allHorizontal`, `exists_verticalPassage`, `horizontal_of_same_exit`, `capture_of_onLine`, `horizontal_term_phase_lock`, `central_phase_lock`, `junction_vertical_vertical`, `junction_vertical_horizontal`, `junction_horizontal_vertical`, `lowerSide_enters_horizontal`, `onLine_horizontal_push_zero`, `onLine_passage_vertical`, `onLine_passage_vertical_signature`, `onLine_exit`, `vertical_pure_iff_onLine`, `diagonal_iff_off`, `completedZeta_real_onLine`, `onLine_zero_iff_lineValue`, `lineValue_member_onLine`, `onLine_zero_of_sign_change`, `onLine_member_of_sign_change`, `onLine_clock_sync`, `onLine_passage_pure_vertical`

### h. mondes témoins (11)

Relecture : contrôles hors zêta ; non touchés.

`regimeWitness_change_detected`, `regimeWitness_hasDerivAt_line`, `regimeWitness_reflection_response`, `regimeWitness_mirror`, `regimeWitness_conj`, `regimeWitness_real_onLine`, `regimeWitness_zero_iff`, `regimeWitness_regime_changes`, `engagedBreakWorld_change_detected`, `shiftedWorld_pair_off`, `engagedBreakWorld_line_then_twins`

### i. autres lectures radiales (positions, amplitudes, côtés) (18)

Relecture : lectures de β sur un membre donné (côté, amplitude q^β, position) en tout point ; VALIDES.

`lock_imp_counted_lt_occurrence`, `reflectedFromOrigin_never_reaches_expectedMinimum_beta_blind`, `fiberSuccessor_ordinate_eq`, `canonical_transition_radial_carrier`, `radial_motion_iff_off`, `radial_l`, `radial_l_eq`, `local_euler_modulus_point_irrelevant`, `exists_fiberSuccessor`, `arithmeticChain_and_reflectedFromOrigin_coexist`, `memberIndex_mem_lineWhole_iff`, `off_inside_globalRigidSystem`, `sameHeight_phase_lt`, `off_packet_explicit`, `phase_lt_iff`, `insertionDepth_pos_iff`, `insertionDepth_eq_zero_iff`, `off_clock_slip`

### j. autres bases (rhv3, RHV5) (23)

Relecture : caractérisations héritées (même hauteur, miroir, β = 1/2) énoncées sur la cellule d'un porteur ; valides comme énoncés, à relire « en une cellule quelconque » quand le porteur choisit la cellule par l'occurrence.

`thm_contactMinus_distinct_of_sameHeight_diffRadial` (rhv3_lean), `Certification.cmp_C0_mirror_sameHeight_complementaryRadial` (rhv3_lean), `Certification.cmp_C0_off_gives_two_distinct_sameFiber_members` (rhv3_lean), `Certification.cmp_Y_offMirror_sameHeight_distinct` (rhv3_lean), `thm_mirror_sameHeight` (rhv3_lean), `thm_offCriticalLine_mirror_distinct` (rhv3_lean), `thm_offCriticalLineUpper_twoDistinctSameFiberMembers` (rhv3_lean), `thm_offMirror_sameHeightEvent` (rhv3_lean), `thm_offMirror_cannot_consume_primeGap` (rhv3_lean), `thm_passage_height_strict_or_sameHeight_radial` (rhv3_lean), `thm_offMirror_sameHeight` (rhv3_lean), `thm_upperOff_tower_preserves_mirrorPassageGap` (rhv3_lean), `thm_towerCriticalDefect_eq_zero_iff` (rhv3_lean), `thm_allRadialPositions_of_upperBranch` (rhv3_lean), `thm_sameFiber_iff_sameHeight` (rhv3_lean), `thm_offCriticalLine_existsNullPassage` (rhv3_lean), `thm_offCriticalLine_existsNullRelationPassage` (rhv3_lean), `thm_grammarImage_transition_exhaustive` (rhv3_lean), `thm_offCriticalDefectSum_pos` (rhv3_lean), `thm_criticalDefectSum_eq_zero_iff` (rhv3_lean), `thm_sameHeight_canonical_noProgression_imp_plural` (RHV5Fresh), `thm_trap_expectedMinimum` (RHV5Fresh), `thm_T3_chain_contacts_to_M` (RHV5Fresh)

## 7. Réfutations et énoncés compilés qui anticipaient le fait

| énoncé | base, fichier:ligne | statut | ce qu'il anticipe |
|---|---|---|---|
| `thm_foundPrimes_generallyPlural` (+ `cmp_C2_foundPrimes_generallyPlural`) | rhv3_lean, Objects/AlgebraicAxis.lean:205 (Certification/Challenge.lean:241) | CONFIRMÉE | une cellule algébrique contient en général ≥ 2 premiers |
| `thm_ratioFourInterval_containsTwoPrimes` (+ `cmp_C6_…`) | rhv3_lean, Objects/CanonicalWindowRule.lean:182 | CONFIRMÉE | toute fenêtre `[x, 4x]` contient deux premiers |
| `thm_PCanonicalCellFoundCountOne_is_false` | rhv3_lean, Objects/CanonicalTrueTowerState.lean:383 | RÉFUTATION COMPILÉE (la seule de rhv3) | « la cellule canonique contient exactement un premier » faux pour `T ≥ 2π/log(3/2)` |
| `thm_count_not_determined_by_T_beta_alone` (+ `_v2`) | rhv3_lean, Objects/CanonicalTrueTowerState.lean:525, 639 | CONFIRMÉE | le compte d'une cellule n'est pas fonction de `(β,T)` : cellule terminale vide, fenêtre voisine ≥ 1 |
| `thm_canonicalCell_foundCount_eq_zero_of_height_large` | rhv3_lean, Objects/CanonicalTrueTowerState.lean:324 | CONFIRMÉE | la cellule canonique est vide à grande hauteur |
| `thm_T1_alone_does_not_force_T2_countDiff`, `…_rankEquality` | rhv3_lean, Objects/T1AloneCounterexampleForT2.lean:166, 204 | CONFIRMÉE | même sous T1, aucune succession de rang n'est forcée |
| `thm_originNormalization_refuted_by_T1` (+ `_heightThreshold`) | rhv2_fresh, Master/CanonicalEntryOriginRefutation.lean:60, 85 | RÉFUTATION COMPILÉE | la fenêtre ancrée à l'origine viole T1 à grande hauteur |
| `thm_arbitraryOperator_violates_canonicalT1`, `thm_inhabitation_is_not_M4` | rhv2_fresh, Master/CanonicalOperatorArbitrarinessAudit.lean:61, 82 | CONFIRMÉE | un opérateur de Tour arbitraire viole T1 |
| `thm_canonicalTowerState_carrier_not_subsingleton` | rhv2_fresh, Master/CanonicalTower.lean:213 | CONFIRMÉE | un zéro porte plusieurs états de Tour |
| `thm_contactLawState_not_subsingleton`, `thm_contactLaws_do_not_determine_state` | RHV5Fresh, Diagnostics/ContactLawScope.lean:49 | CONFIRMÉE | les lois de contact ne déterminent pas un état (une cellule) unique |
| `tower_reads_any_prime` (« D1 : la géométrie seule n'impose aucune hauteur : toute Tour lit tout premier ») | RHV6Fresh, Terminal/RayEnergy.lean:158 | CONFIRMÉE | le fait nouveau, au rang `n` près (∀ n) |
| `prime_raccord_has_unique_tower_cell` | RHV6Fresh, Terminal/GeometricEnergyRaccord.lean:40 | CONFIRMÉE | tout `q > 0` a sa cellule ; `every_prime_in_every_tower` n'en est qu'une spécialisation |
| `zeroTerm_real_iff_ray` | RHV6Fresh, Terminal/ExplicitFormulaLink.lean:172 | CONFIRMÉE | tous les `C_k` (k ∈ ℤ) sont des contacts : la Tour n'a pas deux contacts |
| `towerPosition_eq_line_add_residue`, `contact_eq_line_mul_radial`, `sameHeight_grid_rigid_translation`, `tower_grid_normal_form` | RHV6Fresh, CanonicalTransition, DiagonalPassage, MirrorDegeneracy, TowerGrid | CONFIRMÉE | translation rigide de toute la grille, avant `tower_offset_rigid` |
| `grammar_event_reads_no_radial`, `grammar_step_regime_blind`, `pointed_primes_rank_only` | RHV6Fresh, SpontaneousRegimeBreak:75, GrammarKinematics:418, PointedPrimeComparison:42 | CONFIRMÉE | l'occurrence est fonction du rang seul |
| `lastPrimeAtAuthenticPlus_not_lt_expectedMinimum` (`Terminal/OffCountExperiment.lean`) | RHV6Fresh, **retiré** (graphe exécuté du 2026-09-22, maître Lean §22-C) | n'existe plus dans le code ni dans les jsonl | prouvait `¬(p_compté(authentique) < p_min)` sur tout passage (= `PProgressionJaw authenticStateFromZero`, `AUDIT_MACHOIRES_TERMINALES_20260921.md:34`) ; son « état authentique » était sélectionné par l'occurrence. Seule trace : `git log` |

Réfutations RHV6Fresh de l'audit cumulé (§7) à relire : `mirror_event_identity_refuted`, `mirror_transport_refuted`,
`pair_transport_false` (Occ(z*) ≠ Occ(z)) restent vrais et se relisent comme « les étiquettes de rang du membre et du miroir
diffèrent » ; ils ne disent rien de la grille. `reflectedFromOrigin_never_reaches_expectedMinimum` (E, avec une version
`_beta_blind` en ligne) est aveugle à `β`. `mirror_contacts_never_coincide` est R (translation non nulle de la grille miroir).
`energy_balance_two_primes_false` est G : deux raccords à deux points distincts forcent `β_e = β_l` quels que soient les
points (le fait nouveau dit qu'il n'y a pas de point privilégié ; la prémisse d'égalité d'énergie reste ⟺ RH).

## 8. Liste des théorèmes marqués « anticipe » dans le CSV

| nom | base | fichier:ligne | classe | ce qu'il anticipe |
|---|---|---|---|---|
| `countedPrime_analyticPairAt` | RHV6Fresh | RHV6Fresh/Direct/StateCount.lean:81 | G | idem |
| `expectedMinimumPrime_injective` | RHV6Fresh | RHV6Fresh/Grammar/ExpectedMinimum.lean:47 | E | l'étiquette est injective : un comptage |
| `contact_eq_line_mul_radial` | RHV6Fresh | RHV6Fresh/Terminal/DiagonalPassage.lean:70 | R | tous les contacts = contacts de ligne × un facteur radial unique |
| `prime_raccord_has_unique_tower_cell` | RHV6Fresh | RHV6Fresh/Terminal/GeometricEnergyRaccord.lean:40 | G | tout q > 0 a sa cellule (énoncé ∀ q, porteur de every_prime_in_every_tower) |
| `occurrence_is_rank_label` | RHV6Fresh | RHV6Fresh/Terminal/OneZeroOnePrime.lean:33 | E | le fait nouveau lui-même |
| `analyticPairAt_entryContact` | RHV6Fresh | RHV6Fresh/Tower/ProperTower.lean:271 | G | les paires à toute coordonnée k sont des cellules (ProperTower §6 les disait « jamais des contacts ») |
| `analyticPairAt_lastRayContact` | RHV6Fresh | RHV6Fresh/Tower/ProperTower.lean:274 | G | idem |
| `reaches_analyticPairAt_iff` | RHV6Fresh | RHV6Fresh/Direct/Reached.lean:136 | G | idem |
| `towerPosition_eq_line_add_residue` | RHV6Fresh | RHV6Fresh/Terminal/CanonicalTransition.lean:94 | R | décalage D/π indépendant de q : forme compilée du fait |
| `grammar_step_regime_blind` | RHV6Fresh | RHV6Fresh/Terminal/GrammarKinematics.lean:418 | E | pas grammatical aveugle au régime |
| `sameHeight_grid_rigid_translation` | RHV6Fresh | RHV6Fresh/Terminal/MirrorDegeneracy.lean:165 | R | translation rigide de toute la grille à même hauteur |
| `every_prime_in_every_tower` | RHV6Fresh | RHV6Fresh/Terminal/OneZeroOnePrime.lean:41 | G | le fait nouveau lui-même |
| `tower_offset_rigid` | RHV6Fresh | RHV6Fresh/Terminal/OneZeroOnePrime.lean:49 | R | le fait nouveau lui-même |
| `onLine_iff_entry_at_point` | RHV6Fresh | RHV6Fresh/Terminal/OneZeroOnePrime.lean:56 | R | le fait nouveau lui-même |
| `onLine_iff_no_grid_translation` | RHV6Fresh | RHV6Fresh/Terminal/OneZeroOnePrime.lean:70 | R | le fait nouveau lui-même |
| `entry_arrow_point_irrelevant` | RHV6Fresh | RHV6Fresh/Terminal/OneZeroOnePrime.lean:79 | R | le fait nouveau lui-même |
| `tower_reads_any_prime` | RHV6Fresh | RHV6Fresh/Terminal/RayEnergy.lean:158 | G | D1 (RayEnergy) : une Tour à toute hauteur lit tout premier dans une cellule unique |
| `grammar_event_reads_no_radial` | RHV6Fresh | RHV6Fresh/Terminal/SpontaneousRegimeBreak.lean:75 | E | la grammaire ne lit aucun radial |
| `tower_grid_normal_form` | RHV6Fresh | RHV6Fresh/Terminal/TowerGrid.lean:37 | R | forme normale de la grille (TowerGrid) |
| `competing_regime_at_any_point` | RHV6Fresh | RHV6Fresh/Terminal/TowerGrid.lean:71 | R | le régime se lit en tout point de la grille |
| `towerMotion_incidence` | RHV6Fresh | RHV6Fresh/Tower/TrueTower.lean:47 | G | le mouvement porte une incidence pour tout k ∈ ℤ |
| `towerMotion_incidence_strictOrder` | RHV6Fresh | RHV6Fresh/Tower/TrueTower.lean:70 | G | incidences strictement ordonnées sur ℤ : grille infinie |
| `zeroTerm_real_iff_ray` | RHV6Fresh | RHV6Fresh/Terminal/ExplicitFormulaLink.lean:172 | G | le terme q^ρ/ρ est réel exactement aux C_k, pour TOUT k : tous les C_k sont des contacts |
| `pointed_primes_rank_only` | RHV6Fresh | RHV6Fresh/Terminal/PointedPrimeComparison.lean:42 | E | Occ et p_min fonctions du rang seul |
| `thm_PCanonicalCellFoundCountOne_is_false` | rhv3_lean | RHV3Lean/Objects/CanonicalTrueTowerState.lean:383 | G | « la cellule canonique contient exactement un premier » est faux (T ≥ 2π/log 1,5) |
| `thm_count_not_determined_by_T_beta_alone` | rhv3_lean | RHV3Lean/Objects/CanonicalTrueTowerState.lean:525 | E | le compte de premiers d'une cellule n'est pas fonction de (β,T) seul : cellule terminale vide, fenêtre voisine ≥ 1 |
| `thm_count_not_determined_by_T_beta_alone_v2` | rhv3_lean | RHV3Lean/Objects/CanonicalTrueTowerState.lean:639 | E | idem v2 |
| `thm_canonicalCell_foundCount_eq_zero_of_height_large` | rhv3_lean | RHV3Lean/Objects/CanonicalTrueTowerState.lean:324 | E | la cellule canonique est vide à grande hauteur : la Tour ne pointe pas un premier |
| `thm_cellFoundCount_eq_edgeRankDifference` | rhv3_lean | RHV3Lean/Objects/CountingRigidity.lean:170 | G | compte d'une cellule = différence de rangs aux bords (0, 1 ou plus) |
| `thm_foundPrimes_eq_image_rankInterval` | rhv3_lean | RHV3Lean/Objects/CountingRigidity.lean:147 | G | les premiers d'une cellule = un intervalle de rangs (pluriel en général) |
| `thm_T1_alone_does_not_force_T2_countDiff` | rhv3_lean | RHV3Lean/Objects/T1AloneCounterexampleForT2.lean:166 | E | T1 (un premier par cellule) ne force pas la succession de rang |
| `thm_T1_alone_does_not_force_T2_rankEquality` | rhv3_lean | RHV3Lean/Objects/T1AloneCounterexampleForT2.lean:204 | E | idem |
| `TCanonicalTowerState.thm_canonicalTowerState_carrier_not_subsingleton` | rhv2_fresh | RHV2Fresh/Master/CanonicalTower.lean:213 | G | un zéro porte plusieurs états de Tour |
| `subPrimeAuditReadout_not_uniquePrimeLocalization` | rhv2_fresh | RHV2Fresh/Master/PrimeLocalization.lean:109 | G | lecture sous-première : pas de localisation unique |
| `Diagnostics.thm_contactLawState_not_subsingleton` | RHV5Fresh | RHV5Fresh/Diagnostics/ContactLawScope.lean:49 | G | les lois de contact ne déterminent pas un état unique |
| `thm_cellBelowTwo_contradicts_T1` | rhv2_fresh | RHV2Fresh/Master/CanonicalOccurrenceConstraints.lean:177 | G | cellule sous 2 : T1 impossible |
| `Diagnostics.thm_contactLaws_do_not_determine_state` | RHV5Fresh | RHV5Fresh/Diagnostics/ContactLawScope.lean:44 | G | idem |
| `Diagnostics.thresholdCell_empty_of_height` | RHV5Fresh | RHV5Fresh/Diagnostics/ThresholdSelectorScope.lean:22 | G | cellule seuil vide à grande hauteur |


## 9. Conséquences pour la stratégie

1. Rien à retirer du code : aucun type n'est faux. À corriger : la prose de `Tower/TrueTowerStructure.lean`,
   `Tower/ProperTower.lean` (l. 48, §6), `Terminal/EnergyIdentity.lean` (nom/docstring de `geometry_selects_raccord_prime`),
   `Direct/PairTowers.lean` (en-tête) et les trois maîtres qui reprennent « deux contacts ».
2. Tous les R tiennent ; ceux qui sont posés au premier partagé se lisent en un point quelconque.
3. Tous les E de la direction unique (raccord, transport, registre, flèche, terme d'Euler local, charge de fibre) ont une
   part radiale indépendante de l'étiquette ; `M` ne fournit que `log M` à la part de hauteur, ou une non-dégénérescence.
   Toute recherche d'un mécanisme « propre au premier partagé » est donc vide par théorème ; la cible reste
   « la Tour d'arrivée n'est pas translatée » (`onLine_iff_no_grid_translation`), non dérivée.
4. La grappe T1 (rhv2 : 248 ; rhv3 : 19) est vide sur la Tour propre ; elle était déjà réfutée comme hypothèse sur la
   cellule canonique (V151, §8.7 de l'audit cumulé).

RÉFUTÉ : aucune proposition nouvelle ; la lecture « la Tour sélectionne un premier / a deux contacts » est contredite par
`every_prime_in_every_tower` et `zeroTerm_real_iff_ray` (prose seulement).
BORNÉ : E et R réécrits en un point quelconque, sans changement de contenu ; verrou inchangé.
SÉLECTIONS : 1300 théorèmes (RHV6Fresh 818, rhv3_lean 396, RHV5Fresh 48, rhv2_fresh 38).
RH_FOUND=FALSE
