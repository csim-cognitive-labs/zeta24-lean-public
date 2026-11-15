# Fragment C4c — rh_gap_criterion, dernier tiers (181 modules, 2399 théorèmes)

Base : `formalization/rh_gap_criterion/` (Mathlib v4.31.0), hors hiérarchie d'autorité RHV6 (CLAUDE.md §2), auditée selon les mêmes règles. Données : `data/rh_gap_criterion.jsonl`, lot `lots/C4c.txt`. Colonne « entraîne » = nombre de théorèmes (sur tout `rh_gap_criterion.jsonl`, dépendances inverses calculées par script à partir de `deps_project`) dont la preuve utilise le nom ; pour un nom porté par deux déclarations (12 noms dans le projet) le décompte est cumulé. Le TYPE Lean fait foi ; les énoncés sont des lectures du type (et de la docstring, simple aide). Statuts après application du correctif de contrôle n°1 : une hypothèse qui n'est que condition de domaine, antécédent de la relation énoncée (injectivité, unicité, implication entre deux notions, caractérisation) ou paquet de propriétés toutes déjà établies est notée `CONFIRMÉE (domaine : …)` ; `CONFIRMÉE SOUS CONDITION` est réservé à une restriction substantielle (zéro hors ligne, prémisse nommée non déchargée, passage particulier…). Les théorèmes dont la conclusion est l'énoncé `∀ρ non trivial, β = 1/2` (forme dépliée de RH, sans le terme `RiemannHypothesis`) sont notés `IMPLIQUE RH SOUS PRÉMISSE` avec cette précision. Un théorème `RH → P` (RH en hypothèse) est noté `CONFIRMÉE` et signalé dans la section RH.

**Précision sur le périmètre (consigne du lot vs données).** La consigne indiquait que les modules de la bibliothèque `RiemannHypothesisProof` ne sont pas compilés. Les données disent autre chose pour les 20 modules `RiemannHypothesisProof.*` du lot : `data/rh_gap_criterion_modules.tsv` les marque « compilé » (oleans présents, théorèmes extraits avec axiomes standard). Ils sont donc audités ici comme les autres (rubrique dédiée dans les tables). Seuls sont NON COMPILÉS, selon le même fichier, les 15 modules listés en fin de fragment (« Modules non compilés de la bibliothèque »), absents du lot.

Répartition des statuts : CONFIRMÉE : 2189, CONFIRMÉE SOUS CONDITION : 97, IMPLIQUE RH SOUS PRÉMISSE : 42, RÉFUTATION COMPILÉE : 36, ÉQUIVALENTE À RH : 31, HORS STANDARD : 4.

## Termes hors maître utilisés dans ce lot

Un terme absent du glossaire de `VERITES_MAITRE.md` est signalé « (terme hors maître) » à sa première occurrence dans les tables ; définitions :

| terme | définition (lue dans les types/docstrings du lot) |
|---|---|
| constellation | liste ordonnée des zéros de hauteur < T (représentants positifs) ; distincte de la « fibre » du maître (zéros de même hauteur seulement) |
| représentant positif | zéro non trivial de hauteur > 0 d'une constellation (les zéros de hauteur négative en sont les conjugués) |
| partenariat | objet couplant un zéro, son miroir, un bloc premier, un opérateur de transport et une capture zéros/premiers (CanonicalLocalizedZeroPrimePartnership) |
| soudure | « weld » : assemblage d'un zéro hors ligne, de son miroir et d'un bloc premier (LocalizedMirrorPairPrimeWeldCase) |
| jonction | couple (zéro, miroir) placé sur une colonne première (MirrorPairPrimeJunction) |
| cage | paquet de contraintes sur une paire hors ligne (ZeroGapConstraintCage) |
| bloc | fenêtre de rangs premiers consécutifs [pStart, pEnd[ ; « bloc de premier retour » = fenêtre entre deux états mod 6 identiques successifs |
| curl | circulation mixte ligne/colonne : différence de différences de lignes entre colonnes adjacentes |
| porteur | « carrier » : fonction n ↦ terme de Perron individuel du zéro à p(n) (holonomies de bloc) |
| Perron | noyau/intégrande de Perron de −ζ'/ζ, outil de la formule explicite (cf. formule explicite, V100/V121) |
| cocycle | rapport de caractères de Tour entre l'échelle d'un contact et celle d'un premier |
| E44 | loi tangente historique des deux contacts (β·tan(γ·log contact)=γ, largeur log mπ/γ) |
| EncZ | encodage de la grammaire des zéros vers la grammaire première |
| GZ | grammaire des zéros (écarts de hauteur d'une constellation) |
| trouble | écart de hauteur nul entre deux membres adjacents d'une constellation ordonnée |
| voix | « grammar voice » : poids de grammaire fois différence de porteur |
| quartet | les quatre zéros ρ, ρ̄, 1−ρ̄, 1−ρ (cf. V63) |
| naturalité | commutation du renversement grammatical avec l'opérateur du partenariat (R12) ; équivaut à β=1/2 (V140) |
| capture | NOTE homonymie : ici « capture » désigne la capture découplée zéros/premiers (DecoupledZeroPrimeCapture), non la « capture » du maître (rayon miroir posé sur le rayon, V185) |
| tilt | pondération de conservation (∑P=1, ∑d·P=L) annulant la dérive moyenne |
| cobord | différence φ(n+1)−φ(n) d'un potentiel grammatical ; télescope |
| Hadamard | produit de Hadamard de ξ (diviseurs de ξ) ; outil analytique des bornes de −ζ'/ζ |
| digamma | dérivée logarithmique de Γ ; intervient dans l'équation fonctionnelle de −ζ'/ζ |
| Backlund | substitut entier (s−1)ζ(s) et majorant grossier de N(T) |
| rectangle | rectangle de Perron [σL(N),σR]×[−T,T] ; « admissible » = aucun pôle sur son bord |
| producteur | proposition universelle « toute donnée connue produit l'égalité cible » ; ici toujours prouvée équivalente à RH |
| fidélité | conservation d'une propriété (nullité, norme) entre côté zéros et côté premiers |
| défaut | défaut radial β−1/2 (V140/V102) ou défaut de ligne (deux lignes zéro/miroir différentes) |
| paquet | structure « Coverage »/« Profile »/« Packet » regroupant des propriétés toutes établies (déclarée « toujours réalisée » quand un théorème _holds existe) |
| opérateur | matrice 2×2 de transport du partenariat (entrées directe et réfléchie ratio^(∓défaut)) |
| canal | « channel » : somme sur les zéros du terme résiduel, côté explicite |

## Tables par module

<!-- TABLES START -->

### `RhGapCriterion.Round27FField33ProducerAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `offLineCellModel_exists` | Pour tout point du plan et tout bloc de premiers sélectionné, il existe un modèle hors ligne (structure point/bloc) portant ce point et ce bloc. (terme hors maître « bloc » : fenêtre de rangs premiers consécutifs [pStart, pEnd[ ; « bloc de premier retour » = fenêtre entre deux états mod 6 identiques successifs) | CONFIRMÉE | AJOUT | 0 |
| `OffLineCellModel.commonHeightPhase` | Pour tout modèle hors ligne, la phase de hauteur du bloc est la même en M.point et en son réfléchi 1−conj, non nulle, et l'opérateur est l'inverse de cette phase fois le transport (vrai en un point libre, sans zéro). (terme hors maître « opérateur » : matrice 2×2 de transport du partenariat (entrées directe et réfléchie ratio^(∓défaut))) | CONFIRMÉE | AJOUT | 0 |
| `OffLineCellModel.radialDefect` | Pour tout modèle hors ligne, l'opérateur est l'opérateur croisé du bloc au défaut radial β−1/2 (point libre). (terme hors maître « défaut » : défaut radial β−1/2 (V140/V102) ou défaut de ligne (deux lignes zéro/miroir différentes)) | CONFIRMÉE | AJOUT | 0 |
| `OffLineCellModel.reflectionReciprocity` | Pour tout modèle hors ligne, le produit des deux entrées hors diagonale de l'opérateur vaut 1 (réciprocité réfléchie). | CONFIRMÉE | AJOUT | 1 |
| `OffLineCellModel.involution` | Pour tout modèle hors ligne, l'opérateur est une involution (carré = identité). | CONFIRMÉE | AJOUT | 0 |
| `OffLineCellModel.adjoint` | Pour tout modèle hors ligne, l'adjoint de l'opérateur est la matrice antidiagonale de rapport^(±(β−1/2)). | CONFIRMÉE | AJOUT | 0 |
| `OffLineCellModel.ttStar_and_tStarT` | Pour tout modèle hors ligne, T·T† et T†·T sont les matrices diagonales de rapport^(∓2(β−1/2)) (point libre). | CONFIRMÉE | AJOUT | 0 |
| `OffLineCellModel.field33_fails_offLine` | Pour un modèle hors ligne de partie réelle ≠ 1/2, les deux entrées hors diagonale de l'opérateur diffèrent (« field33 » échoue exactement hors ligne). | CONFIRMÉE SOUS CONDITION (point de partie réelle ≠ 1/2) | V140 | 1 |
| `separation_32_cannot_produce_33` | Dériver l'égalité des deux entrées hors diagonale (field33) de la fidélité TDD de tous les partenariats canoniques localisés est équivalent à RH. (terme hors maître « partenariat » : objet couplant un zéro, son miroir, un bloc premier, un opérateur de transport et une capture zéros/premiers (CanonicalLocalizedZeroPrimePartnership)) (terme hors maître « fidélité » : conservation d'une propriété (nullité, norme) entre côté zéros et côté premiers) | ÉQUIVALENTE À RH (la conjonction des surfaces non terminales (fidélité du partenariat) implique field33 pour tout partenariat canonique) | V140 | 0 |
| `unconditional_law_produces_field33_iff_rh` | Méta-impossibilité : pour toute Q vraie, dire que Q produit field33 partout équivaut à RH. | ÉQUIVALENTE À RH (pour toute proposition Q prouvée, « Q entraîne field33 pour tous les partenariats » ⟺ RH) | V140 | 2 |
| `Q1_localization_unique` | Deux partenariats canoniques localisés du même zéro ont même contexte local, même miroir et mêmes porteurs/fibres directs et réfléchis (unicité de la localisation). (terme hors maître « porteur » : « carrier » : fonction n ↦ terme de Perron individuel du zéro à p(n) (holonomies de bloc)) | CONFIRMÉE | AJOUT | 0 |
| `Q1_operator_unique` | Deux partenariats du même zéro et du même bloc ont même transport et même opérateur. | CONFIRMÉE | AJOUT | 2 |
| `Q1_is_generic_control` | L'unicité de la localisation étant vraie sans condition, « unicité ⟹ field33 partout » équivaut à RH (classification contrôle générique). | ÉQUIVALENTE À RH (l'unicité de l'opérateur (même zéro, même bloc) entraîne field33 pour tout partenariat canonique) | V140 | 0 |
| `Q2_transport_injective` | L'opérateur croisé d'un bloc est injectif sur la partie réelle : deux points ayant même opérateur ont même partie réelle. | CONFIRMÉE | AJOUT | 2 |
| `Q2_holds_offLine` | Pour tout point du plan, deux modèles de même bloc et de même opérateur ont même partie réelle (injectivité du transport valable hors zéro). | CONFIRMÉE | AJOUT | 0 |
| `Q3_mirror_naturality` | Le produit des deux lectures orientées de l'opérateur croisé d'un bloc en un point vaut 1. | CONFIRMÉE | AJOUT | 0 |
| `Q3_product_holds_but_field33_fails` | Hors ligne le produit des deux lectures vaut 1 tandis que leur égalité échoue. | CONFIRMÉE SOUS CONDITION (modèle de partie réelle ≠ 1/2) | AJOUT | 0 |
| `Q4_grammatical_assembly_is_member_blind` | L'holonomie grammaticale d'un bloc (produit des 1−2·cross) ne dépend que du bloc, non du membre (deux partenariats de même bloc). | CONFIRMÉE | AJOUT | 0 |
| `Q4_grammatical_assembly_value` | Cette holonomie vaut le produit sigma(pStart)·sigma(pEnd) : valeur explicite indépendante du membre. | CONFIRMÉE | AJOUT | 0 |
| `Q5_two_orientation_compatibility_iff_rh` | Exiger que le transport 0 1 égale le transport 1 0 pour tout partenariat canonique localisé équivaut à RH. | ÉQUIVALENTE À RH (compatibilité des deux orientations du transport pour tout partenariat canonique) | V140 | 0 |
| `Q6_defect_persistence` | Deux partenariats de même bloc et de même entrée d'opérateur ont même défaut radial (persistance du défaut). | CONFIRMÉE | AJOUT | 1 |
| `Q6_persistence_compatible_with_nonzero_defect` | Pour tout bloc et tout défaut d, il existe un modèle hors ligne de défaut d dont l'opérateur porte ratio^(−d). | CONFIRMÉE | AJOUT | 0 |
| `audit_synthesis` | Synthèse : les lois Q1, Q2, Q3, Q4, Q6 tiennent simultanément pour tout partenariat canonique localisé. | CONFIRMÉE | AJOUT | 0 |
| `simultaneousTwoPositionPoleLaw_implies_surface25` | La loi simultanée de pôle aux deux positions entraîne la surface 25 (β=1/2 ou pôle d'ordre −1 en l'une des deux positions) pour tout zéro. | CONFIRMÉE | AJOUT | 0 |
| `simultaneous_pole_available_only_off_the_line` | Pour un zéro strictement à droite de la ligne, la double condition de pôle donne le pôle à la position β (moitié droite de la loi simultanée). | CONFIRMÉE SOUS CONDITION (zéro strictement à droite de 1/2 et pôle simultané aux deux positions) | AJOUT | 0 |

### `RhGapCriterion.Round27GSemanticAlignmentRepair`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `OrderedConstellationTrouble.gapIndex_lt` | Champ de OrderedConstellationTrouble : l'indice d'écart est inférieur à la longueur de la liste des écarts de constellation. (terme hors maître « constellation » : liste ordonnée des zéros de hauteur < T (représentants positifs) ; distincte de la « fibre » du maître (zéros de même hauteur seulement)) (terme hors maître « trouble » : écart de hauteur nul entre deux membres adjacents d'une constellation ordonnée) | CONFIRMÉE | AJOUT | 1 |
| `OrderedConstellationTrouble.twoMemberWindow` | Champ : la fenêtre de deux membres tient dans les représentants positifs. | CONFIRMÉE | AJOUT | 0 |
| `OrderedConstellationTrouble.gap_eq_zero` | Champ : l'écart de constellation à l'indice du trouble vaut 0. | CONFIRMÉE | AJOUT | 0 |
| `OrderedConstellationTrouble.orderedGap_eq_zero` | Champ : l'écart interne ordonné avec le suivant vaut some 0. | CONFIRMÉE | AJOUT | 5 |
| `orderedConstellationTrouble_of_offline` | Un représentant positif hors ligne à la hauteur T produit un trouble de constellation ordonné (simple remise en forme). (terme hors maître « représentant positif » : zéro non trivial de hauteur > 0 d'une constellation (les zéros de hauteur négative en sont les conjugués)) | CONFIRMÉE SOUS CONDITION (il existe un représentant positif hors ligne) | AJOUT | 1 |
| `GlobalZeroPrimePartnership.prime_history_determines_zero_source` | La source de zéros déterminée par une continuation déterminée par les premiers est la source du partenariat global. | CONFIRMÉE | AJOUT | 1 |
| `MirrorPairDefect.signedSeparation_eq_two_mul_radial` | La séparation signée d'un défaut de paire miroir vaut deux fois son défaut radial. | CONFIRMÉE | AJOUT | 0 |
| `positiveRepresentative_height_lt` | Un représentant positif de la constellation T a hauteur strictement inférieure à T. | CONFIRMÉE | AJOUT | 11 |
| `canonicalLocalizedPartnership_context_independent_of_zero_window` | Changer la fenêtre zéro ne change pas le contexte local (membres) du partenariat canonique localisé. | CONFIRMÉE | AJOUT | 0 |
| `canonicalLocalizedPartnership_operator_independent_of_zero_window` | Changer la fenêtre zéro ne change pas l'opérateur du partenariat canonique localisé. | CONFIRMÉE | AJOUT | 1 |
| `offLine_positive_member_yields_partnership_and_ordered_trouble` | Un même représentant positif hors ligne produit un partenariat localisé (défaut radial ≠ 0) sur tout bloc et un trouble ordonné. | CONFIRMÉE SOUS CONDITION (représentant positif hors ligne) | AJOUT | 4 |

### `RhGapCriterion.Round27GTwoBaseReflectedLaurentTDD`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `twoBaseReflectedLaurentEqualityAt_iff_baseChangeRatioEq` | L'égalité de Laurent à deux bases en ρ équivaut à l'égalité des rapports de changement de base direct et réfléchi (par définition). | CONFIRMÉE | AJOUT | 1 |
| `crossTransport_offdiag_eq_of_twoBaseReflectedLaurentEqualityAt` | Cette égalité force l'égalité des deux entrées hors diagonale du transport croisé réfléchi. | CONFIRMÉE | AJOUT | 1 |
| `twoBaseReflectedLaurentEqualityAt_forces_critical` | Cette égalité en ρ force β=1/2. | CONFIRMÉE | AJOUT | 1 |
| `twoBaseReflectedLaurentEqualityAt_of_critical` | Sur la ligne critique l'égalité de Laurent à deux bases tient. | CONFIRMÉE | AJOUT | 1 |
| `twoBaseReflectedLaurentEqualityAt_iff_critical` | L'égalité de Laurent à deux bases en ρ équivaut à ρ sur la ligne critique. | CONFIRMÉE | AJOUT | 1 |
| `twoBaseReflectedLaurentEquality_iff_rh` | Le paquet global de l'égalité de Laurent à deux bases est de force RH exacte. (terme hors maître « paquet » : structure « Coverage »/« Profile »/« Packet » regroupant des propriétés toutes établies (déclarée « toujours réalisée » quand un théorème _holds existe)) | ÉQUIVALENTE À RH (égalité de Laurent à deux bases pour tous les zéros) | AJOUT | 0 |

### `RhGapCriterion.Round27HOrderedHeightFiberContiguity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `orderedPositiveRepresentatives_height_mono` | La hauteur est croissante au sens large le long de la liste ordonnée des représentants positifs. | CONFIRMÉE (domaine : indices dans la liste ordonnée) | V8 | 1 |
| `orderedHeightFiber_sandwich` | Lemme de sandwich : la position intermédiaire a la même hauteur que les extrêmes. | CONFIRMÉE (domaine : indices dans la liste ordonnée) | V50 | 2 |
| `orderedHeightFiber_internal_gap_zero` | Tout écart interne d'un bloc de hauteur partagée est nul. | CONFIRMÉE (domaine : indices dans la liste ordonnée) | V50 | 1 |
| `orderedHeightFiber_internal_gap_zero_constellationGaps` | Le même fait exprimé sur la liste des écarts de constellation (écart à l'indice j nul). | CONFIRMÉE (domaine : indices dans la liste ordonnée) | V50 | 2 |
| `orderedHeightFiber_internal_zero_gap_forall` | Pour un bloc [i,k] de même hauteur aux extrémités, tous les écarts internes j∈[i,k[ sont nuls. | CONFIRMÉE (domaine : indices dans la liste ordonnée) | V50 | 2 |
| `orderedHeightFiber_internal_zero_gap_card` | Le cardinal de Finset.Ico i k vaut k−i. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.Round27ITrueMirrorOrderedFiberBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `OrderedPositiveMirrorPairWitness.zeroIndex_lt` | Champ de OrderedPositiveMirrorPairWitness : l'indice du zéro est dans la liste ordonnée. | CONFIRMÉE | AJOUT | 8 |
| `OrderedPositiveMirrorPairWitness.mirrorIndex_lt` | Champ : l'indice du miroir est dans la liste ordonnée. | CONFIRMÉE | AJOUT | 8 |
| `OrderedPositiveMirrorPairWitness.zeroAt` | Champ : l'entrée de la liste à l'indice du zéro est ρ. | CONFIRMÉE | AJOUT | 6 |
| `OrderedPositiveMirrorPairWitness.mirrorAt` | Champ : l'entrée à l'indice du miroir est reflectConjZero ρ (le miroir). | CONFIRMÉE | AJOUT | 6 |
| `positive_true_zero_mem_orderedPositiveRepresentatives` | Un vrai zéro positif borné appartient à la liste ordonnée positive. | CONFIRMÉE (domaine : hauteur de ρ positive et < T) | V64 | 1 |
| `positive_true_mirror_mem_orderedPositiveRepresentatives` | Le réfléchi conjugué (miroir) d'un zéro positif borné appartient à la même liste. | CONFIRMÉE (domaine : hauteur de ρ positive et < T) | V64 | 1 |
| `orderedPositiveMirrorPairWitness_exists` | Il existe un témoin donnant les deux positions réelles du zéro et de son miroir dans la liste ordonnée. | CONFIRMÉE (domaine : hauteur de ρ positive et < T) | V64 | 10 |
| `OrderedPositiveMirrorPairWitness.same_height` | Les deux positions du témoin portent exactement la même hauteur. | CONFIRMÉE | V65 | 4 |
| `OrderedPositiveMirrorPairWitness.height_eq_zero_between` | Toute position entre les deux positions du couple (dans l'un ou l'autre ordre) porte la hauteur de ρ. | CONFIRMÉE | AJOUT | 1 |
| `OrderedPositiveMirrorPairWitness.internal_constellation_gaps_zero_between` | Selon l'ordre du couple, tous les écarts de constellation entre les deux positions sont nuls. | CONFIRMÉE | AJOUT | 2 |
| `positiveMirrorPair_localContext_and_orderedView` | Le contexte local vrai et la liste ordonnée contiennent simultanément le zéro et son miroir. | CONFIRMÉE (domaine : hauteur de ρ positive et < T) | V64 | 0 |

### `RhGapCriterion.Round27JOrderedRowPrefixRectangle`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `orderedRowPrefix_succ_of_lt` | Étendre le préfixe de ligne d'un rang ajoute exactement l'entrée de cette position. | CONFIRMÉE | AJOUT | 1 |
| `orderedRowPrefix_step_eq_entry` | La différence de deux préfixes successifs récupère exactement l'entrée de la ligne (propriété sans perte). | CONFIRMÉE | AJOUT | 1 |
| `OrderedPositiveMirrorPairWitness.prefixSteps_exact` | Dans un témoin de paire miroir, les deux différences de préfixes récupèrent les entrées du zéro et de son miroir. | CONFIRMÉE | AJOUT | 4 |
| `OrderedPositiveMirrorPairWitness.prefixSteps_separate_of_defect` | Un défaut de ligne sépare les différences de préfixes des deux positions du témoin. | CONFIRMÉE | AJOUT | 5 |
| `positiveMirrorPair_realPrefixDefect_exists` | Un défaut de ligne est visible dans les préfixes d'un témoin réel. | CONFIRMÉE | AJOUT | 0 |
| `positive_offline_true_pair_changeFamily_realPrefixDefect` | Tout zéro positif hors ligne possède une colonne première (classe 2 ou 4 mod 6, poids ≠ 0) où ses préfixes zéro/miroir diffèrent. | CONFIRMÉE SOUS CONDITION (zéro positif borné hors ligne) | AJOUT | 0 |

### `RhGapCriterion.Round27KMixedRowColumnCurl`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `mixedRowColumnCurl_eq_rowDifference_sub` | Le curl mixte ligne/colonne est la variation de la différence de lignes entre colonnes adjacentes. (terme hors maître « curl » : circulation mixte ligne/colonne : différence de différences de lignes entre colonnes adjacentes) | CONFIRMÉE | AJOUT | 2 |
| `mixedRowColumnCurl_swap` | Échanger les deux lignes change le signe du curl. | CONFIRMÉE | AJOUT | 0 |
| `mixedRowColumnCurl_self` | Deux lignes identiques ont un curl nul. | CONFIRMÉE | AJOUT | 0 |
| `mixedRowColumnCurl_eq_zero_iff_rowDifference_eq` | Curl nul ⟺ différence de lignes constante sur deux colonnes adjacentes. | CONFIRMÉE | AJOUT | 1 |
| `OrderedPositiveMirrorPairWitness.mixedCurl_eq_prefixStep_curl` | Pour un témoin du couple miroir, le curl mixte se lit dans les différences de préfixes du témoin. | CONFIRMÉE | AJOUT | 2 |
| `LocalizedMirrorPairPrimeWeldCase.pairAssembly_first_rowDifference_ne_zero` | Dans un cas de soudure paire-miroir localisée, la différence de lignes source de la première arête du bloc d'assemblage est non nulle. (terme hors maître « soudure » : « weld » : assemblage d'un zéro hors ligne, de son miroir et d'un bloc premier (LocalizedMirrorPairPrimeWeldCase)) | CONFIRMÉE | AJOUT | 2 |
| `LocalizedMirrorPairPrimeWeldCase.pairAssembly_curl_eq_zero_iff_adjacent_rowDifference_eq` | Le curl mixte de la paire s'annule ⟺ la différence de lignes de la première arête égale celle de la seconde. | CONFIRMÉE | AJOUT | 1 |
| `LocalizedMirrorPairPrimeWeldCase.pairAssembly_curl_zero_propagates_defect_to_second_edge` | Un curl nul propage le défaut de ligne à la seconde arête du bloc. | CONFIRMÉE | AJOUT | 1 |
| `LocalizedMirrorPairPrimeWeldCase.pairAssembly_curl_ne_zero_of_second_edge_rows_equal` | Si les deux lignes (zéro/miroir) coïncident sur la seconde arête, le curl mixte est non nul. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.Round27LPairwiseHeightFiberRigidity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `distinct_central_trueZeros_have_distinct_heights` | Deux vrais zéros distincts tous deux sur la ligne critique n'ont pas la même hauteur. | CONFIRMÉE (domaine : deux zéros distincts, tous deux de partie réelle 1/2) | V161 | 0 |
| `ordered_central_pair_heightGap_pos` | Dans la liste ordonnée réelle, deux entrées centrales à positions distinctes ont un écart de hauteur strictement positif. | CONFIRMÉE (domaine : deux entrées centrales à positions ordonnées i<j) | V161 | 1 |
| `ordered_adjacent_zeroHeightGap_zero_forces_off` | Un écart de hauteur nul entre deux membres adjacents de la liste ordonnée force au moins l'un d'eux hors ligne. | CONFIRMÉE | AJOUT | 0 |
| `off_trueZero_gives_actual_ordered_zeroGap_constructive` | Un vrai zéro hors ligne donne un écart de constellation nul (route constructive, sans l'équivalence terminale). | CONFIRMÉE SOUS CONDITION (zéro positif borné hors ligne) | V162 | 1 |
| `off_mirror_zeroHeightGap_but_lossless_primeEdgeGap_nonzero` | Pour un zéro hors ligne, l'écart de hauteur zéro/miroir est nul et l'écart transformé sans perte sur l'arête première est non nul, à tout n. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V162 | 1 |

### `RhGapCriterion.Round27MZeroGapConstraintCage`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260901.ZeroGapConstraintCage.quartet_seed` | Champ de ZeroGapConstraintCage : la graine du quartet est ρ. (terme hors maître « cage » : paquet de contraintes sur une paire hors ligne (ZeroGapConstraintCage)) (terme hors maître « quartet » : les quatre zéros ρ, ρ̄, 1−ρ̄, 1−ρ (cf. V63)) | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.mirror_distinct` | Champ : le miroir est distinct de ρ. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.mirror_same_height` | Champ : le miroir a la même partie imaginaire que ρ. | CONFIRMÉE | V65 | 0 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.mirror_complementary_re` | Champ : la partie réelle du miroir est 1−β. | CONFIRMÉE | V65 | 0 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.mirror_same_multiplicity` | Champ : le miroir a la même multiplicité. | CONFIRMÉE | V65 | 0 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.actual_ordered_zero_gap` | Champ : l'écart interne ordonné à l'indice du zéro-gap vaut some 0. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.contact_pair_recovers_member` | Champ : la paire de contacts tangents récupère β (et γ) du membre. | CONFIRMÉE | V45 | 0 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.mirror_contact_distinct` | Champ : le contact tangent du miroir à l'indice du contact diffère de celui de ρ. | CONFIRMÉE | V163 | 0 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.no_common_E44_contact` | Champ : la loi E44 éliminée ne peut tenir à la fois pour β et 1−β (m≥1, domaine). (terme hors maître « E44 » : loi tangente historique des deux contacts (β·tan(γ·log contact)=γ, largeur log mπ/γ)) | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.e44_radial_defect_nonzero` | Champ : le défaut radial E44 tiré de β est non nul (m≥1, domaine). | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.reconstructed_grammar_same_block` | Champ : le bloc de grammaire complète reconstruit depuis les zéros coïncide avec celui de la grammaire première canonique. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.vonMangoldt_prime_gap_exact` | Champ : l'écart premier reconstruit depuis les zéros à l'indice d'arête égale gnat. | CONFIRMÉE | V48 | 1 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.canonical_prime_gap_positive` | Champ : l'écart premier canonique à l'indice d'arête est strictement positif. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.canonical_prime_log_width_positive` | Champ : la largeur log canonique de l'arête première est strictement positive. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.scalar_height_span_same_for_mirror` | Champ : l'étendue de hauteur de la Tour sur l'arête première est la même pour le zéro et son miroir. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.lossless_prime_edge_gap_nonzero` | Champ : l'écart transformé sans perte sur l'arête première est non nul. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.vonMangoldt_lossless_gap_same_as_canonical` | Champ : l'écart von Mangoldt transformé égale l'écart canonique transformé sur l'arête. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.quartet_card_four` | Champ : le quartet a exactement quatre membres. | CONFIRMÉE | V63 | 0 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.quartet_all_multiplicities_equal` | Champ : les quatre membres du quartet ont même multiplicité. | CONFIRMÉE | V63 | 0 |
| `ScientificRebuild20260901.ZeroGapConstraintCage.quartet_six_voice_separations` | Champ : les six séparations de voix du quartet sur l'arête première tiennent. (terme hors maître « voix » : « grammar voice » : poids de grammaire fois différence de porteur) | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.zeroGapConstraintCage_of_off` | Tout membre positif hors ligne engendre la cage complète de contraintes. | CONFIRMÉE SOUS CONDITION (zéro positif borné hors ligne) | V162 | 0 |
| `ScientificRebuild20260901.cage_zero_scalar_but_nonzero_lossless` | Dans toute cage, la différence scalaire des étendues de hauteur entre les membres supérieurs est nulle tandis que l'écart transformé complet est non nul. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.cage_zero_relation_and_positive_prime_edge` | Toute cage porte à la fois une relation nulle côté zéros et un écart premier strictement positif immuable. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.Round27NTripleTransitionRigidity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260901.reconstructedTransitionLabel_eq_canonical` | L'étiquette de transition reconstruite depuis les zéros égale l'étiquette canonique à toute position n. | CONFIRMÉE | V48 | 2 |
| `ScientificRebuild20260901.reconstructedTransitionOccurrence_eq_canonical` | L'occurrence de transition indexée reconstruite égale la canonique. | CONFIRMÉE | V48 | 6 |
| `ScientificRebuild20260901.adjacentCanonicalTransitionOccurrences_ne` | Deux occurrences de transition adjacentes canoniques sont distinctes, même à étiquettes égales. | CONFIRMÉE | AJOUT | 8 |
| `ScientificRebuild20260901.reconstructedTripleTransitionPair_eq_canonical` | La paire de transitions du triplet reconstruite égale la canonique. | CONFIRMÉE | V48 | 2 |
| `ScientificRebuild20260901.no_single_transition_occurrence_double_localization` | Une même occurrence de transition ne peut être à la fois les deux occurrences adjacentes d'un triplet. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.TripleTransitionRigidity.transition_pair_lock` | Sous le paquet de rigidité, la paire de transitions reconstruite égale la canonique. | CONFIRMÉE (domaine : paquet TripleTransitionRigidity (toujours réalisé)) | V48 | 0 |
| `ScientificRebuild20260901.TripleTransitionRigidity.transition_occurrences_distinct` | Sous le paquet, les deux occurrences de transition canoniques sont distinctes. | CONFIRMÉE (domaine : paquet TripleTransitionRigidity (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260901.TripleTransitionRigidity.left_prime_gap_positive` | Sous le paquet, l'écart premier gnat n est positif. | CONFIRMÉE (domaine : paquet TripleTransitionRigidity (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260901.TripleTransitionRigidity.right_prime_gap_positive` | Sous le paquet, l'écart premier gnat (n+1) est positif. | CONFIRMÉE (domaine : paquet TripleTransitionRigidity (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260901.TripleTransitionRigidity.left_log_width_positive` | Sous le paquet, la largeur log canonique de l'arête n est positive. | CONFIRMÉE (domaine : paquet TripleTransitionRigidity (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260901.TripleTransitionRigidity.right_log_width_positive` | Sous le paquet, la largeur log de l'arête n+1 est positive. | CONFIRMÉE (domaine : paquet TripleTransitionRigidity (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260901.TripleTransitionRigidity.left_span_law` | Sous le paquet, la différence d'étendues de hauteur à l'arête n entre T1 et T0 vaut (T1−T0)/π fois la largeur log. | CONFIRMÉE (domaine : paquet TripleTransitionRigidity (toujours réalisé)) | V16 | 0 |
| `ScientificRebuild20260901.TripleTransitionRigidity.right_span_law` | Idem à l'arête n+1 entre T2 et T1. | CONFIRMÉE (domaine : paquet TripleTransitionRigidity (toujours réalisé)) | V16 | 0 |
| `ScientificRebuild20260901.TripleTransitionRigidity.left_span_zero_iff` | Sous le paquet, la différence gauche d'étendues est nulle ⟺ T1=T0. | CONFIRMÉE (domaine : paquet TripleTransitionRigidity (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260901.TripleTransitionRigidity.right_span_zero_iff` | Sous le paquet, la différence droite est nulle ⟺ T2=T1. | CONFIRMÉE (domaine : paquet TripleTransitionRigidity (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260901.tripleTransitionRigidity` | Constructeur universel : le paquet de rigidité de triplet de transitions existe pour tous T0,T1,T2,n. | CONFIRMÉE | AJOUT | 1 |

### `RhGapCriterion.Round27OPassageTransitionOccurrence`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260901.passageReconstructedTransitionOccurrence_eq_canonical` | Dans un raccord structurel, l'occurrence de transition reconstruite d'un passage égale sa canonique. | CONFIRMÉE | V48 | 1 |
| `ScientificRebuild20260901.passageOccurrence_vonMangoldt_locks` | Tous les verrous arithmétiques (position, écart, étiquette de transition) de l'occurrence d'un passage sont fixés par von Mangoldt. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260901.sameRaccordPassageTransitionOccurrenceFidelity` | Dans un raccord passage→place fixé, exactement une occurrence indexée réalise à la fois la reconstruite et la canonique. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.twoPassageRaccord_first_place` | Dans un raccord ordonné à deux passages, le premier passage reçoit la place interne 0. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260901.twoPassageRaccord_second_place` | Dans un raccord ordonné à deux passages, le second reçoit la place interne 1. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260901.threeZeroTwoPassageTransitionOccurrences` | Les deux passages réels d'un raccord à trois membres portent les deux occurrences de transition canoniques adjacentes. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.threeZeroTwoPassageTransitionOccurrences_ne` | Les deux occurrences de passage d'un raccord à trois membres sont distinctes. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.Round27PDoubleLocalizationStrengthAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260901.fullQuartetOffDoubleTransitionLocalization_iff_riemannHypothesis` | Le producteur universel de double localisation de transition est exactement de force RH. (terme hors maître « producteur » : proposition universelle « toute donnée connue produit l'égalité cible » ; ici toujours prouvée équivalente à RH) | ÉQUIVALENTE À RH (double localisation universelle de transition pour le quartet hors ligne) | AJOUT | 0 |
| `ScientificRebuild20260901.false_of_upper_double_transition_localization` | Une occurrence ne peut être à la fois la canonique n et la canonique n+1 : la double localisation dérivée donnerait False. | RÉFUTATION COMPILÉE (double localisation d'une même occurrence de transition (piste « double localisation »)) | AJOUT | 0 |

### `RhGapCriterion.Round27QContactAlgebraicThreePrimeInterval`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.stage_pos` | Champ de ContactAlgebraicThreePrimeInterval : l'étage est ≥ 1. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.left_ge_two` | Champ : le bord gauche de la signature de contact est ≥ 2. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.right_ge_two` | Champ : le bord droit de la signature de contact est ≥ 2. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.arithmetic_count_three` | Champ : le comptage arithmétique local entre les deux bords vaut 3. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.startRank_eq_leftPrimeCount` | Le rang de départ égale le compte de premiers à gauche. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.startRank_eq_floor_piReal_left` | Le rang de départ égale ⌊π réel(gauche)⌋. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.reconstructed_left_count_eq_startRank` | Le comptage reconstruit depuis les zéros (canal von Mangoldt) au bord gauche égale le rang de départ. (terme hors maître « canal » : « channel » : somme sur les zéros du terme résiduel, côté explicite) | CONFIRMÉE | V145 | 0 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.reconstructed_local_count_three` | Le comptage local reconstruit depuis les zéros sur les deux mêmes bords vaut exactement 3. | CONFIRMÉE | V145 | 1 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.triplet_is_prime` | Champ : les trois objets de la lecture (premier, pivot, troisième) sont de vrais premiers. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.pivot_is_middle_of_triplet` | Champ : le premier pivot du triplet issu des contacts est p(rang de départ + 1), le premier central. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.two_gaps_positive` | Champ : les deux écarts entrant et sortant sont strictement positifs. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.two_occurrences_distinct` | Champ : les deux occurrences de transition entrante et sortante sont distinctes. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.vonMangoldt_first_position_lock` | Von Mangoldt reconstruit exactement la position du premier terme du triplet au rang de départ. | CONFIRMÉE | V48 | 1 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.vonMangoldt_pivot_position_lock` | Von Mangoldt reconstruit exactement la position du pivot central (rang de départ + 1). | CONFIRMÉE | V48 | 1 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.vonMangoldt_third_position_lock` | Von Mangoldt reconstruit exactement la position du troisième premier (rang + 2). | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.vonMangoldt_incoming_gap_lock` | Von Mangoldt reconstruit exactement l'écart entrant. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.vonMangoldt_outgoing_gap_lock` | Von Mangoldt reconstruit exactement l'écart sortant. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.vonMangoldt_incoming_occurrence_lock` | L'occurrence de transition entrante reconstruite est la canonique. | CONFIRMÉE | V48 | 2 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.vonMangoldt_outgoing_occurrence_lock` | L'occurrence de transition sortante reconstruite est la canonique. | CONFIRMÉE | V48 | 2 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.vonMangoldt_two_edge_grammar_lock` | Le bloc de grammaire à deux arêtes reconstruit par von Mangoldt égale le bloc canonique au rang de départ. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.contact_interval_three_prime_certificate` | Certificat compact : adresse issue du compte gauche, comptage local 3, pivot premier, deux écarts positifs, deux occurrences distinctes. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.Round27RConsecutiveContactIntervalOverlap`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.startRank_eq_succ_of_vonMangoldtPivotContinuesInto` | Sous continuité du pivot, l'adresse de départ de la cellule suivante avance de un. | CONFIRMÉE | AJOUT | 4 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.next_firstPrime_eq_current_pivot` | Le premier terme lu par la cellule suivante est le pivot de la courante. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.next_pivot_eq_current_third` | Le pivot de la suivante est le troisième premier de la courante. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.incomingEdge_eq_previous_outgoingEdge` | L'arête entrante de la suivante est l'arête sortante de la précédente (recouvrement d'une arête). | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.incomingOccurrence_eq_previous_outgoingOccurrence` | L'arête partagée porte la même occurrence de transition indexée. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.shared_occurrence_double_reconstruction_lock` | L'occurrence partagée est verrouillée par les deux reconstructions zéros/von Mangoldt. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.three_cells_two_successive_overlaps` | Trois cellules consécutives avancent dans le même sens et donnent deux recouvrements exacts. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260901.vonMangoldt_position_locks_alone_do_not_select_successor` | Audit de force : les verrous de position von Mangoldt valent aussi à des positions non adjacentes (m ≠ n+1) et ne sélectionnent donc pas le successeur. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScaleDifference`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `scale_four_discrepancy_reconstructs` | Identité réelle : l'erreur cumulative x−θ(x) se reconstruit depuis l'erreur à x/4 et le défaut de masse première sur (x/4,x]. | CONFIRMÉE | AJOUT | 1 |
| `scale_four_square_contraction` | Inégalité réelle (d+s/2)² ≤ 2d²+s²/2 (coefficient contractant 1/2). | CONFIRMÉE | AJOUT | 1 |
| `contractive_energy_recurrence` | Fermeture abstraite : E n ≤ (B+4C)·G n pour toute suite E satisfaisant la récurrence contractante. | CONFIRMÉE (domaine : hypothèses de la récurrence énergétique contractante) | AJOUT | 2 |
| `one_sub_ne_zero_of_norm_lt_one` | Un symbole de module < 1 ne peut annuler 1−z. | CONFIRMÉE (domaine : ‖z‖<1) | AJOUT | 0 |

### `RhGapCriterion.ScaleRigidity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `transition_residue_coboundary_v2` | La classe de transition entre deux états mod 6 est un cobord plus trois fois l'indicateur de changement d'état. (terme hors maître « cobord » : différence φ(n+1)−φ(n) d'un potentiel grammatical ; télescope) | CONFIRMÉE (domaine : états s,t ∈ {1,5}) | V174 | 2 |
| `lifted_gap_coboundary_v2` | Décomposition exacte d'un écart relevé : 6k+3·(changement d'état)+cobord. | CONFIRMÉE (domaine : états s,t ∈ {1,5}) | V174 | 2 |
| `canonical_increment_coboundary_v2` | L'incrément canonique g−log p est l'innovation arithmétique plus le cobord. | CONFIRMÉE (domaine : g = 6·relèvement+3·croix+φ1−φ0) | AJOUT | 1 |
| `path_coboundary_identity_v2` | Toute somme finie de cobords télescope exactement. | CONFIRMÉE | AJOUT | 2 |
| `unit_potential_difference_bound_v2` | Une différence de potentiels à valeurs dans [0,1] est bornée par 1. | CONFIRMÉE (domaine : a,b ∈ [0,1]) | AJOUT | 3 |
| `path_coboundary_bound_v2` | La partie cobord d'un chemin ne contribue qu'un terme borné par 1. | CONFIRMÉE (domaine : φ à valeurs dans [0,1]) | AJOUT | 1 |
| `subexponential_of_bounded_additive_correction` | Une correction additive bornée ne change pas la sous-exponentialité. | CONFIRMÉE (domaine : K ≥ 0, G sous-exponentielle) | AJOUT | 1 |
| `full_meta_pattern_scale_recomposition` | « Recomposition » de l'injection d'échelle : implication tautologique H → H. [INCIDENT : le nom promet plus que le type (l'hypothèse est la conclusion).] | CONFIRMÉE (domaine : hypothèse identique à la conclusion) | AJOUT | 0 |
| `normalized_scale_square_identity_v2` | Identité quadratique exacte de l'échelle normalisée. | CONFIRMÉE (domaine : q = d + qPrec/2) | AJOUT | 2 |
| `normalized_scale_energy_contraction_v2` | Contraction énergétique q² ≤ 2d²+qPrec²/2. | CONFIRMÉE (domaine : q = d + qPrec/2) | AJOUT | 0 |
| `half_scale_recurrence_closure` | Spécialisation de la fermeture contractante au reste d'injection : E n ≤ (B+4C)·G n. | CONFIRMÉE (domaine : hypothèses de la récurrence contractante) | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260828.Audit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.LegacyP0Audit.p0_definition_exact` | P0 (fidélité sensible au membre) est littéralement la proposition historique : ‖porteur en fin‖ = ‖porteur au début‖ pour tout contexte pleinement aligné. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260828.Boundary`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.FullyAligned.sameObjectCertificate` | Dans un événement pleinement aligné, zéro, partenariat, bloc et source sont un même objet (même événement). | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.FullyAligned.semanticReturnFracture` | Fracture : le retour de la grammaire première tient et le retour de la réflexion d'un membre échoue, pour tout événement pleinement aligné. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.FullyAligned.fracturedMember_coordinates` | Les contacts du membre fracturé récupèrent β et γ du même membre. | CONFIRMÉE (domaine : m ≥ 1) | V45 | 0 |
| `ScientificRebuild20260828.FINAL_SEMANTIC_LOCK_exact` | FINAL_SEMANTIC_LOCK est exactement « pour tout T et tout événement pleinement aligné X, le retour du membre par réflexion de start à finish tient » (certificat d'énoncé). | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.FullyAligned.contradiction_of_FINAL_SEMANTIC_LOCK` | FINAL_SEMANTIC_LOCK entraîne False dès qu'un événement pleinement aligné X existe ; contradiction d'audit, conditionnelle par construction. | RÉFUTATION COMPILÉE (FINAL_SEMANTIC_LOCK (prémisse équivalente à RH par finalSemanticLockIsTerminalStrength) en présence d'un événement pleinement aligné X) | AJOUT | 1 |

### `RhGapCriterion.ScientificRebuild20260828.ConstraintPreludeCoverage99`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.constraintEvidenceCoverage_length` | La liste des preuves associées aux 99 contraintes a longueur 99. | HORS STANDARD (_native) | AJOUT | 1 |
| `ScientificRebuild20260828.C16_is_zeroRegime` | La contrainte C16 est de phase zeroRegime, preuve « rédigée, rejeu en attente ». | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.C48_is_pivotTour` | La contrainte C48 est de phase pivotTour, preuve adossée à un théorème. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.C57_no_selector_task` | La contrainte C57 est de phase sameEventLocalization, alignée par composition même-événement. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.C72_is_betaUniqueness` | La contrainte C72 est de phase betaUniqueness, « rédigée, rejeu en attente ». | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.C98_is_composition_alignment` | La contrainte C98 est de phase proofIntegrity, alignée par composition même-événement. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.ConstraintEvidence.ofNat_ctorIdx` | ofNat ∘ ctorIdx est l'identité sur ConstraintEvidence. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260828.ConstraintRegistry99`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.allConstraints_length` | Le registre allConstraints a exactement 99 éléments. | HORS STANDARD (_native) | AJOUT | 1 |
| `ScientificRebuild20260828.allConstraints_nodup` | Le registre allConstraints est sans doublon. | HORS STANDARD (_native) | AJOUT | 1 |
| `ScientificRebuild20260828.constraintPhaseCoverage_length` | La liste des phases des 99 contraintes a longueur 99. | HORS STANDARD (_native) | AJOUT | 0 |
| `ScientificRebuild20260828.ConstraintId.ofNat_ctorIdx` | ofNat ∘ ctorIdx est l'identité sur ConstraintId. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.ConstraintPhase.ofNat_ctorIdx` | ofNat ∘ ctorIdx est l'identité sur ConstraintPhase. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260828.Core`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.EventContext.trueMember` | Champ d'EventContext : le sujet est un vrai zéro non trivial. | CONFIRMÉE | V6 | 1 |
| `ScientificRebuild20260828.EventContext.offLine` | Champ d'EventContext : ce zéro est hors ligne (β ≠ 1/2), propriété du même zéro. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260828.EventContext.openStrip` | Champ : le zéro est dans la bande ouverte 0<β<1. | CONFIRMÉE | V7 | 1 |
| `ScientificRebuild20260828.EventContext.positiveHeight` | Champ : le zéro a partie imaginaire strictement positive. | CONFIRMÉE | V7 | 2 |
| `ScientificRebuild20260828.EventContext.partnershipIdentity` | Champ : le partenariat localisé a même zéro, même bloc et même source canonique. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.EventContext.vonMangoldtGrammarLockOnBlock` | Champ : la grammaire reconstruite par von Mangoldt égale la grammaire première canonique sur le bloc de premier retour. | CONFIRMÉE | V48 | 3 |
| `ScientificRebuild20260828.EventContext.partnershipPrimeSideIsCanonical` | Champ : le côté premier du partenariat est la grammaire première canonique du bloc. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.EventContext.partnershipPrimeSideIsVonMangoldtReconstruction` | Champ : le côté premier du partenariat est aussi la reconstruction von Mangoldt. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.EventContext.MZ_eq_M` | Champ : M^Z = M (reconstruction égale grammaire canonique du bloc). | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260828.EventContext.quartetIdentity` | Champ : le quartet vrai est semé par ce même zéro (mêmes miroir de même hauteur). | CONFIRMÉE | V63 | 0 |
| `ScientificRebuild20260828.EventContext.sameZeroVonMangoldtQuartet` | Champ (x>1 domaine) : la somme de von Mangoldt lissée s'écrit avec les termes triviaux et la somme sur les zéros du quartet et le complément. | CONFIRMÉE | V121 | 0 |
| `ScientificRebuild20260828.EventContext.primeGrammarReturn` | Champ : le premier retour sélectionné est un retour de la grammaire première. | CONFIRMÉE | AJOUT | 3 |
| `ScientificRebuild20260828.EventContext.memberReflectionAtPrimeReturn` | Champ : au retour premier, la réflexion grammaticale du membre est le transport du même zéro. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.EventContext.offMemberReflectionDoesNotReturn` | Champ : hors ligne, le retour de la réflexion du membre ne tient pas sur ce bloc. | RÉFUTATION COMPILÉE (retour du membre par réflexion (FINAL_SEMANTIC_LOCK) pour un contexte hors ligne) | AJOUT | 3 |
| `ScientificRebuild20260828.EventContext.exactReturnFracture` | Champ : le retour premier tient et le retour du membre échoue (fracture). | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.EventContext.contactPairRecoversSameZero` | Champ : une paire de contacts vraie récupère β et γ du même zéro. | CONFIRMÉE (domaine : m ≥ 1) | V45 | 1 |
| `ScientificRebuild20260828.EventContext.contactFracture` | Champ : la séparation hors ligne est visible dans les contacts vrais du zéro et de son miroir (contact d'indice k différent). | CONFIRMÉE | V163 | 0 |
| `ScientificRebuild20260828.EventContext.contactToPrimeCocycle` | Champ : le transport contact→premier garde le même zéro vrai. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.EventContext.perronCarrierSameBlock` | Champ : Perron et porteur sont soudés sur le même bloc de premier retour. (terme hors maître « Perron » : noyau/intégrande de Perron de −ζ'/ζ, outil de la formule explicite (cf. formule explicite, V100/V121)) | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.EventContext.nonterminal32` | Champ : les 32 surfaces non terminales restent propriétés du même partenariat localisé. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.primesDetermineCanonicalZeroSource` | L'histoire complète des premiers détermine la source canonique complète des zéros, multiplicité incluse. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260828.E44LocalVonMangoldtPivot`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.complexOffPoint_exists` | Il existe un point complexe hors ligne (au sens IsComplexOffPoint). | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.vonMangoldt_local_prime_count_lock` | Pour L,R ≥ 2, l'incrément local du compte de premiers reconstruit depuis les zéros égale l'incrément arithmétique (verrou local von Mangoldt). | CONFIRMÉE (domaine : L,R ≥ 2) | AJOUT | 1 |
| `ScientificRebuild20260828.vonMangoldt_local_psi_lock` | Pour L,R ≥ 2, l'incrément local pondéré ΔΨ récupéré depuis les zéros égale ΔΨ exact sur les mêmes bornes. | CONFIRMÉE (domaine : L,R ≥ 2) | V48 | 2 |
| `ScientificRebuild20260828.riemannVonMangoldt_local_interval_bound` | La soustraction de deux estimations globales de Riemann–von Mangoldt borne le compte local de hauteurs sur [A,B]. | CONFIRMÉE SOUS CONDITION (borne globale de Riemann–von Mangoldt (b1,b2,b3) et A,B ≥ 2) | AJOUT | 0 |
| `ScientificRebuild20260828.E44SelectedPrimePivotCell.stage_pos` | Champ de E44SelectedPrimePivotCell : l'étage vaut au moins 1. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260828.E44SelectedPrimePivotCell.left_ge_two` | Champ : le bord gauche de la signature de contact est ≥ 2. | CONFIRMÉE | AJOUT | 3 |
| `ScientificRebuild20260828.E44SelectedPrimePivotCell.pivot_inside` | Champ : le pivot premier est strictement entre les deux bords de la signature. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.E44SelectedPrimePivotCell.pivot_is_prime` | Champ : le pivot p(primeIndex) est premier. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.E44SelectedPrimePivotCell.right_ge_two` | Champ : le bord droit de la signature est ≥ 2. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260828.E44SelectedPrimePivotCell.exact_local_prime_count` | Le canal zéros reconstruit exactement le nombre de premiers arithmétiques de la cellule de contact. | CONFIRMÉE | V145 | 1 |
| `ScientificRebuild20260828.E44SelectedPrimePivotCell.exact_local_psi` | Le canal zéros récupère exactement ΔΨ sur la cellule de contact. | CONFIRMÉE | V145 | 0 |
| `ScientificRebuild20260828.E44SelectedPrimePivotCell.recovers_gamma` | La cellule de contact récupère γ = partie imaginaire du zéro. | CONFIRMÉE | V45 | 1 |
| `ScientificRebuild20260828.E44SelectedPrimePivotCell.recovers_beta` | La cellule de contact récupère β = partie réelle du zéro (recovers_beta). | CONFIRMÉE | V45 | 1 |
| `ScientificRebuild20260828.E44SinglePrimePivotCell.arithmetic_count_one` | Champ de E44SinglePrimePivotCell : le comptage arithmétique local sur la cellule vaut 1. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.E44SinglePrimePivotCell.zeroChannel_count_one` | Le canal zéros compte exactement 1 premier dans la cellule à pivot unique. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.E44VonMangoldtPivotInjection.oneToOne` | Champ de E44VonMangoldtPivotInjection : l'indice de pivot choisi est injectif en le zéro. | CONFIRMÉE | V149 | 1 |
| `ScientificRebuild20260828.E44VonMangoldtPivotInjection.pivotIndex_injective` | L'indice de pivot est injectif (forme directe). | CONFIRMÉE | V149 | 1 |
| `ScientificRebuild20260828.E44VonMangoldtPivotInjection.reflectionSamePivot_of_heightDetermined` | Un pivot déterminé par la hauteur donne automatiquement le même pivot E44 pour le miroir de même hauteur. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.E44VonMangoldtPivotInjection.allNontrivialZerosCritical_of_reflectionSamePivot` | Pivots injectifs plus même pivot pour le miroir de même hauteur ⟹ tout zéro non trivial est critique. | IMPLIQUE RH SOUS PRÉMISSE (injection de pivots E44 avec « même pivot pour le miroir de même hauteur » (ReflectionSameE44Pivot) ; conclusion ∀ρ non trivial, β=1/2 = forme dépliée de RH) | AJOUT | 2 |
| `ScientificRebuild20260828.E44VonMangoldtPivotInjection.allNontrivialZerosCritical_of_heightDetermined` | Pivots injectifs déterminés par la hauteur ⟹ tout zéro non trivial est critique. | IMPLIQUE RH SOUS PRÉMISSE (indice de pivot déterminé par la hauteur ; conclusion ∀ρ non trivial, β=1/2 = forme dépliée de RH) | AJOUT | 0 |
| `ScientificRebuild20260828.E44VonMangoldtPivotInjection.complexOffPoint_not_nontrivialZetaZero` | Sous cette prémisse, un point complexe hors ligne n'est pas un zéro non trivial de zêta. | CONFIRMÉE SOUS CONDITION (même pivot E44 pour le miroir (ReflectionSameE44Pivot)) | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260828.FinalClosureTarget`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.riemannHypothesis_of_FINAL_SEMANTIC_LOCK` | FINAL_SEMANTIC_LOCK ⟹ RiemannHypothesis (universalisation conditionnelle ; ne dérive pas la prémisse). | IMPLIQUE RH SOUS PRÉMISSE (FINAL_SEMANTIC_LOCK (⟺ RH par FINAL_SEMANTIC_LOCK_iff_riemannHypothesis)) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 2 |
| `ScientificRebuild20260828.RH_of_FINAL_SEMANTIC_LOCK` | Nom équivalent au niveau projet : FINAL_SEMANTIC_LOCK ⟹ RH. | IMPLIQUE RH SOUS PRÉMISSE (FINAL_SEMANTIC_LOCK (⟺ RH) ; « RH » du projet) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 0 |

### `RhGapCriterion.ScientificRebuild20260828.FinalSemanticLockStrengthAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.FINAL_SEMANTIC_LOCK_of_riemannHypothesis` | RH entraîne FINAL_SEMANTIC_LOCK (calcul de norme radiale exact). | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.FINAL_SEMANTIC_LOCK_iff_riemannHypothesis` | FINAL_SEMANTIC_LOCK ⟺ RiemannHypothesis (classification de force exacte). | ÉQUIVALENTE À RH (FINAL_SEMANTIC_LOCK) | AJOUT | 2 |
| `ScientificRebuild20260828.FullyAligned.normalizedMemberReflectionNorm` | Norme de la réflexion du membre sur le bloc de premier retour = (p finish / p start)^(−(β−1/2)…) : normalisation exacte du côté membre (dépend de β). | CONFIRMÉE | V102 | 0 |
| `ScientificRebuild20260828.FullyAligned.collectiveLock_coexists_with_memberNonreturn` | Le verrou collectif von Mangoldt et la non-retour individuel hors ligne coexistent sur le même X. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260828.GrammarReturnFracture`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.memberReflectionReturn_iff_critical` | Sur tout bloc premier non trivial (2≤M<N), le retour sensible au membre équivaut à β=1/2. | CONFIRMÉE | AJOUT | 4 |
| `ScientificRebuild20260828.trueOffLine_memberReflection_doesNotReturn` | Un vrai zéro hors ligne n'a pas de retour sensible au membre sur un bloc non trivial. | RÉFUTATION COMPILÉE (retour du membre par réflexion (FINAL_SEMANTIC_LOCK) pour un zéro vrai hors ligne (condition β ≠ 1/2, bloc 2≤M<N)) | AJOUT | 3 |
| `ScientificRebuild20260828.trueOffLine_primeReturn_reflectionFracture` | Fracture : le retour premier peut tenir tandis que la réflexion d'un membre hors ligne ne retourne pas. | CONFIRMÉE SOUS CONDITION (zéro vrai hors ligne, retour de la grammaire première sur [M,N]) | AJOUT | 0 |
| `ScientificRebuild20260828.memberReturnLock_forces_all_true_zeros_critical` | Si le verrou est dérivé indépendamment, tout vrai zéro non trivial est critique. | IMPLIQUE RH SOUS PRÉMISSE (verrou « von Mangoldt force le retour membre » (VonMangoldtForcesMemberReflectionReturn) ; conclusion β=1/2 pour tout zéro non trivial (forme dépliée de RH)) | AJOUT | 0 |
| `ScientificRebuild20260828.offLine_refutes_unjustified_memberReturnLock` | Anti-falsification : sous un témoin hors ligne et un retour premier réel, le verrou est faux. | RÉFUTATION COMPILÉE (verrou « von Mangoldt force le retour membre » (VonMangoldtForcesMemberReflectionReturn) en présence d'un témoin hors ligne) | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260828.HeightPrimeBetaDeterminacy`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.trueZero_contactWidth_from_height` | La hauteur fixe la largeur logarithmique de la cellule de contact vraie : e44Delta = mπ/γ. | CONFIRMÉE | V17 | 5 |
| `ScientificRebuild20260828.trueZero_beta_from_height_and_leftContact` | β est fixé exactement par la hauteur et le contact gauche : β = γ / tan(γ·log contact). | CONFIRMÉE | V45 | 6 |
| `ScientificRebuild20260828.trueZero_height_beta_contact_coupling` | Relation conjointe hauteur-largeur et hauteur-placement-β sur un même membre. | CONFIRMÉE | V45 | 0 |
| `ScientificRebuild20260828.beta_eq_of_same_height_and_same_leftContact` | Deux zéros de même hauteur et de même contact gauche ont même β. | CONFIRMÉE | V46 | 2 |
| `ScientificRebuild20260828.beta_eq_half_of_reflection_sameEvent_leftContact` | Si le contact porté par le miroir coïncide avec celui de ρ, alors β = 1/2. | CONFIRMÉE | V163 | 0 |

### `RhGapCriterion.ScientificRebuild20260828.LocalGapVonMangoldtContactSpine`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.localVonMangoldtForcesExactPrimeGap` | Champ/état de bord d'objet réel : la reconstruction depuis les zéros redonne l'écart premier consécutif exact. | CONFIRMÉE | V48 | 1 |
| `ScientificRebuild20260828.localForcedPrimeGapPositive` | L'écart premier forcé est strictement positif. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.localVonMangoldtForcesExactPrimeEndpoints` | Les deux positions premières reconstruites sont exactement les premiers consécutifs canoniques. | CONFIRMÉE | V48 | 1 |
| `ScientificRebuild20260828.localVonMangoldtForcesExactDeltaPsi` | Sur ces extrémités, le canal zéros récupère ΔΨ exact. | CONFIRMÉE | V48 | 1 |
| `ScientificRebuild20260828.riemannVonMangoldtGlobalConstraint` | Le contrat de Riemann–von Mangoldt du dépôt est conservé tel quel : N(T) est à RvM près de T/2π log(T/2π) − T/2π + 7/8. | CONFIRMÉE SOUS CONDITION (borne de Riemann–von Mangoldt (b1,b2,b3) et T ≥ 2) | AJOUT | 0 |
| `ScientificRebuild20260828.boundaryZeroGammaPositive` | Un zéro d'un état de bord est de hauteur strictement positive. | CONFIRMÉE | V7 | 3 |
| `ScientificRebuild20260828.localContactSatisfiesCorrectedE44` | La loi E44 multi-étage corrigée tient sur la paire de contacts vraie. | CONFIRMÉE | V45 | 3 |
| `ScientificRebuild20260828.localContactRecoversGamma` | La cellule de contact vraie récupère la hauteur exacte. | CONFIRMÉE | V45 | 1 |
| `ScientificRebuild20260828.localContactRecoversBeta` | La cellule tangente corrigée récupère β exactement. | CONFIRMÉE | V45 | 2 |
| `ScientificRebuild20260828.localContactBetaFormula` | Formule explicite multi-étage corrigée de β en fonction des contacts. | CONFIRMÉE | V45 | 0 |
| `ScientificRebuild20260828.localContactDefect_zero_iff_critical` | Le défaut de contact tangent corrigé s'annule ⟺ β = 1/2. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.localOffLineContactDefectNonzero` | Un état hors ligne actif a un défaut tangent corrigé non nul. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260828.localOffLineMirrorContactsDistinct` | Le contact vrai du zéro et celui de son miroir à même indice diffèrent (hors ligne). | CONFIRMÉE | V163 | 0 |
| `ScientificRebuild20260828.exactLocalGapVonMangoldtContactBundle` | Paquet de toutes les contraintes locales prouvées sur un état de bord réel actif. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.noOffBoundaryState_of_localCompatibility_and_neutrality` | Sous ces deux ingrédients, aucun état de bord hors ligne n'existe (IsEmpty). | CONFIRMÉE SOUS CONDITION (compatibilité contact-cellule locale universelle et neutralité de contact forcée par von Mangoldt local) | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260828.LocalVonMangoldtContactArithmetic`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.primeCountLocal_exact` | Pour L,R ≥ 2, le compte local de premiers reconstruit depuis les zéros égale le compte arithmétique local. | CONFIRMÉE (domaine : L,R ≥ 2) | AJOUT | 3 |
| `ScientificRebuild20260828.deltaPsiLocal_exact` | Pour L,R ≥ 2, l'incrément local de Chebyshev/von Mangoldt récupéré depuis les zéros est exact. | CONFIRMÉE (domaine : L,R ≥ 2) | V48 | 2 |
| `ScientificRebuild20260828.riemannVonMangoldtLocal_interval_bound` | Deux estimations cumulatives de Riemann–von Mangoldt donnent une borne locale sur l'intervalle. | CONFIRMÉE SOUS CONDITION (borne de Riemann–von Mangoldt (b1,b2,b3) et A,B ≥ 2) | AJOUT | 0 |
| `ScientificRebuild20260828.PrimeLocatedTangentCell.stage_pos` | Champ de PrimeLocatedTangentCell : l'étage est ≥ 1. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260828.PrimeLocatedTangentCell.left_ge_two` | Champ : bord gauche ≥ 2. | CONFIRMÉE | AJOUT | 3 |
| `ScientificRebuild20260828.PrimeLocatedTangentCell.prime_inside` | Champ : le premier de la cellule est strictement entre les deux bords. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.PrimeLocatedTangentCell.prime_is_canonical_prime` | Champ : ce premier est un vrai premier canonique. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.PrimeLocatedTangentCell.right_ge_two` | Champ : bord droit ≥ 2. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260828.PrimeLocatedTangentCell.localPrimeCount_exact` | Le compte local de premiers reconstruit depuis les zéros est exact sur la cellule. | CONFIRMÉE | V145 | 1 |
| `ScientificRebuild20260828.PrimeLocatedTangentCell.localDeltaPsi_exact` | ΔΨ local récupéré depuis les zéros est exact sur la cellule. | CONFIRMÉE | V145 | 0 |
| `ScientificRebuild20260828.PrimeLocatedTangentCell.recovers_height` | La cellule récupère la hauteur du zéro. | CONFIRMÉE | V45 | 0 |
| `ScientificRebuild20260828.PrimeLocatedTangentCell.recovers_beta` | La cellule récupère β. | CONFIRMÉE | V45 | 0 |
| `ScientificRebuild20260828.SinglePrimeTangentCell.arithmetic_count_one` | Champ de SinglePrimeTangentCell : comptage arithmétique local égal à 1. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.SinglePrimeTangentCell.zeroChannel_count_one` | Le canal zéros compte exactement 1 premier dans la cellule tangente à premier unique. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260828.RealObjectsSpine`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.trivialZeroFoundation` | Tout point trivial −2(n+1) est un zéro de zêta de multiplicité 1. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.genuineNontrivialZeroData` | Un zéro non trivial est un zéro de zêta, non trivial et différent de 1. | CONFIRMÉE | V6 | 0 |
| `ScientificRebuild20260828.offLineSuppliesDistinctSameHeightPair` | Un zéro hors ligne fournit un second vrai zéro distinct, de même hauteur et de partie réelle 1−β. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V62 | 1 |
| `ScientificRebuild20260828.offLineSuppliesFullQuartet` | Un zéro hors ligne fournit le quartet complet de quatre membres, multiplicité conservée. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | V63 | 0 |
| `ScientificRebuild20260828.offLineForcesOrderedZeroGap` | Un membre hors ligne force un écart interne de hauteur nul dans la constellation ordonnée positive. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne à la hauteur T) | V162 | 0 |
| `ScientificRebuild20260828.canonicalPrimeGapPositive` | Tout écart premier consécutif canonique est strictement positif. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.canonicalPrimeGapNonzero` | Forme non nulle du même fait (gnat n ≠ 0). | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.genuineMirrorPairPrimeJunctionExists` | Tout zéro positif hors ligne engendre une jonction première spécifique à la paire. (terme hors maître « jonction » : couple (zéro, miroir) placé sur une colonne première (MirrorPairPrimeJunction)) | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | AJOUT | 0 |
| `ScientificRebuild20260828.genuineLocalizedWeldExists` | Tout zéro positif hors ligne fournit une soudure localisée portant ce zéro. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | AJOUT | 1 |
| `ScientificRebuild20260828.weldedCaseHasZeroGapAndPairPrimeDefect` | Le cas soudé contient à la fois un écart de hauteur nul et un défaut de contribution de lignes de la paire miroir. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.weldedCasePrimeGapPositive` | Sur la colonne première sélectionnée d'un cas soudé, l'écart premier canonique est strictement positif. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.weldedCaseSamePrimeLabelsDifferentPairEntries` | La paire miroir a les mêmes étiquettes de premier canoniques sur la colonne choisie mais des entrées sensibles à la source différentes. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.trueZeroContactCellSatisfiesCorrectedE44` | Un vrai zéro de hauteur positive fournit une cellule tangente E44 corrigée dont les deux bords sont engendrés par le même zéro. | CONFIRMÉE (domaine : hauteur > 0, m ≥ 1) | V45 | 1 |
| `ScientificRebuild20260828.trueZeroContactCellRecoversGamma` | Les deux mêmes contacts vrais récupèrent la hauteur exacte. | CONFIRMÉE (domaine : hauteur > 0, m ≥ 1) | V45 | 0 |
| `ScientificRebuild20260828.offLineSplitsTrueMirrorContact` | Un zéro hors ligne de hauteur positive a un contact vrai différent de celui de son miroir à tout indice k. | CONFIRMÉE SOUS CONDITION (zéro de hauteur > 0 hors ligne) | V163 | 0 |
| `ScientificRebuild20260828.trueContactToPrimeIsSameZeroCocycle` | Le transport contact→premier est une identité de cocycle exacte pour le même zéro vrai (towerCharacter au premier / au contact). (terme hors maître « cocycle » : rapport de caractères de Tour entre l'échelle d'un contact et celle d'un premier) | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.RealObjectBoundaryState.zero_mem` | Champ de RealObjectBoundaryState : le zéro est dans les représentants positifs de T. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260828.RealObjectBoundaryState.offLine` | Champ : le zéro est hors ligne. | CONFIRMÉE | AJOUT | 3 |
| `ScientificRebuild20260828.RealObjectBoundaryState.quartet_seed` | Champ : la graine du quartet est le zéro. | CONFIRMÉE | V63 | 0 |
| `ScientificRebuild20260828.RealObjectBoundaryState.weld_zero` | Champ : la soudure porte le même zéro. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.RealObjectBoundaryState.stage_pos` | Champ : l'étage est ≥ 1. | CONFIRMÉE | AJOUT | 5 |
| `ScientificRebuild20260828.realObjectBoundaryStateExists` | Tout membre positif hors ligne donne un état de bord réel corrigé, sans prémisse terminale. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V62 | 0 |
| `ScientificRebuild20260828.RealObjectBoundaryState.hasDistinctSameHeightZeros` | Un état de bord contient deux vrais zéros distincts de même hauteur (zéro et miroir). | CONFIRMÉE | V65 | 0 |
| `ScientificRebuild20260828.RealObjectBoundaryState.hasZeroGapAndPositivePrimeGap` | Un état de bord contient à la fois l'écart nul côté zéros et un écart premier canonique positif. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.RealObjectBoundaryState.hasImmutablePrimeLabelsAndDifferentPairEntries` | Un état de bord expose le défaut de réflexion exact tout en gardant les étiquettes premières identiques (cellules gauche/droite distinctes, même écart premier). | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.RealObjectBoundaryState.contactCellIsSameZeroE44` | La cellule de contact choisie est engendrée par le même zéro vrai et satisfait la loi E44 tangente multi-étage corrigée. | CONFIRMÉE | V45 | 0 |
| `ScientificRebuild20260828.finalSemanticLockIsTerminalStrength` | L'ancien verrou sémantique final n'est pas un théorème intermédiaire : il a exactement la force de RH. | ÉQUIVALENTE À RH (FINAL_SEMANTIC_LOCK) | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260828.SameEventPivotVonMangoldtContactComposition`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.tourPivotIndex_eq` | L'indice de pivot de Tour au rang n est n+1. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.tourPivotPrime_eq` | Le premier pivot de Tour au rang n est p(n+1). | CONFIRMÉE | V28 | 0 |
| `ScientificRebuild20260828.tourPivotPrime_isPrime` | Le premier pivot de Tour est un vrai premier canonique. | CONFIRMÉE | AJOUT | 4 |
| `ScientificRebuild20260828.tourPivotPrime_unique` | Le pivot est l'unique premier strictement entre les deux bords de la fenêtre à deux transitions. | CONFIRMÉE (domaine : q premier avec p(n) < q < p(n+2)) | V61 | 1 |
| `ScientificRebuild20260828.tourPivot_vonMangoldt_position_lock` | Von Mangoldt reconstruit exactement le premier utilisé comme pivot de Tour. | CONFIRMÉE | V48 | 4 |
| `ScientificRebuild20260828.tourPivot_vonMangoldt_gap_lock` | L'écart premier canonique à l'indice du pivot est reconstruit exactement. | CONFIRMÉE | V48 | 2 |
| `ScientificRebuild20260828.tourPivot_twoIncidences_sameMemberFactor` | Les deux incidences de Tour autour du même pivot partagent le facteur central du même membre. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.trueContact_to_tourPivot_cocycle` | Un contact vrai du même membre est relié à l'échelle exacte du pivot par le cocycle de Tour exact. | CONFIRMÉE | AJOUT | 3 |
| `ScientificRebuild20260828.trueZero_pivot_vonMangoldt_contact_beta_spine` | Composition directe d'un membre : provenance du pivot, transport contact→pivot et lecture de β coexistent. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.mirrorPair_sameEvent_pivot_vonMangoldt_contact_spine` | Composition de paire miroir au même indice d'événement arithmétique n : provenance du pivot, même hauteur et β complémentaire du miroir, transports coexistent. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260828.SemanticMisinterpretationAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.AUDIT_off_is_only_a_property` | Audit A : un zéro hors ligne reste un vrai zéro non trivial ; hors ligne n'est qu'une propriété, non une autre entité. | CONFIRMÉE SOUS CONDITION (zéro hors ligne (β ≠ 1/2)) | AJOUT | 0 |
| `ScientificRebuild20260828.AUDIT_zeroMemberState_is_terminal_detector` | Audit B : l'ancien zeroMemberState vaut 1 ⟺ β=1/2, donc est un détecteur terminal, non un pont indépendant. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.AUDIT_capturePreservesIntruderDefect_is_terminal_strength` | Audit C : la préservation du défaut d'intrus par la capture est équivalente à « tous les représentants positifs de hauteur < T sont critiques » (fenêtre bornée, pas RH). (terme hors maître « capture » : NOTE homonymie : ici « capture » désigne la capture découplée zéros/premiers (DecoupledZeroPrimeCapture), non la « capture » du maître (rayon miroir posé sur le rayon, V185)) | CONFIRMÉE (domaine : longueur ≤ k et représentants dans la bande ouverte) | AJOUT | 0 |
| `ScientificRebuild20260828.AUDIT_prime_grammar_immutable` | Audit D : la grammaire première reconstruite par von Mangoldt est exactement la grammaire canonique immuable. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260828.AUDIT_memberReflectionReturn_is_terminal_detector` | Audit E : le retour sensible au membre sur un bloc non trivial est un détecteur de criticité (⟺ β=1/2). | CONFIRMÉE (domaine : 2 ≤ M < N) | AJOUT | 0 |
| `ScientificRebuild20260828.AUDIT_return_types_are_explicit` | Audit F : le retour de grammaire première (produit des 1−2cross = 1) et le retour du membre réfléchi (norme = 1) sont deux propositions typées distinctes. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.AUDIT_contact_to_prime_keeps_same_zero` | Audit G : le cocycle contact→premier ne fait intervenir aucune égalité de rang. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.AUDIT_primes_determine_actual_zero_source` | Audit H : la détermination de la source préserve la source vraie complète des zéros. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260828.SemanticZeroPrimePivotContactProof`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.SameEventPivotContactLocalization.eventIndex_ge_two` | Champ de SameEventPivotContactLocalization : l'indice d'événement est ≥ 2. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.stage_pos` | Champ : l'étage est ≥ 1. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.left_ge_two` | Champ : l'échelle gauche est ≥ 2. | CONFIRMÉE | AJOUT | 3 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.member_left_exact` | Champ : le contact vrai du membre à la branche membre égale l'échelle gauche. | CONFIRMÉE | AJOUT | 3 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.member_right_exact` | Champ : le contact droit d'étage du membre égale l'échelle droite. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.mirror_left_exact` | Champ : le contact vrai du miroir à sa branche égale la même échelle gauche. | CONFIRMÉE | AJOUT | 3 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.mirror_right_exact` | Champ : le contact droit d'étage du miroir égale la même échelle droite. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.pivot_inside` | Champ : le premier pivot d'événement est strictement entre les deux échelles. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.pivot_is_prime` | Le pivot d'événement est un vrai premier canonique. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.pivot_vonMangoldt_position_exact` | Le canal zéros/von Mangoldt reconstruit exactement le même pivot de Tour. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.pivot_vonMangoldt_gap_exact` | L'écart premier au même indice de pivot est reconstruit exactement. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.right_ge_two` | L'échelle droite est ≥ 2 (car le pivot est entre les bords). | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.local_prime_count_exact` | Le compte local de premiers reconstruit égale l'arithmétique sur la même cellule localisée. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.local_deltaPsi_exact` | ΔΨ local reconstruit est exact sur la même cellule localisée. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.member_contact_width` | La hauteur fixe la largeur logarithmique de la cellule du membre : e44Delta = étage·π/γ. | CONFIRMÉE | V17 | 0 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.mirror_contact_width` | La même cellule a la même largeur lue par le miroir fonctionnel. | CONFIRMÉE | V17 | 0 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.member_beta_readout` | Lecture de β du membre une fois la position gauche fixée par l'événement. | CONFIRMÉE | V45 | 0 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.mirror_beta_readout` | Lecture de β du miroir fonctionnel sur la même cellule localisée. | CONFIRMÉE | V45 | 0 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.member_beta_eq_mirror_beta` | Dans une telle localisation, les lectures de β du membre et du miroir sont égales. | CONFIRMÉE (domaine : localisation même-événement E fournie (objet inhabitable hors ligne, cf. no_sameEventPivotContactLocalization_of_off)) | AJOUT | 1 |
| `ScientificRebuild20260828.SameEventPivotContactLocalization.beta_eq_half` | Clôture algébrique pour un membre localisé : β = 1/2. | CONFIRMÉE (domaine : localisation même-événement E fournie (objet inhabitable hors ligne, cf. no_sameEventPivotContactLocalization_of_off)) | AJOUT | 2 |
| `ScientificRebuild20260828.allNontrivialZeros_beta_eq_half_of_sameEventLocalization` | Une fois la loi de localisation sémantique implémentée, tout zéro non trivial est sur la ligne critique. | IMPLIQUE RH SOUS PRÉMISSE (loi de localisation même-événement (SameEventLocalizationLaw) ; conclusion ∀ρ non trivial, β=1/2 (forme dépliée de RH)) | AJOUT | 0 |
| `ScientificRebuild20260828.no_sameEventPivotContactLocalization_of_off` | Un membre réellement hors ligne ne peut habiter l'objet historique de localisation même-événement. | RÉFUTATION COMPILÉE (existence d'une localisation même-événement pour un membre hors ligne (objet historique SameEventPivotContactLocalization) ; condition β ≠ 1/2) | V163 | 0 |

### `RhGapCriterion.ScientificRebuild20260828.TrueZeroMemberReflection`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.offLine_is_still_true_zero` | Une branche hors ligne reste littéralement un vrai zéro non trivial de zêta. | CONFIRMÉE SOUS CONDITION (zéro hors ligne (β ≠ 1/2)) | AJOUT | 0 |
| `ScientificRebuild20260828.memberGrammarReflection_def` | La réflexion grammaticale du membre est le facteur de grammaire (produit des 1−2cross) fois le transport du même zéro. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.memberGrammarReflection_eq_tower` | La réflexion du membre égale le rapport de caractères de Tour tordus en N et M. | CONFIRMÉE (domaine : 2 ≤ M ≤ N) | AJOUT | 1 |
| `ScientificRebuild20260828.memberGrammarReflection_at_primeGrammarReturn` | À un retour de la grammaire première, la réflexion du membre est exactement le transport du même zéro. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.norm_memberGrammarReflection` | La norme de la réflexion du membre vaut (p N / p M)^(−(β−1/2)) : elle lit la coordonnée radiale. | CONFIRMÉE (domaine : 2 ≤ M ≤ N) | V102 | 1 |
| `ScientificRebuild20260828.trueZero_beta_from_contact` | Un contact tangent vrai et la hauteur vraie récupèrent β exactement. | CONFIRMÉE (domaine : β ≠ 0, γ ≠ 0) | V45 | 0 |
| `ScientificRebuild20260828.trueZero_gamma_from_contact_pair` | Une paire de contacts vrais du même membre récupère γ exactement. | CONFIRMÉE (domaine : γ ≠ 0, m ≥ 1) | V45 | 1 |
| `ScientificRebuild20260828.trueZero_corrected_E44` | La même paire de contacts satisfait la loi E44 corrigée à tous étages. | CONFIRMÉE (domaine : hauteur > 0, m ≥ 1) | V45 | 1 |
| `ScientificRebuild20260828.trueZero_beta_from_contact_pair` | La même paire récupère β exactement. | CONFIRMÉE (domaine : β ≠ 0, hauteur > 0, m ≥ 1) | V45 | 1 |
| `ScientificRebuild20260828.trueOffLine_contact_ne_mirror` | Hors ligne, le membre et son miroir fonctionnel ont des contacts différents au même indice. | CONFIRMÉE SOUS CONDITION (zéro de hauteur > 0 hors ligne) | V163 | 1 |
| `ScientificRebuild20260828.trueZero_contact_to_prime_cocycle` | La comparaison contact→premier garde le même zéro ; l'indice premier est une entrée. | CONFIRMÉE | AJOUT | 2 |

### `RhGapCriterion.ScientificRebuild20260828.VonMangoldtRigidGrammar`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.vonMangoldt_weighted_count_lock` | Le compte pondéré reconstruit depuis les zéros égale le compte pondéré arithmétique. | CONFIRMÉE (domaine : x ≥ 2) | V48 | 0 |
| `ScientificRebuild20260828.vonMangoldt_real_prime_count_lock` | Le compte réel de premiers reconstruit depuis les zéros égale π(x). | CONFIRMÉE (domaine : x ≥ 2) | V48 | 0 |
| `ScientificRebuild20260828.vonMangoldt_prime_count_lock` | Le compte entier de premiers reconstruit égale piCount. | CONFIRMÉE | V48 | 1 |
| `ScientificRebuild20260828.vonMangoldt_prime_position_lock` | La position première reconstruite au rang n est p n. | CONFIRMÉE | V48 | 10 |
| `ScientificRebuild20260828.vonMangoldt_prime_gap_lock` | L'écart premier reconstruit au rang n est gnat n. | CONFIRMÉE | V48 | 9 |
| `ScientificRebuild20260828.vonMangoldt_grammar_lock` | Verrou de grammaire : la grammaire reconstruite via zéros/von Mangoldt égale la grammaire première canonique. | CONFIRMÉE | V48 | 6 |
| `ScientificRebuild20260828.vonMangoldt_grammar_positions_lock` | Les positions de la grammaire sont fixées par l'histoire première. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260828.vonMangoldt_grammar_gaps_lock` | Les écarts de la grammaire sont fixés par l'histoire première. | CONFIRMÉE | V48 | 1 |
| `ScientificRebuild20260828.vonMangoldt_grammar_transitions_lock` | Les transitions Transform6 sont fixées par l'histoire première. | CONFIRMÉE | V48 | 2 |
| `ScientificRebuild20260828.vonMangoldt_grammar_pattern_lock` | Le motif (pattern) est fixé par l'histoire première. | CONFIRMÉE | V48 | 1 |
| `ScientificRebuild20260828.vonMangoldt_grammar_family_lock` | La famille est fixée par l'histoire première. | CONFIRMÉE | V48 | 1 |
| `ScientificRebuild20260828.vonMangoldt_grammar_boundary_lock` | Entrée et sortie de la grammaire sont fixées, non ajustables. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260828.vonMangoldt_grammar_order_lock` | L'histoire ordonnée transition/motif/famille est fixée. | CONFIRMÉE | V48 | 1 |
| `ScientificRebuild20260828.vonMangoldt_cell_lock` | Verrou exact de l'incrément de Chebyshev/von Mangoldt sur une cellule réelle. | CONFIRMÉE (domaine : L,R ≥ 2) | V48 | 2 |
| `ScientificRebuild20260828.prime_grammar_is_not_free` | La grammaire première reconstruite égale le bloc de grammaire complète canonique : aucun paramètre de mutation. | CONFIRMÉE | V48 | 0 |

### `RhGapCriterion.ScientificRebuild20260828.ZeroFamilyCompleteProfiles`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.TrivialZeroProfile.zerohood` | Un profil de zéro trivial n donne riemannZeta(−2(n+1)) = 0. | CONFIRMÉE (domaine : profil de zéro trivial n) | AJOUT | 0 |
| `ScientificRebuild20260828.TrivialZeroProfile.triviality` | Le profil d'un zéro trivial n donne IsTrivialZetaZero(−2(n+1)). | CONFIRMÉE (domaine : paquet TrivialZeroProfile n (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260828.TrivialZeroProfile.beta_exact` | Le zéro trivial n a partie réelle −2(n+1). | CONFIRMÉE (domaine : paquet TrivialZeroProfile n (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260828.TrivialZeroProfile.beta_negative` | La partie réelle du zéro trivial n est < 0. | CONFIRMÉE (domaine : paquet TrivialZeroProfile n (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260828.TrivialZeroProfile.gamma_zero` | La partie imaginaire du zéro trivial est 0. | CONFIRMÉE (domaine : paquet TrivialZeroProfile n (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260828.TrivialZeroProfile.multiplicity_one` | La multiplicité du zéro trivial est 1. | CONFIRMÉE (domaine : paquet TrivialZeroProfile n (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260828.TrivialZeroProfile.conjugation_fixed` | La conjugaison fixe le zéro trivial. | CONFIRMÉE (domaine : paquet TrivialZeroProfile n (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260828.TrivialZeroProfile.functional_reflection_not_zero` | La réflexion fonctionnelle d'un zéro trivial n'est pas un zéro de zêta. | CONFIRMÉE (domaine : paquet TrivialZeroProfile n (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260828.TrivialZeroProfile.completed_zeta_nonzero` | La fonction complétée ne s'annule pas en un zéro trivial. | CONFIRMÉE (domaine : paquet TrivialZeroProfile n (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260828.TrivialZeroProfile.boundary_beta_recovery` | La récupération de β par la relation de bord triviale rend la partie réelle du zéro trivial. | CONFIRMÉE (domaine : paquet TrivialZeroProfile n (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260828.TrivialZeroProfile.tower_nonunitary` | Le caractère de Tour d'un zéro trivial n'est jamais de norme 1. | CONFIRMÉE (domaine : paquet TrivialZeroProfile n (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260828.trivialZero_complete_profile` | Tout zéro trivial canonique a le profil complet de pré-preuve. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.NontrivialZeroProfile.zerohood` | Un zéro non trivial annule zêta. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V6 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.not_trivial` | Un zéro non trivial n'est pas trivial. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V6 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.not_pole` | Un zéro non trivial est différent de 1. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V6 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.beta_positive` | Un zéro non trivial a β > 0. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V7 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.beta_lt_one` | Un zéro non trivial a β < 1. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V7 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.gamma_nonzero` | Un zéro non trivial a partie imaginaire non nulle. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V7 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.multiplicity_positive` | La multiplicité d'un zéro non trivial est strictement positive. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.conjugate_nontrivial` | Le conjugué d'un zéro non trivial est un zéro non trivial. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V63 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.reflection_nontrivial` | Le réfléchi conjugué (miroir) est un zéro non trivial. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V63 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.reflection_same_height` | Le miroir a même hauteur. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V65 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.reflection_complementary_beta` | Le miroir a partie réelle 1−β. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V65 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.reflection_same_multiplicity` | Le miroir a même multiplicité. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V65 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.reflection_fixed_iff_central` | Le miroir est confondu avec ρ ⟺ β=1/2. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V77 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.contact_width_from_height` | La largeur logarithmique de la cellule de contact vaut mπ/γ, ne dépendant que de la hauteur. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V17 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.beta_from_height_and_left_contact` | β est fixé par la hauteur et le contact gauche. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V45 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.contact_pair_recovers_height` | La paire de contacts récupère la hauteur. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V45 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.contact_pair_recovers_beta` | La paire de contacts récupère β. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V45 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.tower_unitary_iff_central` | Le caractère de Tour est de norme 1 ⟺ β=1/2. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | V102 | 0 |
| `ScientificRebuild20260828.NontrivialZeroProfile.tower_reflection` | Le caractère de Tour du miroir est l'inverse du conjugué de celui de ρ. | CONFIRMÉE (domaine : paquet NontrivialZeroProfile ρ (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260828.nontrivialZero_complete_profile` | Tout vrai zéro non trivial a le profil complet de pré-preuve. | CONFIRMÉE | V6 | 1 |
| `ScientificRebuild20260828.nontrivial_family_contact_pair_injective` | La signature de contact (paire complète de contacts finis) est injective sur les zéros non triviaux. | CONFIRMÉE (domaine : branche k fixée, étage m ≥ 1) | V46 | 0 |
| `ScientificRebuild20260828.OffLineQuartetProfile.seed_zero` | La graine du quartet est un zéro non trivial. | CONFIRMÉE (domaine : paquet OffLineQuartetProfile Q (toujours réalisé)) | V63 | 0 |
| `ScientificRebuild20260828.OffLineQuartetProfile.seed_offline` | La graine du quartet est hors ligne. | CONFIRMÉE (domaine : paquet OffLineQuartetProfile Q (toujours réalisé)) | AJOUT | 0 |
| `ScientificRebuild20260828.OffLineQuartetProfile.seed_gamma_nonzero` | La graine a partie imaginaire non nulle. | CONFIRMÉE (domaine : paquet OffLineQuartetProfile Q (toujours réalisé)) | V7 | 0 |
| `ScientificRebuild20260828.OffLineQuartetProfile.same_height_mirror_zero` | Le miroir de même hauteur est un zéro non trivial. | CONFIRMÉE (domaine : paquet OffLineQuartetProfile Q (toujours réalisé)) | V63 | 0 |
| `ScientificRebuild20260828.OffLineQuartetProfile.conjugate_zero` | Le conjugué est un zéro non trivial. | CONFIRMÉE (domaine : paquet OffLineQuartetProfile Q (toujours réalisé)) | V63 | 0 |
| `ScientificRebuild20260828.OffLineQuartetProfile.opposite_height_mirror_zero` | Le miroir de hauteur opposée (zéro réfléchi) est un zéro non trivial. | CONFIRMÉE (domaine : paquet OffLineQuartetProfile Q (toujours réalisé)) | V63 | 0 |
| `ScientificRebuild20260828.OffLineQuartetProfile.same_height_mirror_gamma` | Le miroir de même hauteur a la hauteur de la graine. | CONFIRMÉE (domaine : paquet OffLineQuartetProfile Q (toujours réalisé)) | V65 | 0 |
| `ScientificRebuild20260828.OffLineQuartetProfile.conjugate_gamma` | Le conjugué a la hauteur opposée. | CONFIRMÉE (domaine : paquet OffLineQuartetProfile Q (toujours réalisé)) | V63 | 0 |
| `ScientificRebuild20260828.OffLineQuartetProfile.opposite_height_mirror_gamma` | Le miroir de hauteur opposée a la hauteur opposée. | CONFIRMÉE (domaine : paquet OffLineQuartetProfile Q (toujours réalisé)) | V63 | 0 |
| `ScientificRebuild20260828.OffLineQuartetProfile.same_height_mirror_beta` | Le miroir de même hauteur a β complémentaire 1−β. | CONFIRMÉE (domaine : paquet OffLineQuartetProfile Q (toujours réalisé)) | V65 | 0 |
| `ScientificRebuild20260828.OffLineQuartetProfile.conjugate_beta` | Le conjugué a même β que la graine. | CONFIRMÉE (domaine : paquet OffLineQuartetProfile Q (toujours réalisé)) | V63 | 0 |
| `ScientificRebuild20260828.OffLineQuartetProfile.opposite_height_mirror_beta` | Le miroir de hauteur opposée a β complémentaire. | CONFIRMÉE (domaine : paquet OffLineQuartetProfile Q (toujours réalisé)) | V63 | 0 |
| `ScientificRebuild20260828.OffLineQuartetProfile.four_members_distinct` | Les quatre membres du quartet sont deux à deux distincts. | CONFIRMÉE (domaine : paquet OffLineQuartetProfile Q (toujours réalisé)) | V63 | 0 |
| `ScientificRebuild20260828.OffLineQuartetProfile.orbit_card_four` | L'orbite a exactement quatre éléments. | CONFIRMÉE (domaine : paquet OffLineQuartetProfile Q (toujours réalisé)) | V63 | 0 |
| `ScientificRebuild20260828.OffLineQuartetProfile.multiplicities_equal` | Les quatre membres ont même multiplicité. | CONFIRMÉE (domaine : paquet OffLineQuartetProfile Q (toujours réalisé)) | V63 | 0 |
| `ScientificRebuild20260828.offlineQuartet_complete_profile` | Tout quartet vrai hors ligne porte le profil complet à quatre membres avant toute localisation. | CONFIRMÉE | V63 | 0 |
| `ScientificRebuild20260828.zeroFamilies_complete_preproof_ledger` | Registre unique : tout zéro trivial et tout zéro non trivial ont leur profil de pré-preuve, sans affirmer la criticité. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260828.ZeroFamilyCriticalityForcing`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.critical_of_reflectionInvariant_injective` | Toute observable injective invariante par réflexion force tous les zéros non triviaux à être critiques. | IMPLIQUE RH SOUS PRÉMISSE (observable injectif F sur les zéros non triviaux invariant par la réflexion canonique ; conclusion ∀ρ non trivial, β=1/2 (forme dépliée de RH)) | AJOUT | 2 |
| `ScientificRebuild20260828.critical_on_heightConstellation_of_reflectionInvariant_injOn` | Version à constellation finie : tous les zéros de la constellation de hauteur T sont critiques. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.critical_on_heightConstellation_of_zeroHeight_injective` | Si la hauteur est injective sur une constellation, tous ses zéros sont critiques. | CONFIRMÉE | V59 | 1 |
| `ScientificRebuild20260828.allNontrivialZerosCritical_of_zeroHeight_injective_on_every_constellation` | Injectivité de la hauteur sur toute constellation bornée force la criticalité de tous les zéros non triviaux. | IMPLIQUE RH SOUS PRÉMISSE (zeroHeight injectif sur chaque constellation bornée ; conclusion ∀ρ non trivial, β=1/2 (forme dépliée de RH)) | V59 | 0 |
| `ScientificRebuild20260828.beta_forced_half_of_same_reflected_contact_signature` | L'égalité de la signature de contact d'un zéro et de celle de son miroir force β=1/2. | CONFIRMÉE | V163 | 0 |
| `ScientificRebuild20260828.allNontrivialZerosCritical_of_contactSignature_reflectionInvariant` | L'invariance de la signature de contact par réflexion force la criticalité universelle (l'injectivité étant acquise). | IMPLIQUE RH SOUS PRÉMISSE (signature de contact invariante par réflexion pour tout zéro ; conclusion ∀ρ non trivial, β=1/2 (forme dépliée de RH)) | AJOUT | 1 |
| `ScientificRebuild20260828.allNontrivialZerosCritical_of_contactSignature_heightDetermined` | Même conclusion via l'interface HeightDetermined. | IMPLIQUE RH SOUS PRÉMISSE (signature de contact déterminée par la hauteur (HeightDetermined) ; conclusion ∀ρ non trivial, β=1/2 (forme dépliée de RH)) | AJOUT | 0 |
| `ScientificRebuild20260828.nontrivialCriticality_tool_equivalences` | Sur tout zéro non trivial, β=1/2 ⟺ point fixe de la réflexion ∧ signature de contact réflexion-invariante ∧ ‖caractère de Tour‖=1. | CONFIRMÉE (domaine : P > 1, étage m ≥ 1) | AJOUT | 0 |
| `ScientificRebuild20260828.verified_dual_rigidities` | La signature de contact est injective et la hauteur est invariante par réflexion. | CONFIRMÉE (domaine : étage m ≥ 1) | V46 | 0 |

### `RhGapCriterion.ScientificRebuild20260828.ZeroFamilyToolFoundation`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.trivialZero_re` | La partie réelle du zéro trivial n est −2(n+1). | CONFIRMÉE | AJOUT | 8 |
| `ScientificRebuild20260828.trivialZero_im` | La partie imaginaire du zéro trivial est 0. | CONFIRMÉE | AJOUT | 11 |
| `ScientificRebuild20260828.trivialZero_re_lt_zero` | La partie réelle du zéro trivial est < 0. | CONFIRMÉE | AJOUT | 8 |
| `ScientificRebuild20260828.trivialZero_isTrivial` | Le point −2(n+1) est un zéro trivial. | CONFIRMÉE | AJOUT | 3 |
| `ScientificRebuild20260828.trivialZero_notNontrivial` | Un zéro trivial n'est pas un zéro non trivial. | CONFIRMÉE | V6 | 0 |
| `ScientificRebuild20260828.trivialZero_complete_foundation` | Fondation complète du zéro trivial : zérohood, trivialité, γ=0, β<0, multiplicité 1, fonction complétée non nulle. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.trivialZero_conj_eq_self` | La conjugaison fixe chaque zéro trivial. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.trivialZero_functionalReflect_not_zetaZero` | La réflexion fonctionnelle d'un zéro trivial n'est pas un zéro de zêta. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.tangentContact_zeroHeight` | À hauteur 0, le contact tangent vaut 1 (totalisation Lean, sans sens géométrique). | CONFIRMÉE | AJOUT | 5 |
| `ScientificRebuild20260828.tangentStageRight_zeroHeight` | À hauteur 0, le contact d'étage droit vaut 1. | CONFIRMÉE | AJOUT | 4 |
| `ScientificRebuild20260828.trivialZero_tangentContact_eq_one` | Le contact tangent d'un zéro trivial vaut 1. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.trivialZero_tangentStageRight_eq_one` | Le contact d'étage droit d'un zéro trivial vaut 1. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.trivialZero_contactDelta_eq_zero` | La largeur de contact d'un zéro trivial est 0. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.trivialZero_contactRecoveredGamma_eq_zero` | La paire de contacts d'un zéro trivial récupère γ = 0. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.trivialZero_contactRecoveredBeta_eq_zero` | La paire de contacts d'un zéro trivial récupère β = 0. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260828.trivialZero_contactRecoveredBeta_ne_realPart` | Le β récupéré par la paire dégénérée ne vaut pas la partie réelle du zéro trivial. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.trivialZero_no_positiveStage_correctedE44` | Aux étages positifs, la paire de contacts effondrée d'un zéro trivial ne satisfait pas la loi E44 corrigée. | CONFIRMÉE (domaine : m ≥ 1) | AJOUT | 0 |
| `ScientificRebuild20260828.trivialZero_tower_not_unitary` | Le caractère de Tour d'un zéro trivial n'est jamais de norme 1 à une échelle P > 1. | CONFIRMÉE (domaine : P > 1) | AJOUT | 1 |
| `ScientificRebuild20260828.nontrivialZero_complete_foundation` | Fondation complète du zéro non trivial : annule zêta, non trivial, ≠1, 0<β<1, γ≠0, multiplicité > 0. | CONFIRMÉE | V7 | 1 |
| `ScientificRebuild20260828.nontrivialZero_conjugate_isNontrivial` | Le conjugué d'un zéro non trivial est un zéro non trivial. | CONFIRMÉE | V63 | 1 |
| `ScientificRebuild20260828.nontrivialZero_reflection_foundation` | La réflexion-conjuguée est une involution interne aux non triviaux : même hauteur, β complémentaire, même multiplicité, point fixe ⟺ β=1/2. | CONFIRMÉE | V65 | 1 |
| `ScientificRebuild20260828.nontrivialContactSignature_recoversGamma` | La signature de contact d'un zéro non trivial récupère γ. | CONFIRMÉE (domaine : m ≥ 1) | V45 | 8 |
| `ScientificRebuild20260828.nontrivialContactSignature_satisfiesCorrectedE44` | La signature de contact d'un zéro non trivial satisfait la loi E44 tangente corrigée. | CONFIRMÉE (domaine : étage m ≥ 1) | V45 | 2 |
| `ScientificRebuild20260828.nontrivialContactSignature_recoversBeta` | La signature de contact d'un zéro non trivial récupère β (partie réelle). | CONFIRMÉE (domaine : étage m ≥ 1) | V45 | 9 |
| `ScientificRebuild20260828.nontrivialContactSignature_injective` | À indice de contact et étage positif fixés, la paire de contacts vrais est injective sur les zéros non triviaux. | CONFIRMÉE (domaine : étage m ≥ 1) | V46 | 4 |
| `ScientificRebuild20260828.nontrivialContactSignature_reflect_eq_iff_critical` | La signature de contact d'un zéro et celle de son miroir sont égales ⟺ β=1/2. | CONFIRMÉE (domaine : étage m ≥ 1) | V163 | 2 |
| `ScientificRebuild20260828.nontrivialZero_tower_unitary_iff_critical` | Le caractère de Tour d'un zéro non trivial est de norme 1 ⟺ β=1/2. | CONFIRMÉE (domaine : P > 1) | V102 | 2 |
| `ScientificRebuild20260828.nontrivialZero_tower_reflection` | Le caractère de Tour du miroir est l'inverse du conjugué du caractère de Tour de ρ. | CONFIRMÉE (domaine : P > 0) | AJOUT | 1 |
| `ScientificRebuild20260828.zeroFamily_tool_separation` | Séparation des outils : les zéros triviaux (γ=0, contact 1, β récupéré 0) et non triviaux (γ≠0, multiplicité > 0, β récupéré exact) ont des domaines certifiés différents. | CONFIRMÉE (domaine : m ≥ 1) | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260828.ZeroRegimeTransitionBeta`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.trivial_nontrivial_chart_kinds_ne` | Les types de carte E44 des zéros triviaux et non triviaux diffèrent. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.trivialZero_beta_exact` | β exact de la famille triviale : −2(n+1). | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.nontrivialZero_beta_openUnit` | β d'un zéro non trivial est dans ]0,1[ (bande ouverte, pas RH). | CONFIRMÉE | V7 | 1 |
| `ScientificRebuild20260828.trivial_nontrivial_beta_regimes_disjoint` | Les régimes de β triviaux (<0) et non triviaux (]0,1[) sont disjoints indépendamment de β=1/2. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.trivialBoundary_gamma_eq_zero` | La carte de bord triviale a hauteur exactement 0. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.trivialBoundary_recovers_actual_beta` | L'inverse de bord récupère le β négatif réel de chaque zéro trivial. | CONFIRMÉE (domaine : m ≥ 1) | AJOUT | 1 |
| `ScientificRebuild20260828.trivialBoundaryLeft_pos` | Le contact de bord gauche fini est strictement positif. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260828.nontrivialInterior_gamma_ne_zero` | Un zéro non trivial a hauteur non nulle : la carte intérieure est non dégénérée. | CONFIRMÉE | V7 | 1 |
| `ScientificRebuild20260828.nontrivialInterior_recovers_actual_beta` | Dans la carte intérieure, la paire de contacts d'étage positif récupère le β réel. | CONFIRMÉE (domaine : m ≥ 1) | V45 | 1 |
| `ScientificRebuild20260828.nontrivialInterior_recovers_actual_gamma` | La même cellule récupère la hauteur réelle non nulle. | CONFIRMÉE (domaine : m ≥ 1) | V45 | 1 |
| `ScientificRebuild20260828.zeroRegimeTransition_beta_E44` | Contrainte de transition de régime (β, hauteurs, récupérations de bord et intérieures), sans cacher la criticité. | CONFIRMÉE (domaine : m ≥ 1) | AJOUT | 0 |
| `ScientificRebuild20260828.E44ZeroChartKind.ofNat_ctorIdx` | ofNat ∘ ctorIdx est l'identité sur E44ZeroChartKind. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260828.ZeroRegimeTransitionSemantics`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260828.zeroFamilies_beta_domains` | Séparation exacte des domaines de β entre zéros triviaux et non triviaux. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.zeroFamilies_height_domains` | Séparation exacte des hauteurs (0 pour trivial, ≠ 0 pour non trivial). | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260828.trivialRelation_recovers_beta` | La relation triviale à hauteur zéro récupère son β négatif depuis son échelle gauche finie. | CONFIRMÉE (domaine : m ≥ 1) | AJOUT | 2 |
| `ScientificRebuild20260828.nontrivialRelation_recovers_beta` | Dans le régime non trivial, une paire de contacts d'étage positif récupère β. | CONFIRMÉE (domaine : m ≥ 1) | V45 | 1 |
| `ScientificRebuild20260828.nontrivialRelation_recovers_height` | La même paire récupère la hauteur non nulle. | CONFIRMÉE (domaine : m ≥ 1) | V45 | 1 |
| `ScientificRebuild20260828.zeroRegimeTransition_joint_constraints` | Théorème collecteur du changement simultané de régime, sans objet E44. | CONFIRMÉE (domaine : m ≥ 1) | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260829.ActualFiberedGrammar`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.actualZeroGrammar_gaps_eq_constellationGaps` | Le champ écarts de la grammaire zéros réelle est l'objet constellationGaps déjà établi. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.actualZeroGrammar_members_eq_ordered` | Les membres de la grammaire zéros réelle sont la liste ordonnée canonique des vrais membres. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.actualZeroGapReadout_eq_zero` | Pour une entrée de miroir hors ligne, la lecture de l'écart côté zéros est some 0 (relation nulle de la grammaire zéros réelle). | CONFIRMÉE | V162 | 1 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.mirrorZeroGap_is_entry_of_actualZeroGrammar` | L'indice de l'écart produit par le miroir est dans la liste des écarts de la grammaire zéros et vaut 0. | CONFIRMÉE | V162 | 0 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.canonicalPrimeGapReadout_pos` | L'écart premier canonique lu par l'entrée est strictement positif. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.zeroEntryIsNull` | Pour une entrée hors ligne, l'entrée zéro exacte produite par le miroir est nulle. | CONFIRMÉE | V162 | 2 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.primeEntryIsNotNull` | L'entrée première canonique du même événement n'est pas nulle. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.RelationalGapEntry.zeroIndex_eq` | Champ de RelationalGapEntry : l'indice zéro est celui de l'entrée. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.RelationalGapEntry.primeIndex_eq` | Champ : l'indice premier est celui de l'entrée. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.false_of_fiberedGapNullityFidelity` | Sur une entrée hors ligne, la fidélité de nullité entraîne False : elle contredit la progression première canonique. | RÉFUTATION COMPILÉE (fidélité de nullité de l'écart sur une entrée de miroir hors ligne (FiberedGapNullityFidelity)) | AJOUT | 4 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.actualGrammar_is_existing_zeroGrammar` | La grammaire zéros portée par cet événement est la grammaire zéros canonique existante. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.eventCapture_zeroSide_eq_actualZeroGrammar` | Le côté zéros de la capture même-événement est la grammaire zéros réelle complète GZ. (terme hors maître « GZ » : grammaire des zéros (écarts de hauteur d'une constellation)) | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.eventCapture_primeSide_eq_encodedZeroGrammar` | Le côté premier de la même capture est exactement EncZ sur le bloc de l'événement. (terme hors maître « EncZ » : encodage de la grammaire des zéros vers la grammaire première) | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.encodedZeroSource_eq_canonicalPrimeGrammar` | La source zéros encodée reconstruit la grammaire première canonique sur tout bloc. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260829.false_of_positive_offline_of_fiberedMZEqM` | Tout vrai membre positif hors ligne contredit la loi de grammaire fibrée de même entrée. | IMPLIQUE RH SOUS PRÉMISSE (loi de grammaire fibrée FiberedMZEqM (⟺ RH par fiberedMZEqM_iff_riemannHypothesis) ; conclusion : aucun représentant positif hors ligne à aucune hauteur (forme dépliée de RH)) | V140 | 4 |
| `ScientificRebuild20260829.positiveRepresentative_beta_eq_half_of_fiberedMZEqM` | Sous l'identité de grammaire fibrée, tout représentant positif est critique. | IMPLIQUE RH SOUS PRÉMISSE (loi de grammaire fibrée FiberedMZEqM (⟺ RH) ; conclusion : tout représentant positif est critique (forme dépliée de RH)) | V140 | 2 |
| `ScientificRebuild20260829.riemannHypothesis_of_fiberedMZEqM` | FiberedMZEqM ⟹ RiemannHypothesis (conséquence de la loi littérale du maître sémantique de l'époque). | IMPLIQUE RH SOUS PRÉMISSE (loi de grammaire fibrée FiberedMZEqM (⟺ RH par fiberedMZEqM_iff_riemannHypothesis)) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 4 |

### `RhGapCriterion.ScientificRebuild20260829.DirectMirrorZeroGap`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.gaps_forall_iff_chain_direct` | Copie locale de l'identité de liste : tous les écarts consécutifs vérifient P ⟺ la liste est une chaîne pour P sur les différences. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.trueOffMirror_positive_distinct_sameHeight` | Le miroir fonctionnel exact d'un zéro positif hors ligne est dans la même liste positive, distinct, de même hauteur. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V62 | 1 |
| `ScientificRebuild20260829.trueOffMirror_forces_zero_constellation_gap` | Un membre positif hors ligne a son miroir exact dans la même constellation, d'où un écart de constellation nul. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V162 | 1 |
| `ScientificRebuild20260829.trueOffMirror_forces_zero_ordered_gap` | Forme au niveau des positions : il existe i avec écart interne ordonné some 0. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V162 | 2 |
| `ScientificRebuild20260829.trueOffQuartet_forces_zero_ordered_gap` | Forme quartet : la source sémantique de l'écart nul est le miroir de même hauteur du quartet hors ligne. | CONFIRMÉE SOUS CONDITION (quartet dont la graine est positive (quartet hors ligne)) | V162 | 0 |

### `RhGapCriterion.ScientificRebuild20260829.FinsetChannelFactorization`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.selection_rest_tsum_decomposition` | Décomposition exacte inconditionnelle de la série des résidus non triviaux en sélection A plus reste. | CONFIRMÉE (domaine : x > 1) | V121 | 2 |
| `ScientificRebuild20260829.offlineOrbit_tsum_decomposition_is_selection_instance` | La décomposition historique par orbite de conjugaison est l'instance A := offlineZeroOrbitFinset. | CONFIRMÉE (domaine : x > 1, hzero zéro non trivial) | V121 | 0 |
| `ScientificRebuild20260829.selection_Pi_rest_decomposition` | Décomposition inconditionnelle de la formule explicite lissée : termes déterministes, sélection et reste, tous conservés. | CONFIRMÉE (domaine : x > 1) | V121 | 1 |
| `ScientificRebuild20260829.selection_primitive_rest_decomposition` | Découpage exact de la primitive lissée des zéros en partie sélection et reste. | CONFIRMÉE (domaine : x > 1) | AJOUT | 1 |
| `ScientificRebuild20260829.selection_psi_rest_decomposition` | Découpage exact de psiRecoveredFromZeros en sélection et reste. | CONFIRMÉE (domaine : t ≥ 2) | AJOUT | 2 |
| `ScientificRebuild20260829.selection_weighted_count_rest_decomposition` | Découpage exact du compte pondéré reconstruit en sélection et reste. | CONFIRMÉE (domaine : x ≥ 2) | AJOUT | 2 |
| `ScientificRebuild20260829.selection_prime_count_rest_decomposition` | Découpage exact du compte premier réel reconstruit (inversion de Möbius) en sélection et reste. | CONFIRMÉE (domaine : x ≥ 2) | AJOUT | 2 |
| `ScientificRebuild20260829.offlineOrbitPrimitivePart_eq_selection` | La partie primitive de l'orbite hors ligne égale la partie primitive de sélection sur cette orbite. | CONFIRMÉE (domaine : ρ zéro non trivial) | AJOUT | 0 |
| `ScientificRebuild20260829.offlineRestPrimitivePart_eq_selection` | La partie primitive du reste hors ligne égale la partie reste de la sélection. | CONFIRMÉE (domaine : ρ zéro non trivial) | AJOUT | 0 |
| `ScientificRebuild20260829.offlineOrbitPsiRecovered_eq_selection` | ψ récupéré de l'orbite égale ψ récupéré de la sélection. | CONFIRMÉE (domaine : ρ zéro non trivial) | AJOUT | 0 |
| `ScientificRebuild20260829.offlineRestPsiRecovered_eq_selection` | ψ récupéré du reste égale celui du reste de sélection. | CONFIRMÉE (domaine : ρ zéro non trivial) | AJOUT | 0 |
| `ScientificRebuild20260829.offlineOrbitWeightedPart_eq_selection` | La partie pondérée de l'orbite égale la partie pondérée de la sélection. | CONFIRMÉE (domaine : ρ zéro non trivial) | AJOUT | 0 |
| `ScientificRebuild20260829.offlineRestWeightedPart_eq_selection` | La partie pondérée du reste égale celle du reste de sélection. | CONFIRMÉE (domaine : ρ zéro non trivial) | AJOUT | 0 |
| `ScientificRebuild20260829.offlineOrbit_prime_count_decomposition_is_selection_instance` | L'énoncé terminal d'orbite du Round 25 est retrouvé mot pour mot depuis la chaîne générique. | CONFIRMÉE (domaine : x ≥ 2, ρ zéro non trivial) | AJOUT | 0 |
| `ScientificRebuild20260829.selectionPrimitivePart_pair` | Certificat de non-vacuité : sur une sélection à deux éléments, la partie sélection est x fois la somme des deux termes. | CONFIRMÉE (domaine : a ≠ b) | AJOUT | 1 |

### `RhGapCriterion.ScientificRebuild20260829.GrammaticalGapKindNaturality`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.realGapKind_eq_nullRel_iff` | Le genre d'un écart réel est nullRel ⟺ l'écart vaut 0. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.realGapKind_eq_forwardRel_iff` | Le genre d'un écart réel est forwardRel ⟺ l'écart est non nul. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.natGapKind_eq_nullRel_iff` | Le genre d'un écart entier est nullRel ⟺ l'écart vaut 0. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.natGapKind_eq_forwardRel_iff` | Le genre d'un écart entier est forwardRel ⟺ l'écart est non nul. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.primeGapKindOfPassage_eq_forwardRel` | La réalisation première canonique de tout passage identifié est inconditionnellement forwardRel. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.gapKindNaturalityAt_iff_zeroGapKind_forward` | La naturalité de genre en un passage équivaut à : le genre zéros est forwardRel. (terme hors maître « naturalité » : commutation du renversement grammatical avec l'opérateur du partenariat (R12) ; équivaut à β=1/2 (V140)) | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.gapKindNaturalityAt_iff_actualGZGap_ne_zero` | La naturalité de genre en un passage équivaut à la non-nullité de l'écart GZ réel. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.actualGZGap_ne_zero_of_gapKindNaturalityAt` | Une fois la naturalité dérivée, l'écart GZ réel du passage ne peut être nul. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.gapKindNaturalityAt_of_actualGZGap_ne_zero` | La non-nullité de l'écart GZ du passage suffit à établir la naturalité ponctuelle de genre. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.all_actualGZGaps_ne_zero_of_gapKindNaturality` | La naturalité de famille force tout écart GZ réel du même raccord à être non nul. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.GrammaticalGapKind.ofNat_ctorIdx` | ofNat ∘ ctorIdx est l'identité sur GrammaticalGapKind. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260829.MirrorGapEventConstruction`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.fiberedMirrorGapEntry_exists` | Tout membre positif hors ligne fournit canoniquement l'entrée d'événement de miroir fibrée complète. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V62 | 6 |
| `ScientificRebuild20260829.fiberedMirrorGapEventRepresentation_proved` | Forme universelle : toutes les données d'événement de miroir établies indépendamment sont constructibles sans RH. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.fullyAlignedSameEventContextOf.congr_simp` | Lemme de congruence auto-généré pour fullyAlignedSameEventContextOf (égalité de zéros entraîne égalité de contextes). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260829.MirrorGapFiberSpec`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.FiberedMirrorGapEntry.zero_mem` | Champ de FiberedMirrorGapEntry : le membre fourni est dans la constellation positive bornée. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.offLine` | Champ : ce même membre est hors ligne. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.zeroGap` | Champ : l'écart interne ordonné à l'indice zéro-gap vaut some 0. | CONFIRMÉE | V162 | 5 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.event_zero` | Champ : le zéro de l'événement est ρ. | CONFIRMÉE | AJOUT | 4 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.event_mirror` | Champ de FiberedMirrorGapEntry : le miroir de l'événement est reflectConjZero ρ. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.stage_pos` | Champ : l'étage est ≥ 1. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.mirror_is_genuine` | Le miroir fonctionnel retenu par l'événement est un vrai zéro non trivial (entrée hors ligne). | CONFIRMÉE | V63 | 0 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.mirror_same_height` | Le miroir a exactement la même hauteur que ρ. | CONFIRMÉE | V65 | 1 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.mirror_complementary_re` | Le miroir a partie réelle complémentaire 1−β. | CONFIRMÉE | V65 | 1 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.contact_pair_recovers_member` | La paire de contacts du même membre récupère β et γ de ρ. | CONFIRMÉE | V45 | 2 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.true_contacts_distinct` | Hors ligne, les contacts du membre et du miroir au même indice diffèrent. | CONFIRMÉE | V163 | 2 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.partnership_zero` | Le partenariat localisé est attaché au même zéro ρ. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.partnership_mirror` | Le partenariat localisé porte le miroir fonctionnel vrai de ρ. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.partnership_block` | Le partenariat localisé utilise le même bloc de premier retour. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.reconstructedGrammar_eq_primeGrammar` | Sur le même bloc, la reconstruction zéros de la grammaire première égale la grammaire complète canonique. | CONFIRMÉE | V48 | 1 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.tower_contact_to_same_prime` | Le cocycle contact/Tour du même membre atteint l'échelle exacte du premier sélectionné. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.vonMangoldt_prime_gap_exact` | L'écart premier canonique à l'entrée est reconstruit exactement par von Mangoldt. | CONFIRMÉE | V48 | 2 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.canonicalPrimeGapPositive` | L'écart premier canonique à l'entrée est strictement positif. | CONFIRMÉE | AJOUT | 3 |

### `RhGapCriterion.ScientificRebuild20260829.MirrorGapFourRouteAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.FiberedMirrorGapEntry.routeA_independent_gap_boundary` | Route A : trois faits indépendants coexistent sans substitution d'objet (écart zéros nul, écart premier reconstruit exact, écart premier > 0). | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.routeA_nullityFidelity_contradiction` | Sur un événement hors ligne, la fidélité de nullité donne False. | RÉFUTATION COMPILÉE (fidélité de nullité de l'écart (FiberedGapNullityFidelity) sur une entrée de miroir hors ligne (route A)) | AJOUT | 0 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.routeB_samePrimeCocycles_coexist_with_distinctContacts` | Route B : contacts vrais du membre et du miroir distincts, malgré les deux identités de cocycle exactes possibles vers les mêmes premiers. | CONFIRMÉE | V163 | 0 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.routeC_no_heightDetermined_leftInverse` | Aucun placement déterminé par la hauteur seule ne peut avoir un inverse à gauche membre par membre sur la constellation de cet événement hors ligne. | RÉFUTATION COMPILÉE (placement déterminé par la hauteur seule avec inverse à gauche membre par membre sur l'événement hors ligne (route C)) | AJOUT | 0 |
| `ScientificRebuild20260829.FiberedMirrorGapEntry.routeD_localMemberReturn_refuted` | L'événement hors ligne prouve la négation du retour local du membre requis. | RÉFUTATION COMPILÉE (retour local du membre exigé (RouteDLocalMemberReturn) sur l'événement hors ligne (route D)) | AJOUT | 0 |
| `ScientificRebuild20260829.routeA_universal_fiberedMZEqM_iff_RH` | La loi de grammaire fibrée FiberedMZEqM est équivalente à RH (certificat de force, route A). | ÉQUIVALENTE À RH (FiberedMZEqM) | V140 | 0 |
| `ScientificRebuild20260829.routeD_universal_memberReturn_iff_RH` | Le producteur universel de retour du membre (FINAL_SEMANTIC_LOCK) équivaut à RH (route D). | ÉQUIVALENTE À RH (FINAL_SEMANTIC_LOCK) | AJOUT | 0 |
| `ScientificRebuild20260829.routeD_endpointAssemblyProducer_iff_RH` | Le producteur d'égalité d'extrémités pré-R12 équivaut à RH. | ÉQUIVALENTE À RH (FirstReturnEndpointAssemblyProducer) | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260829.MirrorGapStrengthAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.fiberedMZEqM_of_riemannHypothesis` | RH entraîne FiberedMZEqM (sens RH → loi ; RH en hypothèse, aucun membre hors ligne : la loi indexée hors ligne tient à vide). | CONFIRMÉE | V140 | 1 |
| `ScientificRebuild20260829.fiberedMZEqM_iff_riemannHypothesis` | FiberedMZEqM ⟺ RH : classification de force de la loi terminale de nullité même-entrée. | ÉQUIVALENTE À RH (FiberedMZEqM) | V140 | 2 |
| `ScientificRebuild20260829.establishedMirrorPrimeEventData` | La couche événement/provenance du miroir hors ligne reste inconditionnelle (représentation FiberedMirrorGapEventRepresentation). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260829.MirrorGapTerminalClosure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.false_of_true_offline_mirror_gap` | Un vrai membre positif hors ligne contredit la loi fibrée de nullité même-entrée. | IMPLIQUE RH SOUS PRÉMISSE (loi de grammaire fibrée FiberedMZEqM (⟺ RH) ; conclusion : aucun représentant positif hors ligne (forme dépliée de RH)) | V140 | 0 |
| `ScientificRebuild20260829.positiveRepresentative_beta_eq_half_of_mirrorGap` | Les représentants positifs sont critiques sous la loi de grammaire fibrée. | IMPLIQUE RH SOUS PRÉMISSE (loi de grammaire fibrée FiberedMZEqM (⟺ RH) ; conclusion : tout représentant positif est critique (forme dépliée de RH)) | V140 | 0 |
| `ScientificRebuild20260829.riemannHypothesis_mirrorGapClosure_of_fiberedMZEqM` | FiberedMZEqM ⟹ RiemannHypothesis (conséquence de la loi fibrée « faisant autorité »). | IMPLIQUE RH SOUS PRÉMISSE (loi de grammaire fibrée FiberedMZEqM (⟺ RH par fiberedMZEqM_iff_riemannHypothesis)) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 0 |

### `RhGapCriterion.ScientificRebuild20260829.PreOffSameObjectGapRigidity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.actualGZGapOfPassage_eq_zeroPassageGaps` | actualGZGapOfPassage est littéralement le passage de hauteur successif canonique. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.sameObject_primeHistory_determines_zeroSource` | Sur le même objet couplé, toute continuation de zêta déterminée par l'histoire première a exactement la source canonique des zéros. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.sameObject_primeHistory_determines_GZ_block` | La fenêtre complète de la grammaire zéros réelle est fixée par la même histoire première. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.sameObject_primeHistory_determines_GZ_gaps` | La liste des écarts de hauteur GZ réels est elle-même déterminée par l'histoire première. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.sameObject_EncZGap_eq_primeGap` | L'écart EncZ au passage/place est exactement l'écart premier stocké par l'objet couplé. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.encodedPrimeGapOfPassage_eq_EncZGap` | Le décodeur explicite de la source zéros évalué au passage est la même cellule EncZ. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.encodedPrimeGapOfPassage_eq_sameObjectPrimeGap` | Le morphisme source-zéros du passage égale l'écart premier de l'objet couplé. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.encodedPrimeGapOfPassage_eq_gnat` | Le même écart premier est gnat au rang premier sélectionné par le raccord. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.encodedPrimeGapOfPassage_pos` | Pré-OFF : l'image de tout passage identifié par le morphisme source-zéros est un écart strictement positif. | CONFIRMÉE | AJOUT | 4 |
| `ScientificRebuild20260829.preOff_sameObject_primeGap_rigidity` | Certificat compact de rigidité pré-OFF sur un objet et un passage (décodeur, EncZ, M et positivité). | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.preOff_sameObject_bidirectional_rigidity` | Rigidité bidirectionnelle pré-OFF sur un raccord : l'histoire première détermine la source zéros et son bloc GZ. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.actualGZGap_ne_zero_of_local_nullity_reflection` | Réduction : si un morphisme local reflétait la nullité (écart GZ nul ⟹ écart premier nul), l'écart GZ du passage serait non nul. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260829.PreOffTowerPrimeGapCoupling`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.canonicalPrimeAt_add_gap` | p n + gnat n = p (n+1). | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.canonicalPrimeEdge_ratio_eq_one_add_gap` | p(n+1)/p n = 1 + gnat n / p n. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.canonicalPrimeEdgeLogWidth_eq_log_one_add_gap` | La largeur log canonique de l'arête première est log(1 + gnat n / p n). | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.canonicalPrimeEdgeLogWidth_pos` | La largeur log canonique de toute arête première est > 0. | CONFIRMÉE | AJOUT | 4 |
| `ScientificRebuild20260829.towerHeightSpanOnPrimeEdge_eq_log_one_add_gap` | L'étendue scalaire de Tour sur l'arête première vaut γ/π · log(1 + gnat n / p n). | CONFIRMÉE | V16 | 0 |
| `ScientificRebuild20260829.towerHeightSpanOnPrimeEdge_sub` | La différence des étendues de Tour à deux hauteurs sur la même arête vaut (γ2−γ1)/π fois la largeur log. | CONFIRMÉE | V17 | 2 |
| `ScientificRebuild20260829.towerHeightSpanOnPrimeEdge_eq_iff` | L'étendue scalaire de Tour sur une arête première est injective en la hauteur. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.towerHeightSpanDifference_eq_zero_iff` | La différence d'étendues est nulle ⟺ les hauteurs sont égales. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.preOff_twoChannel_zeroPrimeGap_rigidity` | Pré-OFF : pour deux vrais zéros distincts, l'arête première est > 0, de largeur log > 0, et l'écart transformé est non nul. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260829.PreOffTransformedZeroGap`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.transformedZeroGapOnPrimeEdge_eq_zero_iff` | L'écart transformé sur l'arête première est nul ⟺ les deux membres complexes coïncident. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.transformedZeroGapOnPrimeEdge_ne_zero_of_distinct_trueZeros` | Deux vrais zéros distincts ont un écart transformé non nul sur toute arête première canonique. | CONFIRMÉE | V46 | 6 |
| `ScientificRebuild20260829.transformedZeroGapOnVonMangoldtEdge_eq_canonical` | L'écart transformé sur l'arête von Mangoldt égale celui de l'arête canonique. | CONFIRMÉE | V48 | 2 |
| `ScientificRebuild20260829.transformedZeroGapOnVonMangoldtEdge_ne_zero_of_distinct_trueZeros` | Deux vrais zéros distincts ont un écart transformé non nul sur l'arête reconstruite par von Mangoldt. | CONFIRMÉE | V46 | 0 |

### `RhGapCriterion.ScientificRebuild20260829.PreOffZeroPrimeEdgeRigidity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.canonicalPrimeEdgeVoiceSignature_injective` | Sur toute arête première canonique, la signature des deux voix d'extrémité est injective en le zéro. | CONFIRMÉE | V46 | 3 |
| `ScientificRebuild20260829.distinct_trueZeros_separated_on_every_canonicalPrimeEdge` | Deux vrais zéros distincts ont une signature transformée non nulle sur toute arête première canonique. | CONFIRMÉE | V46 | 7 |
| `ScientificRebuild20260829.vonMangoldtPrimeEdgeVoiceSignature_eq_canonical` | La signature reconstruite par von Mangoldt égale la signature canonique. | CONFIRMÉE | V48 | 1 |
| `ScientificRebuild20260829.distinct_trueZeros_separated_on_every_vonMangoldtPrimeEdge` | Les zéros distincts sont séparés sur toute arête reconstruite depuis les zéros. | CONFIRMÉE | V46 | 0 |
| `ScientificRebuild20260829.vonMangoldt_consecutivePrimeEdge_lock` | Verrou arithmétique pré-OFF d'une arête : positions reconstruites, écart reconstruit et positivité. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260829.individualPerronContribution_is_same_canonicalPrimeEdge` | La contribution individuelle d'un zéro sur l'arête première est une différence d'extrémités du même porteur de Perron vrai. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.preOff_zeroPrimeEdge_rigidity` | Certificat de rigidité pré-OFF : écart reconstruit exact, positif, et signature de voix distincte pour deux zéros distincts. | CONFIRMÉE | V46 | 0 |

### `RhGapCriterion.ScientificRebuild20260829.SameEventSingletonPassage`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.MirrorFiberPassageWitness.positions_distinct` | Champ de MirrorFiberPassageWitness : les indices du zéro et du miroir sont distincts. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.MirrorFiberPassageWitness.gap_between_exact_positions` | Champ : l'indice de l'écart est entre les deux positions exactes (dans un sens ou l'autre). | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.MirrorFiberPassageWitness.gapIndex_succ_lt` | Champ : gapIndex+1 est dans la liste ordonnée. | CONFIRMÉE | AJOUT | 4 |
| `ScientificRebuild20260829.MirrorFiberPassageWitness.gapIndex_lt_GZ` | Champ : gapIndex est dans la liste des écarts de constellation. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.MirrorFiberPassageWitness.actual_GZ_gap_eq_zero` | Champ : l'écart de constellation à gapIndex vaut 0. | CONFIRMÉE | V162 | 1 |
| `ScientificRebuild20260829.MirrorFiberPassageWitness.local_two_member_window_full` | Champ : la fenêtre locale à deux membres tient dans les représentants positifs. | CONFIRMÉE | AJOUT | 7 |
| `ScientificRebuild20260829.MirrorFiberPassageWitness.left_endpoint_common_height` | Champ : l'extrémité gauche de la fenêtre a la hauteur de ρ. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.MirrorFiberPassageWitness.right_endpoint_common_height` | Champ : l'extrémité droite de la fenêtre a la hauteur de ρ. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.MirrorFiberPassageWitness.orderedGap_eq_zero` | Le passage choisi est la lecture positionnelle de la grammaire zéros canonique (écart ordonné some 0). | CONFIRMÉE | V162 | 4 |
| `ScientificRebuild20260829.MirrorFiberPassageWitness.localWindow_eq_orderedSlice` | La fenêtre locale est la tranche à deux membres de la constellation ordonnée vraie. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.MirrorFiberPassageWitness.localWindow_length` | La fenêtre locale a exactement deux vrais membres. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.mirrorFiberPassageWitness_exists` | Construction de l'arête adjacente sélectionnée sans aucun objet premier (témoin de passage de fibre miroir). | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V162 | 2 |
| `ScientificRebuild20260829.SameEventSingletonPassageRaccord.weld_zero` | Champ de SameEventSingletonPassageRaccord : la soudure porte ρ. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.SameEventSingletonPassageRaccord.raccord_is_canonical` | Champ : le raccord est le raccord structurel canonique. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.SameEventSingletonPassageRaccord.selectedPrimeBlock_length` | Le bloc premier sélectionné du couple est exactement une place première. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.SameEventSingletonPassageRaccord.uniquePlace_maps_to_selectedPrimeStart` | L'unique passage local est assigné à l'unique place première locale (début du bloc). | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.SameEventSingletonPassageRaccord.uniqueLocalPassage` | Fin 1 n'a pas d'ambiguïté de permutation côté passages zéros. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.SameEventSingletonPassageRaccord.uniqueLocalPrimePlace` | Fin 1 n'a pas d'ambiguïté de permutation côté places premières. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.SameEventSingletonPassageRaccord.partnership_zero` | Le partenariat localisé porte le membre fourni. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.SameEventSingletonPassageRaccord.partnership_mirror` | Le partenariat localisé porte le miroir fonctionnel exact. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.SameEventSingletonPassageRaccord.selectedCell_EncZ_eq_M` | Champ/lecture : le côté premier de la cellule sélectionnée est l'encodage canonique de la source zéros sur la même cellule et égale la grammaire complète canonique. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.sameEventSingletonPassageRaccord_exists` | Construction du raccord à passage singleton pour tout membre positif vrai hors ligne (condition d'existence hors ligne). | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V62 | 1 |
| `ScientificRebuild20260829.SingletonPassageCrosswalk.left_row` | Champ de SingletonPassageCrosswalk : la ligne de la cellule gauche est l'indice de l'écart du passage. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.SingletonPassageCrosswalk.right_row` | Champ : la ligne de la cellule droite est gapIndex+1. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.SingletonPassageCrosswalk.left_column` | Champ : la colonne de la cellule gauche est 0. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.SingletonPassageCrosswalk.right_column` | Champ : la colonne de la cellule droite est 0. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.SingletonPassageCrosswalk.leftInternalGap_eq_zero` | La cellule gauche lit l'écart interne exact some 0 du passage GZ sélectionné. | CONFIRMÉE | V162 | 1 |
| `ScientificRebuild20260829.SingletonPassageCrosswalk.endpointMembers_exact` | Les deux lignes de la table de correspondance sont exactement les deux extrémités du passage local sélectionné. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.SingletonPassageCrosswalk.sameSelectedPrimeColumn` | Les deux cellules d'extrémité portent la colonne d'événement sélectionnée (écart premier gnat en pStart). | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.SingletonPassageCrosswalk.refinementEntries_read_endpoint_members` | Les entrées de raffinement sensibles au membre sont les contributions zéro-premier pré-agrégation des deux extrémités. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.encodeSingletonPassage_zeroRealization` | Réalisation côté zéros : l'observable lit some 0 (passage GZ sélectionné). | CONFIRMÉE | V162 | 1 |
| `ScientificRebuild20260829.encodeSingletonPassage_primeLabelRealization` | Réalisation côté premiers : l'observable lit gnat en pStart (cellule première canonique). | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.selectedColumn_aggregate_factors_through_zeroChannel` | La somme sur tous les zéros de la contribution zéro-premier à la colonne sélectionnée factorise par le canal zéros de la source canonique. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.selectedPrimeSide_independent_of_localPassage` | Audit de perte d'information : le côté premier encodé est indépendant du passage local sélectionné (définitionnellement). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260829.SemanticMasterTerminal`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.semanticMaster_no_positive_offline` | Contradiction du demi-plan positif fournie par le M^Z=M fibré du maître sémantique de l'époque. | IMPLIQUE RH SOUS PRÉMISSE (loi de grammaire fibrée FiberedMZEqM (⟺ RH) ; conclusion : aucun représentant positif hors ligne (forme dépliée de RH)) | V140 | 0 |
| `ScientificRebuild20260829.semanticMaster_positive_beta_eq_half` | Tout représentant positif est sur la ligne critique sous M^Z=M fibré. | IMPLIQUE RH SOUS PRÉMISSE (loi de grammaire fibrée FiberedMZEqM (⟺ RH) ; conclusion : tout représentant positif est critique (forme dépliée de RH)) | V140 | 0 |
| `ScientificRebuild20260829.semanticMaster_riemannHypothesis` | Théorème terminal : la chaîne du maître sémantique de l'époque entraîne RH (FiberedMZEqM ⟹ RH). | IMPLIQUE RH SOUS PRÉMISSE (loi de grammaire fibrée FiberedMZEqM (⟺ RH par fiberedMZEqM_iff_riemannHypothesis)) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 1 |
| `ScientificRebuild20260829.riemannHypothesis_mirrorGapClosure_of_fiberedMZEqM` | Alias conditionnel public FiberedMZEqM ⟹ RH (même énoncé que riemannHypothesis_mirrorGapClosure_of_fiberedMZEqM du module MirrorGapTerminalClosure). [INCIDENT : docstring ≠ état du type : elle annonce le remplacement par un alias inconditionnel « une fois la représentation… », le type reste conditionnel (FiberedMZEqM → RH) ; nom dupliqué entre deux modules.] | IMPLIQUE RH SOUS PRÉMISSE (loi de grammaire fibrée FiberedMZEqM (⟺ RH) ; nom dupliqué avec le théorème de MirrorGapTerminalClosure) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 0 |

### `RhGapCriterion.ScientificRebuild20260829.SingletonPassageEncZFactorization`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.selectedEncZCell_eq_sourcePrimeGap` | La cellule EncZ sélectionnée est exactement l'écart premier reconstruit par la source zéros à la colonne d'événement. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.selectedEncZCell_eq_gnat` | EncZ = M sur la cellule sélectionnée : la cellule reconstruite est l'écart premier canonique gnat. | CONFIRMÉE | V48 | 3 |
| `ScientificRebuild20260829.localPrimeReadout_agrees_with_encZ_selected_cell` | La lecture première de l'encodeur local coïncide avec la cellule EncZ sélectionnée. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.selectedEncZCell_pos` | La cellule EncZ sélectionnée est strictement positive (un vrai écart premier consécutif). | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.seamMirrorPairSelection_card` | Hors ligne, la sélection du couple miroir a exactement deux éléments distincts. | CONFIRMÉE SOUS CONDITION (zéro hors ligne (β ≠ 1/2)) | V62 | 0 |
| `ScientificRebuild20260829.seamMirrorPairSelection_same_height` | Les deux membres sélectionnés (ρ et son miroir) sont à exactement la même hauteur. | CONFIRMÉE | V65 | 0 |
| `ScientificRebuild20260829.seamPairPrimitivePart_reads_both_members` | La partie primitive de la paire lit les deux membres : x·(terme(ρ)+terme(miroir)). | CONFIRMÉE SOUS CONDITION (zéro hors ligne (β ≠ 1/2)) | AJOUT | 0 |
| `ScientificRebuild20260829.seam_psi_rest_decomposition` | Découpage exact inconditionnel de ψ reconstruit au couple miroir du raccord et au reste. | CONFIRMÉE (domaine : t ≥ 2) | V121 | 0 |
| `ScientificRebuild20260829.seam_weighted_count_rest_decomposition` | Découpage exact du compte pondéré reconstruit au couple miroir et au reste. | CONFIRMÉE (domaine : x ≥ 2) | AJOUT | 0 |
| `ScientificRebuild20260829.seam_prime_count_rest_decomposition` | Le compte premier réel reconstruit se scinde exactement en la partie du couple miroir propre du raccord et le reste. | CONFIRMÉE (domaine : x ≥ 2) | AJOUT | 1 |
| `ScientificRebuild20260829.countOfRealCount_congr` | L'opérateur d'extraction de compte n'inspecte son argument qu'aux seuils réels ≥ 2 (deux fonctions égales sur x ≥ 2 ont même extraction). | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.primeGapOfRealCount_congr` | Idem pour l'extraction de l'écart premier. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.sourcePrimeGap_canonical_eq_extraction` | L'écart premier de la source zéros canonique est l'extraction appliquée au compte premier reconstruit. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.selectedEncZCell_factors_through_seam_split` | Couture typée : la cellule EncZ sélectionnée est l'extraction appliquée à la fonction « partie du couple + reste » du compte premier reconstruit. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.localEncoder_factors_through_seam_split` | Même couture énoncée sur l'encodeur local : la lecture première est l'extraction du découpage couple/reste. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.seam_two_realizations` | Les deux réalisations de la couture coexistent sur une cellule : lecture zéros some 0 et lecture première gnat. | CONFIRMÉE | V162 | 0 |
| `ScientificRebuild20260829.selectedEncZCell_ne_restOnlyCell_of_noAbsorption` | Audit, non fermeture : sous non-absorption, la cellule EncZ sélectionnée diffère de la cellule construite du reste seul. | CONFIRMÉE SOUS CONDITION (le reste n'absorbe pas le couple à la colonne du raccord (SeamRestDoesNotAbsorbPair, prémisse nommée)) | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260829.TerminalSocketForceAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.terminalSocket_is_rh_strength` | La prise terminale FiberedMZEqM est de force RH (certificat réutilisé). | ÉQUIVALENTE À RH (FiberedMZEqM) | V140 | 0 |
| `ScientificRebuild20260829.zeroEntry_always_null` | L'entrée zéros d'une entrée construite est toujours nulle. | CONFIRMÉE | V162 | 0 |
| `ScientificRebuild20260829.primeEntry_never_null` | L'entrée première d'une entrée construite n'est jamais nulle. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.fiberedGapNullityFidelity_iff_false` | La fidélité de nullité d'une entrée construite équivaut à False (« True ⟺ False ») : aucune liberté résiduelle. | RÉFUTATION COMPILÉE (fidélité de nullité de l'écart (FiberedGapNullityFidelity) d'une entrée construite hors ligne) | AJOUT | 0 |
| `ScientificRebuild20260829.seam_is_constructible_without_rh` | La couture de SingletonPassageEncZFactorization se construit sans RH pour tout membre positif hors ligne. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V62 | 0 |

### `RhGapCriterion.ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEvent`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.canonicalEventAxisPrime_eq` | Le premier occupant de l'axe canonique d'un événement de départ n est p(n+1). | CONFIRMÉE | V28 | 0 |
| `ScientificRebuild20260829.canonicalEventAxisPrime_isPrime` | L'occupant de l'axe est un vrai premier. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.canonicalEventAxis_rigid` | L'axe d'événement canonique est rigide : même premier ⟹ même départ d'événement. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.stage_pos` | Champ de TrueContactCanonicalAxisPrimeEventCell : l'étage est ≥ 1. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.gamma_pos` | Champ : la hauteur de ρ est > 0. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.left_ge_two` | Champ : le contact gauche vrai est ≥ 2. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.eventStart_ge_two` | Champ : le départ d'événement est ≥ 2. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.axis_inside` | Champ : l'axe est strictement entre le contact gauche et le contact droit. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.axis_eq_tourPivotPrime` | Le pivot d'événement est exactement l'occupant p(n+1) de l'axe canonique. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.vonMangoldt_axis_position_lock` | Von Mangoldt reconstruit exactement le même premier central canonique. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.vonMangoldt_axis_gap_lock` | Von Mangoldt reconstruit exactement l'écart sortant au même indice de pivot. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.canonical_axis_gap_pos` | L'écart sortant canonique à l'axe est non nul. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.recovers_gamma` | La même paire de contacts vrais récupère γ. | CONFIRMÉE | V45 | 0 |
| `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.recovers_beta` | La même paire de contacts vrais récupère β. | CONFIRMÉE | V45 | 0 |
| `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.contact_to_canonicalAxis_cocycle` | Transport contact/Tour du même membre vers l'axe d'événement canonique rigide (cocycle). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260829.TrueContactCenterPrimeEvent`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.trueContactCenter_congr` | Le centre de la paire de contacts ne dépend que de la paire : même paire, même centre. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.contactSignature_fst` | Le premier composant de la signature de contact est le contact vrai gauche. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.contactSignature_snd` | Le second composant est le contact d'étage droit. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.tangentStageRight_eq_contact_mul` | Le contact droit d'étage m est le contact gauche multiplié par exp(mπ/γ) (facteur ne dépendant que de la hauteur). | CONFIRMÉE (domaine : γ ≠ 0) | V17 | 2 |
| `ScientificRebuild20260829.stageFactor_pos` | Le facteur d'étage est strictement positif. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.trueContactCenter_eq_contact_mul_stageFactor` | Le centre de la paire de contacts vrais est le contact gauche fois le facteur d'étage. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.trueContactCenter_pos` | Le centre de la paire est strictement positif. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.contact_lt_stageRight` | Le contact gauche est strictement inférieur au contact droit d'étage positif. | CONFIRMÉE (domaine : hauteur > 0, m ≥ 1) | AJOUT | 2 |
| `ScientificRebuild20260829.trueContactCenter_strictly_between` | Le centre est strictement entre les deux contacts vrais. | CONFIRMÉE (domaine : hauteur > 0, m ≥ 1) | AJOUT | 2 |
| `ScientificRebuild20260829.trueContactCenter_eq_mirror_iff_critical` | Le centre du membre égale celui de son miroir ⟺ β=1/2 (le centre voit β). | CONFIRMÉE (domaine : hauteur > 0) | AJOUT | 2 |
| `ScientificRebuild20260829.trueOffline_center_ne_mirror_center` | Hors ligne, les deux membres de même hauteur ont des centres distincts. | CONFIRMÉE SOUS CONDITION (zéro de hauteur > 0 hors ligne) | V163 | 0 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.stage_pos` | Champ de TrueContactCenterPrimeEventCell : l'étage est ≥ 1 (paire ordonnée). | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.gamma_pos` | Champ : la hauteur de ρ est > 0 (représentant supérieur du quartet). | CONFIRMÉE | AJOUT | 3 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.left_ge_two` | Champ : le contact gauche est ≥ 2. | CONFIRMÉE | AJOUT | 3 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.primeIndex_ge_two` | Champ : l'indice d'événement est ≥ 2 (convention de placement). | CONFIRMÉE | AJOUT | 3 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.center_eq_prime` | Champ : le centre de la paire de contacts vrais est exactement le premier canonique p(primeIndex) (le pointage). | CONFIRMÉE | AJOUT | 6 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.primeIndex_unique` | Le centre détermine de façon unique l'indice pointé : deux cellules d'événement du même membre ont même indice premier. | CONFIRMÉE | V61 | 0 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.event_prime_isPrime` | L'objet pointé est un vrai premier canonique, jamais une puissance de premier. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.right_ge_two` | Le contact droit est ≥ 2 (région de von Mangoldt). | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.event_prime_strictly_inside` | Le premier d'événement est strictement à l'intérieur de la cellule de contact du membre. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.toSelectedPivotCell_primeIndex` | L'indice premier de la cellule à pivot sélectionné égale celui de la cellule d'événement. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.recovers_gamma` | La même paire de contacts récupère la hauteur du membre. | CONFIRMÉE | V45 | 1 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.recovers_beta` | La même paire de contacts récupère β. | CONFIRMÉE | V45 | 1 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.vonMangoldt_event_position` | Le canal zéros reconstruit exactement la position du premier d'événement. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.vonMangoldt_event_gap` | Le canal zéros reconstruit exactement l'écart canonique de la cellule d'événement. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.event_gap_pos` | L'écart premier canonique de la cellule d'événement est strictement positif. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.eventBlock_start` | Le bloc d'événement commence à l'indice pointé. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.eventBlock_length` | Le bloc d'événement a longueur 1. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.encZ_eq_M_on_event_block` | EncZ = M sur la cellule d'événement vraie : la grammaire première reconstruite depuis la source zéros canonique égale la grammaire complète canonique. | CONFIRMÉE | V48 | 1 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.eventEncZCell_eq_gnat` | La cellule EncZ d'événement égale gnat de l'indice pointé. | CONFIRMÉE | V48 | 3 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.eventEncZCell_pos` | La cellule EncZ d'événement est strictement positive. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.contactCell_contains_event_prime` | La cellule de contact du membre contient au moins le premier d'événement (incrément arithmétique ≥ 1). | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.event_prime_eq_tourPivot` | Si le centre tombe dans une fenêtre de Tour à deux transitions, le premier pointé est exactement le pivot de cette fenêtre. | CONFIRMÉE (domaine : p n < centre < p(n+2)) | AJOUT | 0 |
| `ScientificRebuild20260829.contactPairCenter_pointing_shape_satisfiable` | La forme de la contrainte de pointage est satisfaisable : pour tout N il existe une paire ordonnée de réels dont le centre est p N. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.critical_of_shared_center_event_prime` | Audit de force : un membre et son miroir fonctionnel ne peuvent pointer sur le même premier d'événement que si β=1/2. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.offline_center_event_primes_distinct` | Forme contraposée : hors ligne, les deux membres de même hauteur pointent sur des premiers d'événement différents. | CONFIRMÉE SOUS CONDITION (zéro hors ligne (β ≠ 1/2)) | AJOUT | 0 |
| `ScientificRebuild20260829.trueContactCenterPrimeEventCell_of_hit` | Ce théorème manquant est exactement ce que la cellule d'événement exige : sous « le centre atteint un premier canonique », une cellule d'événement existe. | CONFIRMÉE SOUS CONDITION (prémisse nommée TrueContactCenterHitsCanonicalPrime (« le théorème manquant »), zéro de hauteur > 0) | AJOUT | 1 |
| `ScientificRebuild20260829.trueEventCompatibility_eq_localCompatibility` | Mise à niveau canonique de la compatibilité locale : quand un état de bord réel et une cellule d'événement pointent au même indice, leurs compatibilités coïncident. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.trueEvent_contactCell_exact_readout` | Ce que le pointage donne : le canal zéros complet lit exactement ΔΨ de la cellule de contact du membre. | CONFIRMÉE | V145 | 0 |

### `RhGapCriterion.ScientificRebuild20260829.TrueEventSingletonPassage`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.TrueEventSingletonPassageRaccord.raccord_is_canonical` | Champ de TrueEventSingletonPassageRaccord : le raccord est le raccord structurel canonique. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.TrueEventSingletonPassageRaccord.uniquePlace_maps_to_trueEventPrime` | L'unique passage local est assigné à l'unique place première locale, qui est la colonne d'événement vraie. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.TrueEventSingletonPassageRaccord.orderedGap_eq_zero` | Le passage GZ sélectionné de la fibre miroir est nul (some 0). | CONFIRMÉE | V162 | 0 |
| `ScientificRebuild20260829.TrueEventSingletonPassageRaccord.center_points_at_event_prime` | Le premier d'événement est exactement le centre de la paire de contacts vrais de ρ. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.TrueEventSingletonPassageRaccord.encZ_eq_M_on_trueEvent` | EncZ = M sur la colonne d'événement vraie. | CONFIRMÉE | V48 | 0 |
| `ScientificRebuild20260829.trueEventSingletonPassageRaccord_of_hit` | Existence du raccord à passage singleton d'événement vrai, conditionnelle au seul premier théorème typé manquant. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne et prémisse nommée TrueContactCenterHitsCanonicalPrime) | AJOUT | 0 |
| `ScientificRebuild20260829.TrueEventCrosswalk.left_row` | Champ de TrueEventCrosswalk : la ligne gauche est gapIndex. | CONFIRMÉE | AJOUT | 3 |
| `ScientificRebuild20260829.TrueEventCrosswalk.right_row` | Champ : la ligne droite est gapIndex+1. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.TrueEventCrosswalk.left_column` | Champ : la colonne gauche est 0. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.TrueEventCrosswalk.right_column` | Champ : la colonne droite est 0. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.TrueEventCrosswalk.leftInternalGap_eq_zero` | La ligne gauche lit l'écart interne some 0 du passage GZ sélectionné. | CONFIRMÉE | V162 | 1 |
| `ScientificRebuild20260829.TrueEventCrosswalk.endpointMembers_exact` | Les deux lignes sont exactement les deux extrémités du passage local sélectionné. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.TrueEventCrosswalk.sameTrueEventPrimeColumn` | Les deux lignes portent la colonne première d'événement vraie (écart gnat). | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.TrueEventCrosswalk.refinementEntries_read_endpoint_members` | Les entrées sensibles au membre restent les contributions pré-agrégation des deux extrémités sur la colonne vraie. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.encodeTrueEvent_zeroRealization` | Réalisation zéros : l'observable commun lit le passage GZ du témoin de fibre miroir. | CONFIRMÉE | V162 | 1 |
| `ScientificRebuild20260829.encodeTrueEvent_primeEventRealization` | Réalisation premier-événement : le centre de contact vaut p(indice d'événement), qui est premier. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.encodeTrueEvent_encZRealization` | Réalisation EncZ : la cellule EncZ d'événement égale l'encodage de la source zéros sur la colonne du centre. | CONFIRMÉE | V48 | 1 |
| `ScientificRebuild20260829.trueEvent_three_realizations` | Trois réalisations sur un objet pour un membre, sans égalité inter-domaines entre elles. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.seam_and_trueEvent_same_encZ_cell` | Si les deux colonnes coïncident, la cellule EncZ sélectionnée historique et celle de l'événement vrai sont littéralement la même. | CONFIRMÉE SOUS CONDITION (prémisse nommée DefectColumnIsTrueEventPrime (les deux colonnes coïncident)) | AJOUT | 0 |

### `RhGapCriterion.ScientificRebuild20260829.TrueZeroQuartetPrimeEdgeTransport`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.quartet_seedVoice_ne_sameHeightMirrorVoice` | La voix de la graine et celle du miroir de même hauteur restent distinctes dans le porteur transformé complet de l'arête. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.quartet_seedVoice_ne_conjugateVoice` | La voix de la graine et celle du conjugué restent distinctes. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.quartet_seedVoice_ne_oppositeHeightMirrorVoice` | La voix de la graine et celle du miroir de hauteur opposée restent distinctes. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.quartet_conjugateVoice_ne_sameHeightMirrorVoice` | La voix du conjugué et celle du miroir de même hauteur restent distinctes. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.quartet_conjugateVoice_ne_oppositeHeightMirrorVoice` | La voix du conjugué et celle du miroir de hauteur opposée restent distinctes. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.quartet_sameHeightMirrorVoice_ne_oppositeHeightMirrorVoice` | Les voix des deux miroirs complémentaires restent distinctes. | CONFIRMÉE | AJOUT | 1 |
| `ScientificRebuild20260829.quartet_all_six_voice_separations` | Les six séparations complexes deux à deux du quartet survivent simultanément sur toute arête première canonique. | CONFIRMÉE | AJOUT | 2 |
| `ScientificRebuild20260829.quartet_upper_sameHeightSpan` | La moitié haute du quartet a la même étendue scalaire de hauteur. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.quartet_lower_sameHeightSpan` | La moitié basse du quartet a la même étendue scalaire de hauteur. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.quartet_conjugateHeightSpan_eq_neg_seed` | La conjugaison renverse exactement le canal scalaire de hauteur (étendue conjuguée = − étendue de la graine). | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.quartet_oppositeHeightMirrorSpan_eq_neg_upperMirror` | L'étendue du miroir de hauteur opposée est l'opposée de celle du miroir supérieur. | CONFIRMÉE | AJOUT | 0 |
| `ScientificRebuild20260829.quartet_upper_rawHeightGap_zero_but_transformedGap_nonzero` | Collision de hauteur supérieure : l'écart brut d'ordonnée est nul tandis que l'écart transformé complet sur l'arête est non nul. | CONFIRMÉE | V162 | 0 |
| `ScientificRebuild20260829.quartet_lower_rawHeightGap_zero_but_transformedGap_nonzero` | Collision de hauteur inférieure : même constat pour la moitié conjuguée du quartet. | CONFIRMÉE | V162 | 0 |
| `ScientificRebuild20260829.quartet_transport_vonMangoldt_edge_lock` | Le transport complet du quartet est soudé à une arête première von Mangoldt positive immuable (six séparations de voix). | CONFIRMÉE | V63 | 0 |

### `RhGapCriterion.ScientificRebuild20260829.TrustedZetaSeamBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ScientificRebuild20260829.TrustedZetaSeam.zerohood` | Sous la couture de zêta de confiance, tout zéro non trivial annule zêta. | CONFIRMÉE (domaine : TrustedZetaSeam (couture de zêta de confiance, déchargée par trustedZetaSeam)) | V6 | 0 |
| `ScientificRebuild20260829.TrustedZetaSeam.open_strip` | Sous la couture, tout zéro non trivial est dans la bande ouverte. | CONFIRMÉE (domaine : TrustedZetaSeam (couture de zêta de confiance, déchargée par trustedZetaSeam)) | V7 | 0 |
| `ScientificRebuild20260829.TrustedZetaSeam.height_nonzero` | Sous la couture, tout zéro non trivial a hauteur non nulle. | CONFIRMÉE (domaine : TrustedZetaSeam (couture de zêta de confiance, déchargée par trustedZetaSeam)) | V7 | 0 |
| `ScientificRebuild20260829.TrustedZetaSeam.multiplicity_positive` | Sous la couture, tout zéro non trivial a multiplicité > 0. | CONFIRMÉE (domaine : TrustedZetaSeam (couture de zêta de confiance, déchargée par trustedZetaSeam)) | AJOUT | 0 |
| `ScientificRebuild20260829.TrustedZetaSeam.conjugate_is_nontrivial` | Sous la couture, le conjugué d'un zéro non trivial est un zéro non trivial. | CONFIRMÉE (domaine : TrustedZetaSeam (couture de zêta de confiance, déchargée par trustedZetaSeam)) | V63 | 0 |
| `ScientificRebuild20260829.TrustedZetaSeam.mirror_is_nontrivial` | Sous la couture, le miroir est un zéro non trivial. | CONFIRMÉE (domaine : TrustedZetaSeam (couture de zêta de confiance, déchargée par trustedZetaSeam)) | V63 | 2 |
| `ScientificRebuild20260829.TrustedZetaSeam.mirror_same_height` | Sous la couture, le miroir a la même hauteur. | CONFIRMÉE (domaine : TrustedZetaSeam (couture de zêta de confiance, déchargée par trustedZetaSeam)) | V65 | 3 |
| `ScientificRebuild20260829.TrustedZetaSeam.mirror_complementary_re` | Sous la couture, le miroir a partie réelle 1−β. | CONFIRMÉE (domaine : TrustedZetaSeam (couture de zêta de confiance, déchargée par trustedZetaSeam)) | V65 | 2 |
| `ScientificRebuild20260829.TrustedZetaSeam.mirror_multiplicity` | Sous la couture, le miroir a la même multiplicité. | CONFIRMÉE (domaine : TrustedZetaSeam (couture de zêta de confiance, déchargée par trustedZetaSeam)) | V65 | 1 |
| `ScientificRebuild20260829.TrustedZetaSeam.mirror_fixed_iff_critical` | Sous la couture, le miroir est confondu avec ρ ⟺ β=1/2. | CONFIRMÉE (domaine : TrustedZetaSeam (couture de zêta de confiance, déchargée par trustedZetaSeam)) | V77 | 2 |
| `ScientificRebuild20260829.trustedZetaSeam` | La couture de zêta de confiance est entièrement déchargée depuis la couche de vrais zéros de zêta existante. | CONFIRMÉE | V62 | 5 |
| `ScientificRebuild20260829.trustedMirrorProfile` | Vue sous forme de théorème du profil miroir : zéro non trivial, même hauteur, β complémentaire, même multiplicité, point fixe ⟺ β=1/2. | CONFIRMÉE | V65 | 0 |

### `RhGapCriterion.SemanticFullAlignment`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `FullNonterminalSemanticAlignment.exactMirrorRowsAndHeightCollision` | Les deux lignes de la table sont exactement le zéro et son miroir (collision de hauteur). | CONFIRMÉE (domaine : paquet FullNonterminalSemanticAlignment W (toujours réalisé, cf. fullNonterminalSemanticAlignment_holds)) | AJOUT | 0 |
| `FullNonterminalSemanticAlignment.orderedCollectiveTrouble` | Le trouble collectif ordonné est un écart interne some 0. | CONFIRMÉE (domaine : paquet FullNonterminalSemanticAlignment W (toujours réalisé, cf. fullNonterminalSemanticAlignment_holds)) | V162 | 0 |
| `FullNonterminalSemanticAlignment.pairSensitiveZeroPrimeCouplingDefect` | Défaut de couplage zéro-premier sensible à la paire : les lignes zéro/miroir diffèrent à la colonne première. | CONFIRMÉE (domaine : paquet FullNonterminalSemanticAlignment W (toujours réalisé, cf. fullNonterminalSemanticAlignment_holds)) | AJOUT | 0 |
| `FullNonterminalSemanticAlignment.pairPrimeGrammarWeld` | Le côté premier de la capture du partenariat est le bloc premier de la grammaire active de la jonction. | CONFIRMÉE (domaine : paquet FullNonterminalSemanticAlignment W (toujours réalisé, cf. fullNonterminalSemanticAlignment_holds)) | AJOUT | 0 |
| `FullNonterminalSemanticAlignment.collectivePrimeBridgeOnSameColumn` | Le pont collectif premier sur la même colonne : la somme sur tous les zéros de la contribution égale la différence de sommes de von Mangoldt lissées. | CONFIRMÉE (domaine : paquet FullNonterminalSemanticAlignment W (toujours réalisé, cf. fullNonterminalSemanticAlignment_holds)) | V121 | 0 |
| `FullNonterminalSemanticAlignment.localizedPartnership` | Le partenariat localisé est couvert. | CONFIRMÉE (domaine : paquet FullNonterminalSemanticAlignment W (toujours réalisé, cf. fullNonterminalSemanticAlignment_holds)) | AJOUT | 0 |
| `FullNonterminalSemanticAlignment.grammarHierarchy` | La couverture de la hiérarchie sémantique premiers/zéros tient. | CONFIRMÉE (domaine : paquet FullNonterminalSemanticAlignment W (toujours réalisé, cf. fullNonterminalSemanticAlignment_holds)) | AJOUT | 0 |
| `FullNonterminalSemanticAlignment.assemblyWindow` | La fenêtre d'assemblage de la paire est couverte. | CONFIRMÉE (domaine : paquet FullNonterminalSemanticAlignment W (toujours réalisé, cf. fullNonterminalSemanticAlignment_holds)) | AJOUT | 0 |
| `FullNonterminalSemanticAlignment.radialSeparationNonzero` | La séparation radiale du partenariat est non nulle. | CONFIRMÉE (domaine : paquet FullNonterminalSemanticAlignment W (toujours réalisé, cf. fullNonterminalSemanticAlignment_holds)) | V162 | 0 |
| `fullNonterminalSemanticAlignment_holds` | L'alignement sémantique non terminal complet est dérivable pour tout cas soudé spécifique à une paire. | CONFIRMÉE | AJOUT | 1 |
| `fullNonterminalSemanticAlignment_exists` | Forme d'existence du cas hors ligne pleinement aligné pour tout zéro positif supposé hors de la ligne critique. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V62 | 0 |

### `RhGapCriterion.SemanticGrammarHierarchy`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `patternFamilyOf_contains` | Toute forme de motif appartient à sa famille de motifs. | CONFIRMÉE | AJOUT | 0 |
| `zero_prime_patternFamilyAt_eq` | La famille de motifs reconstruite depuis l'histoire des zéros égale celle lue sur l'histoire première canonique. | CONFIRMÉE | V48 | 1 |
| `zero_prime_metaPatternView_eq` | La vue méta-motif complète est transportée exactement de l'histoire reconstruite vers l'histoire première canonique. | CONFIRMÉE | V48 | 1 |
| `zero_prime_patternOccupationProfile_eq` | Les profils d'occupation des motifs coïncident à toute échelle entre histoires reconstruite et première. | CONFIRMÉE | V48 | 1 |
| `zero_prime_primitiveFamilyOccupationProfile_eq` | Les profils d'occupation de familles primitives coïncident à toute échelle. | CONFIRMÉE | V48 | 1 |
| `prime_history_determines_zero_multiplicity` | Toute continuation déterminée par les premiers fixe la multiplicité de la source zéros, non seulement l'appartenance. | CONFIRMÉE | AJOUT | 1 |
| `PrimeZeroSemanticHierarchyCoverage.patternFamilyTransport` | Transport de la famille de motifs (même énoncé que 761, sous la couverture). | CONFIRMÉE SOUS CONDITION (prémisse nommée PrimeZeroSemanticHierarchyCoverage) | V48 | 0 |
| `PrimeZeroSemanticHierarchyCoverage.metaPatternTransport` | Transport de la vue méta-motif (même énoncé que 762, sous la couverture). | CONFIRMÉE SOUS CONDITION (prémisse nommée PrimeZeroSemanticHierarchyCoverage) | V48 | 0 |
| `PrimeZeroSemanticHierarchyCoverage.patternOccupationTransport` | Transport des profils d'occupation de motifs (même énoncé que 763, sous la couverture). | CONFIRMÉE SOUS CONDITION (prémisse nommée PrimeZeroSemanticHierarchyCoverage) | V48 | 0 |
| `PrimeZeroSemanticHierarchyCoverage.primitiveFamilyOccupationTransport` | Transport des profils de familles primitives (même énoncé que 764, sous la couverture). | CONFIRMÉE SOUS CONDITION (prémisse nommée PrimeZeroSemanticHierarchyCoverage) | V48 | 0 |
| `PrimeZeroSemanticHierarchyCoverage.multiplicityDetermination` | Sous la couverture de hiérarchie, toute continuation déterminée par les premiers fixe la multiplicité de la source zéros. | CONFIRMÉE (domaine : PrimeZeroSemanticHierarchyCoverage (établi par primeZeroSemanticHierarchyCoverage_holds)) | AJOUT | 0 |
| `primeZeroSemanticHierarchyCoverage_holds` | La hiérarchie sémantique complète de grammaire non terminale (premiers/zéros) est déjà dérivable (M^Z=M étendu aux motifs et méta-motifs ; cf. O13 : la hiérarchie plus large n'est pas portée dans RHV6Fresh). | CONFIRMÉE | V48 | 1 |

### `RhGapCriterion.SemanticMirrorPairPrimeWeld`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `MirrorPairPrimeJunction.selectedBlock_start` | Champ de MirrorPairPrimeJunction : le bloc sélectionné commence à l'indice premier de la jonction. | CONFIRMÉE | AJOUT | 0 |
| `MirrorPairPrimeJunction.selectedBlock_length` | Le bloc sélectionné a longueur 1. | CONFIRMÉE | AJOUT | 0 |
| `MirrorPairPrimeJunction.selectedBlock_end` | Le bloc sélectionné finit à primeIndex+1. | CONFIRMÉE | AJOUT | 0 |
| `MirrorPairPrimeJunction.rows_are_exact_mirror_pair` | Les deux lignes de la table de correspondance sont littéralement le membre choisi et son miroir fonctionnel. | CONFIRMÉE | V63 | 2 |
| `MirrorPairPrimeJunction.sourceSensitiveEntries_differ` | Sur la colonne première sélectionnée, les deux entrées de table sensibles à la source diffèrent. | CONFIRMÉE | AJOUT | 0 |
| `MirrorPairPrimeJunction.samePrimeLabels_differentSourceEntries` | Les deux lignes portent les mêmes étiquettes premières canoniques sur la colonne tout en gardant des entrées sensibles à la source distinctes. | CONFIRMÉE | AJOUT | 1 |
| `MirrorPairPrimeJunction.reconstructedGrammar_eq_activePrimeBlock` | La grammaire première reconstruite sur la colonne sélectionnée égale le bloc premier canonique de la grammaire active. | CONFIRMÉE | V48 | 1 |
| `MirrorPairPrimeJunction.canonicalZeroSource_encodes_activePrimeBlock` | La source zéros canonique encode le même bloc premier. | CONFIRMÉE | V48 | 0 |
| `MirrorPairPrimeJunction.collectivePrimeBridge` | Le pont collectif de la formule explicite existe sur la même colonne première que le défaut individuel de la paire miroir. | CONFIRMÉE | V121 | 1 |
| `mirrorPairPrimeJunction_exists` | Tout zéro vrai positif supposé hors ligne a une jonction première spécifique à la paire. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | AJOUT | 4 |
| `LocalizedMirrorPairPrimeWeldCase.zero_mem` | Champ de LocalizedMirrorPairPrimeWeldCase : le zéro est dans les représentants positifs. | CONFIRMÉE | AJOUT | 1 |
| `LocalizedMirrorPairPrimeWeldCase.offLine` | Champ : le zéro est hors ligne. | CONFIRMÉE | AJOUT | 2 |
| `LocalizedMirrorPairPrimeWeldCase.partnership_zero` | Champ : le partenariat porte le zéro de la soudure. | CONFIRMÉE | AJOUT | 7 |
| `LocalizedMirrorPairPrimeWeldCase.partnership_block` | Champ : le bloc du partenariat est le bloc sélectionné de la jonction. | CONFIRMÉE | AJOUT | 2 |
| `LocalizedMirrorPairPrimeWeldCase.radial_nonzero` | Champ : le défaut radial du partenariat est non nul. | CONFIRMÉE | V162 | 2 |
| `localizedMirrorPairPrimeWeldCase_exists` | Le cas soudé fort existe pour tout zéro vrai positif hors ligne, sans hypothèse mathématique nouvelle. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | AJOUT | 1 |
| `localizedMirrorPairPrimeWeldCase_exists_same_zero` | Même constructeur en retenant l'identité du membre : ∃ W, W.zero = ρ. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | AJOUT | 5 |
| `LocalizedMirrorPairPrimeWeldCase.partnershipBlock_starts_at_pairPrimeColumn` | Le bloc premier transporté par le partenariat commence exactement à la colonne première sensible à la paire. | CONFIRMÉE | AJOUT | 5 |
| `LocalizedMirrorPairPrimeWeldCase.partnershipBlock_is_one_transition` | Le bloc transporté est exactement une transition première. | CONFIRMÉE | AJOUT | 2 |
| `LocalizedMirrorPairPrimeWeldCase.capturePrimeWindow_starts_at_pairPrimeColumn` | La fenêtre première de la capture commence à la colonne sensible à la paire. | CONFIRMÉE | AJOUT | 6 |
| `LocalizedMirrorPairPrimeWeldCase.capturePrimeWindow_has_one_transition` | La fenêtre première de la capture est exactement le bloc à une transition. | CONFIRMÉE | AJOUT | 6 |
| `LocalizedMirrorPairPrimeWeldCase.capturePrimeSide_eq_pairPrimeGrammar` | Le côté premier du partenariat localisé est le bloc de grammaire première active de la jonction spécifique à la paire. | CONFIRMÉE | AJOUT | 4 |
| `LocalizedMirrorPairPrimeWeldCase.pairSourceDefect_on_partnershipBlock` | Le défaut de ligne sensible à la source de la paire miroir tombe sur la première transition du même bloc premier. | CONFIRMÉE | AJOUT | 6 |
| `LocalizedMirrorPairPrimeWeldCase.pairRows_and_sourceDefect` | Les lignes de la table (zéro et miroir) et le défaut de source sont portés par le même cas soudé. | CONFIRMÉE | V63 | 0 |
| `LocalizedMirrorPairPrimeWeldCase.samePrimeLabels_pairSourceEntriesDiffer` | Les entrées sensibles à la source diffèrent tandis que toutes les étiquettes premières canoniques de la colonne restent identiques. | CONFIRMÉE | AJOUT | 1 |
| `LocalizedMirrorPairPrimeWeldCase.collectivePrimeBridge_on_partnershipBlock` | L'identité collective de colonne première vit sur le même bloc premier que le défaut individuel de la paire. | CONFIRMÉE | V121 | 2 |
| `LocalizedMirrorPairPrimeWeldCase.orderedTrouble_and_pairPrimeDefect_coexist` | Frontière exacte : le même cas soudé contient un écart zéros nul ordonné et un défaut de contribution de la paire miroir sur le bloc premier. | CONFIRMÉE | V162 | 1 |

### `RhGapCriterion.SemanticPairAssemblyWindow`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `LocalizedMirrorPairPrimeWeldCase.assemblyBlock_start` | Le bloc d'assemblage commence à la colonne de la jonction. | CONFIRMÉE | AJOUT | 2 |
| `LocalizedMirrorPairPrimeWeldCase.assemblyBlock_length` | Le bloc d'assemblage a longueur 2. | CONFIRMÉE | AJOUT | 0 |
| `LocalizedMirrorPairPrimeWeldCase.assemblyBlock_end` | Le bloc d'assemblage finit à primeIndex+2. | CONFIRMÉE | AJOUT | 0 |
| `LocalizedMirrorPairPrimeWeldCase.partnershipCell_and_assemblyWindow_same_start` | La cellule minimale du partenariat et la fenêtre d'assemblage commencent à la même colonne première. | CONFIRMÉE | AJOUT | 2 |
| `LocalizedMirrorPairPrimeWeldCase.pairCouplingDefect_on_first_assembly_edge` | Le défaut de couplage de la paire est sur la première arête de la fenêtre d'assemblage étendue. | CONFIRMÉE | AJOUT | 2 |
| `LocalizedMirrorPairPrimeWeldCase.assemblyPivot_prime` | Le pivot d'assemblage est un vrai premier. | CONFIRMÉE | AJOUT | 2 |
| `LocalizedMirrorPairPrimeWeldCase.assemblyPivot_between` | Le pivot d'assemblage est strictement entre les deux premiers de bord de la fenêtre. | CONFIRMÉE | AJOUT | 2 |
| `LocalizedMirrorPairPrimeWeldCase.assemblyPivot_unique` | Le premier central est l'unique premier strictement entre les bords de la fenêtre d'assemblage. | CONFIRMÉE (domaine : q premier strictement entre les bornes) | V61 | 1 |
| `LocalizedMirrorPairPrimeWeldCase.alternatingAssembly_edges_iff_pivotSignWord` | Les deux arêtes successives sont la paire entrante/sortante tau51,tau15 ⟺ le mot de signes de pivot est (−1,+1,−1). | CONFIRMÉE | AJOUT | 2 |
| `LocalizedMirrorPairPrimeWeldCase.alternatingAssembly_has_oddFloorPivot` | Réalisation conditionnelle du pivot harmonique : sous le mot alternant et m impair, le facteur 1+σ^m est non nul (pivot à plancher impair) ; l'hypothèse alternante n'est pas affirmée. | CONFIRMÉE SOUS CONDITION (assemblage alternant (mots tau51 puis tau15) et m impair) | AJOUT | 0 |
| `LocalizedMirrorPairPrimeWeldCase.PairAssemblyWindowCoverage.sameStart` | Sous la couverture de fenêtre d'assemblage, le bloc du partenariat et celui d'assemblage commencent au même point. | CONFIRMÉE (domaine : paquet PairAssemblyWindowCoverage (établi par pairAssemblyWindowCoverage_holds)) | AJOUT | 0 |
| `LocalizedMirrorPairPrimeWeldCase.PairAssemblyWindowCoverage.firstEdgeCarriesPairDefect` | Sous la couverture, la première arête porte le défaut de la paire. | CONFIRMÉE (domaine : paquet PairAssemblyWindowCoverage (établi par pairAssemblyWindowCoverage_holds)) | AJOUT | 0 |
| `LocalizedMirrorPairPrimeWeldCase.PairAssemblyWindowCoverage.pivotIsPrime` | Sous la couverture, le pivot est premier. | CONFIRMÉE (domaine : paquet PairAssemblyWindowCoverage (établi par pairAssemblyWindowCoverage_holds)) | AJOUT | 0 |
| `LocalizedMirrorPairPrimeWeldCase.PairAssemblyWindowCoverage.pivotBetweenBoundaries` | Sous la couverture, le pivot est entre les bornes. | CONFIRMÉE (domaine : paquet PairAssemblyWindowCoverage (établi par pairAssemblyWindowCoverage_holds)) | AJOUT | 0 |
| `LocalizedMirrorPairPrimeWeldCase.PairAssemblyWindowCoverage.pivotUnique` | Sous la couverture, le pivot est l'unique premier entre les bornes. | CONFIRMÉE (domaine : paquet PairAssemblyWindowCoverage (établi par pairAssemblyWindowCoverage_holds)) | V61 | 0 |
| `LocalizedMirrorPairPrimeWeldCase.pairAssemblyWindowCoverage_holds` | La couverture géométrique d'assemblage/pivot est inconditionnelle dès que le cas soudé existe. | CONFIRMÉE | AJOUT | 1 |

### `RhGapCriterion.SemanticProofSpine`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `OffLineMirrorTroubleCase.zero_mem` | Champ de OffLineMirrorTroubleCase : le zéro est dans les représentants positifs. | CONFIRMÉE | AJOUT | 0 |
| `OffLineMirrorTroubleCase.offLine` | Champ : le zéro est hors ligne. | CONFIRMÉE | AJOUT | 1 |
| `OffLineMirrorTroubleCase.partnership_zero` | Champ : le partenariat porte le zéro. | CONFIRMÉE | AJOUT | 1 |
| `OffLineMirrorTroubleCase.partnership_block` | Champ : le bloc du partenariat est le bloc du cas. | CONFIRMÉE | AJOUT | 0 |
| `OffLineMirrorTroubleCase.radial_nonzero` | Champ : le défaut radial du partenariat est non nul. | CONFIRMÉE | V162 | 0 |
| `offLineMirrorTroubleCase_exists` | Tout vrai zéro positif supposé hors ligne donne un cas de trouble miroir hors ligne sémantiquement complet. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | AJOUT | 0 |
| `MemberMirrorGeometry.directCarrierRealizesMember` | Sous la géométrie membre/miroir, le porteur direct réalise le porteur vrai du zéro. | CONFIRMÉE (domaine : paquet MemberMirrorGeometry P (couverture)) | AJOUT | 0 |
| `MemberMirrorGeometry.memberIsFiberPoint` | Le membre est le point de fibre à sa hauteur et à sa partie réelle. | CONFIRMÉE (domaine : paquet MemberMirrorGeometry P (couverture)) | AJOUT | 0 |
| `MemberMirrorGeometry.mirrorIsTrueZero` | Le miroir du partenariat est un vrai zéro non trivial. | CONFIRMÉE (domaine : paquet MemberMirrorGeometry P (couverture)) | V63 | 0 |
| `MemberMirrorGeometry.mirrorSharesHeight` | Le miroir a la même hauteur. | CONFIRMÉE (domaine : paquet MemberMirrorGeometry P (couverture)) | V65 | 0 |
| `MemberMirrorGeometry.mirrorHasReflectedRadialPosition` | Le miroir a partie réelle 1−β. | CONFIRMÉE (domaine : paquet MemberMirrorGeometry P (couverture)) | V65 | 0 |
| `MemberMirrorGeometry.pairOccupiesSameHeightFiber` | La paire occupe la même fibre de hauteur : deux points de fibre sont des zéros non triviaux. | CONFIRMÉE (domaine : paquet MemberMirrorGeometry P (couverture)) | V62 | 0 |
| `PrimeGrammarCoverage.rigid` | Sous la couverture de grammaire première, le bloc premier est rigide. | CONFIRMÉE (domaine : paquet PrimeGrammarCoverage P (couverture)) | AJOUT | 0 |
| `PrimeGrammarCoverage.gapTransitionProjection` | Projection écart/transition : classes d'écart mod 6 (0, 2, 4) et changement/maintien du résidu du premier sur le bloc. | CONFIRMÉE (domaine : paquet PrimeGrammarCoverage P (couverture)) | V174 | 0 |
| `PrimeGrammarCoverage.composition` | Loi de composition : le produit des 1−2cross sur le bloc vaut sigma(début)·sigma(fin). | CONFIRMÉE (domaine : paquet PrimeGrammarCoverage P (couverture)) | AJOUT | 0 |
| `PrimeGrammarCoverage.returnLaw` | Loi de retour : si l'entrée égale la sortie, le produit grammatical sur le bloc vaut 1 (condition entrée = sortie). | CONFIRMÉE (domaine : paquet PrimeGrammarCoverage P (couverture)) | AJOUT | 0 |
| `PrimeGrammarCoverage.chi3AtFirstAnchor` | Le caractère chi3 au premier point d'ancrage vaut sigma. | CONFIRMÉE (domaine : paquet PrimeGrammarCoverage P (couverture)) | AJOUT | 0 |
| `PrimeGrammarCoverage.tau15FromPrimeSide` | L'indicateur de transformation tau15 se lit sur le côté premier (transition = tau15 → 1 sinon 0). | CONFIRMÉE (domaine : paquet PrimeGrammarCoverage P (couverture)) | AJOUT | 0 |
| `PrimeGrammarCoverage.tau51FromPrimeSide` | L'indicateur de transformation tau51 se lit sur le côté premier. | CONFIRMÉE (domaine : paquet PrimeGrammarCoverage P (couverture)) | AJOUT | 0 |
| `PrimeGrammarCoverage.transitionsAreFiniteGraphEdges` | Les transitions sont des arêtes du graphe fini des résidus mod 6 (transformOf des résidus de p et de son successeur). | CONFIRMÉE (domaine : paquet PrimeGrammarCoverage P (couverture)) | V174 | 0 |
| `PrimeGrammarCoverage.orientedCrossNotCoboundary` | La transition signée directe est tau15−tau51 et n'est pas un cobord. | CONFIRMÉE (domaine : paquet PrimeGrammarCoverage P (couverture)) | AJOUT | 0 |
| `FiberTowerCoverage.tau15FiberReading` | Les fibres direct et réfléchie se lisent comme vecteurs de secteur tau15 (première composante). | CONFIRMÉE (domaine : paquet FiberTowerCoverage P (couverture)) | AJOUT | 0 |
| `FiberTowerCoverage.tau51FiberReading` | Les fibres direct et réfléchie se lisent comme vecteurs de secteur tau51 (seconde composante). | CONFIRMÉE (domaine : paquet FiberTowerCoverage P (couverture)) | AJOUT | 0 |
| `FiberTowerCoverage.harmonicTowerRealization` | Le transport du zéro vrai réalise le module de Tour harmonique. | CONFIRMÉE (domaine : paquet FiberTowerCoverage P (couverture)) | AJOUT | 0 |
| `FiberTowerCoverage.sameTowerMechanism` | Même mécanisme de Tour : la fibre directe est la somme sur n de l'indicateur tau15 fois log p · p^(−1/2) fois le caractère de Tour. | CONFIRMÉE (domaine : paquet FiberTowerCoverage P (couverture)) | AJOUT | 0 |
| `FiberTowerCoverage.grammarSelectsTowerSupport` | La grammaire sélectionne le support de Tour (1+σ^m ≠ 0 ⟺ σ=1 ou m pair) et le caractère de Tour se règle sur σ. | CONFIRMÉE (domaine : paquet FiberTowerCoverage P (couverture)) | AJOUT | 0 |
| `TransportProvenanceCoverage.carrierHolonomiesAreTransportDirections` | Les holonomies des porteurs sont les directions de transport (transport 0 1 et 1 0). | CONFIRMÉE (domaine : paquet TransportProvenanceCoverage P (couverture)) | AJOUT | 0 |
| `TransportProvenanceCoverage.commonBlockTransport` | Le transport commun sur le bloc est le rapport des caractères de Tour en pEnd et pStart, dans les deux sens. | CONFIRMÉE (domaine : paquet TransportProvenanceCoverage P (couverture)) | AJOUT | 0 |
| `TransportProvenanceCoverage.commonHeightPhase` | Phase de hauteur commune : même phase au zéro et au miroir, non nulle, et l'opérateur est l'inverse de la phase fois le transport. | CONFIRMÉE (domaine : paquet TransportProvenanceCoverage P (couverture)) | AJOUT | 0 |
| `TransportProvenanceCoverage.primeChannelAndCapture` | Canal premier et capture : prolongement du canal de grammaire première défini par les secteurs de Dirichlet. | CONFIRMÉE (domaine : paquet TransportProvenanceCoverage P (couverture)) | AJOUT | 0 |
| `TransportProvenanceCoverage.trueZeroMeromorphicProvenance` | Provenance méromorphe du vrai zéro : β=1/2 ou pôle d'ordre −1 du canal aux positions de fibre. | CONFIRMÉE (domaine : paquet TransportProvenanceCoverage P (couverture)) | AJOUT | 0 |
| `DefectTransportCoverage.signedRadialReadout` | Lecture radiale signée : l'opérateur est la matrice antidiagonale de ratio^(∓défaut radial). | CONFIRMÉE (domaine : paquet DefectTransportCoverage P (couverture)) | AJOUT | 4 |
| `DefectTransportCoverage.radialOperatorIdentity` | Identité radiale de l'opérateur : opérateur = opérateur croisé radial du bloc au défaut du partenariat. | CONFIRMÉE (domaine : paquet DefectTransportCoverage P (couverture)) | AJOUT | 0 |
| `ReflectionStarCoverage.mirrorReciprocity` | Réciprocité miroir : produit des deux entrées hors diagonale de l'opérateur vaut 1. | CONFIRMÉE (domaine : paquet ReflectionStarCoverage P (couverture)) | AJOUT | 0 |
| `ReflectionStarCoverage.involution` | L'opérateur est une involution. | CONFIRMÉE (domaine : paquet ReflectionStarCoverage P (couverture)) | AJOUT | 0 |
| `ReflectionStarCoverage.adjoint` | L'adjoint de l'opérateur est la matrice antidiagonale de ratio^(±défaut radial). | CONFIRMÉE (domaine : paquet ReflectionStarCoverage P (couverture)) | AJOUT | 0 |
| `ReflectionStarCoverage.operatorMulAdjoint` | T·T† est la diagonale de ratio^(∓2 défaut). | CONFIRMÉE (domaine : paquet ReflectionStarCoverage P (couverture)) | AJOUT | 0 |
| `ReflectionStarCoverage.adjointMulOperator` | T†·T est la diagonale de ratio^(±2 défaut). | CONFIRMÉE (domaine : paquet ReflectionStarCoverage P (couverture)) | AJOUT | 0 |
| `LocalizedPartnershipCoverage.memberMirror` | La couverture du partenariat entraîne la géométrie membre/miroir. | CONFIRMÉE (domaine : paquet LocalizedPartnershipCoverage P (couverture, établi par localizedPartnershipCoverage_holds)) | AJOUT | 0 |
| `LocalizedPartnershipCoverage.primeGrammar` | La couverture du partenariat entraîne la couverture de grammaire première. | CONFIRMÉE (domaine : paquet LocalizedPartnershipCoverage P (couverture, établi par localizedPartnershipCoverage_holds)) | AJOUT | 0 |
| `LocalizedPartnershipCoverage.fiberTower` | La couverture du partenariat entraîne la couverture fibre/Tour. | CONFIRMÉE (domaine : paquet LocalizedPartnershipCoverage P (couverture, établi par localizedPartnershipCoverage_holds)) | AJOUT | 0 |
| `LocalizedPartnershipCoverage.transportProvenance` | La couverture du partenariat entraîne la couverture de provenance du transport. | CONFIRMÉE (domaine : paquet LocalizedPartnershipCoverage P (couverture, établi par localizedPartnershipCoverage_holds)) | AJOUT | 0 |
| `LocalizedPartnershipCoverage.defectTransport` | La couverture du partenariat entraîne la couverture du transport de défaut. | CONFIRMÉE (domaine : paquet LocalizedPartnershipCoverage P (couverture, établi par localizedPartnershipCoverage_holds)) | AJOUT | 4 |
| `LocalizedPartnershipCoverage.reflectionStar` | La couverture du partenariat entraîne la couverture de l'étoile de réflexion. | CONFIRMÉE (domaine : paquet LocalizedPartnershipCoverage P (couverture, établi par localizedPartnershipCoverage_holds)) | AJOUT | 0 |
| `localizedPartnershipCoverage_holds` | Toute la couverture active est déjà démontrable pour tout partenariat localisé, sans prémisse terminale. | CONFIRMÉE | AJOUT | 7 |
| `OffLineMirrorTroubleCase.coverage` | Le cas réel de contradiction hors ligne satisfait toute la couverture non terminale tout en gardant une séparation radiale non nulle. | CONFIRMÉE | AJOUT | 0 |
| `mirrorBranchCoincidence_iff_critical` | La coïncidence de branche miroir équivaut à β=1/2 du membre porté : c'est une lecture terminale de criticité. | CONFIRMÉE | V140 | 4 |
| `mirrorBranchCoincidence_fails_in_offLine_case` | Dans un cas hors ligne, la lecture terminale de coïncidence de branche miroir est fausse malgré toute la couverture non terminale. | RÉFUTATION COMPILÉE (coïncidence de branche miroir / naturalité (lecture terminale) sur un cas hors ligne) | V140 | 0 |
| `mirrorBranchCoincidence_independent_of_zero_window` | La lecture terminale de coïncidence de branche miroir ne dépend pas de la fenêtre zéro stockée dans la capture découplée. | CONFIRMÉE | AJOUT | 0 |
| `riemannHypothesis_of_universal_mirrorBranchCoincidence` | La coïncidence de branche miroir universelle ferme RH ; prise de fermeture seulement, sans identifier de producteur. | IMPLIQUE RH SOUS PRÉMISSE (coïncidence de branche miroir pour tout partenariat canonique (⟺ RH par universal_mirrorBranchCoincidence_iff_rh)) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 1 |
| `universal_mirrorBranchCoincidence_iff_rh` | Comptabilité de force exacte : coïncidence de branche universelle ⟺ RH. | ÉQUIVALENTE À RH (coïncidence de branche miroir universelle) | V140 | 0 |
| `terminalImplicationForceAccounting` | Alias correctement nommé : pour Q vraie, dire que Q produit la coïncidence de branche universelle équivaut à RH. | ÉQUIVALENTE À RH (coïncidence de branche miroir universelle) | V140 | 0 |

### `RhGapCriterion.SemanticScientificBoundary`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `mirrorPairOrderedTroublePrimeCase_exists` | Tout zéro vrai positif supposé hors ligne produit le cas sémantique le plus fort actuellement implémenté (cas paire-trouble-premier). | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V62 | 0 |
| `MirrorPairOrderedTroublePrimeCase.exactMirrorRows_form_heightCollision` | Les deux lignes exactes sont le zéro choisi et son miroir fonctionnel, distincts, et forment la collision de hauteur. | CONFIRMÉE | V63 | 0 |
| `MirrorPairOrderedTroublePrimeCase.pairSensitiveZeroPrimeCouplingDefect_is_localized` | Le défaut de couplage zéro-premier sensible à la paire est localisé sur le bloc utilisé par le partenariat. | CONFIRMÉE | AJOUT | 0 |
| `MirrorPairOrderedTroublePrimeCase.nonterminalCoverage` | Le même partenariat satisfait toute la couverture non terminale active. | CONFIRMÉE | AJOUT | 1 |
| `MirrorPairOrderedTroublePrimeCase.terminalMirrorBranchCoincidence_fails` | La lecture terminale de coïncidence de branche est fausse dans le cas hors ligne supposé (diagnostic seulement). | RÉFUTATION COMPILÉE (coïncidence de branche miroir / naturalité (lecture terminale) sur un cas hors ligne) | V140 | 0 |
| `MirrorPairOrderedTroublePrimeCase.scientificBoundary` | Frontière scientifique non terminale exacte : écart zéros nul, défaut de paire, côté premier du partenariat, etc., coexistent pour le même zéro hors ligne. | CONFIRMÉE | V162 | 1 |
| `MirrorPairOrderedTroublePrimeCase.collectivePrimeBridge_at_pairSensitiveColumn` | Le pont collectif de colonne première est disponible à la colonne sensible à la paire utilisée par le partenariat. | CONFIRMÉE | V121 | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.ActualGrammarReversalNaturality`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.grammarReversalMatrix_sq` | La matrice de renversement grammatical est une involution. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.localizedOperator_eq_radialDiagonal_mul_reversal` | L'opérateur du partenariat réel est le diagonal radial fois le renversement (T_d = D_d S). | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.localizedOperator_sq_eq_one` | L'opérateur du partenariat est une involution pour tout défaut radial (contrôle spectral R10). | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.grammarReversal_conjugates_radialLift` | Covariance de réflexion : conjuguer par le renversement change le signe du défaut radial. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.actualMirrorNaturality` | Carré de naturalité entre le membre et son miroir : renverser avant le transport égale l'opérateur du miroir avant renversement. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.actualGrammarReversalNaturality_iff_mirroredOperator_eq` | La naturalité de renversement de grammaire ⟺ l'opérateur miroir égale l'opérateur direct. | CONFIRMÉE | V140 | 0 |
| `SemanticTransportClosure20260821.actualGrammarReversalNaturality_iff_orientedEntries` | La naturalité de renversement ⟺ égalité des deux entrées orientées de l'opérateur (commutation matricielle). | CONFIRMÉE | V140 | 1 |
| `SemanticTransportClosure20260821.actualGrammarReversalNaturality_iff_critical` | La naturalité de renversement d'un partenariat localisé ⟺ β=1/2 du zéro porté (audit de force du commutateur). | CONFIRMÉE | V140 | 3 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R12MatrixNaturality_iff_critical` | La naturalité matricielle R12 du cas maître hors ligne ⟺ β=1/2 (commutateur discriminant). | CONFIRMÉE | V140 | 3 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.not_R12MatrixNaturality_from_offLine` | Le cas hors ligne ne peut satisfaire la naturalité matricielle sans producteur indépendant. | RÉFUTATION COMPILÉE (coïncidence de branche miroir / naturalité (lecture terminale) sur un cas hors ligne) | V140 | 2 |

### `RhGapCriterion.SemanticTransportClosure20260821.ActualOrderedPairReturnContext`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.actualOrderedMirrorPairContext_exists` | Pour toute soudure de paire miroir, il existe un contexte ordonné de la paire miroir (aucune nouvelle hypothèse). | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.ActualOrderedMirrorPairContext.exactPair_internalConstellationGaps_zero` | Dans l'un ou l'autre ordre des deux positions du couple, tous les écarts de constellation internes sont nuls. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.ActualOrderedMirrorPairContext.firstAssemblyEdge_prefixSteps_exact` | La première arête d'assemblage récupère exactement les deux lignes analytiques individuelles depuis les préfixes successifs. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.ActualOrderedMirrorPairContext.secondAssemblyEdge_prefixSteps_exact` | La seconde arête d'assemblage est de même sans perte aux deux lignes ordonnées. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.ActualOrderedMirrorPairContext.pairAssemblyMixedCurl_eq_exactOrderedPrefixCirculation` | Le curl mixte d'assemblage de la paire est la circulation des quatre lectures de préfixe ordonné sans perte. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.ActualOrderedMirrorPairContext.firstAssemblyEdge_rowDifference_ne_zero` | La première arête reste sensible à la ligne : la différence de lignes est non nulle. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.actualSameZeroReturnPartnership_zero` | Le partenariat de retour du même zéro porte le zéro de la soudure. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.actualSameZeroReturnPartnership_block` | Le bloc du partenariat de retour est terminalPrimeBlock ([2,4)). | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.terminalPrimeBlock_actualReturnEdges` | Mot d'orientation exact du bloc de retour historique : tau51 en pStart et tau15 en pStart+1. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.terminalPrimeBlock_actualGrammaticalReturn` | L'holonomie de la grammaire première du bloc [2,4) se ferme exactement (produit = 1). | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.actualSameZeroReturnPartnership_grammaticalReturn` | R10 sur le même zéro : le partenariat de retour construit à partir de W.zero utilise un retour d'histoire première réel. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.actualSameZeroReturnPartnership_radialDefect` | Le partenariat de retour du même zéro porte exactement le même défaut radial β−1/2. | CONFIRMÉE | V102 | 1 |
| `SemanticTransportClosure20260821.actualSameZeroReturnPartnership_ratio_one_lt` | Le bloc de retour a un rapport d'échelle > 1. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.ActualSameZeroReturnContext.sameMember` | Sous le contexte de retour, le partenariat de retour a le même membre. | CONFIRMÉE (domaine : paquet ActualSameZeroReturnContext W (établi par actualSameZeroReturnContext_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.ActualSameZeroReturnContext.realReturnEdges` | Sous le contexte, les arêtes de retour réelles sont tau51 puis tau15. | CONFIRMÉE (domaine : paquet ActualSameZeroReturnContext W (établi par actualSameZeroReturnContext_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.ActualSameZeroReturnContext.grammaticalReturn` | Sous le contexte, le retour grammatical (produit = 1) tient. | CONFIRMÉE (domaine : paquet ActualSameZeroReturnContext W (établi par actualSameZeroReturnContext_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.ActualSameZeroReturnContext.sameRadialDefect` | Sous le contexte, le défaut radial est celui du zéro (β−1/2). | CONFIRMÉE (domaine : paquet ActualSameZeroReturnContext W (établi par actualSameZeroReturnContext_holds)) | V102 | 0 |
| `SemanticTransportClosure20260821.ActualSameZeroReturnContext.genuineRatio` | Sous le contexte, le rapport du bloc est > 1. | CONFIRMÉE (domaine : paquet ActualSameZeroReturnContext W (établi par actualSameZeroReturnContext_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.actualSameZeroReturnContext_holds` | Le contexte sémantique R10 est habité pour tout cas soudé hors ligne réel, sans nouvelle hypothèse. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.ActualPartneredTransport`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.actualPartneredRatio_one_lt` | Le rapport du transport partenarié réel est un vrai rapport d'histoire première (> 1). | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.actualPartneredDefect_eq_zeroRadial` | Le défaut du partenariat est littéralement la coordonnée radiale du zéro vrai porté. | CONFIRMÉE | V102 | 1 |
| `SemanticTransportClosure20260821.actualPartnered_direct_eq_operator` | L'entrée radiale directe est exactement l'entrée (0,1) de l'opérateur normalisé réel. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.actualPartnered_reflected_eq_operator` | L'entrée radiale réfléchie est exactement l'entrée (1,0) du même opérateur. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.actualPartnered_mirrorReversal` | Le renversement grammatical de la lecture radiale réelle est la réflexion du défaut d ↦ −d. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.actualPartnered_radialReturn` | Le retour radial réciproque (produit des deux lectures = 1) est un théorème sur le même cas. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.actualPartnered_everyStageReturns` | Le retour réciproque persiste à chaque étage harmonique. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.actualPartnered_reversalInvolutive` | Le renversement est involutif sur le transport radial partenarié réel. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.actualAssembly_grammarComposition` | La fenêtre d'assemblage à deux transitions a la loi de composition de grammaire première standard. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.actualAssemblyReturn_iff_pivotSignWord` | Le témoin de retour d'assemblage ⟺ le mot de signes de pivot (−1,+1,−1) de l'histoire première réelle. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.actualAssemblyReturn_product_eq_one` | Quand l'histoire première fournit le témoin alternant, l'holonomie grammaticale de la fenêtre d'assemblage vaut 1. | CONFIRMÉE SOUS CONDITION (témoin de retour d'assemblage réel (ActualAssemblyReturn, mot de signes de pivot)) | AJOUT | 1 |
| `SemanticTransportClosure20260821.actualPartneredNaturality_iff_critical` | Sur le porteur partenarié réel, la naturalité de renversement ⟺ β=1/2 du même zéro vrai. | CONFIRMÉE | V140 | 1 |
| `SemanticTransportClosure20260821.actualPartneredNaturality_fails_offLine` | Un cas soudé explicitement hors ligne ne peut déjà satisfaire la naturalité : évite une clôture accidentelle. | RÉFUTATION COMPILÉE (coïncidence de branche miroir / naturalité (lecture terminale) sur un cas hors ligne) | V140 | 0 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.trueMember` | Sous les rigidités partenariées prouvées, le zéro de la soudure est un vrai zéro non trivial. | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigidities W (rigidités déjà prouvées)) | V6 | 0 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.mirrorTrueMember` | Le miroir du partenariat est un vrai zéro non trivial. | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigidities W (rigidités déjà prouvées)) | V63 | 0 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.sameHeight` | Le miroir a la même hauteur. | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigidities W (rigidités déjà prouvées)) | V65 | 0 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.orderedTrouble` | L'écart ordonné du trouble est some 0. | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigidities W (rigidités déjà prouvées)) | V162 | 0 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.samePrimeGrammar` | Le côté premier du partenariat est la grammaire première du bloc actif de la jonction. | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigidities W (rigidités déjà prouvées)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.assemblyStartsOnPairColumn` | Le bloc du partenariat et celui d'assemblage commencent au même point. | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigidities W (rigidités déjà prouvées)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.assemblyComposition` | La composition d'assemblage est sigma(début)·sigma(fin). | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigidities W (rigidités déjà prouvées)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.pivotPrime` | Le pivot est un vrai premier. | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigidities W (rigidités déjà prouvées)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.pivotBetween` | Le pivot est strictement entre les bornes. | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigidities W (rigidités déjà prouvées)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.radialReadout` | Les entrées radiales directe et réfléchie sont les entrées (0,1) et (1,0) de l'opérateur. | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigidities W (rigidités déjà prouvées)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.mirrorReversal` | Le renversement de la lecture radiale est la réflexion du défaut. | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigidities W (rigidités déjà prouvées)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.radialReturn` | Le retour radial est de produit 1. | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigidities W (rigidités déjà prouvées)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.stagePersistence` | La persistance par étage du retour radial tient. | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigidities W (rigidités déjà prouvées)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.reversalInvolutive` | Le renversement est involutif sur le transport radial partenarié. | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigidities W (rigidités déjà prouvées)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.provedActualPartneredRigidities_holds` | Le paquet de rigidités partenariées prouvées est habité pour tout cas soudé hors ligne réel. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigiditiesWithReturn.base` | Le paquet renforcé avec retour contient le paquet de rigidités prouvées. | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigiditiesWithReturn W) | AJOUT | 0 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigiditiesWithReturn.actualReturn` | Le paquet renforcé fournit le témoin de retour d'assemblage réel. | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigiditiesWithReturn W) | AJOUT | 0 |
| `SemanticTransportClosure20260821.ProvedActualPartneredRigiditiesWithReturn.grammaticalReturn` | Le paquet renforcé donne l'holonomie grammaticale de l'assemblage = 1. | CONFIRMÉE (domaine : paquet ProvedActualPartneredRigiditiesWithReturn W) | AJOUT | 0 |
| `SemanticTransportClosure20260821.provedActualPartneredRigiditiesWithReturn_of_actualReturn` | Construction du paquet renforcé à partir d'un témoin de retour réel fourni indépendamment. | CONFIRMÉE SOUS CONDITION (témoin de retour réel fourni (prémisse nommée ActualAssemblyReturn)) | AJOUT | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.CompleteDiscoverySemanticSpine`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.CompleteOfflineDiscoveryBundle.zero_mem` | Champ de CompleteOfflineDiscoveryBundle : le zéro est dans les représentants positifs. | CONFIRMÉE | AJOUT | 8 |
| `SemanticTransportClosure20260821.CompleteOfflineDiscoveryBundle.offLine` | Champ : le zéro est hors ligne. | CONFIRMÉE | AJOUT | 14 |
| `SemanticTransportClosure20260821.CompleteOfflineDiscoveryBundle.relational` | Champ : le paquet de rigidité relationnelle (grammaire zéros intrinsèque, identité de ligne individuelle, récupération M^Z=M globale). | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.CompleteOfflineDiscoveryBundle.reflectedDifferenceEventuallyStrict` | Champ AV : la différence de Perron réfléchie exacte est strictement croissante à partir d'un rang N sur les colonnes premières consécutives. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.CompleteOfflineDiscoveryBundle.changeFamilyDefect` | Champ AV : une colonne de famille de changement 2/4 réelle porte un défaut de ligne non nul (grammarVoiceStep zéro ≠ miroir). | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.CompleteOfflineDiscoveryBundle.earlyDisturbance` | Champ AW : le même témoin de famille de changement survit à toutes les vues sans perte étiquette/famille/motif. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.CompleteOfflineDiscoveryBundle.reflectedFloorPositive` | Champ BG : le défaut de Perron réfléchi en forme fermée a un plancher canonique strictement positif. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.CompleteOfflineDiscoveryBundle.reflectedFloorAtEveryPrime` | Le plancher positif contrôle la différence réfléchie exacte à chaque colonne première. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.CompleteOfflineDiscoveryBundle.commonOrientedSingularDatum` | Champ : la réflexion préserve la donnée de Laurent singulière orientée du zéro. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.CompleteOfflineDiscoveryBundle.commonOrientedSingularDatum_ne_zero` | Champ : cette donnée de Laurent orientée est non nulle. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.CompleteOfflineDiscoveryBundle.directPerronCarrierWeld` | Champ : le rapport de Perron centré base gauche/base droite est l'holonomie de porteur directe. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.CompleteOfflineDiscoveryBundle.reflectedPerronCarrierWeld` | Champ : le miroir a la même soudure exacte vers son porteur réfléchi. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.CompleteOfflineDiscoveryBundle.reflectedPivotRelation` | Champ : le retour à deux arêtes réel est tau51 puis tau15 et la réflexion agit incidence par incidence par conjugaison réciproque. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.completeOfflineDiscoveryBundle_exists` | Tout vrai zéro positif hors ligne porte toute la colonne vertébrale de découverte assemblée. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | AJOUT | 1 |
| `SemanticTransportClosure20260821.CompleteOfflineDiscoveryBundle.eventual_change_columns_are_defective` | Forme extraite forte : toute colonne 2/4 suffisamment grande est défectueuse (lignes zéro/miroir différentes). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.DefectAnchoredReturnContext`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.exists_prime_index_gt_with_residue_mod_six` | Forme locale publique de la récurrence de Dirichlet : pour toute classe de résidu unitaire mod 6 il existe des indices premiers de cette classe au-delà de tout N. | CONFIRMÉE (domaine : a unité mod 6) | AJOUT | 1 |
| `SemanticTransportClosure20260821.exists_later_same_prime_residue` | À partir de tout état premier n ≥ 2, on peut revenir plus tard au même résidu mod 6. | CONFIRMÉE (domaine : n ≥ 2) | AJOUT | 2 |
| `SemanticTransportClosure20260821.sigma_eq_of_prime_residue_eq` | Deux premiers de même résidu mod 6 ont le même signe de grammaire. | CONFIRMÉE | V174 | 3 |
| `SemanticTransportClosure20260821.DefectAnchoredReturnData.start_ge_two` | Champ de DefectAnchoredReturnData : le départ est ≥ 2. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.DefectAnchoredReturnData.two_edges` | Champ : au moins deux arêtes (départ+1 < fin). | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.DefectAnchoredReturnData.changeFamily` | Champ : l'écart au départ est de classe 2 ou 4 mod 6. | CONFIRMÉE | V174 | 0 |
| `SemanticTransportClosure20260821.DefectAnchoredReturnData.grammarWeight_ne_zero` | Champ : le poids de grammaire au départ est non nul. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.DefectAnchoredReturnData.firstEdgeDefect` | Champ : la première arête porte le défaut de ligne de la paire. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.DefectAnchoredReturnData.endpointPrimeResidue` | Champ : le premier de fin a même résidu mod 6 que celui de départ. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.DefectAnchoredReturnData.block_start` | Le bloc commence au départ. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.DefectAnchoredReturnData.block_end` | Le bloc finit à la fin. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.DefectAnchoredReturnData.endpointSigma_eq` | Les extrémités sont dans le même état primitif de grammaire (même signe). | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.DefectAnchoredReturnData.grammaticalReturn` | Retour grammatical exact sur le même bloc dont la première arête porte le défaut de la paire vraie. | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.DefectAnchoredReturnData.firstEdgeDefect_on_block` | Le défaut de la paire est littéralement la première arête de ce bloc de retour. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.DefectAnchoredReturnData.prefixSteps_separate` | La lecture de préfixes ordonnés H3 voit le même défaut dès qu'un témoin de paire miroir ordonnée est donné. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.DefectAnchoredReturnData.directPerronCarrierWeld` | Provenance Perron→porteur sur le même bloc de retour ancré au défaut, membre direct. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.DefectAnchoredReturnData.reflectedPerronCarrierWeld` | Provenance Perron→porteur sur les mêmes extrémités, membre réfléchi. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.DefectAnchoredReturnData.blockOperator_radial` | Le transport sélectionné sur ce bloc est exactement radial (défaut β−1/2) après retrait de la phase de hauteur commune. | CONFIRMÉE | V102 | 1 |
| `SemanticTransportClosure20260821.DefectAnchoredReturnData.offLine_transport_does_not_return` | Hors ligne, le retour grammatical réel n'est pas un retour du transport relevé du membre (normes du porteur en fin et au début différentes). | CONFIRMÉE SOUS CONDITION (zéro hors ligne (β ≠ 1/2)) | AJOUT | 2 |
| `SemanticTransportClosure20260821.defectAnchoredReturnData_exists` | Tout zéro positif supposé hors ligne produit un bloc de retour réel commençant exactement sur une colonne de changement 2/4 réelle. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | AJOUT | 2 |
| `SemanticTransportClosure20260821.DefectAnchoredSameObjectContext.zero_mem` | Champ de DefectAnchoredSameObjectContext : ρ est dans les représentants positifs. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.DefectAnchoredSameObjectContext.offLine` | Champ : ρ est hors ligne. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.defectAnchoredSameObjectContext_exists` | Construction du contexte réparé depuis le seul vrai zéro positif et l'hypothèse hors ligne. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | AJOUT | 0 |
| `SemanticTransportClosure20260821.DefectAnchoredSameObjectContext.prefixDefect_and_return` | H3 (préfixes ordonnés) et le retour grammatical vivent sur le même intervalle premier réel. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.DefectAnchoredSameObjectContext.finite_return_and_nonreturning_lift` | Frontière d'implémentation : hors ligne, le même intervalle a un retour grammatical fini fermé et un relevé du membre qui ne retourne pas. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.trueZero_and_offLine` | Le paquet exhaustif concerne un vrai zéro non trivial hors ligne unique. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.orderedPrefixDefect_and_sameBlockReturn` | H3 et le retour grammatical réel sont alignés sur le même bloc sélectionné. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.sameBlockPerronCarrierWelds` | Les rapports de Perron direct et réfléchi sont réalisés sur le même bloc de retour ancré au défaut. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.sameBlockRadialOperator` | Réalisation radiale exacte de l'opérateur transformé sélectionné sur ce bloc. | CONFIRMÉE | V102 | 0 |
| `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.sameBlockLiftDoesNotReturn` | Le même retour grammatical n'efface pas la déformation radiale hors ligne (norme fin ≠ norme début). | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.nprime_half_pos` | Le compteur analytique existant de la moitié droite est strictement positif pour le même cas hors ligne. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.weightedRightHalfDefect_pos` | Le défaut radial pondéré de la moitié droite est strictement positif. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.paddedRectangle_exists` | Un rectangle de moitié droite rembourré existe autour de la hauteur (la coupure d'un représentant positif est positive). (terme hors maître « rectangle » : rectangle de Perron [σL(N),σR]×[−T,T] ; « admissible » = aucun pôle sur son bord) | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.rectangleArgumentIdentity` | Identité du principe de l'argument exacte : intégrale de −ζ'/ζ sur le rectangle = −N'(1/2,T), sans annulation de bord supposée. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.weightedRectangleIdentity` | Identité pondérée exacte : −Re(intégrale pondérée) = somme des β−1/2 sur les zéros de ]1/2,1[×]0,T[. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.weightedRectangleRealPart_ne_zero` | L'intégrale pondérée du rectangle ne peut avoir de partie réelle nulle dans un contexte hors ligne. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.partnership_zero` | Champ : le partenariat porte le zéro de la découverte. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.partnership_block` | Champ : le bloc du partenariat est le bloc de retour ancré au défaut. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.not_internalNaturality` | Hors ligne, la naturalité interne correctement typée est fausse sur le même bloc sélectionné. | RÉFUTATION COMPILÉE (naturalité interne de renversement (ActualGrammarReversalNaturality) dans le contexte hors ligne exhaustif) | V140 | 0 |
| `SemanticTransportClosure20260821.exhaustiveSameObjectOfflineContext_exists` | Tout vrai zéro positif hors ligne engendre le contexte exhaustif même-objet avec les seules conséquences déjà prouvées. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | AJOUT | 1 |

### `RhGapCriterion.SemanticTransportClosure20260821.FinalConditionalFirstReturnClosure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.finalObject_zero` | L'objet final est littéralement le partenariat localisé stocké dans X (même zéro). | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.finalObject_block` | L'objet final utilise le même bloc de premier retour. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.finalObject_primeSide_eq_M` | La même capture complète lit la grammaire première canonique M. | CONFIRMÉE | V48 | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.finalObject_primeSide_eq_MZ` | La même capture lit simultanément la grammaire reconstruite depuis les zéros M^Z. | CONFIRMÉE | V48 | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.finalObject_zero_mem_capture` | Le vrai membre est présent dans la capture zéros complète de l'objet final. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.finalObject_mirror_mem_capture` | Son vrai miroir est présent dans la même capture zéros. | CONFIRMÉE | V63 | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.finalObject_directCarrier` | La branche directe est le porteur canonique du membre du partenariat. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.finalObject_reflectedCarrier` | La branche réfléchie est le porteur canonique du miroir du même défaut. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.finalObject_directFiber` | La lecture radiale directe appartient à la fibre de hauteur commune du partenariat. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.finalObject_reflectedFiber` | La lecture radiale réfléchie appartient à la même fibre de hauteur, à la position réfléchie. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.finalObject_grammaticalReturn` | Le bloc sélectionné de l'objet final est un retour grammatical exact (produit = 1). | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.finalObject_offLine_memberDoesNotReturn` | La conséquence hors ligne reste attachée au même membre et au même retour : normes fin ≠ début du porteur vrai. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.finalObject_sameObject_certificate` | Certificat d'objet identique : zéro, bloc, côté premier égal à M et autres identités du noyau, sans hypothèse. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.positive_offLine_zero_gives_fullyAligned_case` | Un vrai zéro hors ligne de hauteur positive produit le contexte pleinement aligné contenant le partenariat localisé même-objet. | CONFIRMÉE SOUS CONDITION (zéro de hauteur > 0 hors ligne) | AJOUT | 2 |
| `SemanticTransportClosure20260821.negative_offLine_zero_gives_fullyAligned_case` | Un vrai zéro hors ligne de hauteur négative est ramené par conjugaison (même β) et produit aussi un contexte pleinement aligné. | CONFIRMÉE SOUS CONDITION (zéro de hauteur < 0 hors ligne) | V63 | 1 |
| `SemanticTransportClosure20260821.offLine_zero_gives_fullyAligned_case` | Tout vrai zéro non trivial hors ligne produit un contexte pleinement aligné contenant le partenariat final même-objet. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | AJOUT | 3 |

### `RhGapCriterion.SemanticTransportClosure20260821.FiniteGrammar`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.flipState_involutive` | Le retournement d'état de grammaire est involutif. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.grammarSign_flip` | Le signe de grammaire d'un état retourné est l'opposé. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.reverseTransition_involutive` | Le renversement d'une transition de grammaire est involutif. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.transitionOf_flipped` | Retourner les deux états d'extrémité renverse la transition. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.ReturnBlock.returnLaw` | Champ de ReturnBlock : la sortie égale l'entrée (loi de retour). | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.splitReturn_incoming` | Dans le bloc de retour scindé canonique, la transition entrante entry→pivot est minusToPlus. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.splitReturn_outgoing` | La transition sortante pivot→exit est plusToMinus. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.splitReturn_orientations_reverse` | Les deux orientations de changement du retour canonique sont exactement inverses l'une de l'autre. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.oddStageSupport_minus` | L'état « moins » n'a pas de support d'étage impair. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.oddStageSupport_plus` | L'état « plus » a un support d'étage impair. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.evenStageSupport_all` | Tout état de grammaire a un support d'étage pair. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.oddStageSupport_faithful` | Le support impair est fidèle à la grammaire à deux états : mêmes valeurs de vérité du support impair ⟹ mêmes états. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.splitReturn_odd_support_pattern` | Le retour canonique a le motif de support (faux, vrai, faux) aux étages impairs. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.splitReturn_even_support_pattern` | Le même retour a un support universel aux étages pairs. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.GrammarState.ofNat_ctorIdx` | ofNat ∘ ctorIdx est l'identité sur GrammarState. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.GrammarTransition.ofNat_ctorIdx` | ofNat ∘ ctorIdx est l'identité sur GrammarTransition. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.ReturnBlock.mk.congr_simp` | Lemme de congruence auto-généré pour la structure ReturnBlock (champs égaux ⟹ blocs égaux). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.FullyAlignedContactBetaWeld`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_positiveHeight` | Le membre pleinement aligné est dans la branche de hauteur positive. | CONFIRMÉE | V7 | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_beta_ne_zero` | La partie réelle d'un vrai zéro non trivial est non nulle : l'inversion tangente est admissible. | CONFIRMÉE | V7 | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_gamma_ne_zero` | La hauteur d'un vrai zéro non trivial est non nulle. | CONFIRMÉE | V7 | 4 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_beta_eq_gamma_div_tan_contact` | Récupération exacte de β depuis un contact tangent vrai : β = γ / tan(γ log contact). | CONFIRMÉE | V45 | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_gamma_recovered_from_contact_pair` | Récupération exacte de γ depuis deux contacts vrais et un étage positif. | CONFIRMÉE (domaine : étage m ≥ 1) | V45 | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_contact_pair_satisfies_corrected_E44` | La paire de contacts vrais satisfait la loi E44 corrigée à tous étages pour le même β. | CONFIRMÉE (domaine : étage m ≥ 1) | V45 | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_beta_recovered_from_contact_pair` | Récupération exacte de β depuis les deux mêmes contacts et le même étage. | CONFIRMÉE (domaine : étage m ≥ 1) | V45 | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_contact_pair_recovers_beta_gamma` | La même paire de contacts récupère simultanément β et γ du même membre. | CONFIRMÉE (domaine : étage m ≥ 1) | V45 | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_betaDefect_eq_contactLog` | Le défaut radial β−1/2 est une reparamétrisation exacte par le log du rapport de contact : (γ/π)·log(contactRatio). | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.blockOperator_eq_contactLogRadial` | L'opérateur radial du bloc de premier retour s'écrit directement dans la coordonnée de contact tangent. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_offLine_contact_ne_mirror` | Sur le même membre hors ligne et son miroir de même hauteur, les contacts tangents au même indice diffèrent. | CONFIRMÉE | V163 | 3 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_contact_to_prime_cocycle` | Le passage contact→premier est le cocycle exact du même zéro (ne prétend pas que le contact soit un premier). | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_firstPrimeEdgeContribution` | La contribution individuelle du même zéro sur la première arête du bloc aligné est la différence de ses termes résiduels en p(start+1) et p(start). | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameBlock_primeGrammar_eq_zeroReconstructedGrammar` | M^Z = M sur le bloc de premier retour exact (grammaire algébrique première distincte de l'entrée sensible au membre). | CONFIRMÉE | V48 | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_contactRatio_eq_one_iff_reflectedPairEnergy_zero` | Le rapport de contact vaut 1 ⟺ l'énergie de paire réfléchie est nulle : deux coordonnées de détecteur exactes du même zéro. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.offLine_primeGrammar_contactTower_fracture` | Fracture scientifique même-objet hors ligne : sur le même zéro hors ligne et le même bloc, la grammaire première égale la reconstruction, tandis que la Tour de contacts voit la séparation du miroir. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.samePartnership_primeVonMangoldt_contactTower_spine` | Épine scientifique de composition sur l'unique X.partnership : conjonction de faits déjà certifiés (même zéro, miroir, bloc, capture, contacts, cocycle). | CONFIRMÉE (domaine : étage m ≥ 1) | AJOUT | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.FullyAlignedFirstReturnCurlFourPoint`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `sourceRowDifference_reflect_eq_reflectedDifference_step` | Une différence de lignes source zéro/miroir est exactement la dérivée discrète par pas premier de la différence de Perron réfléchie. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.firstReturnTotalCurl_eq_reflectedDifference_fourPoint` | Le curl total du premier retour est une expression exacte à quatre points de la différence de Perron réfléchie. | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.grammarVoiceRow_difference_eq_weight_mul_reflectedDifference_fourPoint` | La discordance de voix de grammaire zéro/miroir est le poids fois la forme à quatre points de la différence de Perron réfléchie. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.FullyAlignedFirstReturnCurlPerronClosedForm`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `reflectedResidueDifference_eq_coeff_mul_cpow` | Formule complexe exacte de la différence de Perron réfléchie en tout sommet : coefficients × x^ρ moins coefficient miroir × x^(miroir). | CONFIRMÉE | AJOUT | 1 |
| `nontrivialZeroResidueTerm_edge_factorization` | L'arête de Perron complexe exacte se factorise par le rapport b/a. | CONFIRMÉE (domaine : 0 < a < b) | AJOUT | 2 |
| `mirrorResidueTerm_edge_factorization` | Même factorisation d'arête pour la ligne du miroir fonctionnel. | CONFIRMÉE (domaine : 0 < a < b) | AJOUT | 1 |
| `reflectedResidueDifference_edge_factorization` | Factorisation exacte d'une arête de différence réfléchie en deux facteurs sensibles à la ligne. | CONFIRMÉE (domaine : 0 < a < b) | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.primeScale_pos` | Toute échelle première p n est > 0. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.primeScale_step_lt` | p n < p (n+1). | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.firstReturnTotalCurl_eq_perron_complex_closedForm` | Substitution complexe complète à quatre sommets du curl du premier retour (C9-C). | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.firstReturnTotalCurl_eq_endpoint_ratio_factorization` | Les deux incréments d'extrémité se factorisent indépendamment par les rapports du premier et du dernier premier (C9-D). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.FullyAlignedFirstReturnGrammarSupport`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.last_succ_eq_finish` | Le prédécesseur de finish se termine exactement en finish (last+1 = finish). | CONFIRMÉE | AJOUT | 4 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.interiorPrimeResidues_eq` | Deux états premiers strictement intérieurs du premier retour ont même résidu mod 6. | CONFIRMÉE (domaine : indices strictement à l'intérieur du retour) | AJOUT | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.interiorPrimeEdge_same_residue` | Toute arête entre les deux arêtes de changement d'extrémité est une arête de maintien. | CONFIRMÉE (domaine : arête strictement intérieure) | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.interiorGrammarWeight_zero` | Toute arête strictement intérieure a un poids canonique de grammaire nul. | CONFIRMÉE (domaine : arête strictement intérieure) | AJOUT | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.firstInteriorResidue_eq_last` | L'état après le premier changement égale l'état avant la dernière arête de retour. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.endpointGrammarWeights_opposite` | Les poids de grammaire de la première et de la dernière arête du bloc sont opposés. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.firstReturnGrammarSupport` | Support complet de la grammaire du premier retour : poids d'extrémité non nuls et opposés, poids intérieurs nuls. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.grammarWeight_start_offset` | Formes relative et absolue du poids de grammaire canonique coïncident sur le bloc aligné. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.mixedCurl_sum_telescope` | Le curl mixte télescope algébriquement sur toute série finie de colonnes (H11), sans supposer la nullité. | CONFIRMÉE | AJOUT | 1 |

### `RhGapCriterion.SemanticTransportClosure20260821.FullyAlignedGlobalDefectWeld`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.identifiedRightHalf_re_sub_half_eq_abs_radial` | Le représentant de moitié droite identifié porte exactement le défaut radial absolu ∣β−1/2∣ de la paire miroir d'origine. | CONFIRMÉE | V102 | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.rightHalfFiniteSummand_nonneg` | Chaque terme du défaut radial de la moitié droite stricte est ≥ 0. | CONFIRMÉE (domaine : ρ dans le support fini de la moitié droite stricte) | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.identifiedRightHalf_mem_finset` | Le membre identifié apparaît dans le support fini du défaut global. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.absRadial_mul_order_le_globalRightHalfDefect` | Soudure même-membre S4→S9 : le défaut de moitié droite global est au moins la contribution du représentant identifié. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.identifiedRadialContribution_pos` | Le terme borne inférieure est strictement positif sous la seule hypothèse hors ligne. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.samePairForcesGlobalRightHalfDefect_pos` | La même paire force la positivité du défaut global de moitié droite (désormais sourcée par la paire). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.FullyAlignedIntegerLiftWeld`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.mem_alignedPositiveZeroFinset` | Appartenance à l'ensemble aligné positif ⟺ ∣γ∣ < T et γ > 0. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.mem_alignedLeftZeroFinset` | Appartenance à l'ensemble aligné gauche ⟺ ∣γ∣ < T, γ > 0, β < 1/2. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.mem_alignedLineZeroFinset` | Appartenance à l'ensemble aligné ligne ⟺ ∣γ∣ < T, γ > 0, β = 1/2. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.mem_alignedRightZeroFinset` | Appartenance à l'ensemble aligné droite ⟺ ∣γ∣ < T, γ > 0, β > 1/2. | CONFIRMÉE | AJOUT | 4 |
| `SemanticTransportClosure20260821.alignedTotalMultiplicityNat_eq_left_add_line_add_right` | Le total de multiplicité à hauteur positive est la trichotomie disjointe gauche / ligne / droite comptée avec multiplicité. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.alignedLeftZeroFinset_image_reflect_eq_right` | La réflexion-conjuguée envoie bijectivement le support gauche positif réel sur le support droit positif réel. | CONFIRMÉE | V62 | 1 |
| `SemanticTransportClosure20260821.alignedLeftMultiplicityNat_eq_right` | Gauche et droite ont exactement la même multiplicité totale (la réflexion est injective et conserve la multiplicité analytique). | CONFIRMÉE | V63 | 1 |
| `SemanticTransportClosure20260821.alignedTotalMultiplicityNat_eq_line_add_two_right` | Identité de comptage exacte S9 : total = ligne + 2 × droite (multiplicité positive réelle). | CONFIRMÉE | V63 | 2 |
| `SemanticTransportClosure20260821.alignedRightZeroFinset_coe_image_eq_rightHalf` | L'image par coercition du support droit aligné est le finset de rectangle de moitié droite existant. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.alignedRightMultiplicityNat_eq_rightHalfMultiplicityNat` | La multiplicité droite W est le wrapper naturel de N'(1/2,T). | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.alignedRightMultiplicityNat_cast_eq_nprime_half` | Pont de casting réel vers le compteur analytique N'(1/2,T). | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.alignedTotalCountInt_sub_line_eq_two_W` | Forme entière de N−N0 = 2W sur les supports définis par zêta. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.alignedDiscreteArgumentLift_gap_eq_two_W` | Le relevé d'argument discret abstrait CH a maintenant une instanciation zêta même-objet : écart total−ligne = 2W. | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.alignedOffLinePairCount_pos` | La même paire hors ligne rend le compteur W actuel strictement positif. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.one_le_alignedOffLinePairCountInt` | Le compte entier de paires hors ligne est au moins 1. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameObjectDiscreteArgumentLift_gap_ge_two` | S9 entièrement même-objet : pour tout indice de cellule de phase n, l'écart relevé total/ligne est ≥ 2. | CONFIRMÉE | AJOUT | 1 |

### `RhGapCriterion.SemanticTransportClosure20260821.FullyAlignedIntegratedFirstReturnCurl`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.firstReturnLength_ge_two` | La longueur du premier retour est ≥ 2. | CONFIRMÉE | AJOUT | 4 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.firstReturnLength_pos` | La longueur du premier retour est > 0. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.firstReturnLastOffset_pos` | Le décalage de la dernière arête est > 0. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.firstReturnLastOffset_lt_length` | Le décalage de la dernière arête est < longueur. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.start_add_firstReturnLastOffset_eq_last` | start + décalage = last (indice absolu de l'arête finale). | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.relativeInteriorGrammarWeight_zero` | Forme relative du théorème de support : tout décalage strictement entre la première et la dernière arête a un poids de grammaire nul. | CONFIRMÉE (domaine : 0 < k < offset de la dernière arête) | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.relativeEndpointGrammarWeights_opposite` | Le poids relatif de la dernière arête est l'opposé de celui de la première. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.grammarVoiceRow_difference_eq_weighted_rowDifference_sum` | Pont algébrique générique : la différence des deux rangées de voix de grammaire est la somme pondérée des différences de lignes sensibles à la source. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.weighted_rowDifference_sum_firstReturn_eq_endpoints` | Sur le premier retour exact, tous les termes intérieurs s'annulent et seuls les deux poids d'extrémité opposés survivent dans la somme pondérée des différences de lignes. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.grammarVoiceRow_difference_firstReturn_eq_endpointDifference` | C7-B : la différence des deux rangées de voix de grammaire se réduit à la différence de lignes sensibles à la source aux deux extrémités. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.firstReturnTotalCurl_eq_endpointDifference` | C7-C : le curl total du premier retour est la différence de lignes de la première arête moins celle de la dernière (H11 télescopé). | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.grammarVoiceRow_difference_eq_weight_mul_firstReturnTotalCurl` | Composition C7 d'ordre 2 : la discordance des rangées de voix égale le poids de la première arête fois le curl total du premier retour. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.grammarVoiceRow_difference_eq_zero_iff_firstReturnTotalCurl_eq_zero` | La discordance des rangées de voix est nulle ⟺ le curl total du premier retour est nul (le poids de la première arête étant non nul). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.FullyAlignedLiftRectangleBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.alignedDiscreteArgumentLift_gap_eq_neg_two_rectangle_re` | Soudure S13-S14 exacte : l'écart de relevé discret entier égale −2 fois la partie réelle de l'intégrale de rectangle de moitié droite (argument principe). | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.liftRectangleBridge_ge_two` | Dans le cas hors ligne réel, le même pont s'accompagne de la borne entière inférieure déjà prouvée : −2·Re(intégrale de rectangle) ≥ 2. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.FullyAlignedMetricInertiaReadout`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SelectedPrimeBlock.ratio_rpow_lt_rpow_iff` | Monotonie stricte des puissances réelles pour le rapport du bloc sélectionné. | CONFIRMÉE | AJOUT | 1 |
| `blockRadialMetricDefect_eq` | Forme fermée : le défaut métrique radial est diagonal et lit les deux distorsions radiales réciproques. | CONFIRMÉE | AJOUT | 2 |
| `blockRadialMetricDefect_zero_zero_re` | L'entrée (0,0) du défaut métrique radial vaut ratio^(2d)−1. | CONFIRMÉE | AJOUT | 1 |
| `blockRadialMetricDefect_one_one_re` | L'entrée (1,1) du défaut métrique radial vaut ratio^(−2d)−1. | CONFIRMÉE | AJOUT | 1 |
| `blockRadialMetricDefect_oppositeSigns` | Lecture métrique hyperbolique : un défaut radial non nul force des signes opposés aux deux coordonnées diagonales de TᴴT−I. | CONFIRMÉE (domaine : défaut radial d ≠ 0) | V102 | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.radialDefect_ne_zero` | Le défaut radial β−1/2 du zéro d'un contexte pleinement aligné (hors ligne) est non nul. | CONFIRMÉE | V102 | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.blockMetricDefect_oppositeSigns` | Lecture d'inertie même-événement : les deux coordonnées diagonales du défaut métrique du bloc de premier retour sont de signes opposés. | CONFIRMÉE | V102 | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.FullyAlignedQuartetVonMangoldtWeld`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `TrueZeroQuartet.nontrivialZeroChannel_eq_quartet_add_rest` | Décomposition absolument convergente exacte du canal des zéros non triviaux en ce quartet et son complément. | CONFIRMÉE (domaine : x > 1) | V121 | 1 |
| `TrueZeroQuartet.smoothedVonMangoldtSum_eq_fixed_add_trivial_add_quartet_add_rest` | La formule explicite de von Mangoldt lissée avec tous les termes déterministes et le fond des zéros triviaux, en quartet plus reste. | CONFIRMÉE (domaine : x > 1) | V121 | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.trueQuartet_seed` | Le quartet vrai du contexte est semé par le zéro X.zero. | CONFIRMÉE | V63 | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.trueQuartet_sameHeightMirror` | Le miroir de même hauteur du quartet est X.mirror. | CONFIRMÉE | V63 | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_smoothedVonMangoldt_quartet_decomposition` | La comptabilité von Mangoldt spécialisée au quartet complet du même X.zero (aucune substitution d'objet). | CONFIRMÉE (domaine : x > 1) | V121 | 1 |

### `RhGapCriterion.SemanticTransportClosure20260821.FullyAlignedRigidityClosure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.relationalRigidities` | La rigidité relationnelle (AR) et la récupération de grammaire sont attachées à ce même zéro. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.endpointReflectedFloorBounds` | Le plancher positif BG borne les deux arêtes de changement opposées du même premier retour. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.commonOrientedSingularDatum` | La paire réfléchie partage la même donnée singulière de Laurent orientée non nulle. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.commonOrientedSingularDatum_ne_zero` | Cette donnée orientée est non nulle. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.prime_history_determines_same_zero_source` | La détermination premier→zéros est attachée au même partenariat global que la reconstruction zéros→premiers. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.reconstructs_same_prime_block` | Reconstruction zéros→premiers sur le bloc de premier retour exact. | CONFIRMÉE | V48 | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.MZ_eq_M_same_prime_block` | M^Z = M sur le bloc de premier retour exact. | CONFIRMÉE | V48 | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.interiorPrimeResidue_ne_start` | Tout état intérieur du premier retour est l'état primitif opposé à start (résidu mod 6 différent). | CONFIRMÉE (domaine : indices strictement à l'intérieur du retour) | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.interiorSigma_eq_neg_start` | Tout état intérieur strict a le signe de grammaire opposé à celui de start. | CONFIRMÉE (domaine : indices strictement à l'intérieur du retour) | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.oppositeEndpointOrientations` | Le premier retour a exactement deux arêtes de changement orientées opposées : tau15 à un bout et tau51 à l'autre. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.oppositeEndpointDefectPackage` | Les deux orientations d'extrémité restent défectueuses en lignes et visibles par H3. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.fullyAlignedLoadBearingFacts` | Paquet compact des rigidités porteuses alignées sur un événement (théorème de projection). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.FullyAlignedSameEventContext`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.prime_residue_ne_of_change_family` | Une famille d'écart 2/4 est exactement un changement d'état mod 6 de premier primitif. | CONFIRMÉE (domaine : n ≥ 2 et écart de classe 2 ou 4 mod 6) | V174 | 1 |
| `SemanticTransportClosure20260821.exists_change_family_at_or_after` | Au-delà de tout rang N ≥ 2, il existe une arête de famille de changement (cofinalité). | CONFIRMÉE (domaine : rang ≥ 2) | AJOUT | 1 |
| `SemanticTransportClosure20260821.exists_later_same_residue` | Un retour ultérieur au même résidu primitif existe depuis tout état premier réel. | CONFIRMÉE (domaine : rang ≥ 2) | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.defectThreshold_ge_two` | Champ de FullyAlignedSameEventContext : le seuil de défaut est ≥ 2. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.defectTailStrict` | Champ : au-delà du seuil, la différence réfléchie de Perron est strictement croissante d'un premier au suivant. | CONFIRMÉE (domaine : n ≥ seuil de défaut) | AJOUT | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.start_ge_threshold` | Champ : le départ est ≥ seuil de défaut. | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.startChangeFamily` | Champ : l'écart au départ est de famille de changement (2 ou 4 mod 6). | CONFIRMÉE | V174 | 4 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.start_lt_finish` | Champ : le départ est avant la fin. | CONFIRMÉE | AJOUT | 10 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.endpointPrimeResidue` | Champ : le premier de fin a même résidu mod 6 que celui de départ. | CONFIRMÉE | AJOUT | 6 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.firstReturnMinimal` | Champ : minimalité du premier retour (aucun résidu intérieur égal à celui du départ). | CONFIRMÉE (domaine : j strictement à l'intérieur du retour) | AJOUT | 3 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.start_ge_two` | Le départ synchronisé est un vrai rang premier ≥ 2. | CONFIRMÉE | AJOUT | 11 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.startRowDefect` | La première arête synchronisée est sensible à la ligne (défaut zéro/miroir). | CONFIRMÉE | AJOUT | 5 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.startGrammarWeight_ne_zero` | La famille de changement génuine a un poids de grammaire non nul. | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.startGrammarVoiceDefect` | Le même événement synchronisé est visible dans le canal ligne pondéré par la grammaire. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.two_edges` | Le premier retour ne peut être immédiat en start+1 (la première arête est un changement). | CONFIRMÉE | AJOUT | 5 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.start_lt_last` | La dernière arête est après le départ synchronisé. | CONFIRMÉE | AJOUT | 4 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.last_lt_finish` | La dernière arête est avant la fin. | CONFIRMÉE | AJOUT | 4 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.last_ge_threshold` | La dernière arête est au-delà du seuil de défaut. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.last_ge_two` | La dernière arête est ≥ 2. | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.lastPrimeResidue_ne_start` | L'état juste avant la fin est encore l'état opposé (minimalité du retour). | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.lastPrimeResidue_ne_finish` | Comme finish est revenu à l'état de départ, l'arête finale est un vrai changement. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.lastChangeFamily` | La dernière arête du premier retour est la famille de changement 2/4 opposée. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.lastRowDefect` | Le dernier changement opposé est aussi défectueux (ligne zéro/miroir). | CONFIRMÉE | AJOUT | 5 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.lastGrammarWeight_ne_zero` | Son poids de grammaire est non nul. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.lastGrammarVoiceDefect` | Le dernier changement reste sensible à la source dans le canal de grammaire pondéré. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.block_start` | Le bloc commence au départ. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.block_end` | Le bloc finit à la fin. | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.grammaticalReturn` | Retour grammatical exact sur le bloc de premier retour (produit = 1). | CONFIRMÉE | AJOUT | 5 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.endpointRowDefects` | Les deux défauts de paire miroir vraie sont présents sur les deux arêtes de changement opposées d'un retour. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.firstPrefixDefect` | H3 lit sans perte le défaut de la première extrémité dans la liste réelle ordonnée des zéros. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.lastPrefixDefect` | H3 lit le défaut de l'extrémité opposée dans la même paire ordonnée. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.mixedCurlReadout` | H11 est conservé sans hypothèse artificielle de curl nul pour tout décalage lu sur la même paire miroir ordonnée. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.directPerronCarrierWeld` | Perron→porteur sur le bloc de premier retour aligné, membre direct. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.reflectedPerronCarrierWeld` | Perron→porteur sur le même bloc, membre réfléchi. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.blockOperator_radial` | Le même bloc porte exactement le relevé radial du même vrai zéro (défaut β−1/2). | CONFIRMÉE | V102 | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.liftedMemberDoesNotReturn` | Le retour grammatical reste distinct du retour de norme spectrale hors ligne (norme fin ≠ norme début). | CONFIRMÉE | AJOUT | 8 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.partnership_zero` | Le partenariat porte le zéro de X. | CONFIRMÉE | AJOUT | 10 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.partnership_block` | Le partenariat porte le bloc de X. | CONFIRMÉE | AJOUT | 6 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.partnership_zeroStart` | La capture zéros commence en 0. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.partnership_zeroLength` | La longueur de la capture zéros est la longueur de fenêtre complète. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.capture_zero_members_full` | La fenêtre de capture est la liste canonique ordonnée complète des zéros, non une liste vide. | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.zero_mem_capture` | Le membre direct vrai est présent dans la capture zéros du partenariat. | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.mirror_mem_capture` | Le miroir fonctionnel est présent dans la même capture zéros. | CONFIRMÉE | V63 | 3 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.capture_primeSide_eq_M` | Le côté premier reconstruit de la même capture pleine est exactement M canonique. | CONFIRMÉE | V48 | 5 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.capture_primeSide_eq_MZ` | Et exactement la grammaire première reconstruite depuis les zéros M^Z. | CONFIRMÉE | V48 | 5 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.IdentifiedRightHalfRepresentative.isMemberOrMirror` | Champ de IdentifiedRightHalfRepresentative : le représentant est le membre ou son miroir. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.IdentifiedRightHalfRepresentative.memRightHalf` | Champ : le représentant est dans la moitié droite positive. | CONFIRMÉE | AJOUT | 5 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.identifiedRightHalfRepresentative_exists` | La même paire hors ligne fournit un représentant de moitié droite identifié. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.rightHalfWeightedDefect_pos` | Le défaut global pondéré de la moitié droite reste strictement positif, avec l'identité du témoin individuel disponible. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.weightedRectangleRealPart_ne_zero` | La lecture exacte du rectangle de moitié droite est retenue (partie réelle non nulle). | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.not_internalNaturality` | La naturalité interne n'est pas fabriquée : sous l'hypothèse de contradiction elle reste fausse. | RÉFUTATION COMPILÉE (naturalité interne de renversement (ActualGrammarReversalNaturality) dans le contexte aligné hors ligne) | V140 | 0 |
| `SemanticTransportClosure20260821.fullyAlignedSameEventContext_exists` | Tout vrai zéro positif sous la seule hypothèse hors ligne engendre le contexte pleinement aligné. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V62 | 2 |
| `CanonicalLocalizedZeroPrimePartnership.mk.congr_simp` | Lemme de congruence auto-généré pour FullyAlignedSameEventContext (champs égaux ⟹ contextes égaux). | CONFIRMÉE | AJOUT | 0 |
| `DecoupledZeroPrimeCapture.mk.congr_simp` | Lemme de congruence auto-généré pour DecoupledZeroPrimeCapture. | CONFIRMÉE | AJOUT | 0 |
| `canonicalLocalZeroContext.congr_simp` | Lemme de congruence auto-généré pour canonicalLocalZeroContext (ρ = ρ' ⟹ contextes égaux). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.FullyAlignedStrictRightHalfBarycentricBound`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `rightHalf_weighted_defect_lt_half_mul_nprime` | Sur un support de moitié droite stricte non vide, le défaut pondéré est strictement inférieur à la moitié de N'(1/2,T). | CONFIRMÉE (domaine : support de moitié droite stricte non vide) | AJOUT | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.strictRightHalfBarycentricBound` | C8 : le contexte hors ligne même-événement a un support de moitié droite non vide, donc son défaut pondéré est positif et strictement inférieur à N'(1/2,T)/2. | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.identifiedRadialContribution_lt_half_mul_nprime` | Composition C5-C8 : la contribution du membre identifié est strictement sous la moitié du défaut de moitié droite complet. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.four_mul_weightedDefect_lt_discreteArgumentLift_gap` | Composition C1-C8 : quatre fois le défaut pondéré est strictement inférieur à l'écart de relevé discret réel. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.weightedUnweightedRectangleStrictComparison` | Forme rectangle pondéré/non pondéré de C8 sur le même rectangle rembourré : −Re(intégrale pondérée) est positive et strictement sous la moitié de −Re(intégrale non pondérée). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.KnownRigidityCountermodel`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.knownReturnRigidities_hold` | Toutes les rigidités de retour/covariance connues tiennent pour tout défaut d. | CONFIRMÉE (domaine : R > 0) | AJOUT | 2 |
| `SemanticTransportClosure20260821.knownRigidities_admit_nonzero_defect` | Contre-modèle hors critique explicite : à d=1 toutes les rigidités de retour connues tiennent, d ≠ 0, et la naturalité par renversement échoue. | CONFIRMÉE (domaine : R > 1) | V140 | 1 |
| `SemanticTransportClosure20260821.knownReturnRigidities_do_not_force_naturality` | L'implication des rigidités de retour déjà connues vers la naturalité par renversement est fausse. | RÉFUTATION COMPILÉE (implication « rigidités de retour connues ⟹ naturalité par renversement » (condition R > 1)) | V140 | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.MasterSemanticCase`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.localizedRadialTransport_direct_eq_operator` | La lecture radiale directe est exactement l'entrée directe de l'opérateur réel normalisé. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.localizedRadialTransport_reflected_eq_operator` | La lecture radiale réfléchie est exactement l'entrée réfléchie du même opérateur. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.localizedRadialTransport_mirrorReversal` | Covariance R11 : le renversement échange les deux lectures radiales et envoie d sur −d. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.localizedRadialTransport_returnProduct` | Retour réciproque de la paire radiale sur le même bloc réel (produit = 1). | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.localizedRadialTransport_everyStageReturns` | Le retour réciproque persiste à chaque étage harmonique. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.zero_mem` | Champ de MasterOffLineSemanticCase : le zéro est dans les représentants positifs. | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.offLine` | Champ : le zéro est hors ligne. | CONFIRMÉE | AJOUT | 9 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.partnership_zero` | Champ : le partenariat porte le zéro. | CONFIRMÉE | AJOUT | 4 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.partnership_block` | Champ : le bloc du partenariat est terminalPrimeBlock ([2,4)). | CONFIRMÉE | AJOUT | 5 |
| `SemanticTransportClosure20260821.masterOffLineSemanticCase_exists` | Tout vrai zéro positif supposé hors ligne donne le cas maître ; aucune propriété terminale n'est supposée. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V62 | 1 |
| `SemanticTransportClosure20260821.masterOffLineSemanticCase_exists_same_zero` | Même constructeur en retenant l'identité du zéro dans le type du résultat. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V62 | 1 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1_trueZero` | R1 : le membre est un vrai zéro non trivial de zêta. | CONFIRMÉE | V6 | 1 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R2_trueMirror` | R2 : le miroir fonctionnel exact est aussi un vrai zéro non trivial. | CONFIRMÉE | V63 | 1 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R3_sameHeight` | R3 : la paire choisie a la même hauteur. | CONFIRMÉE | V65 | 1 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.exactOrderedRows_distinct` | Hors ligne, les deux lignes exactes (zéro et miroir) sont distinctes. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R4_exactOrderedTrouble` | R4 : trouble ordonné exact propre à la paire : tout écart de hauteur interne entre les deux positions de ρ est nul. | CONFIRMÉE | V162 | 1 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R5_samePartneredZero` | R5 : le partenariat local porte exactement le même vrai zéro choisi. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R5_globalSourceCanonical` | R5 : la source globale du partenariat est la source canonique des vrais zéros. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R6_samePrimeGrammar` | R6 : sur le bloc actif, la grammaire encodée depuis les zéros est exactement la grammaire première canonique. | CONFIRMÉE | V48 | 1 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.activeBlock_start` | Le bloc maître actif est réellement [2,4) (début 2). | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.activeBlock_end` | Le bloc maître actif finit à 4. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R7_actualTransportReadout` | R7 : le transport radial harmonique du même partenariat est exactement son opérateur réel. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R8_composition` | R8 : loi de composition exacte sur le même intervalle actif. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R9_pivot` | R9 : le même bloc actif a un premier central genuine p 3 = 7. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.activePrimeSide_entry_eq_exit` | Le bloc actif encodé depuis les zéros a le même état de grammaire à l'entrée et à la sortie. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R10_actualReturn` | R10 : le même intervalle actif est un retour grammatical réel (produit = 1). | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R10_actualReturnEdges` | R10 : les deux changements orientés réels du bloc sont tau51 puis tau15. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R10_radialReciprocalReturn` | Contrôle R10 : la clôture réciproque radiale tient sur le même bloc de retour actif. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R11_mirrorReversal` | R11 : covariance miroir exacte du même partenariat transporté. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.stagePersistence` | Tous les étages harmoniques gardent le retour réciproque sur le même cas actif. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.radialDefect_ne_zero` | Défaut radial exactement non nul du cas de contradiction. | CONFIRMÉE | V162 | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11.r1` | R1 : le zéro est un vrai zéro non trivial. | CONFIRMÉE (domaine : paquet R1ThroughR11 (établi par R1ThroughR11_holds)) | V6 | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11.r2` | R2 : le miroir est un vrai zéro non trivial. | CONFIRMÉE (domaine : paquet R1ThroughR11 (établi par R1ThroughR11_holds)) | V63 | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11.r3` | R3 : même hauteur. | CONFIRMÉE (domaine : paquet R1ThroughR11 (établi par R1ThroughR11_holds)) | V65 | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11.r4` | R4 : tous les écarts de hauteur internes entre les deux positions sont nuls. | CONFIRMÉE (domaine : paquet R1ThroughR11 (établi par R1ThroughR11_holds)) | V162 | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11.r5` | R5 : le partenariat porte le même zéro. | CONFIRMÉE (domaine : paquet R1ThroughR11 (établi par R1ThroughR11_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11.r6` | R6 : côté premier égal à la grammaire première canonique. | CONFIRMÉE (domaine : paquet R1ThroughR11 (établi par R1ThroughR11_holds)) | V48 | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11.r7` | R7 : transport radial = opérateur réel. | CONFIRMÉE (domaine : paquet R1ThroughR11 (établi par R1ThroughR11_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11.r8` | R8 : composition sur le bloc. | CONFIRMÉE (domaine : paquet R1ThroughR11 (établi par R1ThroughR11_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11.r9` | R9 : p 3 est le premier central du bloc. | CONFIRMÉE (domaine : paquet R1ThroughR11 (établi par R1ThroughR11_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11.r10` | R10 : produit grammatical = 1. | CONFIRMÉE (domaine : paquet R1ThroughR11 (établi par R1ThroughR11_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11.r11` | R11 : covariance miroir. | CONFIRMÉE (domaine : paquet R1ThroughR11 (établi par R1ThroughR11_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11_holds` | R1 à R11 sont toutes dérivées sans prémisse supplémentaire au-delà du choix du zéro hors ligne genuine. | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R12Naturality_iff_critical` | Sur le porteur maître exact, R12 (naturalité) ⟺ β=1/2 : comptabilité de force. | CONFIRMÉE | V140 | 1 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.not_R12_from_offLine` | Le cas hors ligne supposé ne peut satisfaire R12 sauf producteur sémantique indépendant. | RÉFUTATION COMPILÉE (naturalité R12 dans un cas maître hors ligne) | V140 | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.MasterSemanticClosure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.contradiction_of_R12MatrixNaturality` | Dès que la naturalité matricielle est produite indépendamment, la contradiction locale est immédiate (False). | RÉFUTATION COMPILÉE (naturalité matricielle R12 (fournie) dans un cas maître hors ligne) | V140 | 2 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11_and_not_R12MatrixNaturality` | Frontière scientifique exacte : dans le cas hors ligne, le même objet maître satisfait R1 à R11 et ne satisfait pas la naturalité matricielle R12. | CONFIRMÉE | V140 | 0 |
| `SemanticTransportClosure20260821.r1ThroughR11ProducesR12_iff_masterR12Producer` | « R1..R11 ⟹ R12 » est exactement le producteur R12 maître (R1..R11 étant déjà théorèmes sur tout cas maître). | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.positive_offLine_zero_gives_master_case` | Un vrai zéro hors ligne de hauteur positive se place toujours dans une constellation de coupure explicite. | CONFIRMÉE SOUS CONDITION (zéro de hauteur > 0 hors ligne) | AJOUT | 2 |
| `SemanticTransportClosure20260821.negative_offLine_zero_gives_master_case` | Un vrai zéro hors ligne de hauteur négative donne un cas maître à hauteur positive par conjugaison, sans changer β. | CONFIRMÉE SOUS CONDITION (zéro de hauteur < 0 hors ligne) | V63 | 1 |
| `SemanticTransportClosure20260821.offLine_zero_gives_master_case` | Tout vrai zéro hors ligne hypothétique, de l'un ou l'autre signe de hauteur, produit un cas sémantique maître. | CONFIRMÉE SOUS CONDITION (zéro hors ligne) | AJOUT | 2 |
| `SemanticTransportClosure20260821.riemannHypothesis_of_masterR12Producer` | Clôture en aval : un vrai producteur de la naturalité matricielle sur tout cas maître hors ligne prouve RH. | IMPLIQUE RH SOUS PRÉMISSE (producteur R12 maître (⟺ RH par masterR12Producer_iff_riemannHypothesis) ; conclusion RiemannHypothesis) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 2 |
| `SemanticTransportClosure20260821.masterR12Producer_of_riemannHypothesis` | RH entraîne MasterR12Producer (RH en hypothèse ; sans zéro hors ligne le producteur tient à vide). | CONFIRMÉE | V140 | 1 |
| `SemanticTransportClosure20260821.masterR12Producer_iff_riemannHypothesis` | Certificat de force exact : prouver le producteur universel comme proposition nue est déjà prouver RH. | ÉQUIVALENTE À RH (prémisse nommée (cf. gloss)) | V140 | 2 |
| `SemanticTransportClosure20260821.r1ThroughR11ProducesR12_iff_riemannHypothesis` | L'énoncé apparemment plus faible « R1..R11 ⟹ R12 » a exactement la force de RH. | ÉQUIVALENTE À RH (prémisse nommée (cf. gloss)) | V140 | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.MirrorGeometry`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.mirrorPoint_re` | mirrorPoint ρ a partie réelle 1−β. | CONFIRMÉE | V65 | 1 |
| `SemanticTransportClosure20260821.mirrorPoint_im` | mirrorPoint ρ a même partie imaginaire. | CONFIRMÉE | V65 | 0 |
| `SemanticTransportClosure20260821.mirrorPoint_involutive` | mirrorPoint est une involution. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.radialDefect_mirrorPoint` | Le miroir renverse exactement le défaut radial. | CONFIRMÉE | V102 | 1 |
| `SemanticTransportClosure20260821.mirrorPoint_eq_self_iff` | Le miroir est fixe exactement sur la ligne critique (comptabilité de force géométrique, pas un théorème de vrai zéro). | CONFIRMÉE | V77 | 1 |
| `SemanticTransportClosure20260821.mirrorPoint_ne_self_iff` | Hors ligne, le point miroir de même hauteur est genuinely distinct. | CONFIRMÉE | V74 | 0 |
| `SemanticTransportClosure20260821.radialTransport_mirror_defect` | Le transport radial à deux branches d'un point est échangé par le transport radial de son miroir. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.PreR12MemberSensitiveAssemblyBoundary`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.not_firstReturnEndpointMemberEquality` | Le côté A exclut l'égalité locale manquante aux deux extrémités du même premier retour. | RÉFUTATION COMPILÉE (égalité des membres aux extrémités du premier retour (FirstReturnEndpointMemberEquality) dans un contexte aligné hors ligne) | AJOUT | 1 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.alignedStart_twoIncidences_share_central_member_sensitive_factor` | Les deux incidences locales de pivot central au départ synchronisé partagent le facteur sensible au membre du même zéro vrai. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.outgoingCentralIncidence_eq_last_iff_firstReturnLength_eq_two` | Frontière d'indice : l'incidence centrale sortante atteint l'extrémité opposée ⟺ la longueur du premier retour est 2. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.riemannHypothesis_of_firstReturnEndpointAssemblyProducer` | Le producteur d'extrémités universel nu prouve RH en contredisant les défauts d'extrémité certifiés des contextes hors ligne. | IMPLIQUE RH SOUS PRÉMISSE (producteur universel d'extrémités de premier retour (⟺ RH par firstReturnEndpointAssemblyProducer_iff_riemannHypothesis) ; conclusion RiemannHypothesis) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 1 |
| `SemanticTransportClosure20260821.firstReturnEndpointAssemblyProducer_of_riemannHypothesis` | RH entraîne le producteur d'extrémités universel (RH en hypothèse ; sans contexte hors ligne il est vrai à vide). | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.firstReturnEndpointAssemblyProducer_iff_riemannHypothesis` | Audit de force : le producteur pré-R12 d'extrémités est déjà de force RH en énoncé nu. | ÉQUIVALENTE À RH (prémisse nommée (cf. gloss)) | AJOUT | 1 |
| `SemanticTransportClosure20260821.canonicalMirrorResidualAgreement_of_centralPivotResidualZeroBlind` | Le résiduel de pivot central aveugle à tout zéro (historique) entraîne l'accord de résidu de la paire miroir canonique, plus faible. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.canonicalMirrorResidualAgreement_forces_critical` | L'accord de résidu de la paire miroir canonique force β=1/2 : même l'accord faible est de force cible (facteur de Dirichlet commun non nul annulé). | CONFIRMÉE | V140 | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.ProgressiveFiberedFirstReturnClosure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.contradiction_of_P0` | P0 contredit la non-retour exact du même porteur : False, sans étape de conversion. | RÉFUTATION COMPILÉE (fidélité P0/P1 (norme du porteur au retour) dans un contexte pleinement aligné (hors ligne)) | V140 | 1 |
| `SemanticTransportClosure20260821.riemannHypothesis_of_P0` | Fermeture conditionnelle de RH restaurée depuis la prise P0 exacte. | IMPLIQUE RH SOUS PRÉMISSE (P0 (FirstReturnMemberSensitiveFidelityP0, ⟺ RH par P0_iff_riemannHypothesis) ; conclusion RiemannHypothesis) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 2 |
| `SemanticTransportClosure20260821.P0_of_riemannHypothesis` | RH entraîne P0 (RH en hypothèse ; sans contexte hors ligne P0 est vide). | CONFIRMÉE | V140 | 2 |
| `SemanticTransportClosure20260821.P0_iff_riemannHypothesis` | Audit de force exact : la couche de compatibilité P0 restaurée ⟺ RH. | ÉQUIVALENTE À RH (prémisse nommée (cf. gloss)) | V140 | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP1At.partnershipZero` | Sous P1 en X, le partenariat porte le zéro de X. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP1At X) | AJOUT | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP1At.partnershipBlock` | Sous P1 en X, le partenariat porte le bloc de X. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP1At X) | AJOUT | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP1At.partnershipStart` | Sous P1 en X, le bloc commence au départ. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP1At X) | AJOUT | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP1At.partnershipFinish` | Sous P1 en X, le bloc finit à la fin. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP1At X) | AJOUT | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP1At.returnEq` | Sous P1 en X, les normes du porteur en fin et au début sont égales. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP1At X) | AJOUT | 4 |
| `SemanticTransportClosure20260821.P1_of_P0` | P0 entraîne P1 (enrichissement par les identités de partenariat et d'extrémités déjà prouvées). | CONFIRMÉE | V140 | 3 |
| `SemanticTransportClosure20260821.P0_of_P1` | P1 entraîne P0 (projection vers l'égalité terminale inchangée). | CONFIRMÉE | V140 | 3 |
| `SemanticTransportClosure20260821.P1_iff_P0` | P1 ⟺ P0 (équivalence propositionnelle). | CONFIRMÉE | V140 | 0 |
| `SemanticTransportClosure20260821.riemannHypothesis_of_P1` | P1 préserve la fermeture conditionnelle de RH par projection sur P0. | IMPLIQUE RH SOUS PRÉMISSE (P1 (⟺ P0 ⟺ RH) ; conclusion RiemannHypothesis) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 2 |
| `SemanticTransportClosure20260821.P1_of_riemannHypothesis` | RH entraîne P1 (RH en hypothèse ; par P0 et les identités de partenariat). | CONFIRMÉE | V140 | 2 |
| `SemanticTransportClosure20260821.P1_iff_riemannHypothesis` | Audit de force exact de P1. | ÉQUIVALENTE À RH (prémisse nommée (cf. gloss)) | V140 | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.contradiction_of_P1` | La contradiction locale P1 est encore l'égalité littérale P0 contre la même non-retour. | RÉFUTATION COMPILÉE (fidélité P0/P1 (norme du porteur au retour) dans un contexte pleinement aligné (hors ligne)) | V140 | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.ProgressiveFiberedFirstReturnClosureP2`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP2At.p1` | Sous P2 en X, P1 en X tient. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP2At X) | AJOUT | 3 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP2At.sourceCanonical` | Sous P2 en X, la source de la capture est la source canonique des zéros. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP2At X) | AJOUT | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP2At.zeroCaptureComplete` | Sous P2 en X, les membres de la capture zéros sont la liste ordonnée canonique complète. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP2At X) | AJOUT | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP2At.sameZeroInCapture` | Sous P2 en X, le zéro est dans la capture. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP2At X) | AJOUT | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP2At.sameMirrorInCapture` | Sous P2 en X, le miroir est dans la même capture. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP2At X) | V63 | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP2At.primeSideEqM` | Sous P2 en X, le côté premier de la capture égale M canonique. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP2At X) | V48 | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP2At.primeSideEqMZ` | Sous P2 en X, le côté premier de la capture égale M^Z reconstruit depuis les zéros. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP2At X) | V48 | 0 |
| `SemanticTransportClosure20260821.P1_of_P2` | P2 entraîne P1 (projection vers l'objet P1 littéralement stocké). | CONFIRMÉE | V140 | 4 |
| `SemanticTransportClosure20260821.P2_of_P1` | P1 entraîne P2 (enrichi des seuls faits déjà théorèmes : source canonique, capture complète, même côté premier). | CONFIRMÉE | V140 | 4 |
| `SemanticTransportClosure20260821.P2_iff_P1` | P2 ⟺ P1 : tous les nouveaux champs étaient déjà des théorèmes. | CONFIRMÉE | V140 | 0 |
| `SemanticTransportClosure20260821.P0_of_P2` | P2 entraîne P0 (par P1). | CONFIRMÉE | V140 | 2 |
| `SemanticTransportClosure20260821.P2_of_P0` | P0 entraîne P2 (par P1 puis P2). | CONFIRMÉE | V140 | 2 |
| `SemanticTransportClosure20260821.P2_iff_P0` | P2 ⟺ P0 (équivalence propositionnelle). | CONFIRMÉE | V140 | 0 |
| `SemanticTransportClosure20260821.riemannHypothesis_of_P2` | P2 préserve la fermeture conditionnelle de RH uniquement via sa projection P1/P0. | IMPLIQUE RH SOUS PRÉMISSE (fidélité P2/P3 (⟺ P0 ⟺ RH) ; conclusion RiemannHypothesis) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 2 |
| `SemanticTransportClosure20260821.P2_of_riemannHypothesis` | RH entraîne P2 (RH en hypothèse ; par P0 et P1 déjà audités). | CONFIRMÉE | V140 | 2 |
| `SemanticTransportClosure20260821.P2_iff_riemannHypothesis` | Audit de force exact de P2 : P2 ⟺ RH. | ÉQUIVALENTE À RH (fidélité P2/P3 (⟺ P0 ⟺ RH)) | V140 | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.contradiction_of_P2` | P2 garde l'égalité terminale littérale de P1 face au même non-retour hors ligne : False. | RÉFUTATION COMPILÉE (fidélité P2/P3 (FiberedFirstReturnClosureP2At/P3At) dans un contexte pleinement aligné (hors ligne)) | V140 | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.ProgressiveFiberedFirstReturnClosureP3`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP3At.p2` | Sous P3 en X, P2 en X tient. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP3At X) | AJOUT | 2 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP3At.refinedProperties` | Sous P3 en X, les 32 propriétés non terminales raffinées du partenariat tiennent. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP3At X) | AJOUT | 2 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP3At.directCarrierSameZero` | Compatibilité : la branche directe est le porteur du même zéro. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP3At X) | AJOUT | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP3At.reflectedCarrierSameMirror` | Compatibilité : la branche réfléchie est le porteur du même miroir. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP3At X) | AJOUT | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP3At.directFiberSameMember` | Compatibilité : la fibre directe est le même membre dans la fibre de hauteur commune. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP3At X) | AJOUT | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP3At.reflectedFiberSameMirror` | Compatibilité : la fibre réfléchie est le même vrai miroir. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP3At X) | AJOUT | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP3At.sameHeight` | Compatibilité : même hauteur exacte. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP3At X) | V65 | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP3At.radialDefectSameZero` | Compatibilité : le défaut radial stocké est exactement β−1/2 du même zéro. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP3At X) | V102 | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP3At.mirrorRadialOpposite` | Compatibilité : le miroir porte le défaut radial opposé. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP3At X) | V102 | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP3At.operatorRadialSameBlock` | Compatibilité : l'opérateur du bloc est l'opérateur radial du même défaut. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP3At X) | AJOUT | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP3At.radialRecovery` | Non-régression : la propriété de récupération radiale injective déjà prouvée reste disponible (deux partenariats de même bloc et même entrée d'opérateur ont même défaut). | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP3At X) | AJOUT | 0 |
| `SemanticTransportClosure20260821.FiberedFirstReturnClosureP3At.harmonicTowerSameZero` | Compatibilité : la Tour harmonique appartient toujours au même vrai zéro. | CONFIRMÉE (domaine : paquet FiberedFirstReturnClosureP3At X) | AJOUT | 0 |
| `SemanticTransportClosure20260821.P2_of_P3` | P3 entraîne P2. | CONFIRMÉE | V140 | 4 |
| `SemanticTransportClosure20260821.P3_of_P2` | P2 entraîne P3 : les 32 propriétés raffinées sont des théorèmes inconditionnels du même partenariat. | CONFIRMÉE | V140 | 4 |
| `SemanticTransportClosure20260821.P3_iff_P2` | P3 ⟺ P2 : le raffinement n'ajoute aucune force scientifique. | CONFIRMÉE | V140 | 0 |
| `SemanticTransportClosure20260821.P1_of_P3` | P3 entraîne P1. | CONFIRMÉE | V140 | 1 |
| `SemanticTransportClosure20260821.P0_of_P3` | P3 entraîne P0. | CONFIRMÉE | V140 | 1 |
| `SemanticTransportClosure20260821.P3_iff_P1` | P3 ⟺ P1. | CONFIRMÉE | V140 | 0 |
| `SemanticTransportClosure20260821.P3_iff_P0` | P3 ⟺ P0. | CONFIRMÉE | V140 | 0 |
| `SemanticTransportClosure20260821.riemannHypothesis_of_P3` | Fermeture de compatibilité historique via la prise P0. | IMPLIQUE RH SOUS PRÉMISSE (fidélité P2/P3 (⟺ P0 ⟺ RH) ; conclusion RiemannHypothesis) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 1 |
| `SemanticTransportClosure20260821.P3_of_riemannHypothesis` | RH entraîne P3 (audit de force seulement ; RH en hypothèse). | CONFIRMÉE | V140 | 1 |
| `SemanticTransportClosure20260821.P3_iff_riemannHypothesis` | Audit de force historique : P3 ⟺ RH ; ce n'est pas une prémisse de la fracture scientifique contact/Tour. | ÉQUIVALENTE À RH (fidélité P2/P3 (⟺ P0 ⟺ RH)) | V140 | 0 |
| `SemanticTransportClosure20260821.refinedProperties_hold_for_every_aligned_context` | Les 32 propriétés non terminales raffinées sont disponibles pour tout contexte pleinement aligné. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.contradiction_of_P3` | Contradiction de compatibilité littérale, gardée seulement pour préserver l'identité SI historique. | RÉFUTATION COMPILÉE (fidélité P2/P3 (FiberedFirstReturnClosureP2At/P3At) dans un contexte pleinement aligné (hors ligne)) | V140 | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.ProjectSemanticBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.isTrivialZero_iff_project` | Le prédicat de zéro trivial reconstruit est définitionnellement le prédicat du projet. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.isTrueNontrivialZero_iff_project` | Le prédicat de vrai zéro non trivial reconstruit est définitionnellement le prédicat du projet. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.mirrorPoint_eq_projectMirror` | Le miroir sémantique générique est exactement le point complexe de l'involution miroir totale du projet. | CONFIRMÉE | V65 | 0 |
| `SemanticTransportClosure20260821.radialDefect_eq_actualPartnershipDefect` | Le défaut radial de l'algèbre indépendante égale le défaut radial stocké dans le partenariat localisé réel. | CONFIRMÉE | V102 | 0 |
| `SemanticTransportClosure20260821.zeroRadialTransport_eq_actualPartneredTransport` | zeroRadialTransport de la couche terminale vrai-zéro est exactement le transport radial partenarié réel. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.zeroRadialNaturality_iff_actualPartneredNaturality` | La naturalité radiale locale de la couche terminale ⟺ la naturalité du porteur partenarié réel. | CONFIRMÉE | V140 | 0 |
| `SemanticTransportClosure20260821.actualProjectZero_isTrueNontrivialZero` | Le zéro réel du projet peut être consommé par l'API terminale vrai-zéro indépendante sans changer sa signification mathématique. | CONFIRMÉE | V6 | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.R12ConstructionBoundary`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.reflectionAccumulationRatio_exact` | Le calcul FJ historique donne la valeur exacte du rapport de normalisation de réflexion (facteur source, caractères de Tour). | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.reflectionAccumulationRatio_eq_iff_blockHolonomy_eq` | Égalité des rapports de normalisation de réflexion en M et N ⟺ égalité des holonomies de bloc direct et réfléchi (algèbre de changement de base). | CONFIRMÉE (domaine : M ≤ N) | V140 | 1 |
| `SemanticTransportClosure20260821.reflectionAccumulationRatio_two_eq_four_iff_crossTransport_entries` | Sur le bloc de retour [2,4), l'égalité des rapports en 2 et 4 ⟺ égalité des deux entrées du transport croisé réfléchi. | CONFIRMÉE | V140 | 1 |
| `SemanticTransportClosure20260821.crossTransport_entries_eq_iff_crossOperator_entries` | L'égalité des entrées du transport croisé ⟺ l'égalité des entrées de l'opérateur croisé (retrait de la phase de hauteur commune). | CONFIRMÉE | V140 | 1 |
| `SemanticTransportClosure20260821.reflectionAccumulationRatio_two_eq_four_iff_critical` | L'indépendance de base du rapport de normalisation réfléchi/direct sur [2,4) ⟺ β=1/2. | CONFIRMÉE | V140 | 1 |
| `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R12MatrixNaturality_iff_reflectionAccumulationRatio_baseIndependent` | Sur le cas maître, la naturalité matricielle R12 ⟺ l'indépendance de base du rapport de normalisation de réflexion. | CONFIRMÉE | V140 | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.SameTrueZeroAlignedConstructors`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.completeOfflineDiscoveryBundleOf_zero` | Le zéro du paquet de découverte construit est ρ. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | AJOUT | 0 |
| `SemanticTransportClosure20260821.exhaustiveSameObjectOfflineContextOf_zero` | Le zéro du contexte exhaustif construit est ρ. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | AJOUT | 0 |
| `SemanticTransportClosure20260821.fullyAlignedSameEventContextOf_zero` | Le zéro du contexte pleinement aligné construit est ρ. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | AJOUT | 0 |
| `SemanticTransportClosure20260821.fullyAlignedSameEventContextOf_mirror` | Le miroir du contexte pleinement aligné construit est reflectConjZero ρ. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V65 | 0 |
| `SemanticTransportClosure20260821.fullyAlignedSameEventContext_exists_same_zero` | API d'existence forte : ∃ X, X.zero = ρ, identité exposée dans le type. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | AJOUT | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.TransformedGrammarLift`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.TransformedReturnCase.one_lt_ratio` | Champ de TransformedReturnCase : le rapport est > 1. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.DiscreteReturnRigidity.returns` | Sous la rigidité discrète, sortie = entrée du bloc. | CONFIRMÉE (domaine : paquet DiscreteReturnRigidity C (établi par discreteReturnRigidity_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.DiscreteReturnRigidity.incoming` | Sous la rigidité discrète, la transition entrante est celle du retour canonique. | CONFIRMÉE (domaine : paquet DiscreteReturnRigidity C (établi par discreteReturnRigidity_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.DiscreteReturnRigidity.outgoing` | Sous la rigidité discrète, la transition sortante est celle du retour canonique. | CONFIRMÉE (domaine : paquet DiscreteReturnRigidity C (établi par discreteReturnRigidity_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.DiscreteReturnRigidity.orientationsReverse` | Sous la rigidité discrète, les orientations de changement sont inverses l'une de l'autre. | CONFIRMÉE (domaine : paquet DiscreteReturnRigidity C (établi par discreteReturnRigidity_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.DiscreteReturnRigidity.oddSupportPattern` | Sous la rigidité discrète, motif de support impair (faux, vrai, faux). | CONFIRMÉE (domaine : paquet DiscreteReturnRigidity C (établi par discreteReturnRigidity_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.DiscreteReturnRigidity.evenSupportPattern` | Sous la rigidité discrète, support pair universel. | CONFIRMÉE (domaine : paquet DiscreteReturnRigidity C (établi par discreteReturnRigidity_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.discreteReturnRigidity_holds` | Les rigidités du squelette fini tiennent pour tout défaut radial (elles appartiennent à la grammaire). | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.RadialReturnRigidity.reciprocalReturn` | Sous la rigidité radiale, le produit de retour radial vaut 1. | CONFIRMÉE (domaine : paquet RadialReturnRigidity C (établi par radialReturnRigidity_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.RadialReturnRigidity.mirrorReversal` | Sous la rigidité radiale, le renversement du radial est le transport radial au défaut opposé. | CONFIRMÉE (domaine : paquet RadialReturnRigidity C (établi par radialReturnRigidity_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.RadialReturnRigidity.reversalInvolutive` | Sous la rigidité radiale, le renversement est involutif. | CONFIRMÉE (domaine : paquet RadialReturnRigidity C (établi par radialReturnRigidity_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.RadialReturnRigidity.everyStageReturns` | Sous la rigidité radiale, chaque étage a produit de retour 1. | CONFIRMÉE (domaine : paquet RadialReturnRigidity C (établi par radialReturnRigidity_holds)) | AJOUT | 0 |
| `SemanticTransportClosure20260821.radialReturnRigidity_holds` | Les rigidités de retour radial tiennent aussi pour tout défaut. | CONFIRMÉE | AJOUT | 1 |
| `SemanticTransportClosure20260821.cumulativeKnownRigidity_holds` | Tout cas de retour transformé satisfait toutes les rigidités connues cumulées. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.transformedReturnCase_natural_iff_defect_zero` | Sur l'objet cumulatif, la naturalité est exactement défaut radial nul. | CONFIRMÉE | V140 | 2 |
| `SemanticTransportClosure20260821.cumulative_rigidities_admit_offline_case` | Contre-contrôle cumulatif complet : un même objet porte retour fini, pivot, orientations opposées, support, retour réciproque, défaut ≠ 0 et non-naturalité. | CONFIRMÉE (domaine : R > 1) | V140 | 0 |
| `SemanticTransportClosure20260821.cumulativeKnownRigidity_does_not_force_naturality` | Aucun théorème utilisant seulement CumulativeKnownRigidity ne peut forcer la naturalité de tout cas. | RÉFUTATION COMPILÉE (implication « CumulativeKnownRigidity ⟹ naturalité » (condition R > 1)) | V140 | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.TransformedReturnAlgebra`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.reverse_direct` | Le renversement échange : la branche directe de reverse T est la branche réfléchie de T. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.reverse_reflected` | La branche réfléchie de reverse T est la branche directe de T. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.reverse_reverse` | Le renversement est une involution, indépendamment de toute donnée radiale. | CONFIRMÉE | AJOUT | 3 |
| `SemanticTransportClosure20260821.radialTransport_direct` | La branche directe du transport radial vaut R^(−d). | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.radialTransport_reflected` | La branche réfléchie du transport radial vaut R^d. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.reverse_radialTransport` | La réflexion d ↦ −d est exactement le renversement de branche grammaticale sur le relevé radial. | CONFIRMÉE | AJOUT | 5 |
| `SemanticTransportClosure20260821.radial_returnProduct_eq_one` | Le retour réciproque se ferme pour tout d : contre-contrôle montrant que retour/involution seuls ne discriminent pas. | CONFIRMÉE (domaine : R > 0) | AJOUT | 6 |
| `SemanticTransportClosure20260821.naturalUnderReversal_iff_entries_eq` | La naturalité par renversement ⟺ égalité des deux entrées de branche radiale. | CONFIRMÉE | V140 | 1 |
| `SemanticTransportClosure20260821.rpow_inj_of_one_lt` | Les puissances réelles d'une base fixe R>1 sont injectives dans l'exposant. | CONFIRMÉE (domaine : R > 1) | AJOUT | 1 |
| `SemanticTransportClosure20260821.radial_entries_eq_iff_defect_zero` | Les deux entrées radiales miroir coïncident exactement lorsque le défaut radial est nul. | CONFIRMÉE (domaine : R > 1) | V140 | 1 |
| `SemanticTransportClosure20260821.radial_naturality_iff_defect_zero` | THÉORÈME DISCRIMINANT : pour un rapport genuine R>1, la naturalité du relevé radial transformé par renversement ⟺ d = 0. | CONFIRMÉE (domaine : R > 1) | V140 | 8 |
| `SemanticTransportClosure20260821.return_does_not_force_naturality` | Le retour ne force pas la naturalité : il existe d ≠ 0 de retour réciproque exact mais non naturel. | CONFIRMÉE (domaine : R > 1) | V140 | 0 |
| `SemanticTransportClosure20260821.stage_returnProduct_eq_one` | Chaque étage garde un retour réciproque exact. | CONFIRMÉE (domaine : R > 0) | AJOUT | 3 |
| `SemanticTransportClosure20260821.stage_naturality_iff_defect_zero` | À tout étage harmonique positif, la naturalité par renversement ⟺ d = 0 (criticité). | CONFIRMÉE (domaine : R > 1, étage m > 0) | V140 | 0 |

### `RhGapCriterion.SemanticTransportClosure20260821.TrueZeroClosure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `SemanticTransportClosure20260821.critical_of_zeroRadialTransport_natural` | La naturalité du transport radial du zéro à un seul rapport d'échelle genuine R > 1 suffit à forcer β=1/2 du point. | CONFIRMÉE (domaine : rapport R > 1) | V140 | 1 |
| `SemanticTransportClosure20260821.ScaleWitness.one_lt_ratio` | Champ de ScaleWitness : le rapport est > 1. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.all_nontrivial_zeros_critical_of_partneredNaturality` | Une fois le producteur indépendant disponible, tout vrai zéro non trivial est critique. | IMPLIQUE RH SOUS PRÉMISSE (TrueZeroPartneredNaturality (⟺ RH par partneredNaturality_iff_riemannHypothesis) ; conclusion ∀ρ vrai zéro non trivial, β=1/2 (forme dépliée de RH)) | V140 | 1 |
| `SemanticTransportClosure20260821.riemannHypothesis_of_partneredNaturality` | UNIVERSALISATION TERMINALE : la naturalité partenariée donne immédiatement RH. | IMPLIQUE RH SOUS PRÉMISSE (TrueZeroPartneredNaturality (⟺ RH) ; conclusion RiemannHypothesis) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 1 |
| `SemanticTransportClosure20260821.partneredNaturality_of_riemannHypothesis` | RH entraîne la naturalité partenariée terminale à tout rapport genuine (RH en hypothèse ; comptabilité de force). | CONFIRMÉE | V140 | 1 |
| `SemanticTransportClosure20260821.partneredNaturality_iff_riemannHypothesis` | Comptabilité de force : l'interface du producteur universel a la force de RH ; cela ne fait pas d'un producteur indépendant un théorème. | ÉQUIVALENTE À RH (TrueZeroPartneredNaturality) | V140 | 0 |

### `RhGapCriterion.TiltDriftLaw`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `drift_mode_inverse` | Identité exacte : les dérives de classes (d0,d2,d4) se reconstruisent depuis les dérives de modes. | CONFIRMÉE | AJOUT | 0 |
| `conservation_reduces_drift_to_two_dof` | Sous conservation, la dérive se réduit à deux degrés de liberté. | CONFIRMÉE (domaine : d0+d2+d4 = 0) | AJOUT | 0 |
| `internal_drift_pair_injective` | La correspondance (dB,dO) ↔ (d0,d2,d4) conservée est injective (une bijection). | CONFIRMÉE (domaine : mêmes images) | AJOUT | 0 |
| `reconstructed_drift_triple_conserved` | Le triplet conservé reconstruit depuis (dB,dO) satisfait la conservation (somme nulle). | CONFIRMÉE | AJOUT | 0 |
| `tilt_zero_mean` | Le tilt de conservation annule la dérive moyenne : ∑(d−L)·P = 0. (terme hors maître « tilt » : pondération de conservation (∑P=1, ∑d·P=L) annulant la dérive moyenne) | CONFIRMÉE (domaine : normalisation ∑P=1 et ∑d·P=L) | AJOUT | 3 |
| `constant_weight_drift_vanishes` | La dérive d'un poids constant est nulle sous le tilt. | CONFIRMÉE (domaine : normalisation ∑P=1 et ∑d·P=L) | AJOUT | 0 |
| `tilt_drift_closed_form` | Forme close de la dérive de premier ordre du tilt. | CONFIRMÉE (domaine : normalisation ∑P=1 et ∑d·P=L) | AJOUT | 0 |
| `class_drift_conservation_under_tilt` | Dérives de classes sous le tilt : conservation et deux degrés de liberté. | CONFIRMÉE (domaine : ∑P=1, ∑d·P=L, classes 0/2/4) | AJOUT | 0 |
| `recentering_preserves_total_mode` | Le recentrage interne laisse le canal T exactement inchangé. | CONFIRMÉE | AJOUT | 0 |
| `subexponential_of_subexponential_additive_correction` | Une correction additive sous-exponentielle préserve la sous-exponentialité. | CONFIRMÉE (domaine : F ≤ G+H sur u ≥ 0, G,H sous-exponentielles) | AJOUT | 1 |

### `RhGapCriterion.TransformDecomposition`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `transformOf_edge_correspondence` | Correspondance exacte transition ↔ transformation sur les quatre arêtes du graphe fini des états mod 6 (tau11, tau15, tau51, tau55). | CONFIRMÉE (domaine : états s,t ∈ {1,5}) | V174 | 5 |
| `transform_exhaustive_unique` | Pour tout n ≥ 2, la transformation de la transition (p n mod 6, p(n+1) mod 6) existe et est unique. | CONFIRMÉE (domaine : n ≥ 2) | V174 | 0 |
| `transform_partition` | Partition en quatre classes disjointes et exhaustives des transformations. | CONFIRMÉE (domaine : n ≥ 2) | V174 | 0 |
| `g_eq_gnat_cast` | Le résidu réel du gap g n égale le gap entier gnat n (les premiers sont strictement croissants). | CONFIRMÉE | AJOUT | 7 |
| `gap_transition_residue_exists` | Pour n ≥ 2, gnat n se relève exactement en 6k + résidu de transition. | CONFIRMÉE (domaine : n ≥ 2) | V174 | 3 |
| `transformation_conditioned_increment_decomposition` | Décomposition de l'incrément conditionnée par la transformation : incrément de mode T = 6k + 3·croix − log p + cobord. | CONFIRMÉE (domaine : n ≥ 2) | AJOUT | 3 |
| `energy_kernel_class_partition` | Schéma de partition finie de l'énergie par classes (identité à tout périmètre). | CONFIRMÉE | AJOUT | 3 |
| `coboundary_preserves_subexponential_target` | Le cobord grammatical préserve la sous-exponentialité d'une cible d'énergie. | CONFIRMÉE (domaine : cobord borné et cible sous-exponentielle) | AJOUT | 0 |
| `grammar_coboundary_does_not_break_subexponentiality` | Corollaire sur les chemins finis : la partie cobord n'altère pas la sous-exponentialité. | CONFIRMÉE (domaine : cobord borné et cible sous-exponentielle) | AJOUT | 0 |
| `Transform6.enumList_getElem?_ctorIdx_eq` | La liste d'énumération de Transform6 rend la valeur à l'indice de constructeur. | CONFIRMÉE | AJOUT | 0 |
| `Transform6.enumList_nodup` | La liste d'énumération de Transform6 est sans doublon. | CONFIRMÉE | AJOUT | 0 |
| `Transform6.ofNat_ctorIdx` | ofNat ∘ ctorIdx est l'identité sur Transform6. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.TrueZeroCommonContactProducerAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `masterR12Producer_of_unifiedCommonE44ContactProducer` | Un producteur universel de contact E44 commun entraîne le producteur R12 maître (prémisse et conclusion équivalentes à RH). | CONFIRMÉE | V140 | 1 |
| `riemannHypothesis_of_unifiedCommonE44ContactProducer` | Le producteur universel nu de contact commun prouve RH. | IMPLIQUE RH SOUS PRÉMISSE (producteur commun de contact E44 (⟺ RH par unifiedCommonE44ContactProducer_iff_riemannHypothesis) ; conclusion RiemannHypothesis) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 1 |
| `unifiedCommonE44ContactProducer_of_riemannHypothesis` | RH entraîne le producteur de contact commun (RH en hypothèse ; vrai à vide car chaque cas hors ligne unifié contient un vrai zéro). | CONFIRMÉE | V140 | 1 |
| `unifiedCommonE44ContactProducer_iff_riemannHypothesis` | Certificat de force cible exact : producteur commun ⟺ RH. | ÉQUIVALENTE À RH (UnifiedCommonE44ContactProducer) | V140 | 0 |
| `false_of_common_E44_contact_on_unified_offline` | Diagnostic renforcé : supposer des contacts communs sur un cas hors ligne concret donne False immédiatement. | RÉFUTATION COMPILÉE (contacts E44 communs au zéro et à son miroir sur un cas hors ligne unifié (condition m ≥ 1)) | V163 | 0 |

### `RhGapCriterion.TrueZeroE44MirrorContactRigidity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `e44_same_contacts_for_mirror_force_half` | Rigidité E44 pure : une paire de contacts d'étage positif ne peut décoder les deux coordonnées radiales complémentaires que si β=1/2. | CONFIRMÉE (domaine : étage m ≥ 1, β ≠ 0) | V163 | 1 |
| `trueZero_same_E44_contacts_force_critical` | Spécialisation vrai zéro : mêmes contacts E44 pour le zéro et son miroir ⟹ β=1/2 (dénominateurs non nuls tirés de la zérohood). | CONFIRMÉE (domaine : étage m ≥ 1, β ≠ 0) | V163 | 5 |
| `trueOffline_no_common_E44_contact_pair` | Un vrai zéro hors ligne ne partage pas une paire exacte de contacts E44 avec son miroir de même hauteur. | RÉFUTATION COMPILÉE (paire de contacts E44 commune à un zéro hors ligne et à son miroir (condition β ≠ 1/2, m ≥ 1)) | V163 | 3 |
| `critical_of_independent_common_E44_contact` | Formulation bilatérale : si l'assemblage premier/grammaire fournit indépendamment un contact commun, alors β=1/2. | CONFIRMÉE (domaine : étage m ≥ 1, β ≠ 0) | V163 | 0 |

### `RhGapCriterion.TrueZeroPerronGrammarCarrierWeld`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `perronCenterScale_ne_zero` | L'échelle centrale de Perron est non nulle. | CONFIRMÉE | AJOUT | 1 |
| `nontrivialZeroResidueTerm_eq_centerScale_mul_rawSignature` | Le terme de Perron individuel est l'échelle centrale fois la signature brute vraie du zéro. | CONFIRMÉE (domaine : P > 0) | AJOUT | 1 |
| `carrierPerronEndpoint_eq_nontrivialZeroResidueTerm` | L'extrémité de porteur est littéralement le terme de Perron individuel original au même premier. | CONFIRMÉE | AJOUT | 1 |
| `zeroPrimeStepContribution_eq_carrier_endpoint_difference` | La cellule de la table de raffinement zéro/premier est une différence avant de la même fonction d'extrémité de porteur. | CONFIRMÉE | AJOUT | 3 |
| `grammarVoiceStep_eq_weight_mul_carrier_difference` | La cellule de voix de grammaire est le poids entier de grammaire première fois la différence du porteur. | CONFIRMÉE | AJOUT | 3 |
| `grammarVoiceStep_sub_mirror_eq_carrier_rectangle` | Le défaut de ligne réfléchi est exactement un rectangle de porteur à quatre extrémités. | CONFIRMÉE | AJOUT | 0 |
| `rowContributionDefect_iff_carrier_increment_ne` | Un défaut de contribution de ligne ⟺ inégalité des deux incréments d'extrémité du porteur. | CONFIRMÉE | AJOUT | 2 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.startCarrierIncrementDefect` | À la première arête synchronisée, le défaut sensible au membre (H3/AV) s'exprime directement sur les incréments du porteur. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.lastCarrierIncrementDefect` | La dernière arête opposée du même premier retour porte la même inégalité au niveau du porteur. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.startGrammarVoice_carrier_formula` | Voix de grammaire au départ : poids × différence du porteur du zéro. | CONFIRMÉE | AJOUT | 0 |
| `SemanticTransportClosure20260821.FullyAlignedSameEventContext.lastGrammarVoice_carrier_formula` | Même formule à l'extrémité opposée. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.TrueZeroQuartet`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `TrueZeroQuartet.offLine` | Champ de TrueZeroQuartet : la graine est hors ligne. | CONFIRMÉE | AJOUT | 5 |
| `TrueZeroQuartet.conjugateMember_coe` | Le conjugué est la conjugaison complexe de la graine. | CONFIRMÉE | V63 | 3 |
| `TrueZeroQuartet.sameHeightMirror_coe` | Le miroir de même hauteur est 1 − conjugué de la graine. | CONFIRMÉE | V63 | 5 |
| `TrueZeroQuartet.oppositeHeightMirror_coe` | Le miroir de hauteur opposée est 1 − graine. | CONFIRMÉE | V63 | 7 |
| `TrueZeroQuartet.sameHeightMirror_im` | La moitié supérieure du quartet occupe une seule hauteur. | CONFIRMÉE | V65 | 4 |
| `TrueZeroQuartet.conjugateMember_im` | Le conjugué occupe la hauteur opposée. | CONFIRMÉE | V63 | 2 |
| `TrueZeroQuartet.oppositeHeightMirror_im` | Le quatrième membre partage la hauteur opposée avec le conjugué. | CONFIRMÉE | V63 | 4 |
| `TrueZeroQuartet.sameHeightMirror_re` | Les deux coordonnées radiales du quartet sont complémentaires. | CONFIRMÉE | V65 | 3 |
| `TrueZeroQuartet.conjugateMember_re` | La conjugaison préserve la coordonnée radiale. | CONFIRMÉE | V63 | 3 |
| `TrueZeroQuartet.oppositeHeightMirror_re` | Le quatrième membre a la coordonnée radiale complémentaire. | CONFIRMÉE | V63 | 1 |
| `TrueZeroQuartet.seed_im_ne_zero` | Tout membre non trivial a hauteur non nulle : les deux fibres de hauteur du quartet sont distinctes. | CONFIRMÉE | V7 | 4 |
| `TrueZeroQuartet.seed_ne_sameHeightMirror` | Les deux membres de la fibre de hauteur de la graine sont distincts exactement parce que la graine est hors ligne. | CONFIRMÉE | V63 | 5 |
| `TrueZeroQuartet.seed_ne_conjugateMember` | Les deux fibres de hauteur sont réellement différentes. | CONFIRMÉE | V63 | 4 |
| `TrueZeroQuartet.seed_ne_oppositeHeightMirror` | La graine n'égale pas le membre complémentaire à hauteur opposée. | CONFIRMÉE | V63 | 3 |
| `TrueZeroQuartet.conjugateMember_ne_oppositeHeightMirror` | Le conjugué et son compagnon réfléchi de même hauteur sont distincts hors ligne. | CONFIRMÉE | V63 | 4 |
| `TrueZeroQuartet.sameHeightMirror_ne_oppositeHeightMirror` | Des membres de hauteurs croisées ne peuvent coïncider. | CONFIRMÉE | V63 | 3 |
| `TrueZeroQuartet.conjugateMember_ne_sameHeightMirror` | L'inégalité restante entre membres croisés utilise la séparation radiale hors ligne. | CONFIRMÉE | V63 | 4 |
| `TrueZeroQuartet.four_members_pairwise_distinct` | Les quatre membres nommés du quartet sont deux à deux distincts. | CONFIRMÉE | V63 | 1 |
| `TrueZeroQuartet.members_card_eq_four` | L'orbite finie canonique a réellement cardinal quatre hors ligne. | CONFIRMÉE | V63 | 5 |
| `TrueZeroQuartet.conjugate_multiplicity` | La conjugaison préserve la multiplicité analytique. | CONFIRMÉE | V63 | 2 |
| `TrueZeroQuartet.sameHeightMirror_multiplicity` | La réflexion-conjuguée de même hauteur préserve la multiplicité. | CONFIRMÉE | V63 | 2 |
| `TrueZeroQuartet.oppositeHeightMirror_multiplicity` | Le quatrième membre a la même multiplicité que la graine. | CONFIRMÉE | V63 | 1 |
| `TrueZeroQuartet.all_four_multiplicities_equal` | Paquet complet de multiplicités du quartet. | CONFIRMÉE | V63 | 2 |
| `TrueZeroQuartet.sameHeight_half_not_conjugation_closed` | La paire de même hauteur n'est pas close par conjugaison hors ligne : son conjugué manquant est un membre nommé du quartet. | CONFIRMÉE | V63 | 0 |

### `RhGapCriterion.TrueZeroTangentContactGeometry`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `tangentContact_pos` | Le contact tangent est strictement positif. | CONFIRMÉE | AJOUT | 5 |
| `tangentStageRight_pos` | Le contact d'étage droit tangent est strictement positif. | CONFIRMÉE | AJOUT | 0 |
| `tangentContact_phase_exact` | γ·log(contact tangent) = phase tangente + kπ (phase exacte). | CONFIRMÉE (domaine : β ≠ 0, γ ≠ 0, étage m ≥ 1 selon l'énoncé) | V45 | 2 |
| `tangentContact_equation` | Équation du contact tangent : β·tan(γ log contact) = γ. | CONFIRMÉE (domaine : β ≠ 0, γ ≠ 0, étage m ≥ 1 selon l'énoncé) | V45 | 3 |
| `beta_eq_gamma_div_tan_tangentContact` | β = γ / tan(γ log contact tangent) (récupération de β). | CONFIRMÉE (domaine : β ≠ 0, γ ≠ 0, étage m ≥ 1 selon l'énoncé) | V45 | 4 |
| `e44Delta_tangentStage` | La largeur log entre contact tangent et contact d'étage m est mπ/γ (ne dépend que de la hauteur). | CONFIRMÉE (domaine : β ≠ 0, γ ≠ 0, étage m ≥ 1 selon l'énoncé) | V17 | 4 |
| `e44RecoveredGamma_tangentStage` | Les deux contacts tangents d'étage m récupèrent γ. | CONFIRMÉE (domaine : β ≠ 0, γ ≠ 0, étage m ≥ 1 selon l'énoncé) | V45 | 5 |
| `e44TangentEliminatedLaw_of_contact_width` | Si le contact gauche satisfait l'équation tangente et la largeur vaut mπ/γ, la loi E44 tangente éliminée tient. | CONFIRMÉE (domaine : β ≠ 0, γ ≠ 0, étage m ≥ 1 selon l'énoncé) | V45 | 1 |
| `tangentStage_satisfies_E44TangentEliminatedLaw` | La paire de contacts tangents satisfait la loi E44 tangente éliminée. | CONFIRMÉE (domaine : β ≠ 0, γ ≠ 0, étage m ≥ 1 selon l'énoncé) | V45 | 2 |
| `e44TangentRecoveredBeta_eq` | Sous la loi E44 tangente, le β récupéré est β (la paire redonne β). | CONFIRMÉE (domaine : β ≠ 0, γ ≠ 0, étage m ≥ 1 selon l'énoncé) | V45 | 6 |
| `e44TangentCriticalDefect_eq_radial` | Sous la loi E44 tangente, le défaut critique tangent égale le défaut radial tiré de β. | CONFIRMÉE | AJOUT | 1 |
| `E44TangentEliminatedLaw_stage_one_iff` | À l'étage 1, la loi E44 tangente équivaut à la loi E44 éliminée historique. | CONFIRMÉE | AJOUT | 1 |
| `e44TangentRecoveredBeta_stage_one` | À l'étage 1, le β tangent récupéré égale le β récupéré historique. | CONFIRMÉE | AJOUT | 0 |
| `tangentContact_eq_mirror_iff_half` | Le contact tangent de β égale celui de 1−β ⟺ β=1/2. | CONFIRMÉE (domaine : 0 < β < 1, γ ≠ 0) | V163 | 1 |
| `trueZeroTangentContact_eq_mirror_iff_critical` | Le contact vrai d'un zéro égale celui de son miroir ⟺ β=1/2. | CONFIRMÉE (domaine : hauteur > 0) | V163 | 2 |
| `trueOffline_tangentContact_ne_mirror` | Hors ligne, les contacts tangents vrais du zéro et de son miroir au même indice diffèrent. | CONFIRMÉE SOUS CONDITION (zéro de hauteur > 0 hors ligne) | V163 | 6 |
| `trueZero_tangentStage_satisfies_corrected_E44` | Un vrai zéro satisfait la loi E44 corrigée par sa paire de contacts vrais d'étage m. | CONFIRMÉE (domaine : hauteur > 0, m ≥ 1) | V45 | 5 |
| `trueZero_tangentStage_one_satisfies_legacy_E44` | La paire d'étage 1 satisfait la loi E44 historique pour β du zéro. | CONFIRMÉE (domaine : hauteur > 0) | V45 | 0 |
| `trueZero_tangentContact_towerCharacter` | Le caractère de Tour au contact tangent d'un vrai zéro est contact^(−(β−1/2)) fois une exponentielle de la phase tangente et de kπ. | CONFIRMÉE (domaine : hauteur ≠ 0) | AJOUT | 0 |
| `trueZero_tangentContact_to_prime_cocycle` | Le passage contact tangent→premier est le cocycle exact du même vrai zéro. | CONFIRMÉE | AJOUT | 5 |

### `RhGapCriterion.UnifiedTrueZeroConstraintClosure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `trueZeroBeta_mirror` | β du miroir vaut 1−β. | CONFIRMÉE | V65 | 1 |
| `trueZeroGamma_mirror` | γ du miroir égale γ. | CONFIRMÉE | V65 | 0 |
| `trueZeroDelta_mirror` | Le défaut radial du miroir est l'opposé de celui du zéro. | CONFIRMÉE | V102 | 0 |
| `UnifiedPositiveOfflineCase.zero_mem` | Champ de UnifiedPositiveOfflineCase : le zéro est dans les représentants positifs. | CONFIRMÉE | AJOUT | 2 |
| `UnifiedPositiveOfflineCase.offLine` | Champ : le zéro est hors ligne. | CONFIRMÉE | AJOUT | 8 |
| `UnifiedPositiveOfflineCase.master_zero` | Champ : la réalisation maître porte ce zéro. | CONFIRMÉE | AJOUT | 0 |
| `UnifiedPositiveOfflineCase.weld_zero` | Champ : la soudure porte ce zéro. | CONFIRMÉE | AJOUT | 0 |
| `unifiedPositiveOfflineCase_exists` | Les deux constructions même-objet existantes s'instancient simultanément depuis un même vrai zéro positif hors ligne. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V62 | 0 |
| `UnifiedPositiveOfflineCase.positiveHeight` | La hauteur positive vient de l'appartenance à la constellation positive réelle. | CONFIRMÉE | V7 | 1 |
| `UnifiedPositiveOfflineCase.zero_mem_heightConstellation` | Le même membre appartient à la constellation de hauteur bornée vraie sous-jacente. | CONFIRMÉE | AJOUT | 1 |
| `UnifiedPositiveOfflineCase.quartet_seed` | La graine du quartet est le zéro. | CONFIRMÉE | V63 | 0 |
| `UnifiedPositiveOfflineCase.quartet_card_four` | Le quartet a quatre membres distincts genuine. | CONFIRMÉE | V63 | 1 |
| `UnifiedPositiveOfflineCase.certifiedMirrorSignature` | Toute trace OFF certifiée retenue est présente sur ce même vrai zéro. | CONFIRMÉE | AJOUT | 1 |
| `UnifiedPositiveOfflineCase.R1ThroughR11` | R1..R11 du retour grammaire/Tour réel sont portés par la réalisation maître du même zéro. | CONFIRMÉE | AJOUT | 1 |
| `UnifiedPositiveOfflineCase.pairSensitiveScientificBoundary` | La soudure de premier génuine spécifique à la paire est simultanément disponible pour le même zéro (écart nul, défaut de ligne, etc.). | CONFIRMÉE | V162 | 0 |
| `UnifiedPositiveOfflineCase.trueZeroDelta_ne_zero` | La coordonnée radiale du vrai zéro est non nulle exactement parce que le membre est hors ligne. | CONFIRMÉE | V102 | 0 |
| `UnifiedPositiveOfflineCase.e44RadialDefect_ne_zero` | Le défaut de β côté E44 est non nul à tout étage positif lorsque β est lu sur le même vrai zéro hors ligne. | CONFIRMÉE (domaine : étage m ≥ 1) | V102 | 1 |
| `UnifiedPositiveOfflineCase.e44MirrorDefect_sum` | Identité E44 de somme miroir : le miroir genuine porte le β complémentaire. | CONFIRMÉE | AJOUT | 0 |
| `UnifiedPositiveOfflineCase.not_R12` | La lecture interne R12 correctement typée est fausse sur le même cas maître hors ligne. | RÉFUTATION COMPILÉE (naturalité matricielle R12 dans le cas maître hors ligne unifié) | V140 | 1 |
| `UnifiedPositiveOfflineCase.no_common_E44_contact_pair` | Aucune paire de contacts E44 exacte ne peut décoder à la fois ce vrai membre hors ligne et son vrai miroir au même étage positif. | RÉFUTATION COMPILÉE (paire de contacts E44 commune au zéro hors ligne et à son miroir (condition m ≥ 1)) | V163 | 1 |
| `UnifiedPositiveOfflineCase.no_heightDetermined_leftInverse` | Aucune application déterminée par la seule hauteur ne peut avoir simultanément un inverse à gauche membre par membre sur cette constellation. | RÉFUTATION COMPILÉE (placement déterminé par la hauteur seule avec inverse à gauche membre par membre (cas hors ligne unifié)) | AJOUT | 0 |
| `UnifiedPositiveOfflineCase.E44Attachment.stage_pos` | Champ de E44Attachment : l'étage est ≥ 1. | CONFIRMÉE | AJOUT | 1 |
| `UnifiedPositiveOfflineCase.E44Attachment.law` | Champ : la paire de contacts (L,R) satisfait la loi E44 éliminée pour β du zéro. | CONFIRMÉE | V45 | 1 |
| `UnifiedPositiveOfflineCase.E44Attachment.criticalDefect_ne_zero` | Si une paire de contacts E44 est réellement attachée à ce membre hors ligne, son défaut critique (contacts seuls) est non nul. | CONFIRMÉE | V163 | 0 |
| `UnifiedPositiveOfflineCase.KnownConstraintPacket.quartet` | Le quartet a quatre membres. | CONFIRMÉE (domaine : paquet KnownConstraintPacket C (établi par knownConstraintPacket)) | V63 | 0 |
| `UnifiedPositiveOfflineCase.KnownConstraintPacket.signature` | Le zéro porte la signature OFF certifiée. | CONFIRMÉE (domaine : paquet KnownConstraintPacket C (établi par knownConstraintPacket)) | AJOUT | 0 |
| `UnifiedPositiveOfflineCase.KnownConstraintPacket.semantic` | R1..R11 tiennent. | CONFIRMÉE (domaine : paquet KnownConstraintPacket C (établi par knownConstraintPacket)) | AJOUT | 0 |
| `UnifiedPositiveOfflineCase.KnownConstraintPacket.pairSensitive` | Défaut de ligne de la paire à la première arête du bloc. | CONFIRMÉE (domaine : paquet KnownConstraintPacket C (établi par knownConstraintPacket)) | AJOUT | 0 |
| `UnifiedPositiveOfflineCase.KnownConstraintPacket.e44AllStages` | Défaut E44 de β non nul à tout étage m ≥ 1. | CONFIRMÉE (domaine : paquet KnownConstraintPacket C (établi par knownConstraintPacket)) | V102 | 0 |
| `UnifiedPositiveOfflineCase.KnownConstraintPacket.noCommonContact` | Aucune paire de contacts commune (L,R) pour le zéro et son miroir. | CONFIRMÉE (domaine : paquet KnownConstraintPacket C (établi par knownConstraintPacket)) | V163 | 0 |
| `UnifiedPositiveOfflineCase.KnownConstraintPacket.r12Fails` | La naturalité matricielle R12 échoue. | CONFIRMÉE (domaine : paquet KnownConstraintPacket C (établi par knownConstraintPacket)) | V140 | 0 |
| `UnifiedPositiveOfflineCase.knownConstraintPacket` | Tous les champs du paquet de contraintes connues sont des théorèmes ; aucune prémisse scientifique nouvelle. | CONFIRMÉE | AJOUT | 1 |
| `unifiedKnownConstraintsProduceR12_iff_masterR12Producer` | Le producteur unifié « contraintes connues ⟹ R12 » est exactement aussi fort que le producteur R12 maître. | CONFIRMÉE | V140 | 1 |
| `unifiedKnownConstraintsProduceR12_iff_riemannHypothesis` | Certificat de force exact du paquet même-objet entier connu : « contraintes connues ⟹ R12 » ⟺ RH. | ÉQUIVALENTE À RH (UnifiedKnownConstraintsProduceR12) | V140 | 0 |
| `false_of_independent_R12` | Dès qu'un théorème vraiment indépendant fournit R12 sur un cas hors ligne unifié, les deux côtés se contredisent littéralement (False). | RÉFUTATION COMPILÉE (naturalité matricielle R12 fournie sur un cas hors ligne unifié) | V140 | 0 |

### `RhGapCriterion.XiAGAggregateBudgetNoGo`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `aggregateOnly_blind` | Deux signatures agrégées égales sont indiscernables par toute observable agrégée seule. | CONFIRMÉE | AJOUT | 1 |
| `aggregateOnly_bool_no_separation` | Un certificat booléen agrégé seul ne peut accepter l'une de deux configurations de signature égale et rejeter l'autre. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.XiAGBudgetAndDensityBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `ZeroWindowBudget.total_nonneg` | Champ de ZeroWindowBudget : le total est ≥ 0. | CONFIRMÉE | AJOUT | 0 |
| `ZeroWindowBudget.onLine_nonneg` | Champ : la masse en ligne est ≥ 0. | CONFIRMÉE | AJOUT | 0 |
| `ZeroWindowBudget.offLine_nonneg` | Champ : la masse hors ligne est ≥ 0. | CONFIRMÉE | AJOUT | 0 |
| `ZeroWindowBudget.decomp` | Champ : total = en ligne + hors ligne. | CONFIRMÉE | AJOUT | 1 |
| `offLine_le_of_onLine_fraction` | Une borne inférieure c·total ≤ enLigne laisse au plus (1−c)·total de masse hors ligne. | CONFIRMÉE (domaine : hypothèses de budget (fraction en ligne, masse de paires, majorant)) | AJOUT | 1 |
| `pairMass_budget_of_onLine_fraction` | Si chaque point hors ligne A/G de hauteur positive compte pour deux zéros réfléchis, sa masse de paires est ≤ (1−c)·total/2. | CONFIRMÉE (domaine : hypothèses de budget (fraction en ligne, masse de paires, majorant)) | AJOUT | 1 |
| `agDegree_budget_of_onLine_fraction` | Même estimation pour une masse de degré A/G non négative dominée par la masse de paires. | CONFIRMÉE (domaine : hypothèses de budget (fraction en ligne, masse de paires, majorant)) | AJOUT | 2 |
| `agDegree_twoThirds_budget` | Conséquence algébrique sûre de la borne inférieure asymptotique 2/3−ε en ligne : 6·degré ≤ (1+3ε)·total (théorème d'interface). | CONFIRMÉE (domaine : hypothèses de budget (fraction en ligne, masse de paires, majorant)) | AJOUT | 0 |
| `agDegree_budget_of_total_majorant` | Combine une proportion en ligne avec un majorant du total de type Riemann–von Mangoldt : 2·degré ≤ (1−c)·majorant. | CONFIRMÉE (domaine : hypothèses de budget (fraction en ligne, masse de paires, majorant)) | AJOUT | 2 |
| `scaled_density_eventually_lt_one` | Tout multiple positif fixe d'une densité décroissante est finalement < 1. | CONFIRMÉE (domaine : C > 0, densité décroissante) | AJOUT | 2 |
| `nat_degree_zero_of_real_upper_lt_one` | Quantification entière : un degré entier de borne réelle < 1 est nul. | CONFIRMÉE (domaine : degré ≤ borne < 1) | AJOUT | 2 |
| `eventually_zero_of_degree_density_control` | Interface de clôture TDD : un degré entier borné par C fois une densité décroissante est nul à partir d'une hauteur. | CONFIRMÉE (domaine : C > 0, densité décroissante, degré ≤ C·densité) | AJOUT | 1 |
| `all_zero_of_prefix_and_eventual` | Lemme d'assemblage préfixe fini plus queue : le degré est nul partout. | CONFIRMÉE (domaine : préfixe fini et queue nuls) | AJOUT | 0 |

### `RhGapCriterion.XiAGCertifiedMirrorOffSignature`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `permanent_rightHalf_footprint_of_positive_offline` | Un zéro hors ligne de hauteur positive crée une empreinte entière permanente de moitié droite (degré ≥ 1 à partir d'une hauteur). | CONFIRMÉE SOUS CONDITION (zéro de hauteur > 0 hors ligne) | V63 | 1 |
| `hasCertifiedMirrorOffSignature_of_positive_offline` | Tout zéro vrai hors ligne de hauteur positive porte simultanément toutes les traces miroir retenues. | CONFIRMÉE SOUS CONDITION (zéro de hauteur > 0 hors ligne) | V62 | 3 |
| `hasCertifiedMirrorOffSignature_iff_positive_offline` | La signature OFF certifiée contient (et ne cache pas) les deux prédicats définissants : hauteur > 0 et β ≠ 1/2. | CONFIRMÉE | AJOUT | 0 |
| `noCertifiedMirrorOffSignature_of_riemannHypothesis` | RH exclut la signature OFF certifiée, parce que RH exclut le prédicat OFF qu'elle contient (RH en hypothèse). | CONFIRMÉE | V140 | 1 |
| `positive_height_critical_of_noCertifiedMirrorOffSignature` | Exclure la signature complète force tout zéro non trivial de hauteur positive à être central. | IMPLIQUE RH SOUS PRÉMISSE (NoCertifiedMirrorOffSignature (⟺ RH) ; conclusion : tout zéro non trivial de hauteur > 0 est critique (forme dépliée de RH sur les hauteurs positives)) | AJOUT | 1 |
| `riemannHypothesis_of_noCertifiedMirrorOffSignature` | Exclure la signature certifiée suffit à prouver l'énoncé RH de Mathlib ; les hauteurs négatives se traitent par conjugaison. | IMPLIQUE RH SOUS PRÉMISSE (NoCertifiedMirrorOffSignature (⟺ RH) ; conclusion RiemannHypothesis) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 1 |
| `noCertifiedMirrorOffSignature_iff_riemannHypothesis` | Certificat d'anti-circularité : interdire la signature OFF certifiée complète est exactement RH. | ÉQUIVALENTE À RH (NoCertifiedMirrorOffSignature) | AJOUT | 0 |

### `RhGapCriterion.XiAGConcreteRightHalfDegree`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `concreteRightHalfDegree_cast_eq_nprime` | Le degré concret de moitié droite est exactement le compteur analytique N'(1/2,T). | CONFIRMÉE | AJOUT | 3 |
| `concreteRightHalfDegree_mono` | Le degré concret est monotone en la coupure de hauteur. | CONFIRMÉE (domaine : T ≤ U) | AJOUT | 2 |
| `concreteRightHalfDegree_eq_neg_rectangle_re` | Le degré concret est exactement le compte réel du principe de l'argument sur tout rectangle rembourré. | CONFIRMÉE | AJOUT | 2 |
| `concreteRightHalfDegree_eq_zero_iff_bounded_critical_line` | Degré concret nul ⟺ tout zéro non trivial de hauteur ∈ ]0,T[ est critique (énoncé critique borné à hauteur positive). | CONFIRMÉE | AJOUT | 4 |
| `concreteRightHalfDegree_all_zero_of_eventually_zero` | Si le degré concret s'annule à partir d'une hauteur, la monotonie le force nul à toute hauteur finie. | CONFIRMÉE | AJOUT | 2 |
| `concreteRightHalfDegree_all_zero_of_decay_bound` | Instanciation concrète de l'interface à décroissance quantifiée : la borne brute force tous les degrés concrets à s'annuler. | CONFIRMÉE SOUS CONDITION (borne brute degré ≤ C·reste avec reste décroissant (prémisse nommée équivalente à RH par strictRightDecayCertificate_iff_riemannHypothesis)) | AJOUT | 2 |
| `positive_height_nontrivial_critical_of_concrete_decay_bound` | Prise de clôture de hauteur positive : une borne brute décroissante du compte de moitié droite force tout zéro non trivial de hauteur positive à être critique. | IMPLIQUE RH SOUS PRÉMISSE (borne brute décroissante du compte concret de moitié droite (⟺ RH) ; conclusion : tout zéro non trivial de hauteur > 0 est critique (forme dépliée de RH sur les hauteurs positives)) | AJOUT | 1 |
| `positive_height_nontrivial_critical_of_primeDensity_raw_bound` | La densité première instancie la moitié décroissance ; le pont de compte brut restant est exposé. | IMPLIQUE RH SOUS PRÉMISSE (borne brute par la densité première (⟺ RH) ; conclusion : tout zéro non trivial de hauteur > 0 est critique (forme dépliée de RH sur les hauteurs positives)) | AJOUT | 0 |

### `RhGapCriterion.XiAGPrimeDensityDecay`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `primeDensity_decaysToZeroAtInfinity` | La densité première π(⌊x⌋)/x tend vers 0 (borne supérieure asymptotique de Chebyshev). | CONFIRMÉE | AJOUT | 2 |
| `scaled_primeDensity_eventually_lt_one` | Tout multiple positif de la densité première est finalement < 1 (théorème d'échelle instancié). | CONFIRMÉE (domaine : C > 0) | AJOUT | 0 |

### `RhGapCriterion.XiAGRiemannVonMangoldtBudget`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `agDegree_budget_of_riemannVonMangoldt` | Une fraction en ligne et le majorant explicite RvM bornent la masse de degré A/G possible. | CONFIRMÉE SOUS CONDITION (borne de Riemann–von Mangoldt (b1,b2,b3) et hypothèses de budget) | AJOUT | 1 |
| `agDegree_twoThirds_budget_of_riemannVonMangoldt` | Spécialisation 2/3−ε de l'adaptateur RvM explicite ; conditionnel à la borne en ligne de type externe et à la borne RvM. | CONFIRMÉE SOUS CONDITION (borne de Riemann–von Mangoldt (b1,b2,b3) et hypothèses de budget) | AJOUT | 0 |
| `exists_agDegree_budget_of_crude_zeroCount` | Adaptateur du majorant polynomial existentiel inconditionnel de N(T) : ∃A>0, 2·degré ≤ … | CONFIRMÉE (domaine : hypothèses de budget et T ≥ 2) | AJOUT | 0 |

### `RhGapCriterion.XiAGTerminalClosureEquivalences`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `zeroFunction_decaysToZeroAtInfinity` | La fonction nulle est un reste décroissant positif valide. | CONFIRMÉE | AJOUT | 1 |
| `allConcreteRightHalfCountsZero_of_riemannHypothesis` | RH rend nul tout compte concret positif de moitié droite (RH en hypothèse). | CONFIRMÉE | V140 | 3 |
| `riemannHypothesis_of_allConcreteRightHalfCountsZero` | L'annulation de tous les comptes de moitié droite de hauteur positive entraîne RH (hauteurs négatives par conjugaison). | IMPLIQUE RH SOUS PRÉMISSE (AllConcreteRightHalfCountsZero (⟺ RH) ; conclusion RiemannHypothesis) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 3 |
| `allConcreteRightHalfCountsZero_iff_riemannHypothesis` | Classification exacte de la formulation par comptes nuls bruts : ⟺ RH. | ÉQUIVALENTE À RH (AllConcreteRightHalfCountsZero) | AJOUT | 0 |
| `allConcreteRightHalfCountsZero_of_eventually_subunit` | Un compte concret finalement sous-unitaire force un compte nul global par monotonie et intégralité. | CONFIRMÉE | AJOUT | 1 |
| `eventually_subunit_of_riemannHypothesis` | RH fournit trivialement la propriété finalement sous-unitaire (RH en hypothèse). | CONFIRMÉE | AJOUT | 1 |
| `eventuallyConcreteRightHalfCountSubunit_iff_riemannHypothesis` | Classification exacte de la formulation par quantification entière : ⟺ RH. | ÉQUIVALENTE À RH (EventuallyConcreteRightHalfCountSubunit) | AJOUT | 0 |
| `allConcreteRightHalfCountsZero_of_decayCertificate` | Une borne brute décroissante du compte force tous les comptes concrets à s'annuler. | CONFIRMÉE | AJOUT | 1 |
| `strictRightDecayCertificate_of_riemannHypothesis` | RH fournit le certificat de décroissance avec reste identiquement nul (RH en hypothèse). | CONFIRMÉE | AJOUT | 1 |
| `strictRightDecayCertificate_iff_riemannHypothesis` | La prise brute de décroissance actuelle a exactement la force de RH. | ÉQUIVALENTE À RH (StrictRightDecayCertificate) | AJOUT | 1 |
| `strictRightDecayCertificate_of_rawContour` | Le certificat de contour exact implique le certificat de compte brut. | CONFIRMÉE | AJOUT | 1 |
| `rawContourDecayCertificate_of_strictRight` | Réciproquement, l'identité exacte du principe de l'argument transporte toute borne de décroissance de compte brut à tous les rectangles rembourrés. | CONFIRMÉE | AJOUT | 1 |
| `rawRightHalfContourDecayCertificate_iff_strictRightDecayCertificate` | Les formulations de décroissance par contour et par compte brut sont littéralement équivalentes. | CONFIRMÉE | AJOUT | 1 |
| `rawRightHalfContourDecayCertificate_iff_riemannHypothesis` | Classification finale : l'énoncé de décroissance de contour de moitié droite exact est lui-même équivalent à RH. | ÉQUIVALENTE À RH (RawRightHalfContourDecayCertificate) | AJOUT | 0 |

### `RhGapCriterion.XiAGUnifiedExactInvariants`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `centeredSameHeightFirstMoment_eq` | Le moment premier centré de la paire de même hauteur vaut 2γi. | CONFIRMÉE | V102 | 0 |
| `centeredQuartetFirstMoment_eq_zero` | Le moment premier centré du quartet est nul. | CONFIRMÉE | V63 | 1 |
| `quartetRadialSecondMoment_eq` | Le second moment radial du quartet vaut 4x². | CONFIRMÉE | V63 | 2 |
| `quartetRadialSecondMoment_eq_zero_iff` | Le second moment radial du quartet est nul ⟺ x = 0. | CONFIRMÉE | AJOUT | 0 |
| `quartetRadialSecondMoment_pos_iff` | Le second moment radial du quartet est > 0 ⟺ x ≠ 0. | CONFIRMÉE | AJOUT | 1 |
| `mirror_quotient_coordinate_invariant` | La coordonnée quotient miroir est invariante : (−x)² = x². | CONFIRMÉE | AJOUT | 0 |
| `centeredQuartetPolynomial_closed_form` | Forme close du polynôme du quartet centré : z⁴ + 2(γ²−x²)z² + (x²+γ²)². | CONFIRMÉE | AJOUT | 0 |
| `centeredQuartetSquaredVariableDiscriminant_eq_zero_iff` | Le discriminant en variable carrée du quartet centré s'annule ⟺ x = 0. | CONFIRMÉE (domaine : γ ≠ 0 (et x ≠ 0 selon l'énoncé)) | AJOUT | 0 |
| `centeredQuartetSquaredVariableDiscriminant_neg` | Ce discriminant est strictement négatif pour x ≠ 0 (quartet hors ligne). | CONFIRMÉE (domaine : γ ≠ 0 (et x ≠ 0 selon l'énoncé)) | AJOUT | 0 |
| `implicitVelocity_equation` | Équation de la vitesse implicite : fy + ft·v = 0. | CONFIRMÉE (domaine : ft ≠ 0) | AJOUT | 0 |
| `implicitCurvature_equation` | Équation de la courbure implicite. | CONFIRMÉE (domaine : ft ≠ 0) | AJOUT | 0 |
| `AGVerticalPhaseSpeed_eq_zero_at_common_zero` | La vitesse de phase verticale A/G est nulle en un zéro commun (A=0, G=0). | CONFIRMÉE | AJOUT | 0 |
| `AGJacobian_at_common_zero_of_CR` | Jacobienne A/G au zéro commun sous Cauchy–Riemann : 2Ay² + 2y·Gy². | CONFIRMÉE (domaine : relations de Cauchy–Riemann au zéro commun) | AJOUT | 0 |

### `RhGapCriterion.ZeroPrimeCompleteGrammarBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `patternBlockOf_toShape` | La forme de motif d'un PatternBlock construit par patternBlockOf est la forme construite directement. | CONFIRMÉE | AJOUT | 0 |
| `completeGrammarBlock_pattern_eq_canonical` | Le champ motif de l'objet de grammaire complet est le PatternBlock canonique. | CONFIRMÉE | V48 | 0 |
| `completeGrammarBlock_transitions_eq_pattern_relation` | Le champ transitions est le champ relation du PatternBlock canonique (pas de cinquième relation). | CONFIRMÉE | V48 | 0 |
| `completeGrammarBlock_shape_eq_pattern_shape` | Le champ forme est la projection toShape du champ motif. | CONFIRMÉE | AJOUT | 0 |
| `prime_completeGrammarBlock_entry_eq_blockEntryState` | L'entrée de l'objet de grammaire complet premier est blockEntryState. | CONFIRMÉE | V48 | 0 |
| `prime_completeGrammarBlock_exit_eq_blockExitState` | La sortie de l'objet de grammaire complet premier est blockExitState. | CONFIRMÉE | V48 | 0 |
| `zero_completeGrammarBlock_entry_eq_zeroReconstructedBlockEntryState` | L'entrée de l'objet reconstruit est zeroReconstructedBlockEntryState. | CONFIRMÉE | V48 | 0 |
| `zero_completeGrammarBlock_exit_eq_zeroReconstructedBlockExitState` | La sortie de l'objet reconstruit est zeroReconstructedBlockExitState. | CONFIRMÉE | V48 | 0 |
| `completeGrammarBlock_family_is_the_canonical_family` | Le champ famille de l'objet premier est exactement la classe (0, 2 ou 4) déjà prouvée de l'écart mod 6. | CONFIRMÉE (domaine : 1 ≤ n+i) | V174 | 0 |
| `prime_completeGrammarBlock_globalDensity_eq_rank` | Côté premier, la densité globale se réduit au rang dans l'ordre réel de l'histoire. | CONFIRMÉE | V48 | 1 |
| `prime_completeGrammarBlock_globalDensityTheta_eq_thetaM` | Le champ densité θ de l'objet premier est le champ canonique θm. | CONFIRMÉE | V48 | 0 |
| `zero_completeGrammarBlock_globalDensityTheta_eq_zeroReconstructedTheta` | Le champ densité θ de l'objet reconstruit est zeroReconstructedTheta. | CONFIRMÉE | V48 | 0 |
| `zero_completeGrammarBlock_eq_prime_completeGrammarBlock` | Théorème central : l'objet de grammaire complet construit depuis les suites reconstruites des zéros égale celui construit depuis l'histoire première (M^Z = M complet, tous n, k). | CONFIRMÉE | V48 | 20 |
| `zero_prime_positions_eq_all_positions` | Les positions de l'objet reconstruit et de l'objet premier coïncident. | CONFIRMÉE | V48 | 2 |
| `zero_prime_gaps_eq_all_positions` | Les écarts coïncident. | CONFIRMÉE | V48 | 2 |
| `zero_prime_transitions_eq_all_positions` | Les transitions coïncident. | CONFIRMÉE | V48 | 2 |
| `zero_prime_pattern_object_eq_all_positions_all_lengths` | Le PatternBlock reconstruit égale le PatternBlock premier. | CONFIRMÉE | V48 | 2 |
| `zero_prime_shape_eq_all_positions_all_lengths` | La forme de motif reconstruite égale la forme première. | CONFIRMÉE | V48 | 1 |
| `zero_prime_family_eq_all_positions_all_lengths` | La famille reconstruite égale la famille première. | CONFIRMÉE | V48 | 2 |
| `zero_prime_entry_eq` | L'entrée de bord reconstruite égale la première. | CONFIRMÉE | V48 | 3 |
| `zero_prime_exit_eq` | La sortie de bord reconstruite égale la première. | CONFIRMÉE | V48 | 3 |
| `zero_prime_transition_order_eq` | La succession ordonnée des transitions reconstruite égale la première. | CONFIRMÉE | V48 | 2 |
| `zero_prime_pattern_order_eq` | La succession ordonnée des formes de motif reconstruite égale la première. | CONFIRMÉE | V48 | 2 |
| `zero_prime_family_order_eq` | La succession ordonnée des familles reconstruite égale la première. | CONFIRMÉE | V48 | 2 |
| `zero_prime_global_density_eq` | La densité globale reconstruite égale la première. | CONFIRMÉE | V48 | 1 |
| `zero_prime_global_density_theta_eq` | Le champ de densité θ reconstruit égale le premier. | CONFIRMÉE | V48 | 1 |
| `zero_prime_transitionSuccession_eq` | La succession de transitions reconstruite coïncide avec la première. | CONFIRMÉE | V48 | 3 |
| `zero_prime_familySuccession_eq` | La succession de familles reconstruite coïncide avec la première. | CONFIRMÉE | V48 | 3 |
| `zero_prime_patternSuccession_eq` | La succession de formes de motif reconstruite coïncide avec la première. | CONFIRMÉE | V48 | 3 |
| `zero_prime_patternShape_eq` | La forme de motif reconstruite coïncide avec la première. | CONFIRMÉE | V48 | 1 |
| `zero_prime_completeGrammar_positions_strictMono` | Les suites de positions reconstruite et première sont toutes deux strictement croissantes. | CONFIRMÉE | AJOUT | 0 |
| `zero_prime_block_positions_strictMono` | Les positions du bloc de grammaire complet premier sont strictement croissantes en l'indice interne. | CONFIRMÉE (domaine : i < j) | AJOUT | 0 |
| `zero_prime_complete_grammar_bridge` | Paquet terminal (Tour 10S) : conjonction du théorème central, des égalités champ par champ (positions, écarts, transitions, motif, famille, entrée/sortie, successions, densités). | CONFIRMÉE | V48 | 0 |

### `RhGapCriterion.ZeroPrimeCompleteGrammarOccurrences`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `zero_prime_pattern_occurrence_set_eq` | L'ensemble d'apparition d'un motif est identique entre histoire reconstruite et histoire première. | CONFIRMÉE | V48 | 3 |
| `zero_prime_pattern_occurrence_iff` | Une position est apparition du motif S dans l'histoire reconstruite ⟺ elle l'est dans l'histoire première. | CONFIRMÉE | V48 | 1 |
| `zero_prime_family_occurrence_set_eq` | L'ensemble d'apparition d'une famille est identique. | CONFIRMÉE | V48 | 3 |
| `zero_prime_family_occurrence_iff` | Une position est apparition de la famille f dans l'histoire reconstruite ⟺ dans l'histoire première. | CONFIRMÉE | V48 | 1 |
| `zero_prime_transition_occurrence_set_eq` | L'ensemble d'apparition d'une succession de transitions est identique. | CONFIRMÉE | V48 | 1 |
| `zero_prime_grammar_occurrence_set_eq` | L'ensemble d'apparition d'une propriété quelconque de l'objet de grammaire complet est identique. | CONFIRMÉE | V48 | 2 |
| `zero_prime_pattern_occurrence_initial_segment_eq` | Les apparitions du motif S dans [0,N) sont identiques entre les deux histoires. | CONFIRMÉE | V48 | 3 |
| `zero_prime_pattern_occurrence_count_eq` | Le nombre d'apparitions du motif S dans [0,N) est identique. | CONFIRMÉE | V48 | 2 |
| `zero_prime_pattern_occurrence_order_eq` | La liste ordonnée des positions d'apparition du motif S dans [0,N) est identique. | CONFIRMÉE | V48 | 1 |
| `zero_prime_family_occurrence_initial_segment_eq` | Les apparitions de la famille f dans [0,N) sont identiques. | CONFIRMÉE | V48 | 3 |
| `zero_prime_family_occurrence_count_eq` | Le nombre d'apparitions de la famille f dans [0,N) est identique. | CONFIRMÉE | V48 | 2 |
| `zero_prime_family_occurrence_order_eq` | La liste ordonnée des positions d'apparition de la famille f dans [0,N) est identique. | CONFIRMÉE | V48 | 1 |
| `zero_prime_entry_exit_eq_at_every_occurrence` | L'entrée et la sortie de bord des deux objets coïncident à toute occurrence. | CONFIRMÉE | V48 | 0 |
| `zero_prime_pattern_infinite_occurrence_iff` | Le motif S apparaît une infinité de fois dans l'histoire reconstruite ⟺ dans l'histoire première. | CONFIRMÉE | V48 | 1 |
| `zero_prime_family_infinite_occurrence_iff` | La famille f apparaît une infinité de fois dans l'histoire reconstruite ⟺ dans l'histoire première. | CONFIRMÉE | V48 | 1 |
| `zero_prime_grammar_infinite_occurrence_iff` | Une propriété P de l'objet de grammaire complet se produit une infinité de fois dans l'histoire reconstruite ⟺ dans l'histoire première. | CONFIRMÉE | V48 | 1 |
| `zero_prime_finite_ordered_succession_eq` | Les trois successions ordonnées finies (transitions, familles, motifs) coïncident entre histoire reconstruite et première. | CONFIRMÉE | V48 | 0 |
| `zero_prime_complete_grammar_occurrence_bridge` | Paquet terminal d'occurrences : égalité des ensembles, ordres, comptes, infinité, entrées/sorties (sans hypothèse). | CONFIRMÉE | V48 | 0 |

### `RhGapCriterion.ZeroPrimeExperimentRecovery`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `zero_reconstructed_first_fifteen_positions_eq_canonical` | Le préfixe expérimental exact de quinze positions reconstruit égale le préfixe canonique de l'histoire des nombres premiers. | CONFIRMÉE | V48 | 0 |
| `zero_reconstructed_experiment_positions_eq_canonical` | Les quarante-six positions premières du fichier expérimental predicted_events.csv sont exactement les positions canoniques reconstruites. | CONFIRMÉE | V48 | 0 |
| `zero_reconstructed_experiment_gaps_eq_canonical` | Les quarante-cinq écarts entre ces positions sont les écarts canoniques. | CONFIRMÉE | V48 | 0 |
| `zero_reconstructed_experiment_complete_grammar_eq` | L'objet de grammaire complet couvrant les 46 positions expérimentales est l'objet canonique. | CONFIRMÉE | V48 | 0 |

### `RhGapCriterion.ZeroPrimeGrammarCapture`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `zeroConstellationWindow_length` | Longueur exacte d'une fenêtre de constellation : min k (longueur de la vue ordonnée − n). | CONFIRMÉE | AJOUT | 1 |
| `zeroConstellationWindow_length_of_le` | Une fenêtre pleine porte exactement k membres. | CONFIRMÉE (domaine : fenêtre pleine n+k ≤ longueur) | AJOUT | 1 |
| `zeroConstellationWindowHeights_length` | Les hauteurs d'une fenêtre sont en bijection d'indice avec ses membres. | CONFIRMÉE | AJOUT | 2 |
| `zeroConstellationWindowGaps_length` | Loi k contre k−1 : une fenêtre de k membres porte exactement k−1 écarts internes. | CONFIRMÉE | AJOUT | 2 |
| `zeroConstellationWindowGaps_length_of_le` | Forme explicite de la loi précédente sur une fenêtre pleine. | CONFIRMÉE (domaine : fenêtre pleine n+k ≤ longueur) | AJOUT | 0 |
| `zeroTransitionSuccession_length` | Les transitions internes suivent la même loi : k−1 transitions pour k membres. | CONFIRMÉE | AJOUT | 0 |
| `zipWith_tail_getElem` | Lemme d'appariement générique : l'entrée i de zipWith f l l.tail compare les entrées i et i+1. | CONFIRMÉE (domaine : indice dans la longueur) | AJOUT | 1 |
| `zeroConstellationWindowGaps_getElem` | Loi d'indexation côté zéros : l'écart interne d'indice i est la différence des hauteurs des membres i+1 et i (grammaire par hauteurs). | CONFIRMÉE (domaine : indice dans la longueur) | V59 | 0 |
| `prime_completeGrammarBlock_gaps_getElem` | Loi d'indexation côté premiers : l'écart premier d'indice i est p(n+i+1) − p(n+i). | CONFIRMÉE | V48 | 0 |
| `prime_completeGrammarBlock_positions_getElem` | La position première capturée par l'indice i est p(n+i). | CONFIRMÉE | V48 | 0 |
| `complexZeroOrderKey_val` | La clé d'ordre générique sur ℂ et celle du sous-type sont la même fonction. | CONFIRMÉE | AJOUT | 0 |
| `zeroConstellationWindowHeights_canonical_full` | Les hauteurs de la constellation générique canonique sont celles de la constellation du Tour 26-B4. | CONFIRMÉE (domaine : longueur de la liste ordonnée ≤ k) | V59 | 1 |
| `zeroConstellationWindowGaps_canonical_full` | Les écarts internes de G^Z sont les écarts de constellation (fenêtre pleine). | CONFIRMÉE (domaine : longueur de la liste ordonnée ≤ k) | V59 | 5 |
| `sourceZeroChannel_canonical` | Le canal de la source canonique est le canal des zéros non triviaux de la formule explicite compilée. | CONFIRMÉE | V121 | 2 |
| `sourceSmoothedZeroFormula_canonical` | L'instance canonique de la formule paramétrée est smoothedZeroFormula. | CONFIRMÉE | V121 | 1 |
| `sourceSmoothedZeroPrimitive_canonical` | L'instance canonique de la primitive paramétrée est smoothedZeroPrimitive. | CONFIRMÉE | V121 | 1 |
| `sourcePsiRecovered_canonical` | ψ récupéré de la source canonique est psiRecoveredFromZeros. | CONFIRMÉE | V48 | 1 |
| `sourcePiMangoldt_canonical` | PiMangoldt de la source canonique est PiMangoldtFromZeros. | CONFIRMÉE | V48 | 1 |
| `sourcePrimeCountReal_canonical` | Le compte premier réel de la source canonique est zerosPrimeCountReal. | CONFIRMÉE | V48 | 1 |
| `sourcePrimeCount_canonical` | Le compte premier de la source canonique est zerosPrimeCount. | CONFIRMÉE | V48 | 3 |
| `sourcePrimePosition_canonical` | La position première de la source canonique est zerosPrimePosition. | CONFIRMÉE | V48 | 3 |
| `sourcePrimeGap_canonical` | L'écart premier de la source canonique est zerosPrimeGap. | CONFIRMÉE | V48 | 6 |
| `encodeZeroGrammar_congr_of_channel_eq` | Certificat de non-tautologie : toute la dépendance de l'encodeur en la source passe par son canal (canaux égaux ⟹ encodages égaux). | CONFIRMÉE | AJOUT | 2 |
| `encodeZeroGrammar_reads_source` | Certificat de lecture effective : le canal de l'encodeur est la somme sur les zéros membres de −mult·f_Perron(x,ρ). | CONFIRMÉE | V121 | 0 |
| `encodeZeroGrammar_canonical_eq_prime_grammar` | Théorème central Tour 10U : l'encodage de la grammaire canonique des zéros est le bloc de grammaire complet premier. | CONFIRMÉE | V48 | 7 |
| `capture_compatible_with_MZ_eq_M` | Compatibilité exacte avec M^Z = M : l'encodage canonique est le bloc reconstruit du Tour 10S. | CONFIRMÉE | V48 | 3 |
| `capture_compatible_with_prime_determined_zero_grammar` | Compatibilité avec prime_determined_zero_grammar_bridge : l'encodage de la grammaire de la source déterminée par les premiers égale le bloc de grammaire complet premier (pour toute continuation déterminée par les premiers). | CONFIRMÉE | V48 | 0 |
| `ZeroPrimeGrammarCapture.zeroSide_eq` | Champ de ZeroPrimeGrammarCapture : le côté zéros est la grammaire canonique de la fenêtre de la source. | CONFIRMÉE | AJOUT | 0 |
| `ZeroPrimeGrammarCapture.primeSide_eq` | Champ : le côté premier est l'encodage de la source. | CONFIRMÉE | AJOUT | 0 |
| `capture_encodes_canonical_prime_grammar` | La capture canonique encode exactement le bloc grammatical premier canonique. | CONFIRMÉE | V48 | 13 |
| `capture_preserves_member_order` | Ordre des membres conservé : le côté zéros porte la vue ordonnée exacte. | CONFIRMÉE | AJOUT | 0 |
| `capture_preserves_window` | La fenêtre ordonnée des membres capturés est conservée. | CONFIRMÉE | AJOUT | 0 |
| `capture_preserves_transitions` | Transitions conservées côté premier. | CONFIRMÉE | V48 | 1 |
| `capture_preserves_transition_succession` | Succession des transitions conservée. | CONFIRMÉE | V48 | 0 |
| `capture_preserves_patterns` | Motifs conservés. | CONFIRMÉE | V48 | 1 |
| `capture_preserves_shape` | Formes de motif conservées. | CONFIRMÉE | V48 | 0 |
| `capture_preserves_pattern_order` | Ordre des motifs conservé. | CONFIRMÉE | V48 | 0 |
| `capture_preserves_families` | Familles conservées. | CONFIRMÉE | V48 | 1 |
| `capture_preserves_family_order` | Ordre des familles conservé. | CONFIRMÉE | V48 | 0 |
| `capture_preserves_entry` | Entrée conservée. | CONFIRMÉE | V48 | 1 |
| `capture_preserves_exit` | Sortie conservée. | CONFIRMÉE | V48 | 1 |
| `capture_preserves_positions` | Positions capturées conservées : occurrences dans l'histoire première p(n+i). | CONFIRMÉE | V48 | 0 |
| `capture_preserves_gaps` | Écarts capturés conservés avec leur loi d'indexation exacte. | CONFIRMÉE | V48 | 2 |
| `capture_preserves_occurrences` | Densité globale conservée : rang exact dans l'histoire première. | CONFIRMÉE | V48 | 0 |

### `RhGapCriterion.ZeroPrimeIntruderExclusion`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `gnat_pos` | Tout écart entre deux premiers consécutifs est strictement positif. | CONFIRMÉE | AJOUT | 18 |
| `gnat_no_defect` | Aucun écart premier canonique ne vaut 0 (pas de défaut d'écart premier). | CONFIRMÉE | AJOUT | 1 |
| `canonical_prime_grammar_has_no_captured_zero_gap_defect` | La grammaire première canonique n'admet le défaut d'écart nul capturé à aucun indice (inconditionnel). | CONFIRMÉE | AJOUT | 1 |
| `capture_prime_side_has_no_defect` | Le côté premier de la capture canonique n'admet le défaut à aucun indice. | CONFIRMÉE | AJOUT | 1 |
| `intruder_gives_captured_zero_gap_defect` | Un intrus produit un défaut (écart nul) dans la grammaire interne des zéros G^Z : l'écart nul est lu dans la grammaire zéros. | CONFIRMÉE SOUS CONDITION (représentant positif hors ligne (intrus) dans une constellation en bande ouverte) | V162 | 1 |
| `critical_line_gives_no_captured_zero_gap_defect` | Une constellation entièrement sur la ligne critique ne porte jamais de défaut d'écart nul dans G^Z. | CONFIRMÉE (domaine : constellation entièrement critique, longueur ≤ k) | V161 | 1 |
| `capture_defect_preservation_forbids_zero_gap` | Chaîne A : si la capture conservait le défaut, les écarts de G^Z ne seraient jamais nuls (contradiction avec la grammaire première sans défaut). | CONFIRMÉE SOUS CONDITION (conservation du défaut par la capture (CapturePreservesIntruderDefect, prémisse nommée)) | AJOUT | 2 |
| `capture_defect_preservation_forces_critical_line` | Chaîne A (suite) : sous la conservation du défaut, aucun membre de la constellation n'est hors ligne (exclusion locale de l'intrus). | CONFIRMÉE SOUS CONDITION (conservation du défaut par la capture (CapturePreservesIntruderDefect, prémisse nommée) ; conclusion : tout représentant positif de la constellation bornée est critique) | AJOUT | 2 |
| `capture_defect_preservation_forces_critical_line_via_gap_positivity` | Chaîne B : même conclusion par la positivité des écarts capturés. | CONFIRMÉE SOUS CONDITION (conservation du défaut par la capture (CapturePreservesIntruderDefect, prémisse nommée) ; conclusion : tout représentant positif de la constellation bornée est critique) | AJOUT | 0 |
| `captured_gaps_pos_iff_critical_line` | Tous les écarts capturés sont strictement positifs ⟺ tous les membres capturés sont sur la ligne critique. | CONFIRMÉE (domaine : longueur ≤ k et représentants en bande ouverte) | V161 | 0 |
| `capture_defect_preservation_iff_critical_line` | Portée exacte du Tour 10U : la conservation du défaut par la capture ⟺ tous les représentants positifs de la constellation sont critiques. | CONFIRMÉE (domaine : longueur ≤ k et représentants en bande ouverte) | AJOUT | 2 |
| `capture_prime_side_is_intruder_insensitive` | Insensibilité du côté premier capturé (résultat négatif inconditionnel) : l'écart premier capturé ne dépend pas de la hauteur de coupure T. | CONFIRMÉE | AJOUT | 0 |
| `no_encoder_transports_the_defect` | Aucun encodeur de la grammaire des zéros vers la grammaire première ne transporte le défaut (résultat négatif universel). | RÉFUTATION COMPILÉE (encodeur qui transporte le défaut d'écart nul (E ∘ G^Z = M)) | AJOUT | 1 |
| `defect_transporting_encoder_breaks_capture` | Corollaire : un encodeur qui transporte effectivement le défaut ne peut plus encoder la grammaire première canonique (les deux exigences sont incompatibles). | RÉFUTATION COMPILÉE (encodeur transportant le défaut de la capture (les deux exigences du plan incompatibles)) | AJOUT | 0 |
| `bounded_critical_line_gives_global` | Passage borné vers global : si tout membre de toute constellation bornée est critique, tout zéro non trivial l'est. | IMPLIQUE RH SOUS PRÉMISSE (tout membre de toute constellation bornée est sur la ligne (bornée-critique universelle) ; conclusion ∀ρ non trivial, β=1/2 (forme dépliée de RH)) | AJOUT | 3 |
| `capture_defect_preservation_everywhere_gives_rh` | Composition terminale du Tour 10U : la conservation du défaut universelle donne la criticité de tout zéro non trivial. | IMPLIQUE RH SOUS PRÉMISSE (conservation du défaut par la capture pour toute constellation bornée (⟺ bornée-critique ⟺ RH) ; conclusion ∀ρ non trivial, β=1/2 (forme dépliée de RH)) | AJOUT | 0 |

### `RhGapCriterion.ZeroPrimeReconstruction`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `piCount_le_one` | Aucun premier < 2 : piCount m = 0 pour m ≤ 1. | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou m ≤ 1 selon l'énoncé)) | AJOUT | 2 |
| `piReal_rpow_eq_zero_of_log_lt` | 23-A support : pour m > log₂⌊x⌋, x^(1/m) < 2 donc π(x^(1/m)) = 0. | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou m ≤ 1 selon l'énoncé)) | AJOUT | 2 |
| `PiWeighted_truncation_stable` | 23-A stabilité de troncature : deux troncatures au-delà donnent la même valeur de PiWeighted. | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou m ≤ 1 selon l'énoncé)) | AJOUT | 1 |
| `rpow_one_div_mul` | Composition exacte des puissances réelles : (x^(1/m))^(1/k) = x^(1/(mk)). | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou m ≤ 1 selon l'énoncé)) | AJOUT | 1 |
| `sum_divisors_moebius_eq_ite` | Noyau de Möbius : Σ_{d∣N} μ(d) = [N = 1]. | CONFIRMÉE | AJOUT | 1 |
| `pi_from_PiWeighted_moebius` | 23-C : inversion de Möbius exacte : π(x) = Σ μ(m)/m · PiWeighted(x^(1/m)). | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou m ≤ 1 selon l'énoncé)) | V48 | 1 |
| `piCount_p` | π(p_n) = n+1. | CONFIRMÉE | AJOUT | 5 |
| `piCount_lt_p` | Sous p_n, le comptage reste ≤ n (minimalité de la position). | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou 2 selon l'énoncé)) | AJOUT | 2 |
| `posOfCount_piCount_eq_p` | 23-D(i) : inversion exacte du comptage : min{m : π(m) = n+1} = p_n. | CONFIRMÉE | V48 | 1 |
| `reconstruction_positions_of_counting_eq` | 23-D(ii) fidélité des positions : toute fonction de comptage égale à π sur tout entier reconstruit les positions p_n. | CONFIRMÉE | V48 | 2 |
| `reconstruction_gaps_of_counting_eq` | 23-E fidélité des écarts : la même hypothèse d'égalité des comptages donne posOfCount(n+1) − posOfCount(n) = gnat n. | CONFIRMÉE | V48 | 1 |
| `primes_determine_zeta_in_halfplane` | 23-F (moitié prouvée) : le produit d'Euler sur les premiers détermine ζ dans Re s > 1. | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou m ≤ 1 selon l'énoncé)) | AJOUT | 1 |

### `RhGapCriterion.ZeroPrimeTerminalReconstruction`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `zeros_weighted_count_eq_arithmetic_weighted_count` | Le compte pondéré reconstruit depuis les zéros égale le compte pondéré arithmétique à la troncature canonique. | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou 2 selon l'énoncé)) | V48 | 4 |
| `canonicalPiCutoff_eq_natLogFloor` | La troncature canonique est ⌊log₂⌊x⌋⌋ (Nat.log 2 ⌊x⌋). | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou 2 selon l'énoncé)) | AJOUT | 7 |
| `canonicalPiCutoff_one_le` | La troncature canonique est ≥ 1. | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou 2 selon l'énoncé)) | AJOUT | 1 |
| `canonicalPiCutoff_mono` | La troncature canonique est monotone sur [1,∞) (inconditionnel). | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou 2 selon l'énoncé)) | AJOUT | 3 |
| `mem_canonicalPiCutoff_iff_pow_le` | Caractérisation exacte du seuil : m ≤ troncature(t) ⟺ 2^m ≤ t. | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou 2 selon l'énoncé)) | AJOUT | 4 |
| `Icc_canonicalPiCutoff_subset` | L'ensemble de troncature en t est inclus dans celui en x pour 2 ≤ t ≤ x. | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou 2 selon l'énoncé)) | AJOUT | 0 |
| `rpow_one_div_ge_two_of_mem_canonical_cutoff` | Pour m dans la troncature canonique de x, x^(1/m) ≥ 2. | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou 2 selon l'énoncé)) | AJOUT | 6 |
| `canonicalPiCutoff_rpow_le` | La troncature de x^(1/m) est ≤ celle de x. | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou 2 selon l'énoncé)) | AJOUT | 1 |
| `zerosWeightedCount_eq_PiWeighted_of_admissible_cutoff` | Le compte pondéré reconstruit égale PiWeighted x M pour toute troncature admissible. | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou 2 selon l'énoncé)) | V48 | 1 |
| `zerosPrimeCountReal_eq_piReal` | Le compte premier réel reconstruit depuis les zéros égale π(x). | CONFIRMÉE (domaine : domaine numérique (x ≥ 1 ou 2 selon l'énoncé)) | V48 | 10 |
| `zeros_prime_count_eq_prime_count` | Le compte premier entier reconstruit égale piCount. | CONFIRMÉE | V48 | 8 |
| `zeros_prime_positions_eq_prime_positions` | La position première reconstruite égale p n. | CONFIRMÉE | V48 | 23 |
| `zeros_prime_gaps_eq_prime_gaps` | L'écart premier reconstruit égale gnat n. | CONFIRMÉE | V48 | 23 |

### `RhGapCriterion.ZeroReconstructedMetaPattern`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `zero_reconstructed_any_derived_object_eq` | Transport universel : toute construction déterministe F des deux suites (positions, écarts) donne la même valeur sur les suites reconstruites et sur (p, gnat). | CONFIRMÉE | V48 | 26 |
| `zero_reconstructed_any_count_position_gap_object_eq` | Transport universel avec comptage : toute construction déterministe des trois suites (comptage, positions, écarts) est invariante. | CONFIRMÉE | V48 | 6 |
| `zero_reconstructed_relations_eq` | Les états mod 6 (1 ou 5) et les quatre relations primitives obtenues à part depuis les positions/écarts reconstruits. | CONFIRMÉE (domaine : n ≥ 2) | V174 | 2 |
| `zero_reconstructed_patterns_eq` | Motifs : tout bloc ordonné d'écarts sur k positions consécutives depuis n ≥ 2 vérifie les relations mod 6 sur les suites reconstruites. | CONFIRMÉE (domaine : n ≥ 2) | V174 | 1 |
| `zero_reconstructed_pattern_object_eq` | Égalité d'objet : le bloc de motif construit depuis les suites reconstruites égale le bloc premier. | CONFIRMÉE | V48 | 4 |
| `zero_reconstructed_patterns_eq_of_object` | Le résultat sur les motifs redémontré comme conséquence de l'égalité d'objet. | CONFIRMÉE (domaine : n ≥ 2) | V174 | 0 |
| `zero_reconstructed_families_eq` | Familles : le classificateur canonique appliqué aux écarts reconstruits donne une classe unique dans {0,2,4}. | CONFIRMÉE (domaine : n ≥ 1) | V174 | 2 |
| `zero_reconstructed_family_classifier_eq` | Transport universel de tout classificateur de famille. | CONFIRMÉE | V48 | 2 |
| `zero_reconstructed_order_eq` | Ordre réel : la suite des positions reconstruites est p (extensionnellement), strictement croissante, et les écarts sont gnat. | CONFIRMÉE | V48 | 3 |
| `zero_reconstructed_order_constructor_eq` | Transport universel de tout constructeur d'ordre. | CONFIRMÉE | V48 | 2 |
| `zero_reconstructed_density_fields_eq` | Quatre champs de densité reconstruits (comptage, π réel, θ, ψ) égaux à leurs analogues canoniques (ψ = Chebyshev.psi pour x ≥ 2). | CONFIRMÉE | V48 | 1 |
| `zero_reconstructed_gap_innovation_eq` | Innovation exacte : gap reconstruit − log(position reconstruite) = gnat n − log p n. | CONFIRMÉE | AJOUT | 2 |
| `zero_reconstructed_signed_contribution_eq_aT` | La contribution signée reconstruite coïncide avec aT. | CONFIRMÉE | AJOUT | 5 |
| `zero_reconstructed_S6_eq` | zeroReconstructedS6 = S6. | CONFIRMÉE | AJOUT | 1 |
| `zero_reconstructed_modes_eq` | Les modes T, B, O reconstruits égalent les modes canoniques. | CONFIRMÉE | AJOUT | 3 |
| `zero_reconstructed_energy_term_eq` | Le terme d'énergie reconstruit égale energyTerm aT. | CONFIRMÉE | AJOUT | 3 |
| `zero_reconstructed_energy_partition_eq` | Partition d'énergie : le noyau d'énergie reconstruit et sa partition par toute classification de paires sont égaux aux canoniques. | CONFIRMÉE | AJOUT | 3 |
| `zero_reconstructed_pair_classes_eq` | Transport universel de tout classificateur de paires. | CONFIRMÉE | V48 | 2 |
| `zero_reconstructed_pair_classes_and_energy_eq` | Lien explicite entre l'égalité du classificateur de paires et l'égalité de la somme d'énergie. | CONFIRMÉE | V48 | 0 |
| `zero_reconstructed_cycle_relations_eq` | Transport universel de toute relation de cycle (version classificatrice). | CONFIRMÉE | V48 | 1 |
| `zero_reconstructed_cycle_relation_prop_eq` | Transport universel de toute relation de cycle (version propositionnelle). | CONFIRMÉE | V48 | 0 |
| `zero_reconstructed_complete_metapattern_eq` | Clôture renforcée du transport complet du méta-motif : états mod 6, relations, motifs, familles, ordre, champs de densité (composition des résultats précédents). | CONFIRMÉE | V174 | 0 |

### `RhGapCriterion.ZeroSourceFidelityAudit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `sourceZeroResidueTerm_eq_zero_of_mult_eq_zero` | Le terme de résidu d'un point de multiplicité nulle est nul. | CONFIRMÉE (domaine : multiplicité nulle en w (et w non membre pour 1713)) | AJOUT | 1 |
| `sourceZeroChannel_adjoin_null_member` | Le canal ne voit pas l'adjonction d'un point de multiplicité nulle à la source. | CONFIRMÉE (domaine : multiplicité nulle en w (et w non membre pour 1713)) | AJOUT | 2 |
| `adjoin_null_member_ne` | Les deux sources (avec et sans w adjoint) sont distinctes dès que w n'était pas membre. | CONFIRMÉE (domaine : multiplicité nulle en w (et w non membre pour 1713)) | AJOUT | 2 |
| `encodeZeroGrammar_adjoin_null_member` | La grammaire encodée ne voit pas non plus l'adjonction. | CONFIRMÉE (domaine : multiplicité nulle en w (et w non membre pour 1713)) | AJOUT | 1 |
| `sourceZeroChannel_not_injective` | Non-injectivité du canal sur ZeroSource : deux sources distinctes de même canal existent. | CONFIRMÉE | AJOUT | 0 |
| `encodeZeroGrammar_not_injective` | Non-injectivité de l'encodeur complet, pour toute fenêtre (n,k). | CONFIRMÉE | AJOUT | 0 |
| `isNormalizedZeroSource_canonical` | La source canonique est normalisée (multiplicité nulle hors zéros non triviaux). | CONFIRMÉE | AJOUT | 0 |
| `normalized_eq_of_mult_eq` | Une source normalisée est entièrement déterminée par sa multiplicité. | CONFIRMÉE (domaine : sources normalisées de même multiplicité) | AJOUT | 0 |
| `adjoin_null_member_not_normalized` | Le témoin d'adjonction n'est jamais normalisé : la normalisation exclut la collision exhibée. | CONFIRMÉE (domaine : multiplicité nulle en w (et w non membre pour 1713)) | AJOUT | 0 |
| `zeroHeightSet_ignores_mult` | L'ensemble des zéros de hauteur bornée d'une source ne lit que le champ member (pas la multiplicité). | CONFIRMÉE | AJOUT | 0 |
| `zeroOrderedMembers_ignores_mult` | La vue ordonnée générique ne lit que le champ member. | CONFIRMÉE | AJOUT | 0 |
| `zeroConstellationWindow_blind_to_multiplicity` | La fenêtre de constellation est universellement aveugle à la multiplicité. | CONFIRMÉE | AJOUT | 0 |
| `zeroConstellationWindowHeights_blind_to_multiplicity` | Les hauteurs de la fenêtre sont aveugles à la multiplicité. | CONFIRMÉE | AJOUT | 0 |
| `zeroConstellationWindowGaps_blind_to_multiplicity` | Les écarts de la fenêtre sont aveugles à la multiplicité. | CONFIRMÉE | AJOUT | 0 |
| `zeroCountUpTo_blind_to_multiplicity` | Le comptage de zéros par hauteur est aveugle à la multiplicité : il compte des points, pas des zéros avec multiplicité. | CONFIRMÉE | AJOUT | 0 |
| `isNormalizedZeroSource_double_mult` | Doubler la multiplicité d'une source normalisée donne une source normalisée : la cécité à la multiplicité survit à la normalisation. | CONFIRMÉE (domaine : S source normalisée) | AJOUT | 0 |

### `RhGapCriterion.ZetaConjugationOrbit`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `natCast_arg_ne_pi` | Un entier naturel plongé dans ℂ a un argument différent de π. | CONFIRMÉE | AJOUT | 1 |
| `conj_natCast_cpow` | La conjugaison commute avec la puissance complexe d'un entier naturel. | CONFIRMÉE | AJOUT | 2 |
| `conj_one_div_natCast_cpow` | Conjugaison du terme général 1/n^s de la série de Dirichlet. | CONFIRMÉE | AJOUT | 1 |
| `riemannZeta_conj_eq_of_one_lt_re` | Dans Re s > 1, conj(ζ(s)) = ζ(conj s). | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `conj_ne_one_iff` | conj s ≠ 1 ⟺ s ≠ 1. | CONFIRMÉE | AJOUT | 3 |
| `differentiableAt_conjRiemannZetaConj` | conj ∘ ζ ∘ conj est différentiable en tout s ≠ 1. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `analyticOnNhd_conjRiemannZetaConj` | conj ∘ ζ ∘ conj est analytique sur ℂ∖{1}. | CONFIRMÉE | AJOUT | 2 |
| `riemannZeta_eq_conjRiemannZetaConj_of_one_lt_re` | Pour Re s > 1, ζ(s) = (conj ∘ ζ ∘ conj)(s). | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `riemannZeta_eventuallyEq_conjRiemannZetaConj` | ζ et conj ∘ ζ ∘ conj coïncident sur un voisinage de 2 (demi-plan Re > 1). | CONFIRMÉE | AJOUT | 1 |
| `riemannZeta_eq_conjRiemannZetaConj` | Principe d'identité (réflexion de Schwarz) pour ζ, sans RH : ζ = conj ∘ ζ ∘ conj partout hors 1. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | V63 | 3 |
| `riemannZeta_conj` | Réalité analytique globale de ζ, sans RH : conj(ζ(s)) = ζ(conj s) pour s ≠ 1. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | V63 | 2 |
| `riemannZeta_conj_eq_zero_of_zero` | Si ρ est un zéro de ζ, conj ρ en est un aussi : les zéros sont stables par conjugaison (hypothèse : ρ zéro). | CONFIRMÉE | V63 | 10 |
| `iteratedDeriv_conj_conj` | La n-ième dérivée itérée de conj ∘ f ∘ conj en x est conj de celle de f en conj x. | CONFIRMÉE | AJOUT | 1 |
| `analyticOrderNatAt_conjRiemannZetaConj_eq_riemannZeta_conj` | L'ordre analytique de conj ∘ ζ ∘ conj en ρ égale celui de ζ en conj ρ. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | V63 | 1 |
| `analyticOrderNatAt_riemannZeta_eq_conjRiemannZetaConj` | ζ et conj ∘ ζ ∘ conj ont le même ordre analytique en tout ρ ≠ 1. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | V63 | 1 |
| `zetaZeroMultiplicity_conj` | Conservation exacte de la multiplicité analytique sous conjugaison : m(ρ̄) = m(ρ) pour tout zéro ρ de ζ. | CONFIRMÉE | V12 | 8 |
| `zetaConjugationReflectionOrbit_zero` | Les quatre points de l'orbite conjugaison/réflexion d'un zéro de la bande sont des zéros de ζ. | CONFIRMÉE (domaine : 0 < β < 1 et ρ zéro de zêta) | V63 | 0 |
| `zetaConjugationReflectionOrbit_multiplicity_eq` | Orbite complète à multiplicités égales : conjugué, réfléchi et conjugué du réfléchi ont la multiplicité de ρ. | CONFIRMÉE (domaine : 0 < β < 1 et ρ zéro de zêta) | V63 | 1 |

### `RhGapCriterion.ZetaExactModalProjectionP5`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `explicit_formula_zero_mode_amplitude_ne_zero` | L'amplitude du mode zéro dans la formule explicite est non nulle pour tout zéro non trivial. | CONFIRMÉE | V101 | 2 |
| `residue_unsmoothedZetaPerronIntegrand_at_zero` | Le résidu de l'intégrande de Perron non lissé en un zéro non trivial est −m(ρ)·x^ρ/ρ : le terme q^ρ/ρ du zéro dans la formule explicite. | CONFIRMÉE (domaine : x > 0) | V100 | 2 |
| `exp_cpow_zero_mode_identity` | Identité exp(−U/2)·(e^U)^ρ = exp((ρ − 1/2)U) : le mode zéro en la variable U = log x (β−1/2 dans l'exposant réel). | CONFIRMÉE | V100 | 2 |
| `explicit_formula_zero_mode` | La projection de résidu de Perron d'un zéro est un mode zéro d'amplitude explicite : forme modale exacte. | CONFIRMÉE | V100 | 1 |
| `exact_modal_projection_from_explicit_formula` | Le canal projeté de la formule explicite est exactement le mode zéro d'amplitude explicite. | CONFIRMÉE | V100 | 6 |

### `RhGapCriterion.ZetaHeightReflection`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `mem_criticalStripHeightZerosFinset_raw` | Caractérisation brute de l'ensemble fini des zéros de hauteur bornée de la bande critique, avec enveloppe radiale. | CONFIRMÉE | AJOUT | 1 |
| `mem_criticalStripHeightZerosFinset_iff` | Pour T ≥ 0, l'ensemble fini filtré est exactement la troncature par hauteur de la bande critique fermée. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 2 |
| `criticalStripHeightZerosFinset_mono` | Les troncatures exactes par hauteur sont monotones. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 0 |
| `zetaReflect_re` | zetaReflect ρ a partie réelle 1−β. | CONFIRMÉE | V65 | 0 |
| `zetaReflect_im` | zetaReflect ρ a partie imaginaire −γ (zéro réfléchi 1−ρ). | CONFIRMÉE | V80 | 1 |
| `zetaReflect_involutive` | zetaReflect est une involution. | CONFIRMÉE | AJOUT | 0 |
| `abs_zetaReflect_im` | ∣Im(zetaReflect ρ)∣ = ∣Im ρ∣. | CONFIRMÉE | AJOUT | 0 |
| `ne_neg_nat_of_re_pos` | Un point de partie réelle > 0 n'est aucun entier naturel négatif. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `riemannZeta_zetaReflect_eq_zero` | La formule fonctionnelle transporte tout zéro de partie réelle positive vers le zéro réfléchi 1−ρ. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | V62 | 9 |
| `zetaReflect_mem_criticalStripHeightZerosFinset` | La réflexion conserve la troncature de hauteur et la bande pour un zéro strictement intérieur. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 0 |
| `criticalStripHeightZeroSum_add` | Linéarité exacte de la somme spectrale finie par hauteur. | CONFIRMÉE | AJOUT | 0 |
| `criticalStripHeightZeroSum_zero` | La somme spectrale finie du zéro fonction est nulle. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ZetaHorizontalLogDerivBoundP4_4c`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `P4_4c.fin_orderIso_positive_nat_bound` | Dans l'isomorphisme d'ordre d'un ensemble d'entiers positifs, l'élément d'indice i est ≥ i+1. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.inv_orderIso_le_inv_succ` | L'inverse de l'élément d'indice i est ≤ 1/(i+1). | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.sum_inv_natCast_le_harmonic_card` | La somme des 1/k sur un ensemble d'entiers positifs est ≤ le nombre harmonique de son cardinal. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 2 |
| `P4_4c.harmonic_mono_real` | Le nombre harmonique est monotone. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 4 |
| `P4_4c.grid_distance_eq_abs_sub_u_div` | Distance sur la grille : ∣H+(j+1/2)/M − x∣ = ∣j − (M(x−H)−1/2)∣/M. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 3 |
| `P4_4c.grid_not_close_abs_sub_u_ge_quarter` | Un point de grille pas proche est à distance normalisée ≥ 1/4. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 0 |
| `P4_4c.grid_not_close_inverse_le_fourM` | L'inverse de la distance d'un point de grille pas proche est ≤ 4M. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 0 |
| `P4_4c.left_far_norm_inv_le` | Borne d'inverse de distance pour les points de grille loin à gauche. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.right_far_norm_inv_le` | Borne d'inverse de distance pour les points loin à droite. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.left_far_norm_sum_le_harmonic` | Somme des inverses loin à gauche ≤ nombre harmonique de M. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.right_far_norm_sum_le_harmonic` | Somme des inverses loin à droite ≤ nombre harmonique de M. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.normalized_grid_inverse_sum_le` | Somme normalisée des inverses de grille ≤ 16(1+H_M). | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.grid_close_iff_norm_close` | Proximité de grille ⟺ proximité normalisée. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.grid_inverse_eq_M_mul_norm_inv` | Inverse de distance de grille = M fois l'inverse de la distance normalisée. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.grid_inverse_distance_sum_le_harmonic` | Somme des inverses de distances de grille non proches ≤ 16·M·(1+H_M). | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.grid_point_mem_Ioo` | Les points de grille sont dans ]H, H+1[. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.grid_point_diff_abs` | Différence de deux points de grille = ∣j−k∣/M. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.grid_close_index_unique` | Deux indices de grille proches d'un même x sont égaux. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.grid_bad_card_le` | Le nombre d'indices de grille proches d'une des valeurs ∣a p∣ est ≤ card S. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.exists_le_of_sum_le_card_mul` | Si ∑f ≤ card·B, il existe x avec f x ≤ B. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.exists_grid_point_with_separation_and_inverse_sum` | Existence d'une hauteur T ∈ ]H,H+1[ séparée des ∣a p∣ avec somme des inverses ≤ 64·M·(1+H_M). | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.grid_harmonic_constant_le_power` | 64M(1+H_M) ≤ (512 + 64/θ·4^(1+θ))·(n+1)^(1+θ). | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.exists_height_with_separation_and_inverse_sum_bound` | Existence d'une hauteur T à séparation et somme d'inverses contrôlées avec constante Kθ. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.hadamard_pair_eq` | Identité de paire de Hadamard : 1/(s−ρ) + 1/ρ = s/(ρ(s−ρ)). (terme hors maître « Hadamard » : produit de Hadamard de ξ (diviseurs de ξ) ; outil analytique des bornes de −ζ'/ζ) | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.hadamard_far_term_norm_le` | Borne d'un terme de Hadamard lointain. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.mem_xiDivisorNearFinset` | Appartenance à l'ensemble proche des diviseurs de ξ ⟺ ‖valeur‖ ≤ R. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 2 |
| `P4_4c.xiDivisorNearFinset_card_le_divisorMassClosedBall₀` | Le nombre de diviseurs proches est ≤ la masse de diviseurs de ξ dans la boule fermée. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.completedZetaFactor_eq_riemannXi_of_im_ne_zero` | Le facteur de zêta complétée de Kadiri égale ξ hors de l'axe réel. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 2 |
| `P4_4c.completedZetaFactor_eventuallyEq_riemannXi_of_im_ne_zero` | Ils coïncident sur un voisinage. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.logDeriv_completedZetaFactor_eq_riemannXi_of_im_ne_zero` | Leurs dérivées logarithmiques coïncident hors de l'axe réel. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.xiDivisorZ₂_nonneg` | La constante xiDivisorZ₂ est ≥ 0. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 2 |
| `P4_4c.abs_abs_height_sub_im_le_norm_horizontal` | ∣T − ∣Im ρ∣∣ ≤ distance horizontale de σ+iτ à ρ. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.xiHadamard_near_term_norm_le` | Borne d'un terme de Hadamard proche par l'inverse de la distance à la hauteur. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.horizontal_point_ne_xi_divisor` | Un point horizontal n'est pas un diviseur de ξ sous séparation en hauteur. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.xiDivisor_near_norm_inv_sum_le_card_add_Z₂` | Somme des inverses de normes de diviseurs proches ≤ card + Z₂. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.hadamard_near_sum_norm_le` | Borne de la somme des termes de Hadamard proches. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.hadamard_far_tsum_norm_le` | Borne de la queue de Hadamard lointaine. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.xi_logDeriv_horizontal_raw_bound` | Borne brute horizontale de la dérivée logarithmique de ξ. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.xi_logDeriv_horizontal_absorption` | Absorption de la borne de la dérivée logarithmique horizontale de ξ. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.xi_horizontal_logDeriv_bound_from_quantitative_hadamard` | Borne horizontale de la dérivée logarithmique de ξ à hauteur choisie T ∈ ]H,H+1[ hors des ordonnées de zéros non triviaux, à constante Cξ. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.digamma_add_nat_eq` | Digamma(z+M) = digamma z + ∑ (z+k)⁻¹. (terme hors maître « digamma » : dérivée logarithmique de Γ ; intervient dans l'équation fonctionnelle de −ζ'/ζ) | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 3 |
| `P4_4c.exists_horizontal_digamma_rpow_bound` | Borne rpow horizontale du digamma : ∃CΓ>0 uniforme sur les hauteurs T ∈ ]H,H+1[. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.horizontal_neg_zeta_logDeriv_norm_le_of_xi_digamma` | Borne horizontale de −ζ'/ζ à partir des bornes ξ et digamma. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4c.exists_perron_height_with_horizontal_negLogDeriv_bound` | Existence de hauteurs de Perron avec borne horizontale de −ζ'/ζ, contrôle de rectangle admissible. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |

### `RhGapCriterion.ZetaHorizontalPerronVanishingP4_4d`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `P4_4d.one_half_pos` | 0 < 1/2. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 0 |
| `P4_4d.one_half_lt_one` | 1/2 < 1. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 0 |
| `P4_4d.perronRectangleSigmaL_le_sigmaR` | Le bord gauche du rectangle de Perron est ≤ σR. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4d.perron_kernel_horizontal_bound` | Borne horizontale du noyau de Perron : ∃CK>0, ‖Perron.f x (σ ± iT)‖ ≤ CK/T² pour T ≥ 1. | CONFIRMÉE (domaine : hypothèses numériques/analytiques de l'énoncé (domaine)) | AJOUT | 1 |
| `P4_4d.zetaPerronIntegrand_horizontal_pointwise_bound` | Borne ponctuelle horizontale de l'intégrande de Perron de zêta à des hauteurs T ∈ ]H,H+1[ admissibles, constante C0. | CONFIRMÉE (domaine : x > 1, σR > 1, N ≥ 1) | AJOUT | 1 |
| `P4_4d.horizontal_HIntegral'_norm_le` | Borne de l'intégrale horizontale : ‖HIntegral'‖ ≤ (σR−σL)·B/(2π). | CONFIRMÉE (domaine : σL ≤ σR, B ≥ 0, ‖F‖ ≤ B) | AJOUT | 1 |
| `P4_4d.zetaPerron_horizontal_integrals_bound` | Borne des intégrales horizontales de Perron de zêta à hauteur admissible, constante C1. | CONFIRMÉE (domaine : x > 1, σR > 1, N ≥ 1) | AJOUT | 1 |
| `P4_4d.rpow_three_halves_div_sq_le_four_inv_sqrt` | (1+H)^(3/2)/T² ≤ 4/√(1+H). | CONFIRMÉE (domaine : 1 ≤ H < T) | AJOUT | 1 |
| `P4_4d.zetaPerron_horizontal_integrals_sqrt_bound` | Borne en 1/√ des intégrales horizontales de Perron, constante C2. | CONFIRMÉE (domaine : x > 1, σR > 1, N ≥ 1) | AJOUT | 2 |
| `P4_4d.exists_admissible_heights_horizontal_perron_integrals_tendsto_zero` | Il existe des hauteurs admissibles T n → ∞ (n+1 < T n < n+2) le long desquelles les intégrales horizontales de Perron tendent vers 0. | CONFIRMÉE (domaine : x > 1, σR > 1, N ≥ 1) | AJOUT | 3 |

### `RhGapCriterion.ZetaLeftVerticalPerronVanishingP4_4e`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `P4_4e.sN_eq` | sN N t = σL(N) + i t (point de la droite verticale gauche de Perron). | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.sN_re` | Re(sN N t) = σL(N). | CONFIRMÉE | AJOUT | 0 |
| `P4_4e.sN_im` | Im(sN N t) = t. | CONFIRMÉE | AJOUT | 0 |
| `P4_4e.sN_ne_zero` | sN N t ≠ 0. | CONFIRMÉE (domaine : N ≥ 1) | AJOUT | 3 |
| `P4_4e.sN_ne_one` | sN N t ≠ 1. | CONFIRMÉE (domaine : N ≥ 1) | AJOUT | 2 |
| `P4_4e.one_sub_sN_ne_one` | 1 − sN N t ≠ 1. | CONFIRMÉE (domaine : N ≥ 1) | AJOUT | 0 |
| `P4_4e.one_lt_one_sub_sN_re` | Re(1 − sN N t) > 1. | CONFIRMÉE (domaine : N ≥ 1) | AJOUT | 1 |
| `P4_4e.left_vertical_riemannZeta_ne_zero` | La droite verticale gauche de Perron évite tous les zéros de zêta (ni dans la bande critique, ni sur un entier pair négatif). | CONFIRMÉE (domaine : N ≥ 1) | AJOUT | 2 |
| `P4_4e.left_vertical_reflected_riemannZeta_ne_zero` | ζ ne s'annule pas en 1 − sN N t. | CONFIRMÉE (domaine : N ≥ 1) | AJOUT | 1 |
| `P4_4e.left_vertical_negLogDeriv_functional_identity` | Identité fonctionnelle de −ζ'/ζ sur la droite gauche : −ζ'/ζ(s) = −log π + ζ'/ζ(1−s) + (digamma)/2 (équation fonctionnelle). | CONFIRMÉE (domaine : N ≥ 1) | V62 | 1 |
| `P4_4e.left_vertical_reflected_logDeriv_uniform_bound` | Borne uniforme de ζ'/ζ(1−s) sur la droite gauche : ≤ ‖ζ'/ζ(4)‖. | CONFIRMÉE (domaine : N ≥ 1) | AJOUT | 1 |
| `P4_4e.perron_left_div_two_eq_leftDigammaPoint` | sN/2 = leftDigammaPoint N t. | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.leftDigammaPoint_add_nat_re` | Re(leftDigammaPoint + k) = k − N − 1/2. | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.leftDigammaPoint_shift` | leftDigammaPoint + (N+1) = 1/2 + i t/2. | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.leftDigammaPoint_add_nat_ne_neg_nat` | leftDigammaPoint + k n'est aucun entier négatif. | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.leftDigammaPoint_no_poles_in_range` | Pas de pôles du digamma dans la plage k < N+1. | CONFIRMÉE (domaine : k < N+1) | AJOUT | 1 |
| `P4_4e.leftDigammaPoint_digamma_add_nat` | digamma(leftDigammaPoint + N+1) = digamma(leftDigammaPoint) + ∑ (leftDigammaPoint + k)⁻¹. | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.leftDigammaPoint_digamma_eq_shift_sub_sum` | Forme soustractive de l'identité précédente. | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.leftDigammaPoint_abs_re_ge_half` | ∣Re(leftDigammaPoint + k)∣ ≥ 1/2. | CONFIRMÉE (domaine : k < N+1) | AJOUT | 1 |
| `P4_4e.leftDigammaPoint_inv_norm_le_two` | ‖(leftDigammaPoint + k)⁻¹‖ ≤ 2. | CONFIRMÉE (domaine : k < N+1) | AJOUT | 1 |
| `P4_4e.leftDigammaPoint_inv_sum_norm_le` | ‖∑ (leftDigammaPoint + k)⁻¹‖ ≤ 2(N+1). | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.shifted_leftDigammaPoint_norm_bound` | ∃C>0, ‖digamma(1/2 + it/2)‖ ≤ C·log(∣t∣+2). | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.left_vertical_shifted_digamma_bound_uniform` | Borne uniforme en N du digamma décalé sur la droite gauche. | CONFIRMÉE | AJOUT | 2 |
| `P4_4e.left_vertical_shifted_digamma_bound` | Borne du digamma décalé pour N fixé : C(N+1)log(∣t∣+2). | CONFIRMÉE (domaine : N ≥ 1) | AJOUT | 0 |
| `P4_4e.one_sub_sN_div_two_eq_reflectedDigammaBase_add_nat` | (1 − sN)/2 = reflectedDigammaBase t + N. | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.reflectedDigammaBase_add_nat_re` | Re(reflectedDigammaBase + k) = k+1. | CONFIRMÉE | AJOUT | 2 |
| `P4_4e.reflectedDigammaBase_add_nat_ne_neg_nat` | reflectedDigammaBase + k n'est aucun entier négatif. | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.reflectedDigammaBase_no_poles_in_range` | Pas de pôles du digamma réfléchi dans la plage. | CONFIRMÉE (domaine : k < N) | AJOUT | 1 |
| `P4_4e.reflected_digamma_add_nat_identity` | Identité digamma réfléchie : digamma(base+N) = digamma(base) + ∑ (base+k)⁻¹. | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.reflectedDigammaBase_inv_norm_le_one` | ‖(base+k)⁻¹‖ ≤ 1. | CONFIRMÉE (domaine : k < N) | AJOUT | 1 |
| `P4_4e.reflectedDigammaBase_inv_sum_norm_le` | ‖∑ (base+k)⁻¹‖ ≤ N. | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.reflectedDigammaBase_norm_bound` | ‖digamma(reflectedDigammaBase t)‖ ≤ C·log(∣t∣+2). | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.left_vertical_reflected_digamma_bound_uniform` | Borne uniforme du digamma réfléchi sur la droite gauche. | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.log_abs_add_two_le_four_mul_sqrt` | log(∣t∣+2) ≤ 4(1+∣t∣)^(1/2). | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.left_vertical_negLogDeriv_uniform_sqrt_bound` | Borne uniforme en √ de −ζ'/ζ sur la droite verticale gauche. | CONFIRMÉE | AJOUT | 3 |
| `P4_4e.left_vertical_negLogDeriv_rpow_bound` | Borne en puissance 1/2 de −ζ'/ζ sur la droite gauche pour N fixé. | CONFIRMÉE (domaine : N ≥ 1) | AJOUT | 0 |
| `P4_4e.perron_kernel_left_vertical_bound` | Borne du noyau de Perron sur la droite gauche : ≤ 2x^(−(2N+1))/(1+t²). | CONFIRMÉE (domaine : x > 1, N ≥ 1) | AJOUT | 1 |
| `P4_4e.leftVerticalLogDerivConstant_pos` | La constante de dérivée logarithmique gauche est > 0. | CONFIRMÉE | AJOUT | 5 |
| `P4_4e.leftVerticalLogDerivConstant_spec` | Spécification de cette constante : ‖−ζ'/ζ(sN)‖ ≤ K(N+1)(1+∣t∣)^(1/2). | CONFIRMÉE (domaine : N ≥ 1) | AJOUT | 1 |
| `P4_4e.leftVerticalUniversalMajorant_nonneg` | Le majorant universel gauche est ≥ 0. | CONFIRMÉE | AJOUT | 3 |
| `P4_4e.leftVerticalUniversalMajorant_le` | Le majorant universel gauche est ≤ 2(1+‖t‖)^(−3/2). | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.leftVerticalUniversalMajorant_continuous` | Le majorant universel gauche est continu. | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.leftVerticalUniversalMajorant_integrable` | Le majorant universel gauche est intégrable. | CONFIRMÉE | AJOUT | 3 |
| `P4_4e.leftVerticalUniversalMajorantMass_nonneg` | La masse du majorant universel gauche est ≥ 0. | CONFIRMÉE | AJOUT | 1 |
| `P4_4e.sN_ne_neg_one` | sN N t ≠ −1. | CONFIRMÉE (domaine : N ≥ 1) | AJOUT | 1 |
| `P4_4e.analyticAt_zetaPerronIntegrand_left` | L'intégrande de Perron de zêta est analytique en sN N t. | CONFIRMÉE (domaine : x > 1, N ≥ 1) | AJOUT | 1 |
| `P4_4e.continuous_left_vertical_zetaPerronIntegrand` | t ↦ intégrande de Perron en sN N t est continue. | CONFIRMÉE (domaine : x > 1, N ≥ 1) | AJOUT | 1 |
| `P4_4e.left_vertical_zetaPerronIntegrand_pointwise_bound` | Borne ponctuelle de l'intégrande de Perron sur la droite gauche par le majorant universel. | CONFIRMÉE (domaine : x > 1, N ≥ 1) | AJOUT | 3 |
| `P4_4e.left_vertical_zetaPerronIntegrand_integrable` | L'intégrande de Perron sur la droite gauche est intégrable. | CONFIRMÉE (domaine : x > 1, N ≥ 1) | AJOUT | 3 |
| `P4_4e.leftVerticalScalarBound_nonneg` | La borne scalaire gauche est ≥ 0. | CONFIRMÉE (domaine : x > 1) | AJOUT | 0 |
| `P4_4e.left_vertical_normalization_norm_le_one` | ‖1/(2πi)‖ ≤ 1. | CONFIRMÉE | AJOUT | 0 |
| `P4_4e.left_vertical_full_norm_le` | ‖intégrale verticale complète gauche‖ ≤ borne scalaire. | CONFIRMÉE (domaine : x > 1, N ≥ 1) | AJOUT | 2 |
| `P4_4e.left_vertical_truncated_tendsto_full` | L'intégrale verticale tronquée gauche tend vers l'intégrale complète. | CONFIRMÉE (domaine : x > 1, N ≥ 1, T n → ∞) | AJOUT | 2 |
| `P4_4e.leftVertical_rpow_geometric_rewrite` | x^(−(2N+1)) = x^(−1)·(x^(−2))^N. | CONFIRMÉE (domaine : x > 1) | AJOUT | 1 |
| `P4_4e.left_vertical_scalar_bound_tendsto_zero` | La borne scalaire gauche tend vers 0 quand N → ∞. | CONFIRMÉE (domaine : x > 1) | AJOUT | 1 |
| `P4_4e.left_vertical_boundary_tendsto_zero` | L'intégrale verticale gauche de l'intégrande de Perron tend vers 0 quand N → ∞. | CONFIRMÉE (domaine : x > 1) | AJOUT | 2 |
| `P4_4e.exists_admissible_heights_all_left_boundary_limits` | Il existe des hauteurs admissibles le long desquelles toutes les intégrales de bord gauche tendent vers leurs limites. | CONFIRMÉE (domaine : x > 1, σR > 1, N ≥ 1) | AJOUT | 1 |

### `RhGapCriterion.ZetaLogDerivVonMangoldt`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `LSeriesSummable_vonMangoldt_of_one_lt_re` | La série de von Mangoldt est sommable pour Re s > 1 (wrapper Mathlib). | CONFIRMÉE (domaine : Re s > 1) | V48 | 0 |
| `negLogDeriv_riemannZeta_eq_LSeries_vonMangoldt` | Pont arithmétique–spectral d'entrée de Perron : −ζ'/ζ(s) = ∑ Λ(n)/n^s sur Re s > 1. | CONFIRMÉE (domaine : Re s > 1) | V48 | 7 |
| `deriv_sub_const_eq_one` | La dérivée de z ↦ z − x vaut 1. | CONFIRMÉE | AJOUT | 1 |
| `logDeriv_sub_const` | logDeriv de z ↦ z − x en w vaut 1/(w−x). | CONFIRMÉE | AJOUT | 5 |
| `logDeriv_centered_pow` | logDeriv de (z−x)^n en w vaut n/(w−x). | CONFIRMÉE | AJOUT | 2 |
| `tendsto_mul_logDeriv_analyticOrder` | Résidu logarithmique = ordre analytique : (w−x)·logDeriv f w → ordre. | CONFIRMÉE (domaine : f analytique en x, ordre ≠ ⊤) | AJOUT | 2 |
| `tendsto_mul_logDeriv_riemannZeta_zero` | Résidu logarithmique de ζ en un zéro = multiplicité exacte : (w−ρ)·(ζ'/ζ) → m(ρ). | CONFIRMÉE (domaine : ρ zéro de ζ) | V12 | 3 |
| `tendsto_mul_neg_logDeriv_riemannZeta_zero` | Version −ζ'/ζ : résidu −m(ρ) en chaque zéro : le poids exact du terme −x^ρ/ρ de la formule explicite. | CONFIRMÉE (domaine : ρ zéro de ζ) | V100 | 7 |
| `riemannZeta_eq_zetaPoleFactor_div` | ζ(w) = zetaPoleFactor(w)/(w−1) hors {0,1}. | CONFIRMÉE (domaine : w ≠ 0, w ≠ 1) | AJOUT | 6 |
| `zetaPoleFactor_analyticAt_one` | zetaPoleFactor est analytique en 1. | CONFIRMÉE | AJOUT | 5 |
| `zetaPoleFactor_one_ne_zero` | zetaPoleFactor(1) ≠ 0. | CONFIRMÉE | AJOUT | 4 |
| `tendsto_mul_logDeriv_riemannZeta_pole` | Résidu du pôle : (w−1)·(ζ'/ζ)(w) → −1. | CONFIRMÉE | AJOUT | 1 |
| `tendsto_mul_neg_logDeriv_riemannZeta_pole` | Version −ζ'/ζ : résidu +1 au pôle (terme principal de la formule explicite). | CONFIRMÉE | AJOUT | 2 |

### `RhGapCriterion.ZetaNontrivialZeroResidueSeriesP4_5`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `finite_small_nontrivial_zeros` | L'ensemble des zéros non triviaux de hauteur ∣γ∣ < 1 est fini. | CONFIRMÉE | AJOUT | 0 |
| `norm_perron_f_nontrivial_le_imag_square` | ‖Perron.f x ρ‖ ≤ x/γ² pour un zéro non trivial de hauteur ≥ 1. | CONFIRMÉE (domaine : x > 1, ∣γ∣ ≥ 1) | AJOUT | 0 |
| `norm_nontrivialZeroResidueTerm_le_weighted` | ‖terme résiduel du zéro‖ ≤ x·m(ρ)/γ² : borne pondérée du terme explicite. | CONFIRMÉE (domaine : x > 1, ∣γ∣ ≥ 1) | V100 | 0 |
| `nontrivial_zero_residue_series_summable` | La série des termes résiduels des zéros non triviaux est sommable. | CONFIRMÉE (domaine : x > 1) | V121 | 8 |
| `nontrivial_zero_height_finset_bridge` | Pont : la somme des résidus dans le rectangle admissible = somme des −m(ρ)·Perron.f sur les zéros de hauteur < T. | CONFIRMÉE (domaine : rectangle de Perron admissible) | V121 | 0 |
| `mem_nontrivialZetaZerosByHeightSubtypeFinset` | Appartenance à l'ensemble fini des zéros par hauteur indexé par le sous-type ⟺ ∣γ∣ < T. | CONFIRMÉE | AJOUT | 2 |
| `tendsto_nontrivial_height_subtype_finset_atTop` | Cet ensemble diverge vers atTop avec la hauteur T. | CONFIRMÉE | AJOUT | 1 |
| `nontrivial_height_complex_sum_eq_subtype_sum` | La somme complexe canonique sur les zéros de hauteur < T égale la somme des termes résiduels du sous-type. | CONFIRMÉE | V121 | 2 |
| `nontrivial_zero_residue_series_symmetric_convergent` | La série des résidus des zéros non triviaux converge en sommation symétrique par hauteur vers la somme sur tous les zéros. | CONFIRMÉE (domaine : x > 1) | V121 | 2 |

### `RhGapCriterion.ZetaP4_4Closure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `p4_4_quantitative_horizontal_control_complete` | P4.4 complet : contrôle horizontal quantitatif : hauteurs admissibles T n → ∞ avec intégrales horizontales tendant vers 0. | CONFIRMÉE (domaine : x > 1, σR > 1, N ≥ 1) | AJOUT | 0 |

### `RhGapCriterion.ZetaP4_5Closure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `p4_5_boundary_and_zero_series_complete` | P4.5 complet : queues verticales droites tendent vers 0 et la série des zéros converge (conjonction). | CONFIRMÉE (domaine : x > 1, σR > 1) | AJOUT | 0 |

### `RhGapCriterion.ZetaP5Closure`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `P5_complete` | P5 complet : ΠMangoldt reconstruit = PiWeighted (x ≥ 2), amplitude du mode zéro non nulle, et autres conjuncts de la formule explicite lissée. | CONFIRMÉE | V121 | 0 |

### `RhGapCriterion.ZetaPerronAdmissibleHeights`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `mem_nontrivialZetaForbiddenHeightsBelow` | T est une hauteur interdite sous U ⟺ T = ∣γ∣ pour un zéro non trivial de hauteur < U. | CONFIRMÉE | AJOUT | 1 |
| `abs_im_mem_forbiddenHeightsBelow` | ∣γ∣ est une hauteur interdite sous U. | CONFIRMÉE (domaine : ρ zéro non trivial, ∣γ∣ < U) | AJOUT | 2 |
| `exists_nontrivial_zero_free_height_between` | Pour tout H, il existe une hauteur T ∈ ]max(H,0), max(H,0)+1[ qui n'est l'ordonnée d'aucun zéro non trivial. | CONFIRMÉE | AJOUT | 2 |
| `exists_nontrivial_zero_free_height_gt` | Pour tout H, il existe une hauteur T > max(H,0) qui n'est l'ordonnée d'aucun zéro non trivial. | CONFIRMÉE | AJOUT | 0 |
| `zetaPerronIntegrand_pole_classified_global` | Classification globale des pôles de l'intégrande de Perron de zêta : 1, 0, −1, zéro trivial ou zéro non trivial. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `isTrivialZetaZero_im_eq_zero` | Un zéro trivial est réel (Im = 0). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `isTrivialZetaZero_re_lt_one` | Un zéro trivial a Re < 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `isTrivialZetaZero_re_ne_perronRectangleSigmaL` | Un zéro trivial n'est pas sur la droite gauche du rectangle de Perron (N ≥ 1). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `mem_perronRectangleBorder_cases` | Un point de la bordure du rectangle de Perron est sur l'un des quatre côtés. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `one_not_mem_perronRectangleBorder` | Le point 1 n'est pas sur la bordure du rectangle de Perron (σR > 1, N ≥ 1, T > 0). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `zero_not_mem_perronRectangleBorder` | Le point 0 n'est pas sur la bordure. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `neg_one_not_mem_perronRectangleBorder` | Le point −1 n'est pas sur la bordure. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `trivialZero_not_mem_perronRectangleBorder` | Aucun zéro trivial n'est sur la bordure du rectangle de Perron. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `nontrivialZero_not_mem_perronRectangleBorder_of_height` | Un zéro non trivial n'est pas sur la bordure si T n'est l'ordonnée d'aucun zéro non trivial. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `perronRectangle_no_boundary_poles_of_zero_free_height` | Sans zéro de hauteur T, la bordure du rectangle ne rencontre aucun pôle de l'intégrande. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `perronRectangleAdmissible_of_zero_free_height` | Un rectangle de Perron à hauteur libre de zéros est admissible. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 3 |
| `exists_perronRectangleAdmissible_height_between` | Il existe une hauteur admissible T ∈ ]max(H,0), max(H,0)+1[. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `exists_perronRectangleAdmissible_height_gt` | Il existe une hauteur admissible T > H. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |

### `RhGapCriterion.ZetaPerronFiniteRectangle`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `PerronRectangleAdmissible.x_gt` | Un rectangle de Perron admissible a x > 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 11 |
| `PerronRectangleAdmissible.sigmaR_gt` | Il a σR > 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 9 |
| `PerronRectangleAdmissible.N_ge_one` | Il a N ≥ 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 7 |
| `PerronRectangleAdmissible.T_pos` | Il a T > 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 9 |
| `PerronRectangleAdmissible.no_poles_on_boundary` | Un rectangle admissible n'a aucun pôle de l'intégrande sur sa bordure. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |
| `perronRectangleLowerLeft_re` | Re du coin inférieur gauche = σL(N). | CONFIRMÉE | AJOUT | 0 |
| `perronRectangleLowerLeft_im` | Im du coin inférieur gauche = −T. | CONFIRMÉE | AJOUT | 0 |
| `perronRectangleUpperRight_re` | Re du coin supérieur droit = σR. | CONFIRMÉE | AJOUT | 0 |
| `perronRectangleUpperRight_im` | Im du coin supérieur droit = T. | CONFIRMÉE | AJOUT | 0 |
| `perronRectangle_re_le` | Le rectangle admissible a Re(gauche) ≤ Re(droite). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `perronRectangle_im_le` | Le rectangle admissible a Im(bas) ≤ Im(haut). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `perronRectangle_isCompact` | Le rectangle de Perron est compact. | CONFIRMÉE | AJOUT | 0 |
| `zetaPerron_integrand_meromorphicOn` | L'intégrande de Perron de zêta est méromorphe sur le rectangle admissible. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 3 |
| `zetaPerron_integrand_hasSimplePolesOn` | Ses pôles sur le rectangle admissible sont simples. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `zetaPerron_poleSet_subset_divisor_support` | L'ensemble des pôles intérieurs est inclus dans le support du diviseur de l'intégrande. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `zetaPerron_rectangle_poles_finite` | L'ensemble des pôles intérieurs du rectangle est fini. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `zetaPerron_finite_rectangle_residue_identity` | Identité finie : intégrale du rectangle = somme des résidus intérieurs. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V121 | 1 |
| `zetaPerron_finite_rectangle_four_boundaries` | Expansion exacte du rectangle fini en quatre bords orientés. | CONFIRMÉE | AJOUT | 1 |
| `verticalIntegral'_split_right_line` | La droite verticale complète (intégrable) se décompose en queue basse, segment et queue haute. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |
| `integrable_zetaPerronIntegrand_vertical` | L'intégrande de Perron de zêta est intégrable sur toute droite verticale σ > 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 6 |
| `smoothedVonMangoldtSum_eq_finite_residues_and_boundary_terms` | Théorème terminal P3c2 : somme de von Mangoldt lissée = résidus finis + queues et bords conservés. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V121 | 1 |

### `RhGapCriterion.ZetaPerronFiniteResidues`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `isTrivialZetaZero_riemannZeta_zero` | Un zéro trivial est un zéro de zêta. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 6 |
| `zetaZero_trivial_or_nontrivial` | Tout zéro de ζ est trivial ou non trivial. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V6 | 3 |
| `trivialZetaZero_not_nontrivial` | Les prédicats de zéro trivial et non trivial sont disjoints. | CONFIRMÉE | V6 | 0 |
| `p3c3_perronRectangle_isCompact` | Le rectangle de Perron (P3c3) est compact. | CONFIRMÉE | AJOUT | 0 |
| `p3c3_perronRectangle_re_le` | Re(gauche) ≤ Re(droite) dans le rectangle admissible. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `p3c3_perronRectangle_im_le` | Im(bas) ≤ Im(haut). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `one_mem_zetaPerronRectangle` | Le point 1 est dans le rectangle admissible. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `zero_mem_zetaPerronRectangle` | Le point 0 est dans le rectangle admissible. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `neg_one_mem_zetaPerronRectangle` | Le point −1 est dans le rectangle admissible. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `zetaPerron_trivial_zero_set_subset_zeros` | L'ensemble des zéros triviaux du rectangle est inclus dans les zéros de zêta. | CONFIRMÉE | AJOUT | 1 |
| `zetaPerron_nontrivial_zero_set_subset_zeros` | L'ensemble des zéros non triviaux du rectangle est inclus dans les zéros de zêta. | CONFIRMÉE | AJOUT | 1 |
| `zetaPerron_trivial_zero_set_finite` | L'ensemble des zéros triviaux du rectangle est fini. | CONFIRMÉE | AJOUT | 6 |
| `zetaPerron_nontrivial_zero_set_finite` | L'ensemble des zéros non triviaux du rectangle est fini. | CONFIRMÉE | AJOUT | 8 |
| `zetaPerron_classified_singularity_set_finite` | L'ensemble des singularités classées est fini. | CONFIRMÉE | AJOUT | 2 |
| `zetaPerron_classified_singularity_set_eq_union` | L'ensemble des singularités classées est l'union points spéciaux ∪ zéros triviaux ∪ zéros non triviaux. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `zetaPerron_classified_singularity_finset_eq_union` | Même énoncé en Finset. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `zetaPerron_special_disjoint_trivial` | Points spéciaux et zéros triviaux du rectangle sont disjoints. | CONFIRMÉE | AJOUT | 1 |
| `zetaPerron_special_disjoint_nontrivial` | Points spéciaux et zéros non triviaux sont disjoints. | CONFIRMÉE | AJOUT | 1 |
| `zetaPerron_trivial_disjoint_nontrivial` | Zéros triviaux et non triviaux du rectangle sont disjoints. | CONFIRMÉE | V6 | 1 |
| `zetaPerron_special_union_trivial_disjoint_nontrivial` | (spéciaux ∪ triviaux) et non triviaux sont disjoints. | CONFIRMÉE | AJOUT | 1 |
| `isTrivialZetaZero_ne_zero` | Un zéro trivial n'est pas 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `isTrivialZetaZero_ne_negOne` | Un zéro trivial n'est pas −1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `isTrivialZetaZero_ne_one` | Un zéro trivial n'est pas 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `isNontrivialZetaZero_ne_zero` | Un zéro non trivial n'est pas 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |
| `isNontrivialZetaZero_ne_negOne` | Un zéro non trivial n'est pas −1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |
| `zetaPerron_categories_pairwise_disjoint` | Les catégories de singularités de Perron sont deux à deux disjointes. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `zetaPerron_pole_category_unique` | La catégorie d'un pôle du rectangle est unique. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `zetaPerron_poles_in_rectangle_classified` | Tout pôle du rectangle est classé. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `residue_eq_zero_of_meromorphicOrderAt_nonneg` | Un ordre méromorphe ≥ 0 donne un résidu nul. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `sumResiduesIn_poleSet_eq_classified_singularity_sum` | La somme des résidus sur l'ensemble des pôles égale celle sur les singularités classées. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `sumResiduesIn_finite_eq_finset_sum` | Pour un ensemble fini, la somme des résidus est la somme finie des résidus. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `zetaPerron_residue_at_one` | Le résidu de l'intégrande au pôle 1 est Perron.f x 1 (x>1). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `zetaPerron_residue_at_one_eq` | Ce résidu vaut x/2. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `residue_perronKernel_zero` | Le résidu du noyau de Perron en 0 vaut 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `residue_perronKernel_neg_one` | Le résidu du noyau de Perron en −1 vaut −1/x. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `zetaPerron_residue_at_zero` | Le résidu de l'intégrande en 0 vaut −(ζ'/ζ)(0). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `zetaPerron_residue_at_neg_one` | Le résidu de l'intégrande en −1 vaut (ζ'/ζ)(−1)/x. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `zetaPerron_residue_at_zeta_zero` | Le résidu de l'intégrande en un zéro de ζ vaut −m(ρ)·Perron.f x ρ (terme explicite du zéro). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V100 | 3 |
| `zetaPerron_trivial_zero_residue_sum` | Somme des résidus aux zéros triviaux du rectangle = somme des −m·Perron.f. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V100 | 3 |
| `zetaPerron_nontrivial_zero_residue_sum` | Somme des résidus aux zéros non triviaux du rectangle = somme des −m·Perron.f. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V100 | 3 |
| `zetaPerron_special_residue_sum_eq` | Somme des résidus aux points spéciaux = x/2 − (ζ'/ζ)(0) + (ζ'/ζ)(−1)/x. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `sumResiduesIn_classified_eq_special_plus_zeros` | Somme des résidus classés = points spéciaux + zéros. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `zetaPerron_finite_residue_decomposition` | Décomposition finie des résidus du rectangle : x/2 − logDeriv ζ(0) + … + zéros triviaux + non triviaux. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V121 | 1 |
| `smoothedVonMangoldtSum_eq_classified_residues_and_boundary_terms` | Formule explicite lissée avec résidus classés et termes de bord : ψ lissé = x/2 − … − somme sur les zéros + bords. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V121 | 1 |
| `perronKernel_conj` | conj(Perron.f x ρ) = Perron.f x (conj ρ) (x>0). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |
| `isTrivialZetaZero_conj_iff` | Le conjugué d'un zéro trivial est un zéro trivial ⟺ ρ l'est. | CONFIRMÉE | V63 | 1 |
| `isNontrivialZetaZero_conj_iff` | Le conjugué d'un zéro non trivial est un zéro non trivial ⟺ ρ l'est. | CONFIRMÉE | V63 | 21 |
| `zetaPerronRectangle_conj_iff` | Le rectangle admissible est stable par conjugaison. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `zetaPerronNontrivialZeroSet_conj_iff` | L'ensemble des zéros non triviaux du rectangle est stable par conjugaison. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V63 | 1 |
| `zetaPerron_residue_conj` | Le résidu de l'intégrande en conj ρ est conj du résidu en ρ (ρ zéro). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V63 | 1 |
| `zetaPerron_conjugate_orbit_pairing` | Appariement d'orbite de conjugaison : conj(somme des résidus non triviaux) = somme des résidus non triviaux (rectangle admissible). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V63 | 0 |
| `ZetaPerronSingularityKind.ofNat_ctorIdx` | ofNat ∘ ctorIdx est l'identité sur ZetaPerronSingularityKind. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ZetaPerronLineIdentity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `vonMangoldt_term_mul_perronKernel` | term(Λ,s,n)·K_x(s) = Λ(n)·K_{x/n}(s) : le terme de von Mangoldt absorbe le noyau de Perron. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V48 | 1 |
| `neg_logDeriv_mul_perronKernel_eq_tsum` | Sur Re s = σ > 1, −(ζ'/ζ)·K_x se développe en série absolument convergente ∑ Λ(n)·K_{x/n} (P1). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V48 | 2 |
| `integrable_vonMangoldt_perron_term` | Chaque terme Λ(n)·K_{x/n} est verticalement intégrable pour σ > 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |
| `norm_perron_f_eq_rpow_mul` | ‖K_y(s)‖ = y^{Re s}·‖K_1(s)‖ (y > 0). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |
| `summable_integral_norm_vonMangoldt_perron` | La suite des intégrales de normes ∫‖Λ(n)K_{x/n}(σ+it)‖dt est sommable. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `perron_f_one_truncated_integral` | Primitive tronquée du noyau K₁(s) = 1/(s(s+1)) : 2(arctan(T/σ) − arctan(T/(σ+1))). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `verticalIntegral'_perron_f_one` | L'intégrale verticale normalisée de K₁ vaut 0 (cas frontière). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `verticalIntegral'_perron_f_eval` | Valeur exacte de l'intégrale verticale du noyau rescalé : 1 − 1/y si y > 1, 0 sinon. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `verticalIntegral'_eq_smoothedVonMangoldtSum` | Identité P3c1 : pour 1<σ, 1<x, la moyenne de Perron lissée de −ζ'/ζ sur la droite σ vaut la somme de von Mangoldt lissée. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V121 | 1 |

### `RhGapCriterion.ZetaPerronResidueInterface`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `exists_logDeriv_eventuallyEq_principal_add` | Pour f analytique d'ordre fini en x, logDeriv f = ordre/(w−x) + partie analytique g au voisinage épointé. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 4 |
| `logDeriv_sub_principal_isBigO` | logDeriv f − ordre/(w−x) = O(1) au voisinage épointé (O1 général). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `neg_logDeriv_riemannZeta_sub_principal_zero_isBigO` | (O1) au zéro : (−ζ'/ζ) − (−m(ρ))/(·−ρ) = O(1) pour tout zéro de ζ, toute multiplicité. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V100 | 2 |
| `logDeriv_riemannZeta_eventuallyEq_pole` | Au pôle 1 : logDeriv ζ = logDeriv G − 1/(·−1) sur le voisinage épointé. | CONFIRMÉE | AJOUT | 2 |
| `neg_logDeriv_riemannZeta_sub_principal_pole_isBigO` | (O1) au pôle : (−ζ'/ζ) − 1/(·−1) = O(1). | CONFIRMÉE | AJOUT | 1 |
| `meromorphicAt_riemannZeta` | ζ est méromorphe en tout point de ℂ. | CONFIRMÉE | AJOUT | 2 |
| `meromorphicAt_neg_logDeriv_riemannZeta` | −ζ'/ζ est méromorphe en tout point de ℂ. | CONFIRMÉE | AJOUT | 7 |
| `meromorphicOrderAt_logDeriv_eq_neg_one` | Ordre −1 général de la dérivée logarithmique en un zéro d'ordre fini non nul. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 3 |
| `meromorphicOrderAt_neg_logDeriv_riemannZeta_zero` | (O2) au zéro : −ζ'/ζ a un pôle exactement simple en chaque zéro de ζ, quelle que soit la multiplicité. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V100 | 6 |
| `meromorphicOrderAt_neg_logDeriv_riemannZeta_pole` | (O2) au pôle : −ζ'/ζ a un pôle simple en 1. | CONFIRMÉE | AJOUT | 1 |
| `analyticAt_logDeriv_riemannZeta` | Aux points réguliers, ζ'/ζ est analytique. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 11 |
| `hasSimplePolesOn_neg_logDeriv_riemannZeta_univ` | Tous les pôles de −ζ'/ζ sont au plus simples sur ℂ. | CONFIRMÉE | AJOUT | 3 |
| `riemannZeta_zero_ne_zero` | ζ(0) = −1/2 ≠ 0. | CONFIRMÉE | AJOUT | 3 |
| `riemannZeta_neg_one_ne_zero` | ζ(−1) = −1/12 ≠ 0. | CONFIRMÉE | AJOUT | 3 |
| `zetaZero_ne_zero` | Aucun zéro de ζ n'est en 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 12 |
| `zetaZero_ne_negOne` | Aucun zéro de ζ n'est en −1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 10 |
| `analyticAt_const_cpow_of_pos` | Pour x > 0, s ↦ x^s est analytique. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 12 |
| `const_cpow_ne_zero_of_pos` | Pour x > 0, x^s ≠ 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 3 |
| `meromorphicAt_perronKernel` | Le noyau de Perron est méromorphe en tout point. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 3 |
| `meromorphicAt_perronZetaIntegrand` | L'intégrande −ζ'/ζ·K_x est méromorphe en tout point. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |
| `analyticAt_perronKernel` | Hors {0,−1}, le noyau est analytique. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 7 |
| `perronKernel_ne_zero` | Hors {0,−1}, le noyau ne s'annule pas. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |
| `meromorphicOrderAt_perronKernel_zero` | Le noyau a un pôle simple en 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `meromorphicOrderAt_perronKernel_negOne` | Le noyau a un pôle simple en −1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `hasSimplePolesOn_perronZetaIntegrand_univ` | (O2) intégrande complet : tous les pôles sont au plus simples sur ℂ. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `residue_neg_logDeriv_riemannZeta_zero` | Résidu de −ζ'/ζ en un zéro = −m(ρ), toute multiplicité. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V100 | 3 |
| `residue_neg_logDeriv_riemannZeta_pole` | Résidu de −ζ'/ζ en 1 = +1. | CONFIRMÉE | AJOUT | 0 |
| `residue_perronZetaIntegrand_zero` | Résidu de l'intégrande complet en un zéro = −m(ρ)·K_x(ρ) : le poids exact du terme spectral. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V100 | 4 |
| `residue_perronZetaIntegrand_pole` | Résidu de l'intégrande complet en 1 = K_x(1) (terme principal). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |

### `RhGapCriterion.ZetaQuantitativeGoodHeightsP4_4b`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `P4_4b.riemannXi_eq_zero_of_isNontrivialZetaZero` | Un zéro non trivial annule ξ. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |
| `P4_4b.exists_divisorZeroIndex₀_val_eq_of_zero` | Tout zéro non nul d'une fonction entière non identiquement nulle est une valeur d'indice de diviseur de Hadamard. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `P4_4b.exists_riemannXi_divisorZeroIndex₀_val_eq_of_isNontrivialZetaZero` | Tout zéro non trivial de ζ est une valeur d'indice de diviseur de ξ. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |
| `P4_4b.norm_complex_le_abs_re_add_abs_im` | ‖z‖ ≤ ∣Re z∣ + ∣Im z∣. | CONFIRMÉE | AJOUT | 2 |
| `P4_4b.norm_le_height_plus_one_of_mem_nontrivialZetaZerosByHeightFinset` | Tout zéro non trivial de hauteur < R a une norme ≤ R+1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `P4_4b.riemannXi_divisorMassClosedBall₀_le_order_one_plus` | La masse de diviseurs de ξ dans une boule est ≤ C(1+R)^(1+ε) (ordre 1+). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |
| `P4_4b.nontrivialZetaZerosByHeightFinset_card_le_riemannXi_divisorMassClosedBall₀` | Le cardinal des zéros non triviaux de hauteur < R est ≤ la masse de diviseurs de ξ en R+1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `P4_4b.nontrivialZetaZerosByHeightFinset_card_le_order_one_plus` | Le cardinal des zéros non triviaux de hauteur < R est ≤ C(1+R)^(1+ε). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `P4_4b.exists_point_Ioo_separated_from_finset` | Pour tout ensemble fini de réels et tout H, il existe T ∈ ]H,H+1[ à distance ≥ 1/(4(card+1)) de tous les éléments. | CONFIRMÉE | AJOUT | 1 |
| `P4_4b.nontrivialZetaForbiddenHeightsBelow_card_le` | Le nombre de hauteurs interdites sous U est ≤ le nombre de zéros non triviaux de hauteur < U. | CONFIRMÉE | AJOUT | 1 |
| `P4_4b.exists_quantitative_good_height_between` | Existence de hauteurs T ∈ ]H,H+1[ quantitativement séparées des ordonnées des zéros non triviaux : distance ≥ 1/(C(1+H)^(1+ε)). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `P4_4b.exists_quantitative_perronRectangleAdmissible_height_between` | Même existence avec rectangle de Perron admissible. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |

### `RhGapCriterion.ZetaRealAxisNonvanishing`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `dirichletEtaPairedTerm_pos` | Chaque terme apparié de la série êta de Dirichlet est strictement positif pour s > 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 3 |
| `dirichletEtaPairedTerm_le` | Chaque terme apparié est ≤ s(2k+1)^(−s−1) (borne des accroissements finis). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `dirichletEtaPairedTerm_summable` | La série êta appariée est sommable pour tout s > 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `dirichletEtaPaired_pos` | η(s) > 0 pour tout réel s > 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `dirichletEtaPairedTermC_le` | Borne complexe du terme apparié pour Re z > 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |
| `dirichletEtaPairedTermC_summable` | La série appariée complexe est sommable pour Re z > 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `dirichletEtaPairedC_differentiableAt` | La série êta appariée complexe est différentiable en Re z₀ > 0 (M-test de Weierstrass). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `dirichletEtaPairedC_eq_of_one_lt_re` | Pour Re z > 1, êta appariée = (1 − 2^(1−z))·ζ(z). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `dirichletEtaPairedC_eq_of_mem_Ioo` | Même identité au point réel s₀ ∈ ]0,1[. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `dirichletEtaPairedC_ofReal` | La série appariée complexe en un point réel est la série réelle. | CONFIRMÉE | AJOUT | 1 |
| `riemannZeta_real_neg_Ioo_zero_one` | Re ζ(s) < 0 pour s réel dans ]0,1[. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `riemannZeta_real_ne_zero_Ioo_zero_one` | Théorème principal : ζ(s) ≠ 0 pour s réel dans ]0,1[ (absence de zéro réel dans la bande ouverte). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `riemannZeta_real_ne_zero_of_not_trivial_nonpos` | Un zéro réel non trivial ne peut avoir σ ≤ 0, σ ≠ 0 (via équation fonctionnelle pour σ ≤ −1). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `nontrivial_zeta_zero_im_ne_zero` | Un zéro non trivial a une partie imaginaire non nulle (V7 exige γ > 0 pour les membres ; ici seulement γ ≠ 0). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V7 | 26 |

### `RhGapCriterion.ZetaReflectionMultiplicity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `riemannZeta_eventuallyEq_completed_mul_GammaR_inv` | Pour Re s > 0, ζ = ζ complétée · Γℝ⁻¹ localement. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |
| `analyticOrderAt_GammaR_inv_eq_zero_of_re_pos` | Γℝ⁻¹ a ordre analytique nul dans Re s > 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `analyticOrderAt_riemannZeta_eq_completed_of_re_pos` | Dans le demi-plan droit hors pôle, ζ et sa complétée ont le même ordre analytique. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `zetaReflect_deriv_ne_zero` | La réflexion affine zetaReflect a une dérivée non nulle. | CONFIRMÉE | V80 | 1 |
| `analyticOrderAt_completedZeta_zetaReflect` | L'équation fonctionnelle de la zêta complétée conserve l'ordre analytique sous s ↦ 1−s. | CONFIRMÉE | V63 | 1 |
| `zetaZeroMultiplicity_zetaReflect` | Tout zéro de la bande ouverte conserve sa multiplicité analytique sous la réflexion fonctionnelle (conservation de multiplicité, quatre zéros). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V12 | 3 |

### `RhGapCriterion.ZetaRightVerticalTailsP4_5`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `right_vertical_lower_tail_tendsto_zero` | La queue verticale droite basse de l'intégrande de Perron tend vers 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `right_vertical_upper_tail_tendsto_zero` | La queue verticale droite haute tend vers 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `right_vertical_split_zetaPerron` | Décomposition de la droite verticale droite en queue basse, segment et queue haute. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `right_vertical_tails_tendsto_zero` | Les deux queues verticales droites tendent vers 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 3 |

### `RhGapCriterion.ZetaSmoothedBoundaryExplicitDecayP4_8`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `rightVerticalLogDerivConstant_nonneg` | La constante de dérivée logarithmique droite est ≥ 0. | CONFIRMÉE | AJOUT | 4 |
| `right_vertical_negLogDeriv_uniform_bound` | Borne uniforme de −ζ'/ζ sur la droite verticale droite. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `norm_perron_f_right_vertical_le_inv_sq` | ‖K_x(σR + it)‖ ≤ x^σR/t² pour ∣t∣ ≥ 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `norm_zetaPerronIntegrand_right_vertical_le` | Borne de l'intégrande complet sur la droite droite. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |
| `explicitRightVerticalTailDecay_nonneg` | La décroissance explicite des queues droites est ≥ 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `integral_Ici_inv_sq_le_inv` | ∫ sur [T,∞[ de 1/t² ≤ 1/T. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `integral_Iic_inv_sq_le_inv` | ∫ sur ]−∞,−T] de 1/t² ≤ 1/T. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `right_tail_envelope_upper_le_explicit` | Enveloppe haute ≤ décroissance explicite. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `right_tail_envelope_lower_le_explicit` | Enveloppe basse ≤ décroissance explicite. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `norm_rightVerticalUpperTail_le_explicit_decay` | ‖queue haute‖ ≤ décroissance explicite. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `norm_rightVerticalLowerTail_le_explicit_decay` | ‖queue basse‖ ≤ décroissance explicite. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `explicitRightVerticalTailDecay_tendsto_zero` | La décroissance explicite des queues droites tend vers 0. | CONFIRMÉE | AJOUT | 0 |
| `norm_leftVerticalTruncated_le_scalarBound` | ‖intégrale verticale gauche tronquée‖ ≤ borne scalaire. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `exists_admissible_height_full_boundary_bound` | Existence d'une hauteur admissible avec borne du reste de bord lissé complet. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `exists_height_smoothed_formula_with_explicit_remainder` | Existence d'une hauteur avec formule lissée et reste explicite. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V121 | 0 |

### `RhGapCriterion.ZetaSmoothedBoundaryRemainderP4_7`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `smoothedVonMangoldtSum_eq_height_truncated_main_add_boundaryRemainder` | Somme lissée = principal tronqué en hauteur + reste de bord (rectangle admissible). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V121 | 1 |
| `norm_five_boundary_terms_le` | Inégalité triangulaire à cinq termes : ‖a+b−c+d+e‖ ≤ ∑ normes. | CONFIRMÉE | AJOUT | 0 |
| `norm_smoothedPerronBoundaryRemainder_le` | ‖reste de bord lissé de Perron‖ ≤ somme des normes des queues et bords. | CONFIRMÉE | AJOUT | 1 |
| `norm_rightVerticalUpperTail_le_integralEnvelope` | ‖queue verticale droite haute‖ ≤ enveloppe intégrale. | CONFIRMÉE | AJOUT | 1 |
| `norm_rightVerticalLowerTail_le_integralEnvelope` | ‖queue verticale droite basse‖ ≤ enveloppe intégrale. | CONFIRMÉE | AJOUT | 1 |
| `left_vertical_full_boundary_bound_available` | ‖intégrale verticale gauche complète‖ ≤ borne scalaire gauche. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `horizontal_admissible_height_sqrt_bound_available` | Disponibilité de la borne en √ des intégrales horizontales à hauteur admissible. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `right_vertical_tails_tendsto_zero_available` | Disponibilité : les queues verticales droites tendent vers 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |

### `RhGapCriterion.ZetaSmoothedExplicitFormulaP4_6`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `smoothedVonMangoldtSum_eq_height_truncated_residues_and_boundary_terms` | Somme lissée = principal + résidus tronqués en hauteur + termes de bord (rectangle admissible). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V121 | 2 |
| `exists_admissible_heights_all_boundary_limits_with_tendsto` | Il existe des hauteurs admissibles T n → ∞ le long desquelles tous les termes de bord tendent vers leurs limites. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `smoothedVonMangoldtSum_eq_fixed_left_boundary_limit` | La somme lissée égale principal + résidus triviaux (N premiers) + limite du bord gauche fixé. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V121 | 1 |
| `smoothed_riemann_explicit_formula` | Formule explicite de Riemann lissée : pour x > 1, ψ lissé = x/2 − ζ'/ζ(0) + ζ'/ζ(−1)/x + série des zéros triviaux + série des zéros non triviaux. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V121 | 5 |

### `RhGapCriterion.ZetaSmoothedUnsmoothingP5`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `smoothed_mangoldt_weight_difference` | Différence de poids de von Mangoldt lissé entre N+1 et N pour n < N. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V48 | 0 |
| `smoothed_mangoldt_new_weight` | Nouveau poids de von Mangoldt lissé : (N+1)·Λ(N)·(1 − N/(N+1)) = Λ(N). | CONFIRMÉE | V48 | 0 |
| `smoothedMangoldtPrimitive_nat_difference` | La différence des primitives de von Mangoldt lissé entre N+1 et N vaut ψ(N). | CONFIRMÉE | V48 | 1 |
| `smoothedZeroPrimitive_eq_arithmetic` | La primitive lissée des zéros égale la primitive arithmétique (x > 1). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V48 | 1 |
| `smoothedZeroPrimitive_nat_difference` | La différence de la primitive lissée des zéros entre N+1 et N vaut ψ(N). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V48 | 1 |
| `chebyshev_psi_floor_eq` | ψ(⌊x⌋) = ψ(x). | CONFIRMÉE | AJOUT | 0 |
| `psiRecoveredFromZeros_eq_psi` | psiRecoveredFromZeros_eq_psi : pour x ≥ 2, ψ reconstruit depuis les zéros égale la fonction de Chebyshev ψ(x) (inconditionnel). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V48 | 6 |
| `PiMangoldtFromZeros_eq_PiMangoldt` | Pour x ≥ 2, PiMangoldt reconstruit depuis les zéros égale PiMangoldt. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V48 | 1 |
| `smoothed_formula_recovers_weighted_prime_count` | La formule lissée redonne le compte premier pondéré : PiMangoldtFromZeros = PiWeighted à la troncature ⌊log x/log 2⌋. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V48 | 2 |

### `RhGapCriterion.ZetaSmoothedZeroFormulaP5`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `smoothedZeroFormula_eq_smoothedVonMangoldtSum` | La formule lissée des zéros égale la somme de von Mangoldt lissée (x > 1). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V121 | 4 |
| `smoothedZeroFormula_sub_background` | La formule lissée moins le fond est la série des termes résiduels des zéros non triviaux. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V121 | 2 |

### `RhGapCriterion.ZetaTour22InstantiationP5`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `tour22_decomposition_instantiated` | Décomposition Tour 22 instanciée : canal projeté explicite = mode zéro d'amplitude explicite + reste. | CONFIRMÉE | V100 | 1 |
| `tour22_remainder_eq_explicit_formula_remainder` | Le reste de la formule explicite Tour 22 est identiquement nul. | CONFIRMÉE | V100 | 1 |
| `tour22_remainder_subexponential_bound` | Ce reste est sous-exponentiel. | CONFIRMÉE | AJOUT | 2 |
| `tour22_P5_parameters_closed` | Les paramètres P5 de la Tour 22 sont fermés (conjonction : zéros, canaux, amplitudes, sous-exponentialité). | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ZetaTrivialZeroResidueSeriesP4_5`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `trivial_zero_residue_term_eq` | Le terme résiduel d'un zéro trivial n est −Perron.f x (zéro trivial n). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `trivialZetaZeroAt_mul_succ` | Le zéro trivial n est −2(n+1). | CONFIRMÉE | AJOUT | 0 |
| `perronRectangle_re_le_for_trivial_series` | Re(gauche) ≤ Re(droite) du rectangle admissible (série triviale). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `perronRectangle_im_le_for_trivial_series` | Im(bas) ≤ Im(haut) du rectangle admissible. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `one_le_norm_trivial_denominator` | ‖s(s+1)‖ ≥ 1 aux zéros triviaux. | CONFIRMÉE | AJOUT | 0 |
| `norm_perron_f_trivial_le_geometric` | ‖Perron.f x (zéro trivial n)‖ est majoré par une géométrique de raison < 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `trivial_zero_residue_series_summable` | La série des termes résiduels des zéros triviaux est sommable. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |
| `trivial_zero_residue_partial_sums_tendsto` | Les sommes partielles de cette série convergent vers sa somme. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `trivialZetaZeroAt_mem_rectangle_iff` | Le zéro trivial n est dans le rectangle admissible ⟺ n < N. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `trivialZetaZeroAt_injective` | n ↦ zéro trivial n est injective. | CONFIRMÉE | AJOUT | 0 |
| `zetaPerron_trivial_zero_residue_sum_eq_range` | La somme des résidus aux zéros triviaux du rectangle est la somme sur range N des termes résiduels. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |

### `RhGapCriterion.ZetaTrivialZeroSimplicityP4_5`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `riemannZeta_trivialZetaZeroAt` | ζ s'annule en tout zéro trivial −2(n+1). | CONFIRMÉE | AJOUT | 3 |
| `trivialZetaZeroAt_ne_zero` | Le zéro trivial n est ≠ 0. | CONFIRMÉE | AJOUT | 2 |
| `trivialZetaZeroAt_ne_one` | Le zéro trivial n est ≠ 1. | CONFIRMÉE | AJOUT | 1 |
| `inv_Gammaℝ_eq_shift_two` | Γℝ⁻¹(s) = s/(2π)·Γℝ⁻¹(s+2). | CONFIRMÉE | AJOUT | 1 |
| `inv_Gammaℝ_eq_finite_shift_product` | Γℝ⁻¹(s) = produit fini de (s+2k)/(2π) fois Γℝ⁻¹(s+2m). | CONFIRMÉE | AJOUT | 1 |
| `inv_Gammaℝ_trivial_factorization` | Γℝ⁻¹ se factorise au voisinage du zéro trivial n en (s − zéro)·facteur régulier. | CONFIRMÉE | AJOUT | 1 |
| `analyticAt_trivialGammaRRegularFactor` | Le facteur régulier est analytique au zéro trivial. | CONFIRMÉE | AJOUT | 1 |
| `trivialGammaRRegularFactor_ne_zero` | Le facteur régulier ne s'annule pas au zéro trivial. | CONFIRMÉE | AJOUT | 1 |
| `analyticOrderAt_inv_Gammaℝ_trivial_eq_one` | Γℝ⁻¹ a ordre analytique 1 au zéro trivial. | CONFIRMÉE | AJOUT | 2 |
| `analyticOrderNatAt_inv_Gammaℝ_trivial_eq_one` | Idem en ordre naturel. | CONFIRMÉE | AJOUT | 0 |
| `completedRiemannZeta_trivialZetaZeroAt_ne_zero` | La zêta complétée ne s'annule pas au zéro trivial. | CONFIRMÉE | AJOUT | 3 |
| `analyticAt_completedRiemannZeta_trivialZetaZeroAt` | La zêta complétée est analytique au zéro trivial. | CONFIRMÉE | AJOUT | 2 |
| `analyticOrderAt_completedRiemannZeta_trivial_eq_zero` | La zêta complétée a ordre analytique 0 au zéro trivial. | CONFIRMÉE | AJOUT | 1 |
| `riemannZeta_eventuallyEq_completed_mul_invGammaR` | Au voisinage du zéro trivial, ζ = complétée · Γℝ⁻¹. | CONFIRMÉE | AJOUT | 1 |
| `analyticOrderAt_riemannZeta_trivial_eq_one` | ζ a ordre analytique 1 en chaque zéro trivial. | CONFIRMÉE | AJOUT | 2 |
| `zetaZeroMultiplicity_trivialZetaZeroAt` | Multiplicité 1 des zéros triviaux. | CONFIRMÉE | AJOUT | 5 |

### `RhGapCriterion.ZetaUnsmoothedPerronTransformP5`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `unsmoothedZetaPerronIntegrand_eq` | Intégrande de Perron non lissé : −ζ'/ζ·(x^s/s) hors {0,−1}. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `perronResidueProjection_congr` | La projection de résidu de Perron ne dépend que des valeurs en exp U. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |

### `RhGapCriterion.ZetaZeroCountingCrude`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `Backlund.zetaSurrogate_eventuallyEq` | Hors s=1, le substitut de Backlund coïncide avec (s−1)ζ(s) sur un voisinage. (terme hors maître « Backlund » : substitut entier (s−1)ζ(s) et majorant grossier de N(T)) | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `Backlund.zetaSurrogate_differentiable` | Le substitut de Backlund est entier. | CONFIRMÉE | AJOUT | 4 |
| `Backlund.log_le_two_mul_sqrt` | log x ≤ 2√x pour x ≥ 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `Backlund.exists_zeta_bound_right` | Borne uniforme de ζ sur Re ≥ 2. | CONFIRMÉE | AJOUT | 0 |
| `Backlund.surrogate_growth_right` | Croissance log-linéaire du substitut sur Re ≥ 2. | CONFIRMÉE | AJOUT | 0 |
| `Backlund.zeta_norm_le_subband` | Borne polynomiale de ζ sur 1/2 ≤ Re, 1 ≤ ∣Im∣ : ‖ζ‖ ≤ 3+‖z‖. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `Backlund.norm_Gamma_le_Gamma_re` | ‖Γ(z)‖ ≤ Γ(Re z) pour Re z > 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `Backlund.Gamma_le_two_of_mem_Icc` | Γ ≤ 2 sur [1,2]. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `Backlund.Gamma_le_two_mul_factorial` | Γ(x) ≤ 2·(n+1)! pour 1 ≤ x ≤ n+2. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `Backlund.norm_cos_le_exp` | ‖cos v‖ ≤ exp‖v‖. | CONFIRMÉE | AJOUT | 0 |
| `Backlund.log_one_add_mul_le` | log(1+ab) ≤ log(1+a) + log(1+b). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `Backlund.surrogate_growth_left` | Croissance log du substitut sur Re ≤ −1 en (1+‖z‖)^(3/2). | CONFIRMÉE | AJOUT | 0 |
| `Backlund.surrogate_growth_band` | Croissance log-linéaire du substitut sur la bande −1 ≤ Re ≤ 2. | CONFIRMÉE | AJOUT | 0 |
| `Backlund.zetaSurrogate_log_growth` | Majorant log-croissance en exposant 3/2 pour le substitut sur tout ℂ. | CONFIRMÉE | AJOUT | 1 |
| `Backlund.zetaSurrogate_zeros_in_closedBall₀_count` | Masse des zéros du substitut dans une boule ≤ C'(1+R)^(3/2). | CONFIRMÉE | AJOUT | 1 |
| `Backlund.zeta_zero_re_mem_of_im_pos` | Tout zéro de ζ de partie imaginaire > 0 est dans la bande fermée 0 ≤ Re ≤ 1 (localisation de Backlund portée). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V7 | 2 |
| `Backlund.divisor_surrogate_eq_order` | Hors s=1, la valeur du diviseur du substitut est l'ordre de ζ. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `Backlund.zetaCounting_le_surrogate_mass` | ∣N(T)∣ ≤ masse de diviseurs du substitut en T+1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `Backlund.zetaCounting_crude_majorant` | Majorant polynomial grossier de la fonction de comptage des zéros N(T) ≤ A T^(3/2), inconditionnel. | CONFIRMÉE | AJOUT | 2 |
| `zeta_zero_re_mem_of_im_pos` | Alias racine de la localisation (contrat P4.1) : zéro de ζ de Im > 0 dans la bande fermée. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V7 | 0 |

### `RhGapCriterion.ZetaZeroHeightPerronBridge`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `zetaPerronIntegrand_pole_at_nontrivial_zero` | L'intégrande de Perron a un pôle (ordre méromorphe < 0) en tout zéro non trivial. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `zetaPerron_border_of_rect_abs_im_eq` | Un point du rectangle admissible avec ∣Im∣ = T est sur la bordure. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `abs_im_lt_of_zetaPerron_nontrivial_mem` | Un zéro non trivial du rectangle admissible a ∣Im∣ < T. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `zetaPerronNontrivialZeroSet_eq_byHeight` | L'ensemble des zéros non triviaux du rectangle est l'ensemble des zéros non triviaux de hauteur < T. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `zetaPerronNontrivialZeroFinset_eq_byHeight` | Même énoncé en Finset. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `zetaPerron_nontrivial_zero_residue_sum_eq_byHeight` | La somme des résidus aux zéros non triviaux du rectangle est la somme sur les zéros de hauteur < T. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 2 |

### `RhGapCriterion.ZetaZeroHeightSummability`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `riemannZeta_order_eq_zetaZeroMultiplicity` | Pour un zéro non trivial, l'ordre de ζ (au sens du port) égale la multiplicité analytique. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V12 | 6 |
| `weighted_zetaZeroMultiplicity_imagSquare_summable` | La série des m(ρ)·∣γ∣⁻² sur les zéros non triviaux est sommable. | CONFIRMÉE | AJOUT | 1 |
| `weighted_zetaZeroMultiplicity_shiftedImagSquare_summable` | La série des m(ρ)·∣Im(s−ρ)∣⁻² est sommable pour tout s. | CONFIRMÉE | AJOUT | 0 |

### `RhGapCriterion.ZetaZeroHeightTruncation`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `complex_eq_of_im_eq_zero` | Un complexe de partie imaginaire nulle est son propre réel. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `int_one_le_of_real_le_neg_one` | Si σ = −2k et σ ≤ −1 alors k ≥ 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `isTrivialZetaZero_of_real_cos_eq_zero` | Un réel ρ ≤ −1 annulant le cosinus de fonctionnelle est un zéro trivial. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `riemannZeta_ne_zero_of_real_nontrivial_left` | Un zéro non trivial réel de partie réelle ≤ 0 est impossible (False). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `isNontrivialZetaZero_re_mem_Ioo` | Tout zéro non trivial local est dans la bande critique ouverte 0 < β < 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V7 | 62 |
| `nontrivialZetaZerosByHeight_finite` | L'ensemble des zéros non triviaux de hauteur < T est fini. | CONFIRMÉE | AJOUT | 5 |
| `mem_nontrivialZetaZerosByHeightFinset` | Appartenance à l'ensemble fini des zéros par hauteur ⟺ zéro non trivial de ∣γ∣ < T. | CONFIRMÉE | AJOUT | 6 |
| `nontrivialZetaZerosByHeightFinset_mono` | Les troncatures par hauteur sont monotones. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `nontrivialZetaZerosByHeightFinset_conj` | L'ensemble des zéros non triviaux de hauteur < T est stable par conjugaison. | CONFIRMÉE | V63 | 0 |

### `RhGapCriterion.ZetaZeroMultiplicity`

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `zetaZero_ne_one` | Un zéro de ζ n'est pas le pôle 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 15 |
| `analyticAt_riemannZeta_of_zero` | ζ est analytique en chacun de ses zéros. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 11 |
| `isPreconnected_compl_one_complex` | Le complément du pôle est préconnexe dans ℂ. | CONFIRMÉE | AJOUT | 3 |
| `riemannZeta_analyticOrderAt_ne_top` | L'ordre analytique de ζ en un zéro est fini. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 16 |
| `zetaZeroMultiplicity_pos` | Chaque zéro de ζ a une multiplicité strictement positive. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V12 | 23 |
| `zetaZerosInClosedBall_finite` | Tout disque fermé contient un nombre fini de zéros de ζ. | CONFIRMÉE | AJOUT | 2 |
| `mem_zetaZerosFinset` | Appartenance à zetaZerosFinset R ⟺ dans la boule de rayon R et ζ = 0. | CONFIRMÉE | AJOUT | 1 |
| `zetaZerosFinset_mono` | Les troncatures radiales sont emboîtées. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `mem_nontrivialZetaZerosFinset` | Appartenance à nontrivialZetaZerosFinset R ⟺ ‖ρ‖ ≤ R et ρ non trivial. | CONFIRMÉE | AJOUT | 0 |
| `truncatedZetaZeroSum_add` | Linéarité exacte de la somme spectrale tronquée. | CONFIRMÉE | AJOUT | 0 |
| `truncatedZetaZeroSum_zero` | La somme spectrale tronquée de la fonction nulle est nulle. | CONFIRMÉE | AJOUT | 0 |

### `RiemannHypothesisProof.CanonicalPrimeEvent`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.CanonicalPrimeEvent.centerPrime_ofTwoTransitionStart` | Le centre d'un événement premier construit depuis un départ à deux transitions est l'occupant p(eventStart+1) de l'axe canonique. | CONFIRMÉE | V28 | 0 |
| `RiemannHypothesisProof.CanonicalPrimeEvent.centerPrime_isPrime` | Le premier central d'un événement est premier. | CONFIRMÉE | AJOUT | 2 |
| `RiemannHypothesisProof.CanonicalPrimeEvent.eq_of_centerPrime_eq` | Le premier central identifie injectivement l'événement (même premier central ⟹ même événement). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V182 | 3 |
| `RiemannHypothesisProof.CanonicalPrimeEvent.piCount_centerPrime` | Comptage exact du premier central : π(centre) = primeIndex+1. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.CanonicalPrimeEvent.threePrimeWindow` | Triplet canonique (avant, centre, après) autour du premier central. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.CanonicalPrimeEvent.vonMangoldt_position_lock` | Rigidité locale von Mangoldt/EncZ : la position reconstruite depuis les zéros à l'indice de l'événement est le premier central. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.CanonicalPrimeEvent.vonMangoldt_incomingGap_lock` | L'écart entrant est reconstruit exactement. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.CanonicalPrimeEvent.vonMangoldt_outgoingGap_lock` | L'écart sortant est reconstruit exactement. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.CanonicalPrimeEvent.reconstructedGrammar_eq_eventGrammar` | EncZ = M sur l'événement : la grammaire reconstruite égale la grammaire de l'événement. | CONFIRMÉE | V48 | 1 |
| `RiemannHypothesisProof.CanonicalPrimeEvent.same_centerPrime_rigidifies_environment` | Même premier central ⟹ même événement ⟹ même environnement grammatical. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V182 | 0 |
| `RiemannHypothesisProof.CanonicalPrimeEvent.relationIsNull_iff_eq` | La relation entre deux événements est nulle ⟺ les événements sont égaux. | CONFIRMÉE | AJOUT | 1 |
| `RiemannHypothesisProof.CanonicalPrimeEvent.distinctEvents_haveNonNullRelation` | Deux événements distincts ont une relation non nulle. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |

### `RiemannHypothesisProof.ChebyshevVonMangoldt`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.VonMangoldtRelationDeterminesPrimePresence` | Détection exacte des puissances de premier : relation von Mangoldt ≠ 0 ⟺ n est puissance de premier. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.VonMangoldtRelationDeterminesPrimePosition` | Sur un premier canonique le poids von Mangoldt est log p. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.ChebyshevRelationDeterminesLocalArithmeticVariation` | Variation locale exacte de Chebyshev : ψ(x+1) − ψ(x) = poids von Mangoldt(x+1). | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.VonMangoldtReconstructsPrimeCount` | Le canal zéros reconstruit exactement le comptage premier. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.VonMangoldtReconstructsPrimePosition` | Le canal zéros reconstruit exactement les positions premières. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.VonMangoldtReconstructsGapForPrime` | Le canal zéros reconstruit exactement chaque gap grammatical. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.VonMangoldtReconstructsWholePrimeGrammar` | EncZ/M : égalité de structure complète. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.VonMangoldtReconstructsPrimeGrammarGap` | Projection : gaps de la grammaire reconstruite = gaps de M. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.VonMangoldtReconstructsPrimeGrammarTransition` | Projection : transitions égales. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.VonMangoldtReconstructsPrimeGrammarPattern` | Projection : motif égal. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.VonMangoldtReconstructsPrimeGrammarFamily` | Projection : famille égale. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.VonMangoldtRelationRigidifiesPrimeHistory` | Von Mangoldt ne permet aucune autre suite de premiers portant les mêmes poids (rigidité de l'histoire première). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V48 | 0 |

### `RiemannHypothesisProof.ContactGeometry`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.ContactsRecoverGamma` | Sous la loi de largeur logarithmique mπ/γ (γ ≠ 0, étage ≥ 1), la paire de vrais contacts relit γ. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V45 | 1 |
| `RiemannHypothesisProof.ContactsRecoverBeta` | Sous la loi tangente éliminée (β ≠ 0, étage ≥ 1), les mêmes contacts relisent β. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V45 | 2 |
| `RiemannHypothesisProof.ContactsRecoverZeroIdentity` | Les deux lois canoniques sur la même paire réelle restituent le même vrai membre (zéro non trivial). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V45 | 1 |
| `RiemannHypothesisProof.SameRealContactPairGivesSameZero` | Une même paire réelle de contacts qui relit exactement deux vrais membres relit le même complexe. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V46 | 1 |
| `RiemannHypothesisProof.NonCentralFunctionalMirrorCannotShareSameContacts` | Un membre hors ligne et son vrai miroir ne peuvent être relus par la même paire réelle de contacts. | RÉFUTATION COMPILÉE (paire de contacts E44 commune à un membre hors ligne et à son miroir (condition β ≠ 1/2, étage ≥ 1)) | V163 | 0 |

### `RiemannHypothesisProof.CriticalStripConfinement`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.re_lt_one_of_zeta_eq_zero` | Bord droit : aucun zéro de ζ n'a Re ≥ 1 (Hadamard–de la Vallée Poussin, Mathlib). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V7 | 1 |
| `RiemannHypothesisProof.ZeroTrivial_of_riemannZeta_eq_zero_of_re_nonpos` | Bord gauche : un zéro de Re ≤ 0 est nécessairement trivial. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V7 | 1 |
| `RiemannHypothesisProof.inStrip_of_mathlib` | Confinement : un zéro non trivial est strictement dans la bande 0 < β < 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V7 | 0 |
| `RiemannHypothesisProof.ZeroNonTrivial_of_riemannZeta_eq_zero` | Confinement complet sous le fait classique orthogonal (absence de zéro réel dans ]0,1[). | CONFIRMÉE (domaine : NoRealZetaZeroInOpenUnitSegment (fait classique, établi par noRealZetaZeroInOpenUnitSegment dans RealSegmentNonvanishing)) | V7 | 0 |

### `RiemannHypothesisProof.NonCompensation`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.ContactsRecoverIndividualZeroData` | Les contacts récupèrent la donnée individuelle du zéro : β, γ et l'identité complète du membre. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V45 | 0 |
| `RiemannHypothesisProof.HarmonicTowerPreservesIndividualZeroReading` | La Tour conserve la lecture individuelle du membre. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V45 | 0 |
| `RiemannHypothesisProof.IndividualZeroReadingRequiresContactRecoverability` | La lecture individuelle exige la récupérabilité par les contacts (deux vrais membres relus par la même paire sont égaux). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V46 | 0 |
| `RiemannHypothesisProof.CollectiveCompensationDoesNotEraseIndividualZero` | Une compensation collective n'efface jamais un membre individuel. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `RiemannHypothesisProof.ZeroIdentityIsPreservedAcrossWholeProof` | L'identité du zéro est conservée tout au long de la chaîne démontrée (composition). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V45 | 0 |

### `RiemannHypothesisProof.PrimeBlockFirstReturn`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.PrimeHistoryDeterminesPrimeBlock` | Le bloc premier au rang n est le triplet (histoire n, n+1, n+2). | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.PrimeBlockContainsSuccessivePrimes` | Le bloc contient trois premiers canoniques successifs strictement croissants. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.PrimeBlockDeterminesTransitions` | Le bloc détermine les deux transitions du triplet. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.PrimeBlockDeterminesMaintenancesAndChanges` | Maintien ⟺ non changement entre deux positions. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.PrimeBlockDeterminesPatternsAndFamilies` | Le bloc détermine motifs et familles (écart et classe). | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.PrimeBlockDeterminesOrder` | Le bloc détermine l'ordre : p(n) < p(n+1) < p(n+2). | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.TwoTransitionPrimeBlockHasUniqueCentralPrime` | Le bloc à deux transitions a un unique premier central : p(n+1). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V61 | 0 |
| `RiemannHypothesisProof.CentralPrimeForZeroBelongsToSamePrimeBlock` | Le premier central de l'événement à deux transitions est le composant central du bloc premier. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.PrimeHistoryDeterminesFirstReturnForPrime` | Le premier retour est la borne inférieure des positions ultérieures qui restaurent le même état. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.FirstReturnForPrimeHasSameGrammarState` | Le premier retour restaure le même état grammatical dès qu'un retour existe. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `RiemannHypothesisProof.FirstReturnForPrimeHasNoEarlierSameGrammarState` | Aucune position antérieure ne restaure le même état. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `RiemannHypothesisProof.FirstReturnForPrimeIsUnique` | Le premier retour est unique : valeur canonique, jamais un choix. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `RiemannHypothesisProof.PrimeHistoryFirstReturnRestoresGrammarState` | L'état grammatical est réellement restauré au premier retour. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `RiemannHypothesisProof.HarmonicTowerPreservesSameZeroAcrossFirstReturn` | La Tour conserve le même zéro d'un bord du premier retour à l'autre. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V45 | 0 |
| `RiemannHypothesisProof.FirstReturnContactsRecoverSameGamma` | Les contacts au premier retour récupèrent le même γ. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V45 | 0 |
| `RiemannHypothesisProof.FirstReturnContactsRecoverSameBeta` | Les contacts au premier retour récupèrent le même β. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V45 | 0 |
| `RiemannHypothesisProof.FirstReturnContactsRecoverSameZero` | Les contacts au premier retour récupèrent le même zéro. [INCIDENT : nom plus fort que le type ? (le type compare deux Tours du même ρ).] | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V45 | 0 |
| `RiemannHypothesisProof.FirstReturnPreservesRadialDeformationForZero` | « Le premier retour préserve la déformation radiale » : énoncé de la forme x = x (tautologie réflexive). [INCIDENT : le nom promet plus que le type (aucun contenu sur le premier retour).] | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.FirstReturnPreservesFunctionalMirrorDifference` | Pour ρ hors ligne (β ≠ 1/2), le miroir fonctionnel de ρ diffère de ρ (indices s,t non utilisés). [INCIDENT : le nom « préserve … au premier retour » promet plus que le type (indices s, t inutilisés).] | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V74 | 0 |
| `RiemannHypothesisProof.NonCentralFirstReturnCannotEraseRadialDeformation` | Un premier retour ne peut effacer la déformation radiale d'un membre hors centre : RadialDeformation(ρ) ≠ 0 pour β ≠ 1/2 (indices s,t inutilisés). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |

### `RiemannHypothesisProof.PrimeEnvironment`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.CenterForZeroIsOccupiedByCentralPrimeForZero` | Le centre d'un événement est occupé par son premier central. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.CentralPrimeForZeroIsPrime` | Le premier central d'un événement est premier. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.CentralPrimeForZeroBelongsToPrimeAlgebraicAxis` | Le premier central appartient à l'axe algébrique premier. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.SameCentralPrimeDeterminesSamePrimeEvent` | Même premier central ⟹ même événement. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V182 | 1 |
| `RiemannHypothesisProof.SameCentralPrimeDeterminesSamePrimeEnvironment` | Même premier central ⟹ même environnement premier complet. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V182 | 0 |
| `RiemannHypothesisProof.CentralPrimeDeterminesSameEncZAndMEvent` | EncZ = M sur le même événement central. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.PrimeEnvironmentIncomingGapPositive` | L'écart entrant de l'événement est strictement positif. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.PrimeEnvironmentOutgoingGapPositive` | L'écart sortant de l'événement est strictement positif. | CONFIRMÉE | AJOUT | 0 |

### `RiemannHypothesisProof.PrimeGrammarStrictPositivity`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.PrimeGrammarGapIsStrictlyPositive` | Chaque entrée de gap du M canonique est strictement positive. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.PrimeGrammarExcludesNullGap` | M n'admet aucune entrée de gap nulle. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.PrimeGrammarBlockGapIsStrictlyPositive` | La même loi à toute place d'un bloc de M. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.DistinctPrimeHistoryPositionsHavePositiveSeparation` | Deux positions premières distinctes ont une séparation strictement positive. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `RiemannHypothesisProof.PrimeGrammarIsImmutableAndExcludesNullity` | Synthèse : M est immuable (histoire = p) et chaque gap est > 0. | CONFIRMÉE | AJOUT | 0 |

### `RiemannHypothesisProof.PrimeHistoryFromZeros`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.ZerosReconstructWeightedPrimeCount` | Les zéros reconstruisent le compte premier pondéré : WeightedPrimeCountFromZeros = PiWeighted à la troncature canonique. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V48 | 0 |
| `RiemannHypothesisProof.ZerosReconstructPrimeCount` | Les zéros reconstruisent le compte premier. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.ZerosReconstructPrimePositions` | Les zéros reconstruisent les positions premières. | CONFIRMÉE | V48 | 6 |
| `RiemannHypothesisProof.ZerosReconstructGapForPrime` | Les zéros reconstruisent chaque gap. | CONFIRMÉE | V48 | 7 |
| `RiemannHypothesisProof.ZerosReconstructWholePrimeGrammar` | EncZ = M, égalité de structure complète et inconditionnelle. | CONFIRMÉE | V48 | 6 |
| `RiemannHypothesisProof.PrimeHistoryFromZerosEqualsPrimeHistory` | Histoire première reconstruite depuis les zéros = histoire première (égalité de fonctions). | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.ZerosReconstructTransitionForPrime` | Projection de EncZ = M : les transitions de la grammaire reconstruite sont TransitionForPrime. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.ZerosReconstructPatternForPrime` | Projection : le motif reconstruit est PatternForPrime. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.ZerosReconstructFamilyForPrime` | Projection : la famille reconstruite est FamilyForPrime. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.ZerosReconstructTransitionOrderForPrime` | Projection : l'ordre de transitions reconstruit est TransitionOrderForPrime. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.PrimeHistoryFromZerosPreservesDistinctPrimePositions` | La lecture issue des zéros ne peut fusionner deux positions premières distinctes. | CONFIRMÉE (domaine : m ≠ n) | AJOUT | 0 |
| `RiemannHypothesisProof.PrimeHistoryFromZerosInheritsStrictPositivity` | Chaque gap EncZ est strictement positif (c'est exactement le gap M). | CONFIRMÉE | AJOUT | 1 |

### `RiemannHypothesisProof.RHV2CanonicalPrimeCell`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.CanonicalContactCell.endpoint_convention_sound` | Convention des extrémités saine : contact gauche < contact droit pour tout vrai zéro non trivial. | CONFIRMÉE | AJOUT | 1 |
| `RiemannHypothesisProof.CanonicalContactCell.metricMidpointReadout_strictly_inside` | Le milieu métrique est strictement à l'intérieur des deux contacts. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.CanonicalContactCell.left_ge_two` | Le contact gauche est ≥ 2. | CONFIRMÉE | AJOUT | 2 |
| `RiemannHypothesisProof.CanonicalContactCell.metricMidpointReadout_ge_two` | Le milieu métrique est ≥ 2. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.CanonicalContactCell.right_ge_two` | Le contact droit est ≥ 2. | CONFIRMÉE | AJOUT | 1 |
| `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_left_count_lock` | Verrou von Mangoldt du compte gauche : compte reconstruit depuis les zéros = π réel du contact gauche. | CONFIRMÉE | V145 | 2 |
| `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_midpoint_count_lock` | Verrou du compte au milieu. | CONFIRMÉE | V145 | 0 |
| `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_right_count_lock` | Verrou du compte droit. | CONFIRMÉE | V145 | 1 |
| `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_local_count_lock` | Verrou du compte local (entre les deux contacts). | CONFIRMÉE | V145 | 0 |
| `RiemannHypothesisProof.CanonicalContactCell.localPrimeCount_eq_three_iff_right_eq_left_add_three` | Le compte local arithmétique vaut 3 ⟺ π(droite) = π(gauche)+3. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.CanonicalContactCell.startRank_eq_floor_piReal_left` | Le rang de départ est ⌊π réel(contact gauche)⌋. | CONFIRMÉE | V145 | 0 |
| `RiemannHypothesisProof.CanonicalContactCell.left_zero_count_floor_eq_startRank` | Le compte gauche reconstruit depuis les zéros a pour plancher le rang de départ. | CONFIRMÉE | V145 | 0 |

### `RiemannHypothesisProof.RHV2TrueContacts`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.trueContacts_exactly_two` | Un vrai zéro non trivial a exactement deux contacts vrais. | CONFIRMÉE | V20 | 0 |
| `RiemannHypothesisProof.trueContacts_ordered` | Les deux contacts sont ordonnés (gauche < droit). | CONFIRMÉE | V20 | 2 |
| `RiemannHypothesisProof.trueContacts_left_ge_two` | Le contact gauche est dans la région de comptage von Mangoldt (≥ 2). | CONFIRMÉE | AJOUT | 2 |
| `RiemannHypothesisProof.trueContacts_right_ge_two` | Le contact droit est ≥ 2. | CONFIRMÉE | AJOUT | 1 |
| `RiemannHypothesisProof.trueContacts_recover_gamma` | Les deux contacts vrais (étage 1) récupèrent γ. | CONFIRMÉE | V45 | 1 |
| `RiemannHypothesisProof.trueContacts_recover_beta` | Les deux contacts vrais récupèrent β. | CONFIRMÉE | V45 | 3 |
| `RiemannHypothesisProof.trueContacts_recover_member` | Les deux contacts vrais récupèrent le membre complet. | CONFIRMÉE | V45 | 2 |
| `RiemannHypothesisProof.trueContacts_member_injective` | L'application zéro ↦ paire de contacts vrais est injective. | CONFIRMÉE | V46 | 0 |
| `RiemannHypothesisProof.sameHeight_distinctBeta_contacts_ne` | Deux vrais zéros de même hauteur et de β différents ont des paires de contacts différentes. | CONFIRMÉE (domaine : deux vrais zéros de même hauteur et de β différents) | V163 | 2 |
| `RiemannHypothesisProof.sameHeight_not_contact_identity` | Deux vrais zéros de même hauteur et de β différents ne partagent pas l'identité de contacts. | CONFIRMÉE (domaine : deux vrais zéros de même hauteur et de β différents) | V163 | 0 |
| `RiemannHypothesisProof.tower_preserves_member` | La Tour conserve le membre : ZeroFromContacts(contacts) = zéro. | CONFIRMÉE | V45 | 0 |
| `RiemannHypothesisProof.tower_preserves_gamma` | La Tour conserve γ. | CONFIRMÉE | V45 | 0 |
| `RiemannHypothesisProof.tower_preserves_beta` | La Tour conserve β. | CONFIRMÉE | V45 | 0 |
| `RiemannHypothesisProof.tower_preserves_off_distinction` | Un zéro de β ≠ 1/2 a des contacts différents de ceux de son miroir (distinction hors ligne conservée). | CONFIRMÉE SOUS CONDITION (zéro hors ligne (β ≠ 1/2)) | V163 | 0 |
| `RiemannHypothesisProof.tower_no_recentering` | Un zéro hors ligne n'est pas recentré : le β relu depuis ses contacts reste le sien. | CONFIRMÉE SOUS CONDITION (zéro hors ligne (β ≠ 1/2)) | V45 | 0 |
| `RiemannHypothesisProof.trueContactCell_unique` | La cellule de contact canonique est unique : elle égale la paire de contacts vrais. | CONFIRMÉE | V20 | 0 |
| `RiemannHypothesisProof.HarmonicTower.mk.congr_simp` | Lemme de congruence auto-généré (contacts et étage égaux ⟹ tours égales). | CONFIRMÉE | AJOUT | 0 |

### `RiemannHypothesisProof.RHV2VonMangoldtCellRigidity`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.CanonicalContactCell.three_candidate_primes` | Les trois candidats (premier, pivot, troisième) de la cellule canonique sont premiers. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.CanonicalContactCell.three_candidate_primes_strictly_ordered` | Les trois candidats sont strictement ordonnés. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.CanonicalContactCell.two_candidate_gaps_positive` | Les deux écarts candidats sont strictement positifs. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_leftPrime_lock` | Verrou von Mangoldt : histoire reconstruite au rang de départ = premier gauche de la cellule. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_pivot_lock` | Verrou au pivot (rang de départ + 1). | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_rightPrime_lock` | Verrou au troisième premier (rang de départ + 2). | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_incomingGap_lock` | Verrou de l'écart entrant. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_outgoingGap_lock` | Verrou de l'écart sortant. | CONFIRMÉE | V48 | 0 |
| `RiemannHypothesisProof.CanonicalContactCell.occurrence_pair_distinct` | Les occurrences entrante et sortante sont distinctes. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_occurrence_pair_lock` | Verrou de la paire d'occurrences : la paire de transitions reconstruite au rang de départ égale la paire canonique. | CONFIRMÉE | V48 | 0 |

### `RiemannHypothesisProof.RHV2ZeroIdentity`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.TrueNontrivialZero.isTrue` | Un vrai zéro non trivial (structure) est un zéro non trivial. | CONFIRMÉE | V7 | 9 |
| `RiemannHypothesisProof.TrueNontrivialZero.gamma_pos` | Sa hauteur est strictement positive. | CONFIRMÉE | V7 | 2 |
| `RiemannHypothesisProof.trueZero_is_source_member` | Un vrai zéro non trivial est membre de la source des zéros. | CONFIRMÉE | V6 | 0 |
| `RiemannHypothesisProof.trivial_nontrivial_disjoint` | Un vrai zéro non trivial n'est pas trivial. | CONFIRMÉE | V6 | 0 |
| `RiemannHypothesisProof.trueZero_individual_identity` | Identité individuelle du vrai zéro (rho = rho) : énoncé tautologique. [INCIDENT : le nom « trueZero_individual_identity » promet plus que le type (x = x).] | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.same_member_all_readings` | Toutes les lectures (γ, β, multiplicité) d'un vrai zéro sont celles du même membre. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.no_member_substitution` | Aucune substitution de membre : mêmes valeurs ⟹ même vrai zéro. | CONFIRMÉE | AJOUT | 1 |
| `RiemannHypothesisProof.functionalMirror_trueNontrivialZero_gamma` | Le miroir fonctionnel d'un vrai zéro a même hauteur. | CONFIRMÉE | V65 | 2 |
| `RiemannHypothesisProof.functionalMirror_trueNontrivialZero_beta` | Le miroir a β complémentaire 1−β. | CONFIRMÉE | V65 | 2 |
| `RiemannHypothesisProof.off_member_ne_mirror` | Hors ligne, un vrai zéro diffère de son miroir fonctionnel. | CONFIRMÉE SOUS CONDITION (zéro hors ligne (β ≠ 1/2)) | V62 | 0 |
| `RiemannHypothesisProof.off_quartet_four_distinct` | Hors ligne, le quartet a quatre zéros non triviaux distincts. | CONFIRMÉE SOUS CONDITION (zéro hors ligne (β ≠ 1/2)) | V63 | 0 |
| `RiemannHypothesisProof.off_quartet_multiplicity_lock` | Le miroir fonctionnel a la même multiplicité. | CONFIRMÉE | V63 | 0 |
| `RiemannHypothesisProof.off_upperPair_sameHeight_distinctBeta` | Hors ligne, la paire supérieure a même hauteur et β différents. | CONFIRMÉE SOUS CONDITION (zéro hors ligne (β ≠ 1/2)) | V65 | 0 |
| `RiemannHypothesisProof.TrueNontrivialZero.mk.congr_simp` | Lemme de congruence auto-généré pour TrueNontrivialZero. | CONFIRMÉE | AJOUT | 1 |

### `RiemannHypothesisProof.RealSegmentNonvanishing`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.four_le_one_div_add_one_div_one_sub` | Le minimum de 1/x + 1/(1−x) sur ]0,1[ vaut 4. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `RiemannHypothesisProof.noRealZetaZeroInOpenUnitSegment_of_completedZeta₀_norm_lt_four` | Si ‖complétée₀‖ < 4 sur ]0,1[ alors ζ n'a pas de zéro réel dans ]0,1[. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `RiemannHypothesisProof.noRealZetaZeroInOpenUnitSegment` | THÉORÈME : ζ n'a aucun zéro réel dans le segment ouvert ]0,1[ (fait classique orthogonal, absent de Mathlib v4.31.0 selon la docstring). | CONFIRMÉE | AJOUT | 1 |

### `RiemannHypothesisProof.RiemannHypothesis`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.NonCentralFunctionalMirrorContradiction_of_samePassageComposition` | Sous la composition même-passage, tout vrai zéro non trivial hors ligne donne False. | IMPLIQUE RH SOUS PRÉMISSE (SamePassageGrammaticalRelationIsPreserved (⟺ RH par SamePassageGrammaticalRelationIsPreserved_iff_RiemannHypothesis) ; conclusion pointwise : tout zéro non trivial est critique (forme dépliée de RH)) | V140 | 1 |
| `RiemannHypothesisProof.ZeroNonTrivialIsCentral_proved_of_samePassageComposition` | Universalisation immédiate de la contradiction hors ligne : tout zéro non trivial est central. | IMPLIQUE RH SOUS PRÉMISSE (SamePassageGrammaticalRelationIsPreserved (⟺ RH) ; conclusion ZeroNonTrivialIsCentral (∀ρ non trivial, β=1/2 : forme dépliée de RH)) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 1 |
| `RiemannHypothesisProof.RiemannHypothesis_proved_of_samePassageComposition` | Terminal Mathlib après composition même-passage : RiemannHypothesis. | IMPLIQUE RH SOUS PRÉMISSE (SamePassageGrammaticalRelationIsPreserved (⟺ RH) ; conclusion RiemannHypothesis) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 0 |

### `RiemannHypothesisProof.SamePassageGrammar`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.ZeroGrammarPassage.index_lt` | Champ de ZeroGrammarPassage : l'indice est dans la liste des écarts. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.NonCentralFunctionalMirrorCreatesActualZeroGrammarNullPassage` | Un zéro hors ligne produit un passage nul dans la grammaire zéros canonique GZ. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V162 | 0 |
| `RiemannHypothesisProof.NonCentralFunctionalMirrorCreatesActualZeroGapReadout` | Forme positionnelle : il existe un indice i avec ZeroGapAt T i = some 0. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V162 | 0 |
| `RiemannHypothesisProof.NonCentralMirrorHasActualNullZeroPassageAndPositivePrimePlace` | Les données même-événement donnent à la fois un passage zéro nul et une place première à gap positif. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V162 | 0 |
| `RiemannHypothesisProof.NonCentralMirrorSameEventContactsRecoverMember` | Sur le même contexte, les contacts tangentiels relisent β et γ du membre fourni. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V45 | 0 |
| `RiemannHypothesisProof.NonCentralMirrorSameEventVonMangoldtGapLock` | Le même événement porte l'égalité entre le gap premier reconstruit depuis les zéros et le gap premier canonique. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V48 | 0 |
| `RiemannHypothesisProof.NonCentralMirrorSameEventPrimeGrammarIsCanonical` | EncZ = M est verrouillé sur le bloc même-événement construit. | CONFIRMÉE SOUS CONDITION (zéro positif hors ligne) | V48 | 0 |
| `RiemannHypothesisProof.False_of_SamePassageNullityFidelity` | Frontière formelle du terminal : la conservation de « ce même passage est nul » entre côté zéros et côté premiers donnerait False. | RÉFUTATION COMPILÉE (fidélité de nullité « ce même passage est nul » conservée côté premier (ZeroEntryIsNull ↔ PrimeEntryIsNull), sur une entrée hors ligne) | AJOUT | 0 |
| `RiemannHypothesisProof.ZeroNonTrivialIsCentral_of_SamePassageGrammaticalRelationIsPreserved` | Si la composition même-passage est fournie, tout zéro non trivial est central. | IMPLIQUE RH SOUS PRÉMISSE (SamePassageGrammaticalRelationIsPreserved (⟺ RH) ; conclusion ZeroNonTrivialIsCentral (forme dépliée de RH)) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 2 |
| `RiemannHypothesisProof.RiemannHypothesis_of_SamePassageGrammaticalRelationIsPreserved` | Pont terminal vers l'énoncé Mathlib, conditionnel exactement sur la composition même-passage. | IMPLIQUE RH SOUS PRÉMISSE (SamePassageGrammaticalRelationIsPreserved (⟺ RH) ; conclusion RiemannHypothesis) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 1 |
| `RiemannHypothesisProof.SamePassageGrammaticalRelationIsPreserved_of_RiemannHypothesis` | RH entraîne la composition même-passage (RH en hypothèse). | CONFIRMÉE | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 1 |
| `RiemannHypothesisProof.SamePassageGrammaticalRelationIsPreserved_iff_RiemannHypothesis` | Certificat de force : composition même-passage ⟺ RiemannHypothesis (non utilisé dans la preuve terminale). | ÉQUIVALENTE À RH (SamePassageGrammaticalRelationIsPreserved) | O7 (touche le point ouvert : RH atteinte seulement sous prémisse) | 0 |

### `RiemannHypothesisProof.TrivialZeroGeometry`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.ZeroTrivialAtIndex_eq` | Recollement : le zéro trivial d'indice n du maître est −2(n+1). | CONFIRMÉE | AJOUT | 1 |
| `RiemannHypothesisProof.ZeroTrivialMultiplicityIsOne` | La multiplicité d'un zéro trivial est exactement 1 (inconditionnel). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `RiemannHypothesisProof.ZeroTrivialFamilyIsFixedUnitBackground` | Le fond trivial est fixe et sans multiplicité libre : chaque zéro trivial est un zéro de ζ d'ordre 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `RiemannHypothesisProof.ZeroTrivialHasNoContactGeometry` | Un zéro trivial n'a pas de hauteur (γ=0) donc pas de paire de contacts : géométrie propre (le trivial n'est pas un vrai zéro non trivial). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V9 | 0 |
| `RiemannHypothesisProof.ZeroTrivialMirrorStaysAtZeroHeight` | Le miroir fonctionnel d'un zéro trivial reste à hauteur nulle. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `RiemannHypothesisProof.FunctionalQuartetDoesNotModifyZeroTrivialFamily` | Un quartet non trivial ne modifie jamais la famille triviale (aucun de ses membres n'est trivial). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V63 | 0 |
| `RiemannHypothesisProof.EveryCompensatingZeroMustBelongToCompleteNonTrivialZeroSource` | Tout zéro compensateur (zéro de ζ de hauteur ≠ 0) appartient à la source non triviale, jamais au fond trivial. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |

### `RiemannHypothesisProof.ZeroObjects`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.ZeroTrivial_eq_canonical` | ZeroTrivial de la bibliothèque est IsTrivialZetaZero. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.ZeroNonTrivial_eq_canonical` | ZeroNonTrivial de la bibliothèque est IsNontrivialZetaZero. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.MultiplicityForZero_eq_canonical` | MultiplicityForZero est zetaZeroMultiplicity. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.zeroBeta_def` | BetaForZero ρ = Re ρ. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.zeroGamma_def` | GammaForZero ρ = Im ρ. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.ZeroNonTrivial.isZero` | Un zéro non trivial annule ζ. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V6 | 7 |
| `RiemannHypothesisProof.ZeroNonTrivial.notZeroTrivial` | Un zéro non trivial n'est pas trivial. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V6 | 6 |
| `RiemannHypothesisProof.ZeroNonTrivial.ne_one` | Un zéro non trivial est ≠ 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V6 | 4 |
| `RiemannHypothesisProof.ZeroNonTrivial.re_pos` | Un zéro non trivial a β > 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V7 | 7 |
| `RiemannHypothesisProof.ZeroNonTrivial.re_lt_one` | Un zéro non trivial a β < 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V7 | 5 |
| `RiemannHypothesisProof.not_ZeroTrivial_of_re_pos` | Un point de partie réelle > 0 n'est jamais un zéro trivial. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `RiemannHypothesisProof.ne_one_of_re_lt_one` | Un point de partie réelle < 1 n'est jamais le pôle. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `RiemannHypothesisProof.ZeroNonTrivial.mk'` | Constructeur canonique : annulation de ζ plus 0 < β < 1 donnent un zéro non trivial. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V7 | 2 |
| `RiemannHypothesisProof.ZeroNonTrivial.ne_neg_nat` | Un vrai zéro non trivial n'est en aucun entier négatif (équation fonctionnelle). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V6 | 1 |
| `RiemannHypothesisProof.ZeroZetaHasZeroValue` | Un ZeroZeta annule ζ. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `RiemannHypothesisProof.ZeroTrivialIsZeroZeta` | Un zéro trivial est un ZeroZeta. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `RiemannHypothesisProof.ZeroTrivialHasRealNegativeCoordinate` | Un zéro trivial a β < 0 et γ = 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 1 |
| `RiemannHypothesisProof.ZeroTrivialHasZeroGamma` | Un zéro trivial a γ = 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 3 |
| `RiemannHypothesisProof.ZeroTrivialIsFixedByConjugation` | La conjugaison fixe un zéro trivial. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `RiemannHypothesisProof.ZeroNonTrivialIsZeroZeta` | Un zéro non trivial est un ZeroZeta. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `RiemannHypothesisProof.ZeroNonTrivialMultiplicityPositive'` | Un zéro non trivial a une multiplicité strictement positive. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V12 | 0 |
| `RiemannHypothesisProof.ZeroNonTrivialBetaPositive` | β d'un zéro non trivial est > 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V7 | 0 |
| `RiemannHypothesisProof.ZeroNonTrivialBetaLessThanOne` | β d'un zéro non trivial est < 1. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V7 | 0 |
| `RiemannHypothesisProof.ZeroNonTrivialIsNotZeroTrivial` | Un zéro non trivial n'est pas trivial. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V6 | 0 |
| `RiemannHypothesisProof.ZeroTrivialAndZeroNonTrivialAreDisjoint` | Les deux régimes (trivial / non trivial) sont disjoints. | CONFIRMÉE | V6 | 0 |
| `RiemannHypothesisProof.ZeroTrivialFamilyIsFixed` | La famille triviale est fixe : ρ est trivial ⟺ ρ = −2(n+1). | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.ZeroMultiplicityIsIntegral` | La multiplicité est entière. | CONFIRMÉE | AJOUT | 0 |

### `RiemannHypothesisProof.ZeroSymmetries`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.ZeroNonTrivial.im_ne_zero` | La hauteur d'un vrai zéro non trivial est non nulle (théorème, non champ postulé). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V7 | 4 |
| `RiemannHypothesisProof.ZeroNonTrivialGammaNonZero` | Forme sémantique : γ d'un membre non trivial est non nulle. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V7 | 0 |
| `RiemannHypothesisProof.FunctionalMirrorPreservesGamma` | Le miroir conserve exactement la hauteur. | CONFIRMÉE | V65 | 2 |
| `RiemannHypothesisProof.FunctionalMirrorComplementsBeta` | Le miroir a la position radiale complémentaire 1−β. | CONFIRMÉE | V65 | 1 |
| `RiemannHypothesisProof.FunctionalMirrorIsInvolutive` | Le miroir est une involution. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.ConjugateForZeroPreservesBeta` | Le conjugué conserve β. | CONFIRMÉE | V63 | 0 |
| `RiemannHypothesisProof.ConjugateForZeroOpposesGamma` | Le conjugué inverse la hauteur. | CONFIRMÉE | V63 | 0 |
| `RiemannHypothesisProof.FunctionalMirrorEqualsZeroIffCentral` | Point fixe du miroir : le membre et son miroir sont le même ⟺ β=1/2. | CONFIRMÉE | V77 | 3 |
| `RiemannHypothesisProof.NonCentralFunctionalMirrorIsDistinct` | Hors du centre, le membre et son miroir sont deux membres distincts. | CONFIRMÉE SOUS CONDITION (zéro hors ligne (β ≠ 1/2)) | V62 | 1 |
| `RiemannHypothesisProof.FunctionalMirrorForZeroIsZeroNonTrivial` | Le miroir fonctionnel d'un vrai zéro non trivial est un vrai zéro non trivial (théorème, non hypothèse). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V63 | 2 |
| `RiemannHypothesisProof.FunctionalMirrorPreservesMultiplicity` | Le miroir conserve la multiplicité (théorème par transport de l'ordre analytique). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V63 | 2 |
| `RiemannHypothesisProof.ConjugateForZeroIsZeroNonTrivial` | Le conjugué d'un vrai zéro non trivial est un vrai zéro non trivial. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V63 | 2 |
| `RiemannHypothesisProof.ConjugateForZeroPreservesMultiplicity` | Le conjugué conserve la multiplicité. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V63 | 1 |
| `RiemannHypothesisProof.ConjugateForZeroIsDistinctFromZeroNonTrivial` | Le conjugué n'est jamais le membre lui-même (hauteur non nulle). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V63 | 1 |
| `RiemannHypothesisProof.NonCentralFunctionalQuartetHasFourDistinctZeros` | Quartet vrai : les quatre membres sont de vrais zéros non triviaux, deux à deux distincts hors ligne. | CONFIRMÉE SOUS CONDITION (zéro non trivial hors ligne (β ≠ 1/2)) | V63 | 1 |

### `RiemannHypothesisProof.ZetaReflection`

_Bibliothèque RiemannHypothesisProof : module marqué « compilé » dans `data/rh_gap_criterion_modules.tsv` (oleans présents, théorèmes extraits) : audité comme les autres modules du lot ; voir « Incidents »._

| théorème | énoncé sémantique | statut | Vi / AJOUT | entraîne |
|---|---|---|---|---|
| `RiemannHypothesisProof.zeta_conj_of_one_lt_re` | Pour Re s > 1, conj(ζ(conj s)) = ζ(s). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `RiemannHypothesisProof.riemannZeta_conj` | Réflexion de Schwarz pour zêta : ζ(conj s) = conj(ζ s) hors du pôle. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V63 | 3 |
| `RiemannHypothesisProof.tendsto_conj_nhds` | La conjugaison tend vers w quand z tend vers conj w. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.analyticAt_conj_conj` | Si f est analytique en w, z ↦ conj(f(conj z)) est analytique en conj w. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `RiemannHypothesisProof.analyticOrderAt_conj_conj` | L'ordre d'annulation de conj ∘ f ∘ conj en conj w est celui de f en w. | CONFIRMÉE | AJOUT | 1 |
| `RiemannHypothesisProof.analyticOrderAt_zeta_conj` | L'ordre de zêta est symétrique par conjugaison hors du pôle. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V63 | 2 |
| `RiemannHypothesisProof.two_pi_ne_zero'` | 2π ≠ 0. | CONFIRMÉE | AJOUT | 0 |
| `RiemannHypothesisProof.Efac_ne_zero` | Le facteur Efac est non nul dans la bande ouverte. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `RiemannHypothesisProof.analyticAt_Efac` | Efac est analytique pour Re s > 0. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `RiemannHypothesisProof.analyticOrderAt_zeta_one_sub` | Transport d'ordre par l'équation fonctionnelle : dans la bande ouverte, ord_{1−w} ζ = ord_w ζ. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V63 | 1 |
| `RiemannHypothesisProof.analyticAt_riemannZeta` | ζ est analytique en tout point autre que son pôle. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `RiemannHypothesisProof.analyticOrderAt_riemannZeta_ne_top` | L'ordre d'annulation de ζ en w ≠ 1 est fini. | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | AJOUT | 0 |
| `RiemannHypothesisProof.ZeroNonTrivialMultiplicityPositive` | La multiplicité d'un vrai zéro non trivial est strictement positive (démontrée, non postulée). | CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé) | V12 | 0 |
<!-- TABLES END -->

## Modules non compilés de la bibliothèque `RiemannHypothesisProof` (hors lot, non audités comme vérités)

Selon `data/rh_gap_criterion_modules.tsv` (colonne d'état de compilation) et `data/SUMMARY.md` : les 15 modules suivants ne sont pas compilés (« source plus récent » ou « olean absent ») ; leurs théorèmes ne sont pas dans `rh_gap_criterion.jsonl` et ne sont audités ici ni comme vérités ni autrement.

- `RiemannHypothesisProof` : NON COMPILÉ (source plus récent)
- `RiemannHypothesisProof.CompletedZetaZeroBound` : NON COMPILÉ (source plus récent)
- `RiemannHypothesisProof.ContactPrimeBlockOverlap` : NON COMPILÉ (olean absent)
- `RiemannHypothesisProof.HarmonicTower` : NON COMPILÉ (source plus récent)
- `RiemannHypothesisProof.PrimeHistory` : NON COMPILÉ (source plus récent)
- `RiemannHypothesisProof.RHV2ContactPrimeReadout` : NON COMPILÉ (olean absent)
- `RiemannHypothesisProof.RHV2FirstThreePrimeStage` : NON COMPILÉ (olean absent)
- `RiemannHypothesisProof.RHV2ForwardPrimeWindow` : NON COMPILÉ (olean absent)
- `RiemannHypothesisProof.RHV2GrammarFragment` : NON COMPILÉ (source plus récent)
- `RiemannHypothesisProof.RHV2Master` : NON COMPILÉ (source plus récent)
- `RiemannHypothesisProof.RHV2PivotFreeThreePrimeLocalization` : NON COMPILÉ (olean absent)
- `RiemannHypothesisProof.RHV2ThreeZeroOverlap` : NON COMPILÉ (source plus récent)
- `RiemannHypothesisProof.RHV2TwoZeroPrimeBridge` : NON COMPILÉ (olean absent)
- `RiemannHypothesisProof.Universalisation` : NON COMPILÉ (source plus récent)
- `RiemannHypothesisProof.ZeroGrammar` : NON COMPILÉ (source plus récent)

(15 modules.)

## Correspondance avec RHV6Fresh

Méthode : comparaison mécanique des types (après retrait des préfixes de namespace `RhGap.`, `RHV3Lean.`, `RHV6Fresh.`, `RiemannHypothesisProof.`) avec `data/RHV6Fresh.jsonl` (théorèmes de RHV6Fresh) et `data/rhv3_lean.jsonl` (base `rhv3_lean` de RHV6Fresh, première autorité §2 avec le code RHV6Fresh), puis relecture manuelle pour les correspondances sémantiques.

### A. Types identiques dans RHV6Fresh (8 théorèmes du lot)

| théorème du lot | théorème RHV6Fresh | remarque |
|---|---|---|
| `zetaReflect_re` | `RHV6Fresh.zetaReflect_re` | statement identique ; NB : `zetaReflect` est défini `1 − conj ρ` dans RHV6Fresh (port zeta23) et `1 − ρ` ici (cf. Incidents), le type de `zetaReflect_re` coïncide sans que les définitions coïncident |
| `RiemannHypothesisProof.Efac_ne_zero` | `RHV6Fresh.Efac_ne_zero` | type identique après retrait des préfixes |
| `RiemannHypothesisProof.analyticAt_Efac` | `RHV6Fresh.analyticAt_Efac` | type identique après retrait des préfixes |
| `RiemannHypothesisProof.analyticAt_conj_conj` | `RHV6Fresh.analyticAt_conj_conj` | type identique après retrait des préfixes |
| `RiemannHypothesisProof.analyticOrderAt_conj_conj` | `RHV6Fresh.analyticOrderAt_conj_conj` | type identique après retrait des préfixes |
| `RiemannHypothesisProof.analyticOrderAt_zeta_one_sub` | `RHV6Fresh.analyticOrderAt_zeta_one_sub` | type identique après retrait des préfixes |
| `RiemannHypothesisProof.tendsto_conj_nhds` | `RHV6Fresh.tendsto_conj_nhds` | type identique après retrait des préfixes |
| `RiemannHypothesisProof.two_pi_ne_zero'` | `RHV6Fresh.two_pi_ne_zero'` | type identique après retrait des préfixes |

### B. Types identiques dans la base `rhv3_lean` de RHV6Fresh (404 théorèmes du lot)

Ces vérités (essentiellement les ports d'analyse `P4_*`, `Perron*`, `Zeta*`, les zéros triviaux, la réflexion/multiplicité et les objets quartet/soudure) sont donc aussi établies dans la base de RHV6Fresh ; RHV6Fresh les importe, elles ne sont pas des théorèmes de `RHV6Fresh/` proprement dit. Certaines instances (`congr_simp`, `ofNat_ctorIdx`) sont des lemmes auto-générés.

| théorème du lot | théorème `rhv3_lean` |
|---|---|
| `Backlund.Gamma_le_two_mul_factorial` | `Backlund.Gamma_le_two_mul_factorial` |
| `Backlund.Gamma_le_two_of_mem_Icc` | `Backlund.Gamma_le_two_of_mem_Icc` |
| `Backlund.divisor_surrogate_eq_order` | `Backlund.divisor_surrogate_eq_order` |
| `Backlund.exists_zeta_bound_right` | `Backlund.exists_zeta_bound_right` |
| `Backlund.log_le_two_mul_sqrt` | `Backlund.log_le_two_mul_sqrt` |
| `Backlund.log_one_add_mul_le` | `Backlund.log_one_add_mul_le` |
| `Backlund.norm_Gamma_le_Gamma_re` | `Backlund.norm_Gamma_le_Gamma_re` |
| `Backlund.norm_cos_le_exp` | `Backlund.norm_cos_le_exp` |
| `Backlund.surrogate_growth_band` | `Backlund.surrogate_growth_band` |
| `Backlund.surrogate_growth_left` | `Backlund.surrogate_growth_left` |
| `Backlund.surrogate_growth_right` | `Backlund.surrogate_growth_right` |
| `Backlund.zetaCounting_crude_majorant` | `Backlund.zetaCounting_crude_majorant` |
| `Backlund.zetaCounting_le_surrogate_mass` | `Backlund.zetaCounting_le_surrogate_mass` |
| `Backlund.zetaSurrogate_differentiable` | `Backlund.zetaSurrogate_differentiable` |
| `Backlund.zetaSurrogate_eventuallyEq` | `Backlund.zetaSurrogate_eventuallyEq` |
| `Backlund.zetaSurrogate_log_growth` | `Backlund.zetaSurrogate_log_growth` |
| `Backlund.zetaSurrogate_zeros_in_closedBall₀_count` | `Backlund.zetaSurrogate_zeros_in_closedBall₀_count` |
| `Backlund.zeta_norm_le_subband` | `Backlund.zeta_norm_le_subband` |
| `Backlund.zeta_zero_re_mem_of_im_pos` | `Backlund.zeta_zero_re_mem_of_im_pos` |
| `LSeriesSummable_vonMangoldt_of_one_lt_re` | `RHV3Lean.LSeriesSummable_vonMangoldt_of_one_lt_re` |
| `P4_4b.exists_divisorZeroIndex₀_val_eq_of_zero` | `RHV3Lean.P4_4b.exists_divisorZeroIndex₀_val_eq_of_zero` |
| `P4_4b.exists_point_Ioo_separated_from_finset` | `RHV3Lean.P4_4b.exists_point_Ioo_separated_from_finset` |
| `P4_4b.exists_quantitative_good_height_between` | `RHV3Lean.P4_4b.exists_quantitative_good_height_between` |
| `P4_4b.exists_quantitative_perronRectangleAdmissible_height_between` | `RHV3Lean.P4_4b.exists_quantitative_perronRectangleAdmissible_height_between` |
| `P4_4b.exists_riemannXi_divisorZeroIndex₀_val_eq_of_isNontrivialZetaZero` | `RHV3Lean.P4_4b.exists_riemannXi_divisorZeroIndex₀_val_eq_of_isNontrivialZetaZero` |
| `P4_4b.nontrivialZetaForbiddenHeightsBelow_card_le` | `RHV3Lean.P4_4b.nontrivialZetaForbiddenHeightsBelow_card_le` |
| `P4_4b.nontrivialZetaZerosByHeightFinset_card_le_order_one_plus` | `RHV3Lean.P4_4b.nontrivialZetaZerosByHeightFinset_card_le_order_one_plus` |
| `P4_4b.nontrivialZetaZerosByHeightFinset_card_le_riemannXi_divisorMassClosedBall₀` | `RHV3Lean.P4_4b.nontrivialZetaZerosByHeightFinset_card_le_riemannXi_divisorMassClosedBall₀` |
| `P4_4b.norm_complex_le_abs_re_add_abs_im` | `RHV3Lean.P4_4b.norm_complex_le_abs_re_add_abs_im` |
| `P4_4b.norm_le_height_plus_one_of_mem_nontrivialZetaZerosByHeightFinset` | `RHV3Lean.P4_4b.norm_le_height_plus_one_of_mem_nontrivialZetaZerosByHeightFinset` |
| `P4_4b.riemannXi_divisorMassClosedBall₀_le_order_one_plus` | `RHV3Lean.P4_4b.riemannXi_divisorMassClosedBall₀_le_order_one_plus` |
| `P4_4b.riemannXi_eq_zero_of_isNontrivialZetaZero` | `RHV3Lean.P4_4b.riemannXi_eq_zero_of_isNontrivialZetaZero` |
| `P4_4c.abs_abs_height_sub_im_le_norm_horizontal` | `RHV3Lean.P4_4c.abs_abs_height_sub_im_le_norm_horizontal` |
| `P4_4c.completedZetaFactor_eq_riemannXi_of_im_ne_zero` | `RHV3Lean.P4_4c.completedZetaFactor_eq_riemannXi_of_im_ne_zero` |
| `P4_4c.completedZetaFactor_eventuallyEq_riemannXi_of_im_ne_zero` | `RHV3Lean.P4_4c.completedZetaFactor_eventuallyEq_riemannXi_of_im_ne_zero` |
| `P4_4c.digamma_add_nat_eq` | `RHV3Lean.P4_4c.digamma_add_nat_eq` |
| `P4_4c.exists_grid_point_with_separation_and_inverse_sum` | `RHV3Lean.P4_4c.exists_grid_point_with_separation_and_inverse_sum` |
| `P4_4c.exists_height_with_separation_and_inverse_sum_bound` | `RHV3Lean.P4_4c.exists_height_with_separation_and_inverse_sum_bound` |
| `P4_4c.exists_horizontal_digamma_rpow_bound` | `RHV3Lean.P4_4c.exists_horizontal_digamma_rpow_bound` |
| `P4_4c.exists_le_of_sum_le_card_mul` | `RHV3Lean.P4_4c.exists_le_of_sum_le_card_mul` |
| `P4_4c.exists_perron_height_with_horizontal_negLogDeriv_bound` | `RHV3Lean.P4_4c.exists_perron_height_with_horizontal_negLogDeriv_bound` |
| `P4_4c.fin_orderIso_positive_nat_bound` | `RHV3Lean.P4_4c.fin_orderIso_positive_nat_bound` |
| `P4_4c.grid_bad_card_le` | `RHV3Lean.P4_4c.grid_bad_card_le` |
| `P4_4c.grid_close_iff_norm_close` | `RHV3Lean.P4_4c.grid_close_iff_norm_close` |
| `P4_4c.grid_close_index_unique` | `RHV3Lean.P4_4c.grid_close_index_unique` |
| `P4_4c.grid_distance_eq_abs_sub_u_div` | `RHV3Lean.P4_4c.grid_distance_eq_abs_sub_u_div` |
| `P4_4c.grid_harmonic_constant_le_power` | `RHV3Lean.P4_4c.grid_harmonic_constant_le_power` |
| `P4_4c.grid_inverse_distance_sum_le_harmonic` | `RHV3Lean.P4_4c.grid_inverse_distance_sum_le_harmonic` |
| `P4_4c.grid_inverse_eq_M_mul_norm_inv` | `RHV3Lean.P4_4c.grid_inverse_eq_M_mul_norm_inv` |
| `P4_4c.grid_not_close_abs_sub_u_ge_quarter` | `RHV3Lean.P4_4c.grid_not_close_abs_sub_u_ge_quarter` |
| `P4_4c.grid_not_close_inverse_le_fourM` | `RHV3Lean.P4_4c.grid_not_close_inverse_le_fourM` |
| `P4_4c.grid_point_diff_abs` | `RHV3Lean.P4_4c.grid_point_diff_abs` |
| `P4_4c.grid_point_mem_Ioo` | `RHV3Lean.P4_4c.grid_point_mem_Ioo` |
| `P4_4c.hadamard_far_term_norm_le` | `RHV3Lean.P4_4c.hadamard_far_term_norm_le` |
| `P4_4c.hadamard_far_tsum_norm_le` | `RHV3Lean.P4_4c.hadamard_far_tsum_norm_le` |
| `P4_4c.hadamard_near_sum_norm_le` | `RHV3Lean.P4_4c.hadamard_near_sum_norm_le` |
| `P4_4c.hadamard_pair_eq` | `RHV3Lean.P4_4c.hadamard_pair_eq` |
| `P4_4c.harmonic_mono_real` | `RHV3Lean.P4_4c.harmonic_mono_real` |
| `P4_4c.horizontal_neg_zeta_logDeriv_norm_le_of_xi_digamma` | `RHV3Lean.P4_4c.horizontal_neg_zeta_logDeriv_norm_le_of_xi_digamma` |
| `P4_4c.horizontal_point_ne_xi_divisor` | `RHV3Lean.P4_4c.horizontal_point_ne_xi_divisor` |
| `P4_4c.inv_orderIso_le_inv_succ` | `RHV3Lean.P4_4c.inv_orderIso_le_inv_succ` |
| `P4_4c.left_far_norm_inv_le` | `RHV3Lean.P4_4c.left_far_norm_inv_le` |
| `P4_4c.left_far_norm_sum_le_harmonic` | `RHV3Lean.P4_4c.left_far_norm_sum_le_harmonic` |
| `P4_4c.logDeriv_completedZetaFactor_eq_riemannXi_of_im_ne_zero` | `RHV3Lean.P4_4c.logDeriv_completedZetaFactor_eq_riemannXi_of_im_ne_zero` |
| `P4_4c.mem_xiDivisorNearFinset` | `RHV3Lean.P4_4c.mem_xiDivisorNearFinset` |
| `P4_4c.normalized_grid_inverse_sum_le` | `RHV3Lean.P4_4c.normalized_grid_inverse_sum_le` |
| `P4_4c.right_far_norm_inv_le` | `RHV3Lean.P4_4c.right_far_norm_inv_le` |
| `P4_4c.right_far_norm_sum_le_harmonic` | `RHV3Lean.P4_4c.right_far_norm_sum_le_harmonic` |
| `P4_4c.sum_inv_natCast_le_harmonic_card` | `RHV3Lean.P4_4c.sum_inv_natCast_le_harmonic_card` |
| `P4_4c.xiDivisorNearFinset_card_le_divisorMassClosedBall₀` | `RHV3Lean.P4_4c.xiDivisorNearFinset_card_le_divisorMassClosedBall₀` |
| `P4_4c.xiDivisorZ₂_nonneg` | `RHV3Lean.P4_4c.xiDivisorZ₂_nonneg` |
| `P4_4c.xiDivisor_near_norm_inv_sum_le_card_add_Z₂` | `RHV3Lean.P4_4c.xiDivisor_near_norm_inv_sum_le_card_add_Z₂` |
| `P4_4c.xiHadamard_near_term_norm_le` | `RHV3Lean.P4_4c.xiHadamard_near_term_norm_le` |
| `P4_4c.xi_horizontal_logDeriv_bound_from_quantitative_hadamard` | `RHV3Lean.P4_4c.xi_horizontal_logDeriv_bound_from_quantitative_hadamard` |
| `P4_4c.xi_logDeriv_horizontal_absorption` | `RHV3Lean.P4_4c.xi_logDeriv_horizontal_absorption` |
| `P4_4c.xi_logDeriv_horizontal_raw_bound` | `RHV3Lean.P4_4c.xi_logDeriv_horizontal_raw_bound` |
| `P4_4d.exists_admissible_heights_horizontal_perron_integrals_tendsto_zero` | `RHV3Lean.P4_4d.exists_admissible_heights_horizontal_perron_integrals_tendsto_zero` |
| `P4_4d.horizontal_HIntegral'_norm_le` | `RHV3Lean.P4_4d.horizontal_HIntegral'_norm_le` |
| `P4_4d.one_half_lt_one` | `RHV3Lean.P4_4d.one_half_lt_one` |
| `P4_4d.one_half_pos` | `RHV3Lean.P4_4d.one_half_pos` |
| `P4_4d.perronRectangleSigmaL_le_sigmaR` | `RHV3Lean.P4_4d.perronRectangleSigmaL_le_sigmaR` |
| `P4_4d.perron_kernel_horizontal_bound` | `RHV3Lean.P4_4d.perron_kernel_horizontal_bound` |
| `P4_4d.rpow_three_halves_div_sq_le_four_inv_sqrt` | `RHV3Lean.P4_4d.rpow_three_halves_div_sq_le_four_inv_sqrt` |
| `P4_4d.zetaPerronIntegrand_horizontal_pointwise_bound` | `RHV3Lean.P4_4d.zetaPerronIntegrand_horizontal_pointwise_bound` |
| `P4_4d.zetaPerron_horizontal_integrals_bound` | `RHV3Lean.P4_4d.zetaPerron_horizontal_integrals_bound` |
| `P4_4d.zetaPerron_horizontal_integrals_sqrt_bound` | `RHV3Lean.P4_4d.zetaPerron_horizontal_integrals_sqrt_bound` |
| `P4_4e.analyticAt_zetaPerronIntegrand_left` | `RHV3Lean.P4_4e.analyticAt_zetaPerronIntegrand_left` |
| `P4_4e.continuous_left_vertical_zetaPerronIntegrand` | `RHV3Lean.P4_4e.continuous_left_vertical_zetaPerronIntegrand` |
| `P4_4e.exists_admissible_heights_all_left_boundary_limits` | `RHV3Lean.P4_4e.exists_admissible_heights_all_left_boundary_limits` |
| `P4_4e.leftDigammaPoint_abs_re_ge_half` | `RHV3Lean.P4_4e.leftDigammaPoint_abs_re_ge_half` |
| `P4_4e.leftDigammaPoint_add_nat_ne_neg_nat` | `RHV3Lean.P4_4e.leftDigammaPoint_add_nat_ne_neg_nat` |
| `P4_4e.leftDigammaPoint_add_nat_re` | `RHV3Lean.P4_4e.leftDigammaPoint_add_nat_re` |
| `P4_4e.leftDigammaPoint_digamma_add_nat` | `RHV3Lean.P4_4e.leftDigammaPoint_digamma_add_nat` |
| `P4_4e.leftDigammaPoint_digamma_eq_shift_sub_sum` | `RHV3Lean.P4_4e.leftDigammaPoint_digamma_eq_shift_sub_sum` |
| `P4_4e.leftDigammaPoint_inv_norm_le_two` | `RHV3Lean.P4_4e.leftDigammaPoint_inv_norm_le_two` |
| `P4_4e.leftDigammaPoint_inv_sum_norm_le` | `RHV3Lean.P4_4e.leftDigammaPoint_inv_sum_norm_le` |
| `P4_4e.leftDigammaPoint_no_poles_in_range` | `RHV3Lean.P4_4e.leftDigammaPoint_no_poles_in_range` |
| `P4_4e.leftDigammaPoint_shift` | `RHV3Lean.P4_4e.leftDigammaPoint_shift` |
| `P4_4e.leftVerticalLogDerivConstant_pos` | `RHV3Lean.P4_4e.leftVerticalLogDerivConstant_pos` |
| `P4_4e.leftVerticalLogDerivConstant_spec` | `RHV3Lean.P4_4e.leftVerticalLogDerivConstant_spec` |
| `P4_4e.leftVerticalScalarBound_nonneg` | `RHV3Lean.P4_4e.leftVerticalScalarBound_nonneg` |
| `P4_4e.leftVerticalUniversalMajorantMass_nonneg` | `RHV3Lean.P4_4e.leftVerticalUniversalMajorantMass_nonneg` |
| `P4_4e.leftVerticalUniversalMajorant_continuous` | `RHV3Lean.P4_4e.leftVerticalUniversalMajorant_continuous` |
| `P4_4e.leftVerticalUniversalMajorant_integrable` | `RHV3Lean.P4_4e.leftVerticalUniversalMajorant_integrable` |
| `P4_4e.leftVerticalUniversalMajorant_le` | `RHV3Lean.P4_4e.leftVerticalUniversalMajorant_le` |
| `P4_4e.leftVerticalUniversalMajorant_nonneg` | `RHV3Lean.P4_4e.leftVerticalUniversalMajorant_nonneg` |
| `P4_4e.leftVertical_rpow_geometric_rewrite` | `RHV3Lean.P4_4e.leftVertical_rpow_geometric_rewrite` |
| `P4_4e.left_vertical_boundary_tendsto_zero` | `RHV3Lean.P4_4e.left_vertical_boundary_tendsto_zero` |
| `P4_4e.left_vertical_full_norm_le` | `RHV3Lean.P4_4e.left_vertical_full_norm_le` |
| `P4_4e.left_vertical_negLogDeriv_functional_identity` | `RHV3Lean.P4_4e.left_vertical_negLogDeriv_functional_identity` |
| `P4_4e.left_vertical_negLogDeriv_rpow_bound` | `RHV3Lean.P4_4e.left_vertical_negLogDeriv_rpow_bound` |
| `P4_4e.left_vertical_negLogDeriv_uniform_sqrt_bound` | `RHV3Lean.P4_4e.left_vertical_negLogDeriv_uniform_sqrt_bound` |
| `P4_4e.left_vertical_normalization_norm_le_one` | `RHV3Lean.P4_4e.left_vertical_normalization_norm_le_one` |
| `P4_4e.left_vertical_reflected_digamma_bound_uniform` | `RHV3Lean.P4_4e.left_vertical_reflected_digamma_bound_uniform` |
| `P4_4e.left_vertical_reflected_logDeriv_uniform_bound` | `RHV3Lean.P4_4e.left_vertical_reflected_logDeriv_uniform_bound` |
| `P4_4e.left_vertical_reflected_riemannZeta_ne_zero` | `RHV3Lean.P4_4e.left_vertical_reflected_riemannZeta_ne_zero` |
| `P4_4e.left_vertical_riemannZeta_ne_zero` | `RHV3Lean.P4_4e.left_vertical_riemannZeta_ne_zero` |
| `P4_4e.left_vertical_scalar_bound_tendsto_zero` | `RHV3Lean.P4_4e.left_vertical_scalar_bound_tendsto_zero` |
| `P4_4e.left_vertical_shifted_digamma_bound` | `RHV3Lean.P4_4e.left_vertical_shifted_digamma_bound` |
| `P4_4e.left_vertical_shifted_digamma_bound_uniform` | `RHV3Lean.P4_4e.left_vertical_shifted_digamma_bound_uniform` |
| `P4_4e.left_vertical_truncated_tendsto_full` | `RHV3Lean.P4_4e.left_vertical_truncated_tendsto_full` |
| `P4_4e.left_vertical_zetaPerronIntegrand_integrable` | `RHV3Lean.P4_4e.left_vertical_zetaPerronIntegrand_integrable` |
| `P4_4e.left_vertical_zetaPerronIntegrand_pointwise_bound` | `RHV3Lean.P4_4e.left_vertical_zetaPerronIntegrand_pointwise_bound` |
| `P4_4e.log_abs_add_two_le_four_mul_sqrt` | `RHV3Lean.P4_4e.log_abs_add_two_le_four_mul_sqrt` |
| `P4_4e.one_lt_one_sub_sN_re` | `RHV3Lean.P4_4e.one_lt_one_sub_sN_re` |
| `P4_4e.one_sub_sN_div_two_eq_reflectedDigammaBase_add_nat` | `RHV3Lean.P4_4e.one_sub_sN_div_two_eq_reflectedDigammaBase_add_nat` |
| `P4_4e.one_sub_sN_ne_one` | `RHV3Lean.P4_4e.one_sub_sN_ne_one` |
| `P4_4e.perron_kernel_left_vertical_bound` | `RHV3Lean.P4_4e.perron_kernel_left_vertical_bound` |
| `P4_4e.perron_left_div_two_eq_leftDigammaPoint` | `RHV3Lean.P4_4e.perron_left_div_two_eq_leftDigammaPoint` |
| `P4_4e.reflectedDigammaBase_add_nat_ne_neg_nat` | `RHV3Lean.P4_4e.reflectedDigammaBase_add_nat_ne_neg_nat` |
| `P4_4e.reflectedDigammaBase_add_nat_re` | `RHV3Lean.P4_4e.reflectedDigammaBase_add_nat_re` |
| `P4_4e.reflectedDigammaBase_inv_norm_le_one` | `RHV3Lean.P4_4e.reflectedDigammaBase_inv_norm_le_one` |
| `P4_4e.reflectedDigammaBase_inv_sum_norm_le` | `RHV3Lean.P4_4e.reflectedDigammaBase_inv_sum_norm_le` |
| `P4_4e.reflectedDigammaBase_no_poles_in_range` | `RHV3Lean.P4_4e.reflectedDigammaBase_no_poles_in_range` |
| `P4_4e.reflectedDigammaBase_norm_bound` | `RHV3Lean.P4_4e.reflectedDigammaBase_norm_bound` |
| `P4_4e.reflected_digamma_add_nat_identity` | `RHV3Lean.P4_4e.reflected_digamma_add_nat_identity` |
| `P4_4e.sN_eq` | `RHV3Lean.P4_4e.sN_eq` |
| `P4_4e.sN_im` | `RHV3Lean.P4_4e.sN_im` |
| `P4_4e.sN_ne_neg_one` | `RHV3Lean.P4_4e.sN_ne_neg_one` |
| `P4_4e.sN_ne_one` | `RHV3Lean.P4_4e.sN_ne_one` |
| `P4_4e.sN_ne_zero` | `RHV3Lean.P4_4e.sN_ne_zero` |
| `P4_4e.sN_re` | `RHV3Lean.P4_4e.sN_re` |
| `P4_4e.shifted_leftDigammaPoint_norm_bound` | `RHV3Lean.P4_4e.shifted_leftDigammaPoint_norm_bound` |
| `PerronRectangleAdmissible.N_ge_one` | `RHV3Lean.PerronRectangleAdmissible.N_ge_one` |
| `PerronRectangleAdmissible.T_pos` | `RHV3Lean.PerronRectangleAdmissible.T_pos` |
| `PerronRectangleAdmissible.no_poles_on_boundary` | `RHV3Lean.PerronRectangleAdmissible.no_poles_on_boundary` |
| `PerronRectangleAdmissible.sigmaR_gt` | `RHV3Lean.PerronRectangleAdmissible.sigmaR_gt` |
| `PerronRectangleAdmissible.x_gt` | `RHV3Lean.PerronRectangleAdmissible.x_gt` |
| `ZetaPerronSingularityKind.ofNat_ctorIdx` | `RHV3Lean.ZetaPerronSingularityKind.ofNat_ctorIdx` |
| `abs_im_lt_of_zetaPerron_nontrivial_mem` | `RHV3Lean.abs_im_lt_of_zetaPerron_nontrivial_mem` |
| `abs_im_mem_forbiddenHeightsBelow` | `RHV3Lean.abs_im_mem_forbiddenHeightsBelow` |
| `abs_zetaReflect_im` | `RHV3Lean.abs_zetaReflect_im` |
| `analyticAt_completedRiemannZeta_trivialZetaZeroAt` | `RHV3Lean.analyticAt_completedRiemannZeta_trivialZetaZeroAt` |
| `analyticAt_const_cpow_of_pos` | `RHV3Lean.analyticAt_const_cpow_of_pos` |
| `analyticAt_logDeriv_riemannZeta` | `RHV3Lean.analyticAt_logDeriv_riemannZeta` |
| `analyticAt_perronKernel` | `RHV3Lean.analyticAt_perronKernel` |
| `analyticAt_riemannZeta_of_zero` | `RHV3Lean.analyticAt_riemannZeta_of_zero` |
| `analyticAt_trivialGammaRRegularFactor` | `RHV3Lean.analyticAt_trivialGammaRRegularFactor` |
| `analyticOnNhd_conjRiemannZetaConj` | `RHV3Lean.analyticOnNhd_conjRiemannZetaConj` |
| `analyticOrderAt_GammaR_inv_eq_zero_of_re_pos` | `RHV3Lean.analyticOrderAt_GammaR_inv_eq_zero_of_re_pos` |
| `analyticOrderAt_completedRiemannZeta_trivial_eq_zero` | `RHV3Lean.analyticOrderAt_completedRiemannZeta_trivial_eq_zero` |
| `analyticOrderAt_completedZeta_zetaReflect` | `RHV3Lean.analyticOrderAt_completedZeta_zetaReflect` |
| `analyticOrderAt_inv_Gammaℝ_trivial_eq_one` | `RHV3Lean.analyticOrderAt_inv_Gammaℝ_trivial_eq_one` |
| `analyticOrderAt_riemannZeta_eq_completed_of_re_pos` | `RHV3Lean.analyticOrderAt_riemannZeta_eq_completed_of_re_pos` |
| `analyticOrderAt_riemannZeta_trivial_eq_one` | `RHV3Lean.analyticOrderAt_riemannZeta_trivial_eq_one` |
| `analyticOrderNatAt_conjRiemannZetaConj_eq_riemannZeta_conj` | `RHV3Lean.analyticOrderNatAt_conjRiemannZetaConj_eq_riemannZeta_conj` |
| `analyticOrderNatAt_inv_Gammaℝ_trivial_eq_one` | `RHV3Lean.analyticOrderNatAt_inv_Gammaℝ_trivial_eq_one` |
| `analyticOrderNatAt_riemannZeta_eq_conjRiemannZetaConj` | `RHV3Lean.analyticOrderNatAt_riemannZeta_eq_conjRiemannZetaConj` |
| `chebyshev_psi_floor_eq` | `RHV3Lean.chebyshev_psi_floor_eq` |
| `completedRiemannZeta_trivialZetaZeroAt_ne_zero` | `RHV3Lean.completedRiemannZeta_trivialZetaZeroAt_ne_zero` |
| `complex_eq_of_im_eq_zero` | `RHV3Lean.complex_eq_of_im_eq_zero` |
| `conj_natCast_cpow` | `RHV3Lean.conj_natCast_cpow` |
| `conj_ne_one_iff` | `RHV3Lean.conj_ne_one_iff` |
| `conj_one_div_natCast_cpow` | `RHV3Lean.conj_one_div_natCast_cpow` |
| `const_cpow_ne_zero_of_pos` | `RHV3Lean.const_cpow_ne_zero_of_pos` |
| `criticalStripHeightZeroSum_add` | `RHV3Lean.criticalStripHeightZeroSum_add` |
| `criticalStripHeightZeroSum_zero` | `RHV3Lean.criticalStripHeightZeroSum_zero` |
| `criticalStripHeightZerosFinset_mono` | `RHV3Lean.criticalStripHeightZerosFinset_mono` |
| `deriv_sub_const_eq_one` | `RHV3Lean.deriv_sub_const_eq_one` |
| `differentiableAt_conjRiemannZetaConj` | `RHV3Lean.differentiableAt_conjRiemannZetaConj` |
| `exists_admissible_heights_all_boundary_limits_with_tendsto` | `RHV3Lean.exists_admissible_heights_all_boundary_limits_with_tendsto` |
| `exists_logDeriv_eventuallyEq_principal_add` | `RHV3Lean.exists_logDeriv_eventuallyEq_principal_add` |
| `exists_nontrivial_zero_free_height_between` | `RHV3Lean.exists_nontrivial_zero_free_height_between` |
| `exists_nontrivial_zero_free_height_gt` | `RHV3Lean.exists_nontrivial_zero_free_height_gt` |
| `exists_perronRectangleAdmissible_height_between` | `RHV3Lean.exists_perronRectangleAdmissible_height_between` |
| `exists_perronRectangleAdmissible_height_gt` | `RHV3Lean.exists_perronRectangleAdmissible_height_gt` |
| `finite_small_nontrivial_zeros` | `RHV3Lean.finite_small_nontrivial_zeros` |
| `hasSimplePolesOn_neg_logDeriv_riemannZeta_univ` | `RHV3Lean.hasSimplePolesOn_neg_logDeriv_riemannZeta_univ` |
| `hasSimplePolesOn_perronZetaIntegrand_univ` | `RHV3Lean.hasSimplePolesOn_perronZetaIntegrand_univ` |
| `int_one_le_of_real_le_neg_one` | `RHV3Lean.int_one_le_of_real_le_neg_one` |
| `integrable_vonMangoldt_perron_term` | `RHV3Lean.integrable_vonMangoldt_perron_term` |
| `integrable_zetaPerronIntegrand_vertical` | `RHV3Lean.integrable_zetaPerronIntegrand_vertical` |
| `inv_Gammaℝ_eq_finite_shift_product` | `RHV3Lean.inv_Gammaℝ_eq_finite_shift_product` |
| `inv_Gammaℝ_eq_shift_two` | `RHV3Lean.inv_Gammaℝ_eq_shift_two` |
| `inv_Gammaℝ_trivial_factorization` | `RHV3Lean.inv_Gammaℝ_trivial_factorization` |
| `isNontrivialZetaZero_conj_iff` | `RHV3Lean.isNontrivialZetaZero_conj_iff` |
| `isNontrivialZetaZero_ne_negOne` | `RHV3Lean.isNontrivialZetaZero_ne_negOne` |
| `isNontrivialZetaZero_ne_zero` | `RHV3Lean.isNontrivialZetaZero_ne_zero` |
| `isNontrivialZetaZero_re_mem_Ioo` | `RHV3Lean.isNontrivialZetaZero_re_mem_Ioo` |
| `isPreconnected_compl_one_complex` | `RHV3Lean.isPreconnected_compl_one_complex` |
| `isTrivialZetaZero_conj_iff` | `RHV3Lean.isTrivialZetaZero_conj_iff` |
| `isTrivialZetaZero_im_eq_zero` | `RHV3Lean.isTrivialZetaZero_im_eq_zero` |
| `isTrivialZetaZero_ne_negOne` | `RHV3Lean.isTrivialZetaZero_ne_negOne` |
| `isTrivialZetaZero_ne_one` | `RHV3Lean.isTrivialZetaZero_ne_one` |
| `isTrivialZetaZero_ne_zero` | `RHV3Lean.isTrivialZetaZero_ne_zero` |
| `isTrivialZetaZero_of_real_cos_eq_zero` | `RHV3Lean.isTrivialZetaZero_of_real_cos_eq_zero` |
| `isTrivialZetaZero_re_lt_one` | `RHV3Lean.isTrivialZetaZero_re_lt_one` |
| `isTrivialZetaZero_re_ne_perronRectangleSigmaL` | `RHV3Lean.isTrivialZetaZero_re_ne_perronRectangleSigmaL` |
| `isTrivialZetaZero_riemannZeta_zero` | `RHV3Lean.isTrivialZetaZero_riemannZeta_zero` |
| `iteratedDeriv_conj_conj` | `RHV3Lean.iteratedDeriv_conj_conj` |
| `logDeriv_centered_pow` | `RHV3Lean.logDeriv_centered_pow` |
| `logDeriv_riemannZeta_eventuallyEq_pole` | `RHV3Lean.logDeriv_riemannZeta_eventuallyEq_pole` |
| `logDeriv_sub_const` | `RHV3Lean.logDeriv_sub_const` |
| `logDeriv_sub_principal_isBigO` | `RHV3Lean.logDeriv_sub_principal_isBigO` |
| `mem_criticalStripHeightZerosFinset_iff` | `RHV3Lean.mem_criticalStripHeightZerosFinset_iff` |
| `mem_criticalStripHeightZerosFinset_raw` | `RHV3Lean.mem_criticalStripHeightZerosFinset_raw` |
| `mem_nontrivialZetaForbiddenHeightsBelow` | `RHV3Lean.mem_nontrivialZetaForbiddenHeightsBelow` |
| `mem_nontrivialZetaZerosByHeightFinset` | `RHV3Lean.mem_nontrivialZetaZerosByHeightFinset` |
| `mem_nontrivialZetaZerosByHeightSubtypeFinset` | `RHV3Lean.mem_nontrivialZetaZerosByHeightSubtypeFinset` |
| `mem_nontrivialZetaZerosFinset` | `RHV3Lean.mem_nontrivialZetaZerosFinset` |
| `mem_perronRectangleBorder_cases` | `RHV3Lean.mem_perronRectangleBorder_cases` |
| `mem_zetaZerosFinset` | `RHV3Lean.mem_zetaZerosFinset` |
| `meromorphicAt_neg_logDeriv_riemannZeta` | `RHV3Lean.meromorphicAt_neg_logDeriv_riemannZeta` |
| `meromorphicAt_perronKernel` | `RHV3Lean.meromorphicAt_perronKernel` |
| `meromorphicAt_perronZetaIntegrand` | `RHV3Lean.meromorphicAt_perronZetaIntegrand` |
| `meromorphicAt_riemannZeta` | `RHV3Lean.meromorphicAt_riemannZeta` |
| `meromorphicOrderAt_logDeriv_eq_neg_one` | `RHV3Lean.meromorphicOrderAt_logDeriv_eq_neg_one` |
| `meromorphicOrderAt_neg_logDeriv_riemannZeta_pole` | `RHV3Lean.meromorphicOrderAt_neg_logDeriv_riemannZeta_pole` |
| `meromorphicOrderAt_neg_logDeriv_riemannZeta_zero` | `RHV3Lean.meromorphicOrderAt_neg_logDeriv_riemannZeta_zero` |
| `meromorphicOrderAt_perronKernel_negOne` | `RHV3Lean.meromorphicOrderAt_perronKernel_negOne` |
| `meromorphicOrderAt_perronKernel_zero` | `RHV3Lean.meromorphicOrderAt_perronKernel_zero` |
| `natCast_arg_ne_pi` | `RHV3Lean.natCast_arg_ne_pi` |
| `ne_neg_nat_of_re_pos` | `RHV3Lean.ne_neg_nat_of_re_pos` |
| `negLogDeriv_riemannZeta_eq_LSeries_vonMangoldt` | `RHV3Lean.negLogDeriv_riemannZeta_eq_LSeries_vonMangoldt` |
| `neg_logDeriv_mul_perronKernel_eq_tsum` | `RHV3Lean.neg_logDeriv_mul_perronKernel_eq_tsum` |
| `neg_logDeriv_riemannZeta_sub_principal_pole_isBigO` | `RHV3Lean.neg_logDeriv_riemannZeta_sub_principal_pole_isBigO` |
| `neg_logDeriv_riemannZeta_sub_principal_zero_isBigO` | `RHV3Lean.neg_logDeriv_riemannZeta_sub_principal_zero_isBigO` |
| `neg_one_mem_zetaPerronRectangle` | `RHV3Lean.neg_one_mem_zetaPerronRectangle` |
| `neg_one_not_mem_perronRectangleBorder` | `RHV3Lean.neg_one_not_mem_perronRectangleBorder` |
| `nontrivialZero_not_mem_perronRectangleBorder_of_height` | `RHV3Lean.nontrivialZero_not_mem_perronRectangleBorder_of_height` |
| `nontrivialZetaZerosByHeightFinset_conj` | `RHV3Lean.nontrivialZetaZerosByHeightFinset_conj` |
| `nontrivialZetaZerosByHeightFinset_mono` | `RHV3Lean.nontrivialZetaZerosByHeightFinset_mono` |
| `nontrivialZetaZerosByHeight_finite` | `RHV3Lean.nontrivialZetaZerosByHeight_finite` |
| `nontrivial_height_complex_sum_eq_subtype_sum` | `RHV3Lean.nontrivial_height_complex_sum_eq_subtype_sum` |
| `nontrivial_zero_height_finset_bridge` | `RHV3Lean.nontrivial_zero_height_finset_bridge` |
| `nontrivial_zero_residue_series_summable` | `RHV3Lean.nontrivial_zero_residue_series_summable` |
| `nontrivial_zero_residue_series_symmetric_convergent` | `RHV3Lean.nontrivial_zero_residue_series_symmetric_convergent` |
| `norm_nontrivialZeroResidueTerm_le_weighted` | `RHV3Lean.norm_nontrivialZeroResidueTerm_le_weighted` |
| `norm_perron_f_eq_rpow_mul` | `RHV3Lean.norm_perron_f_eq_rpow_mul` |
| `norm_perron_f_nontrivial_le_imag_square` | `RHV3Lean.norm_perron_f_nontrivial_le_imag_square` |
| `norm_perron_f_trivial_le_geometric` | `RHV3Lean.norm_perron_f_trivial_le_geometric` |
| `one_le_norm_trivial_denominator` | `RHV3Lean.one_le_norm_trivial_denominator` |
| `one_mem_zetaPerronRectangle` | `RHV3Lean.one_mem_zetaPerronRectangle` |
| `one_not_mem_perronRectangleBorder` | `RHV3Lean.one_not_mem_perronRectangleBorder` |
| `p3c3_perronRectangle_im_le` | `RHV3Lean.p3c3_perronRectangle_im_le` |
| `p3c3_perronRectangle_isCompact` | `RHV3Lean.p3c3_perronRectangle_isCompact` |
| `p3c3_perronRectangle_re_le` | `RHV3Lean.p3c3_perronRectangle_re_le` |
| `p4_5_boundary_and_zero_series_complete` | `RHV3Lean.p4_5_boundary_and_zero_series_complete` |
| `perronKernel_conj` | `RHV3Lean.perronKernel_conj` |
| `perronKernel_ne_zero` | `RHV3Lean.perronKernel_ne_zero` |
| `perronRectangleAdmissible_of_zero_free_height` | `RHV3Lean.perronRectangleAdmissible_of_zero_free_height` |
| `perronRectangleLowerLeft_im` | `RHV3Lean.perronRectangleLowerLeft_im` |
| `perronRectangleLowerLeft_re` | `RHV3Lean.perronRectangleLowerLeft_re` |
| `perronRectangleUpperRight_im` | `RHV3Lean.perronRectangleUpperRight_im` |
| `perronRectangleUpperRight_re` | `RHV3Lean.perronRectangleUpperRight_re` |
| `perronRectangle_im_le` | `RHV3Lean.perronRectangle_im_le` |
| `perronRectangle_im_le_for_trivial_series` | `RHV3Lean.perronRectangle_im_le_for_trivial_series` |
| `perronRectangle_isCompact` | `RHV3Lean.perronRectangle_isCompact` |
| `perronRectangle_no_boundary_poles_of_zero_free_height` | `RHV3Lean.perronRectangle_no_boundary_poles_of_zero_free_height` |
| `perronRectangle_re_le` | `RHV3Lean.perronRectangle_re_le` |
| `perronRectangle_re_le_for_trivial_series` | `RHV3Lean.perronRectangle_re_le_for_trivial_series` |
| `perron_f_one_truncated_integral` | `RHV3Lean.perron_f_one_truncated_integral` |
| `psiRecoveredFromZeros_eq_psi` | `RHV3Lean.psiRecoveredFromZeros_eq_psi` |
| `residue_eq_zero_of_meromorphicOrderAt_nonneg` | `RHV3Lean.residue_eq_zero_of_meromorphicOrderAt_nonneg` |
| `residue_neg_logDeriv_riemannZeta_pole` | `RHV3Lean.residue_neg_logDeriv_riemannZeta_pole` |
| `residue_neg_logDeriv_riemannZeta_zero` | `RHV3Lean.residue_neg_logDeriv_riemannZeta_zero` |
| `residue_perronKernel_neg_one` | `RHV3Lean.residue_perronKernel_neg_one` |
| `residue_perronKernel_zero` | `RHV3Lean.residue_perronKernel_zero` |
| `residue_perronZetaIntegrand_pole` | `RHV3Lean.residue_perronZetaIntegrand_pole` |
| `residue_perronZetaIntegrand_zero` | `RHV3Lean.residue_perronZetaIntegrand_zero` |
| `riemannZeta_analyticOrderAt_ne_top` | `RHV3Lean.riemannZeta_analyticOrderAt_ne_top` |
| `riemannZeta_conj` | `RHV3Lean.riemannZeta_conj` |
| `riemannZeta_conj_eq_of_one_lt_re` | `RHV3Lean.riemannZeta_conj_eq_of_one_lt_re` |
| `riemannZeta_conj_eq_zero_of_zero` | `RHV3Lean.riemannZeta_conj_eq_zero_of_zero` |
| `riemannZeta_eq_conjRiemannZetaConj` | `RHV3Lean.riemannZeta_eq_conjRiemannZetaConj` |
| `riemannZeta_eq_conjRiemannZetaConj_of_one_lt_re` | `RHV3Lean.riemannZeta_eq_conjRiemannZetaConj_of_one_lt_re` |
| `riemannZeta_eq_zetaPoleFactor_div` | `RHV3Lean.riemannZeta_eq_zetaPoleFactor_div` |
| `riemannZeta_eventuallyEq_completed_mul_GammaR_inv` | `RHV3Lean.riemannZeta_eventuallyEq_completed_mul_GammaR_inv` |
| `riemannZeta_eventuallyEq_completed_mul_invGammaR` | `RHV3Lean.riemannZeta_eventuallyEq_completed_mul_invGammaR` |
| `riemannZeta_eventuallyEq_conjRiemannZetaConj` | `RHV3Lean.riemannZeta_eventuallyEq_conjRiemannZetaConj` |
| `riemannZeta_ne_zero_of_real_nontrivial_left` | `RHV3Lean.riemannZeta_ne_zero_of_real_nontrivial_left` |
| `riemannZeta_neg_one_ne_zero` | `RHV3Lean.riemannZeta_neg_one_ne_zero` |
| `riemannZeta_order_eq_zetaZeroMultiplicity` | `RHV3Lean.riemannZeta_order_eq_zetaZeroMultiplicity` |
| `riemannZeta_trivialZetaZeroAt` | `RHV3Lean.riemannZeta_trivialZetaZeroAt` |
| `riemannZeta_zero_ne_zero` | `RHV3Lean.riemannZeta_zero_ne_zero` |
| `riemannZeta_zetaReflect_eq_zero` | `RHV3Lean.riemannZeta_zetaReflect_eq_zero` |
| `right_vertical_lower_tail_tendsto_zero` | `RHV3Lean.right_vertical_lower_tail_tendsto_zero` |
| `right_vertical_split_zetaPerron` | `RHV3Lean.right_vertical_split_zetaPerron` |
| `right_vertical_tails_tendsto_zero` | `RHV3Lean.right_vertical_tails_tendsto_zero` |
| `right_vertical_upper_tail_tendsto_zero` | `RHV3Lean.right_vertical_upper_tail_tendsto_zero` |
| `smoothedMangoldtPrimitive_nat_difference` | `RHV3Lean.smoothedMangoldtPrimitive_nat_difference` |
| `smoothedVonMangoldtSum_eq_classified_residues_and_boundary_terms` | `RHV3Lean.smoothedVonMangoldtSum_eq_classified_residues_and_boundary_terms` |
| `smoothedVonMangoldtSum_eq_finite_residues_and_boundary_terms` | `RHV3Lean.smoothedVonMangoldtSum_eq_finite_residues_and_boundary_terms` |
| `smoothedVonMangoldtSum_eq_fixed_left_boundary_limit` | `RHV3Lean.smoothedVonMangoldtSum_eq_fixed_left_boundary_limit` |
| `smoothedVonMangoldtSum_eq_height_truncated_residues_and_boundary_terms` | `RHV3Lean.smoothedVonMangoldtSum_eq_height_truncated_residues_and_boundary_terms` |
| `smoothedZeroFormula_eq_smoothedVonMangoldtSum` | `RHV3Lean.smoothedZeroFormula_eq_smoothedVonMangoldtSum` |
| `smoothedZeroFormula_sub_background` | `RHV3Lean.smoothedZeroFormula_sub_background` |
| `smoothedZeroPrimitive_eq_arithmetic` | `RHV3Lean.smoothedZeroPrimitive_eq_arithmetic` |
| `smoothedZeroPrimitive_nat_difference` | `RHV3Lean.smoothedZeroPrimitive_nat_difference` |
| `smoothed_mangoldt_new_weight` | `RHV3Lean.smoothed_mangoldt_new_weight` |
| `smoothed_mangoldt_weight_difference` | `RHV3Lean.smoothed_mangoldt_weight_difference` |
| `smoothed_riemann_explicit_formula` | `RHV3Lean.smoothed_riemann_explicit_formula` |
| `sumResiduesIn_classified_eq_special_plus_zeros` | `RHV3Lean.sumResiduesIn_classified_eq_special_plus_zeros` |
| `sumResiduesIn_finite_eq_finset_sum` | `RHV3Lean.sumResiduesIn_finite_eq_finset_sum` |
| `sumResiduesIn_poleSet_eq_classified_singularity_sum` | `RHV3Lean.sumResiduesIn_poleSet_eq_classified_singularity_sum` |
| `summable_integral_norm_vonMangoldt_perron` | `RHV3Lean.summable_integral_norm_vonMangoldt_perron` |
| `tendsto_mul_logDeriv_analyticOrder` | `RHV3Lean.tendsto_mul_logDeriv_analyticOrder` |
| `tendsto_mul_logDeriv_riemannZeta_pole` | `RHV3Lean.tendsto_mul_logDeriv_riemannZeta_pole` |
| `tendsto_mul_logDeriv_riemannZeta_zero` | `RHV3Lean.tendsto_mul_logDeriv_riemannZeta_zero` |
| `tendsto_mul_neg_logDeriv_riemannZeta_pole` | `RHV3Lean.tendsto_mul_neg_logDeriv_riemannZeta_pole` |
| `tendsto_mul_neg_logDeriv_riemannZeta_zero` | `RHV3Lean.tendsto_mul_neg_logDeriv_riemannZeta_zero` |
| `tendsto_nontrivial_height_subtype_finset_atTop` | `RHV3Lean.tendsto_nontrivial_height_subtype_finset_atTop` |
| `trivialGammaRRegularFactor_ne_zero` | `RHV3Lean.trivialGammaRRegularFactor_ne_zero` |
| `trivialZero_not_mem_perronRectangleBorder` | `RHV3Lean.trivialZero_not_mem_perronRectangleBorder` |
| `trivialZetaZeroAt_injective` | `RHV3Lean.trivialZetaZeroAt_injective` |
| `trivialZetaZeroAt_mem_rectangle_iff` | `RHV3Lean.trivialZetaZeroAt_mem_rectangle_iff` |
| `trivialZetaZeroAt_mul_succ` | `RHV3Lean.trivialZetaZeroAt_mul_succ` |
| `trivialZetaZeroAt_ne_one` | `RHV3Lean.trivialZetaZeroAt_ne_one` |
| `trivialZetaZeroAt_ne_zero` | `RHV3Lean.trivialZetaZeroAt_ne_zero` |
| `trivialZetaZero_not_nontrivial` | `RHV3Lean.trivialZetaZero_not_nontrivial` |
| `trivial_zero_residue_partial_sums_tendsto` | `RHV3Lean.trivial_zero_residue_partial_sums_tendsto` |
| `trivial_zero_residue_series_summable` | `RHV3Lean.trivial_zero_residue_series_summable` |
| `trivial_zero_residue_term_eq` | `RHV3Lean.trivial_zero_residue_term_eq` |
| `truncatedZetaZeroSum_add` | `RHV3Lean.truncatedZetaZeroSum_add` |
| `truncatedZetaZeroSum_zero` | `RHV3Lean.truncatedZetaZeroSum_zero` |
| `verticalIntegral'_eq_smoothedVonMangoldtSum` | `RHV3Lean.verticalIntegral'_eq_smoothedVonMangoldtSum` |
| `verticalIntegral'_perron_f_eval` | `RHV3Lean.verticalIntegral'_perron_f_eval` |
| `verticalIntegral'_perron_f_one` | `RHV3Lean.verticalIntegral'_perron_f_one` |
| `verticalIntegral'_split_right_line` | `RHV3Lean.verticalIntegral'_split_right_line` |
| `vonMangoldt_term_mul_perronKernel` | `RHV3Lean.vonMangoldt_term_mul_perronKernel` |
| `weighted_zetaZeroMultiplicity_imagSquare_summable` | `RHV3Lean.weighted_zetaZeroMultiplicity_imagSquare_summable` |
| `weighted_zetaZeroMultiplicity_shiftedImagSquare_summable` | `RHV3Lean.weighted_zetaZeroMultiplicity_shiftedImagSquare_summable` |
| `zero_mem_zetaPerronRectangle` | `RHV3Lean.zero_mem_zetaPerronRectangle` |
| `zero_not_mem_perronRectangleBorder` | `RHV3Lean.zero_not_mem_perronRectangleBorder` |
| `zetaConjugationReflectionOrbit_multiplicity_eq` | `RHV3Lean.zetaConjugationReflectionOrbit_multiplicity_eq` |
| `zetaConjugationReflectionOrbit_zero` | `RHV3Lean.zetaConjugationReflectionOrbit_zero` |
| `zetaPerronIntegrand_pole_at_nontrivial_zero` | `RHV3Lean.zetaPerronIntegrand_pole_at_nontrivial_zero` |
| `zetaPerronIntegrand_pole_classified_global` | `RHV3Lean.zetaPerronIntegrand_pole_classified_global` |
| `zetaPerronNontrivialZeroFinset_eq_byHeight` | `RHV3Lean.zetaPerronNontrivialZeroFinset_eq_byHeight` |
| `zetaPerronNontrivialZeroSet_conj_iff` | `RHV3Lean.zetaPerronNontrivialZeroSet_conj_iff` |
| `zetaPerronNontrivialZeroSet_eq_byHeight` | `RHV3Lean.zetaPerronNontrivialZeroSet_eq_byHeight` |
| `zetaPerronRectangle_conj_iff` | `RHV3Lean.zetaPerronRectangle_conj_iff` |
| `zetaPerron_border_of_rect_abs_im_eq` | `RHV3Lean.zetaPerron_border_of_rect_abs_im_eq` |
| `zetaPerron_categories_pairwise_disjoint` | `RHV3Lean.zetaPerron_categories_pairwise_disjoint` |
| `zetaPerron_classified_singularity_finset_eq_union` | `RHV3Lean.zetaPerron_classified_singularity_finset_eq_union` |
| `zetaPerron_classified_singularity_set_eq_union` | `RHV3Lean.zetaPerron_classified_singularity_set_eq_union` |
| `zetaPerron_classified_singularity_set_finite` | `RHV3Lean.zetaPerron_classified_singularity_set_finite` |
| `zetaPerron_conjugate_orbit_pairing` | `RHV3Lean.zetaPerron_conjugate_orbit_pairing` |
| `zetaPerron_finite_rectangle_four_boundaries` | `RHV3Lean.zetaPerron_finite_rectangle_four_boundaries` |
| `zetaPerron_finite_rectangle_residue_identity` | `RHV3Lean.zetaPerron_finite_rectangle_residue_identity` |
| `zetaPerron_finite_residue_decomposition` | `RHV3Lean.zetaPerron_finite_residue_decomposition` |
| `zetaPerron_integrand_hasSimplePolesOn` | `RHV3Lean.zetaPerron_integrand_hasSimplePolesOn` |
| `zetaPerron_integrand_meromorphicOn` | `RHV3Lean.zetaPerron_integrand_meromorphicOn` |
| `zetaPerron_nontrivial_zero_residue_sum` | `RHV3Lean.zetaPerron_nontrivial_zero_residue_sum` |
| `zetaPerron_nontrivial_zero_residue_sum_eq_byHeight` | `RHV3Lean.zetaPerron_nontrivial_zero_residue_sum_eq_byHeight` |
| `zetaPerron_nontrivial_zero_set_finite` | `RHV3Lean.zetaPerron_nontrivial_zero_set_finite` |
| `zetaPerron_nontrivial_zero_set_subset_zeros` | `RHV3Lean.zetaPerron_nontrivial_zero_set_subset_zeros` |
| `zetaPerron_poleSet_subset_divisor_support` | `RHV3Lean.zetaPerron_poleSet_subset_divisor_support` |
| `zetaPerron_pole_category_unique` | `RHV3Lean.zetaPerron_pole_category_unique` |
| `zetaPerron_poles_in_rectangle_classified` | `RHV3Lean.zetaPerron_poles_in_rectangle_classified` |
| `zetaPerron_rectangle_poles_finite` | `RHV3Lean.zetaPerron_rectangle_poles_finite` |
| `zetaPerron_residue_at_neg_one` | `RHV3Lean.zetaPerron_residue_at_neg_one` |
| `zetaPerron_residue_at_one` | `RHV3Lean.zetaPerron_residue_at_one` |
| `zetaPerron_residue_at_one_eq` | `RHV3Lean.zetaPerron_residue_at_one_eq` |
| `zetaPerron_residue_at_zero` | `RHV3Lean.zetaPerron_residue_at_zero` |
| `zetaPerron_residue_at_zeta_zero` | `RHV3Lean.zetaPerron_residue_at_zeta_zero` |
| `zetaPerron_residue_conj` | `RHV3Lean.zetaPerron_residue_conj` |
| `zetaPerron_special_disjoint_nontrivial` | `RHV3Lean.zetaPerron_special_disjoint_nontrivial` |
| `zetaPerron_special_disjoint_trivial` | `RHV3Lean.zetaPerron_special_disjoint_trivial` |
| `zetaPerron_special_residue_sum_eq` | `RHV3Lean.zetaPerron_special_residue_sum_eq` |
| `zetaPerron_special_union_trivial_disjoint_nontrivial` | `RHV3Lean.zetaPerron_special_union_trivial_disjoint_nontrivial` |
| `zetaPerron_trivial_disjoint_nontrivial` | `RHV3Lean.zetaPerron_trivial_disjoint_nontrivial` |
| `zetaPerron_trivial_zero_residue_sum` | `RHV3Lean.zetaPerron_trivial_zero_residue_sum` |
| `zetaPerron_trivial_zero_residue_sum_eq_range` | `RHV3Lean.zetaPerron_trivial_zero_residue_sum_eq_range` |
| `zetaPerron_trivial_zero_set_finite` | `RHV3Lean.zetaPerron_trivial_zero_set_finite` |
| `zetaPerron_trivial_zero_set_subset_zeros` | `RHV3Lean.zetaPerron_trivial_zero_set_subset_zeros` |
| `zetaPoleFactor_analyticAt_one` | `RHV3Lean.zetaPoleFactor_analyticAt_one` |
| `zetaPoleFactor_one_ne_zero` | `RHV3Lean.zetaPoleFactor_one_ne_zero` |
| `zetaReflect_deriv_ne_zero` | `RHV3Lean.zetaReflect_deriv_ne_zero` |
| `zetaReflect_im` | `RHV3Lean.zetaReflect_im` |
| `zetaReflect_involutive` | `RHV3Lean.zetaReflect_involutive` |
| `zetaReflect_mem_criticalStripHeightZerosFinset` | `RHV3Lean.zetaReflect_mem_criticalStripHeightZerosFinset` |
| `zetaReflect_re` | `RHV3Lean.zetaReflect_re` |
| `zetaZeroMultiplicity_conj` | `RHV3Lean.zetaZeroMultiplicity_conj` |
| `zetaZeroMultiplicity_pos` | `RHV3Lean.zetaZeroMultiplicity_pos` |
| `zetaZeroMultiplicity_trivialZetaZeroAt` | `RHV3Lean.zetaZeroMultiplicity_trivialZetaZeroAt` |
| `zetaZeroMultiplicity_zetaReflect` | `RHV3Lean.zetaZeroMultiplicity_zetaReflect` |
| `zetaZero_ne_negOne` | `RHV3Lean.zetaZero_ne_negOne` |
| `zetaZero_ne_one` | `RHV3Lean.zetaZero_ne_one` |
| `zetaZero_ne_zero` | `RHV3Lean.zetaZero_ne_zero` |
| `zetaZero_trivial_or_nontrivial` | `RHV3Lean.zetaZero_trivial_or_nontrivial` |
| `zetaZerosFinset_mono` | `RHV3Lean.zetaZerosFinset_mono` |
| `zetaZerosInClosedBall_finite` | `RHV3Lean.zetaZerosInClosedBall_finite` |
| `zeta_zero_re_mem_of_im_pos` | `Backlund.zeta_zero_re_mem_of_im_pos` |

### C. Correspondances sémantiques (même vérité, énoncé ou objet différent)

| vérité | théorèmes du lot | théorème RHV6Fresh | nature de la correspondance |
|---|---|---|---|
| V45 : les deux contacts redonnent β | `ScientificRebuild20260828.E44SelectedPrimePivotCell.recovers_beta`, `ScientificRebuild20260828.trueZero_beta_from_height_and_leftContact`, `ScientificRebuild20260828.PrimeLocatedTangentCell.recovers_beta`, `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.recovers_beta`, `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.recovers_beta`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_beta_eq_gamma_div_tan_contact`, `beta_eq_gamma_div_tan_tangentContact` | `AnalyticContactPair.recovers_beta`, `InvertedContactPair.recovers_beta` | même formule β = γ / tan(γ·log contact d'entrée) ; objets différents (contact tangent vrai d'un zéro ici, contact d'entrée de la Tour analytique/inversée dans RHV6Fresh) |
| V163 : hors ligne, aucun contact du miroir ne coïncide avec un contact de z | `ScientificRebuild20260828.localOffLineMirrorContactsDistinct`, `ScientificRebuild20260829.FiberedMirrorGapEntry.true_contacts_distinct`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_offLine_contact_ne_mirror`, `trueZeroTangentContact_eq_mirror_iff_critical`, `trueOffline_tangentContact_ne_mirror`, `RiemannHypothesisProof.tower_preserves_off_distinction` | `mirror_contacts_never_coincide` | même vérité ; RHV6Fresh la borne au côté `β < 1/2` (`contactMinusAt`) et à tout indice k ; ici hors ligne (`β ≠ 1/2`) au même indice |
| V46 : deux zéros distincts ne partagent pas les deux contacts | `ScientificRebuild20260828.nontrivial_family_contact_pair_injective`, `ScientificRebuild20260828.nontrivialContactSignature_injective`, `RiemannHypothesisProof.trueContacts_member_injective`, `RiemannHypothesisProof.sameHeight_distinctBeta_contacts_ne`, `RiemannHypothesisProof.sameHeight_not_contact_identity` | `contactMinus_eq_iff_radial_eq` | apparentée : RHV6Fresh traite le cas de même hauteur (contact égal ⟺ même position radiale) ; ici injectivité de la paire de contacts en le zéro |
| V145 : rang et premier constatés = comptage de Chebyshev/von Mangoldt au contact | `ScientificRebuild20260828.E44SelectedPrimePivotCell.exact_local_prime_count`, `ScientificRebuild20260828.PrimeLocatedTangentCell.localPrimeCount_exact`, `ScientificRebuild20260829.trueEvent_contactCell_exact_readout`, `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_left_count_lock`, `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_local_count_lock`, `RiemannHypothesisProof.CanonicalContactCell.startRank_eq_floor_piReal_left` | `countedPrime_eq_vonMangoldt` | apparentée : deux formulations de « le comptage lu au contact est la fonction de von Mangoldt » (compte local exact ici, premier constaté à l'entrée dans RHV6Fresh) |
| V182 : injectivité du pointeur zéro → premier | `ScientificRebuild20260829.canonicalEventAxis_rigid`, `RiemannHypothesisProof.CanonicalPrimeEvent.eq_of_centerPrime_eq`, `RiemannHypothesisProof.CanonicalPrimeEvent.same_centerPrime_rigidifies_environment`, `RiemannHypothesisProof.SameCentralPrimeDeterminesSamePrimeEvent`, `RiemannHypothesisProof.SameCentralPrimeDeterminesSamePrimeEnvironment` | `expectedMinimumPrime_injective` | même forme d'injectivité ; objet différent (premier central d'un événement ici, minimum attendu d'un zéro dans RHV6Fresh) |
| V102/V157 : la position radiale β entre dans l'amplitude | `ScientificRebuild20260828.FullyAligned.normalizedMemberReflectionNorm`, `ScientificRebuild20260828.norm_memberGrammarReflection`, `SemanticTransportClosure20260821.actualSameZeroReturnPartnership_radialDefect`, `SemanticTransportClosure20260821.radialDefect_mirrorPoint`, `trueZeroDelta_mirror` | `zeroTerm_norm`, `amplitude_ratio_sameHeight` | apparentée : l'exposant réel β − 1/2 de l'amplitude ; RHV6Fresh le lit sur le terme explicite ‖q^ρ/ρ‖ = q^β/‖ρ‖, ici sur la réflexion du membre (p_N/p_M)^(−(β−1/2)) et sur le défaut radial |
| V63/V65/V12 : quatre zéros, miroir, multiplicité conservée | `TrueZeroQuartet.four_members_pairwise_distinct`, `TrueZeroQuartet.members_card_eq_four`, `TrueZeroQuartet.sameHeightMirror_multiplicity`, `zetaZeroMultiplicity_conj`, `zetaZeroMultiplicity_zetaReflect`, `RiemannHypothesisProof.FunctionalMirrorPreservesMultiplicity`, `RiemannHypothesisProof.NonCentralFunctionalQuartetHasFourDistinctZeros` | `quartet_chain`, `mirror_multiplicity`, `upperMirror_multiplicity` | même vérité, formulations distinctes (orbite/cardinal et multiplicité ici ; chaîne des supports et multiplicité du miroir dans RHV6Fresh) |
| V121/V48 : Chebyshev reconstruit depuis les zéros | `smoothed_riemann_explicit_formula`, `psiRecoveredFromZeros_eq_psi` | (base `rhv3_lean`) `psiRecoveredFromZeros_eq_psi`, `smoothed_riemann_explicit_formula` | types identiques dans la base (voir B) ; V121 les nomme |
| V174 : états mod 6, classes 0/2/4, alternance | `transition_residue_coboundary_v2`, `lifted_gap_coboundary_v2`, `transformOf_edge_correspondence`, `transform_exhaustive_unique`, `transform_partition`, `gap_transition_residue_exists`, `zero_reconstructed_relations_eq`, `zero_reconstructed_patterns_eq`, `zero_reconstructed_families_eq`, `zero_reconstructed_complete_metapattern_eq` | `gapClass6_alternates` | partielle : le lot prouve états mod 6, relations et classes (et leur transport aux suites reconstruites) ; l'alternance forcée 2,4,2,4 n'est un théorème de RHV6Fresh (`gapClass6_alternates`) qu'ici seulement sous forme conditionnelle (`alternatingAssembly_edges_iff_pivotSignWord`, `alternatingAssembly_has_oddFloorPivot`) |
| V140/V188 : prémisse ⟺ RH (caractérisations) | `ScientificRebuild20260829.routeA_universal_fiberedMZEqM_iff_RH`, `ScientificRebuild20260829.fiberedMZEqM_iff_riemannHypothesis`, `SemanticTransportClosure20260821.masterR12Producer_iff_riemannHypothesis`, `SemanticTransportClosure20260821.P0_iff_riemannHypothesis`, `SemanticTransportClosure20260821.P2_iff_riemannHypothesis`, `SemanticTransportClosure20260821.partneredNaturality_iff_riemannHypothesis`, `unifiedKnownConstraintsProduceR12_iff_riemannHypothesis`, `RiemannHypothesisProof.SamePassageGrammaticalRelationIsPreserved_iff_RiemannHypothesis` | `riemannHypothesis_iff_noLowerSide`, `premise_ladder_tfae` | même genre de théorème (une prémisse ⟺ RH) ; prémisses différentes (fidélité fibrée, retour, naturalité, passage nul…) ; aucune n'est celle de RHV6Fresh |

### D. Divergences relevées (même nom, énoncé différent)

- `zetaReflect` : `1 − ρ` dans `rh_gap_criterion/RhGapCriterion/ZetaHeightReflection.lean` (ainsi `zetaReflect_im` : Im(zetaReflect ρ) = −Im ρ) ; `1 − conj ρ` dans `RHV6Fresh/Foundation/ZetaReflect.lean` (port zeta23 : `zetaReflect_im` : Im = Im ρ). Dans le vocabulaire du maître : `1 − ρ` est le « zéro réfléchi », `1 − conj ρ` le « miroir » (V63). Les théorèmes de même nom ne sont donc pas interchangeables ; `RhGap.reflectConjZero` (`1 − conj ρ`) est le miroir du maître.
- `RhGap.ScientificRebuild20260828.PrimeLocatedTangentCell.recovers_beta` et les champs `recovers_beta` homonymes portent sur une cellule tangente d'un vrai zéro ; ceux de RHV6Fresh sur `AnalyticContactPair`/`InvertedContactPair` (voir C).
- `RhGap.ScientificRebuild20260829.TrustedZetaSeam.mirror_multiplicity` est conditionné à `TrustedZetaSeam` ; `RHV6Fresh.mirror_multiplicity` est inconditionnel (sur `TNonTrivialZetaZero`).

## Théorèmes mentionnant `RiemannHypothesis`

NB : le champ `mentions_RH` du jsonl est pollué pour la bibliothèque `RiemannHypothesisProof` (le préfixe de namespace contient la chaîne) : 259 lignes du lot marquées, dont 195 seulement par le nom du namespace ; le terme Mathlib `RiemannHypothesis` figure dans 64 types du lot (recherche du mot isolé dans le type). Aucun théorème du lot n'a pour type exactement `RiemannHypothesis` sans hypothèse : pas de TERME RH FERMÉ (vérifié par script).

### A. Types contenant le terme `RiemannHypothesis`

| théorème | module | forme | statut exact | prémisse en mots |
|---|---|---|---|---|
| `separation_32_cannot_produce_33` | `Round27FField33ProducerAudit` | P ⟺ RH | ÉQUIVALENTE À RH (la conjonction des surfaces non terminales (fidélité du partenariat) implique field33 pour tout partenariat canonique) | la conjonction des surfaces non terminales (fidélité du partenariat) implique field33 pour tout partenariat canonique |
| `unconditional_law_produces_field33_iff_rh` | `Round27FField33ProducerAudit` | P ⟺ RH | ÉQUIVALENTE À RH (pour toute proposition Q prouvée, « Q entraîne field33 pour tous les partenariats » ⟺ RH) | pour toute proposition Q prouvée, « Q entraîne field33 pour tous les partenariats » ⟺ RH |
| `Q1_is_generic_control` | `Round27FField33ProducerAudit` | P ⟺ RH | ÉQUIVALENTE À RH (l'unicité de l'opérateur (même zéro, même bloc) entraîne field33 pour tout partenariat canonique) | l'unicité de l'opérateur (même zéro, même bloc) entraîne field33 pour tout partenariat canonique |
| `Q5_two_orientation_compatibility_iff_rh` | `Round27FField33ProducerAudit` | P ⟺ RH | ÉQUIVALENTE À RH (compatibilité des deux orientations du transport pour tout partenariat canonique) | compatibilité des deux orientations du transport pour tout partenariat canonique |
| `twoBaseReflectedLaurentEquality_iff_rh` | `Round27GTwoBaseReflectedLaurentTDD` | P ⟺ RH | ÉQUIVALENTE À RH (égalité de Laurent à deux bases pour tous les zéros) | égalité de Laurent à deux bases pour tous les zéros |
| `ScientificRebuild20260901.fullQuartetOffDoubleTransitionLocalization_iff_riemannHypothesis` | `Round27PDoubleLocalizationStrengthAudit` | P ⟺ RH | ÉQUIVALENTE À RH (double localisation universelle de transition pour le quartet hors ligne) | double localisation universelle de transition pour le quartet hors ligne |
| `ScientificRebuild20260828.riemannHypothesis_of_FINAL_SEMANTIC_LOCK` | `ScientificRebuild20260828.FinalClosureTarget` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (FINAL_SEMANTIC_LOCK (⟺ RH par FINAL_SEMANTIC_LOCK_iff_riemannHypothesis)) | FINAL_SEMANTIC_LOCK (⟺ RH par FINAL_SEMANTIC_LOCK_iff_riemannHypothesis) |
| `ScientificRebuild20260828.FINAL_SEMANTIC_LOCK_of_riemannHypothesis` | `ScientificRebuild20260828.FinalSemanticLockStrengthAudit` | RH ⟹ P (RH en hypothèse) | CONFIRMÉE | la prémisse est RH elle-même (non déchargée) ; le théorème établit seulement que la propriété nommée découle de RH (sens facile de la caractérisation) |
| `ScientificRebuild20260828.FINAL_SEMANTIC_LOCK_iff_riemannHypothesis` | `ScientificRebuild20260828.FinalSemanticLockStrengthAudit` | P ⟺ RH | ÉQUIVALENTE À RH (FINAL_SEMANTIC_LOCK) | FINAL_SEMANTIC_LOCK — FINAL_SEMANTIC_LOCK ⟺ RiemannHypothesis (classification de force exacte). |
| `ScientificRebuild20260828.finalSemanticLockIsTerminalStrength` | `ScientificRebuild20260828.RealObjectsSpine` | P ⟺ RH | ÉQUIVALENTE À RH (FINAL_SEMANTIC_LOCK) | FINAL_SEMANTIC_LOCK — L'ancien verrou sémantique final n'est pas un théorème intermédiaire : il a exactement la force de RH. |
| `ScientificRebuild20260829.riemannHypothesis_of_fiberedMZEqM` | `ScientificRebuild20260829.ActualFiberedGrammar` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (loi de grammaire fibrée FiberedMZEqM (⟺ RH par fiberedMZEqM_iff_riemannHypothesis)) | loi de grammaire fibrée FiberedMZEqM (⟺ RH par fiberedMZEqM_iff_riemannHypothesis) |
| `ScientificRebuild20260829.routeA_universal_fiberedMZEqM_iff_RH` | `ScientificRebuild20260829.MirrorGapFourRouteAudit` | P ⟺ RH | ÉQUIVALENTE À RH (FiberedMZEqM) | FiberedMZEqM — La loi de grammaire fibrée FiberedMZEqM est équivalente à RH (certificat de force, route A). |
| `ScientificRebuild20260829.routeD_universal_memberReturn_iff_RH` | `ScientificRebuild20260829.MirrorGapFourRouteAudit` | P ⟺ RH | ÉQUIVALENTE À RH (FINAL_SEMANTIC_LOCK) | FINAL_SEMANTIC_LOCK — Le producteur universel de retour du membre (FINAL_SEMANTIC_LOCK) équivaut à RH (route D). |
| `ScientificRebuild20260829.routeD_endpointAssemblyProducer_iff_RH` | `ScientificRebuild20260829.MirrorGapFourRouteAudit` | P ⟺ RH | ÉQUIVALENTE À RH (FirstReturnEndpointAssemblyProducer) | FirstReturnEndpointAssemblyProducer — Le producteur d'égalité d'extrémités pré-R12 équivaut à RH. |
| `ScientificRebuild20260829.fiberedMZEqM_of_riemannHypothesis` | `ScientificRebuild20260829.MirrorGapStrengthAudit` | RH ⟹ P (RH en hypothèse) | CONFIRMÉE | la prémisse est RH elle-même (non déchargée) ; le théorème établit seulement que la propriété nommée découle de RH (sens facile de la caractérisation) |
| `ScientificRebuild20260829.fiberedMZEqM_iff_riemannHypothesis` | `ScientificRebuild20260829.MirrorGapStrengthAudit` | P ⟺ RH | ÉQUIVALENTE À RH (FiberedMZEqM) | FiberedMZEqM — FiberedMZEqM ⟺ RH : classification de force de la loi terminale de nullité même-entrée. |
| `ScientificRebuild20260829.riemannHypothesis_mirrorGapClosure_of_fiberedMZEqM` | `ScientificRebuild20260829.MirrorGapTerminalClosure` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (loi de grammaire fibrée FiberedMZEqM (⟺ RH par fiberedMZEqM_iff_riemannHypothesis)) | loi de grammaire fibrée FiberedMZEqM (⟺ RH par fiberedMZEqM_iff_riemannHypothesis) |
| `ScientificRebuild20260829.semanticMaster_riemannHypothesis` | `ScientificRebuild20260829.SemanticMasterTerminal` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (loi de grammaire fibrée FiberedMZEqM (⟺ RH par fiberedMZEqM_iff_riemannHypothesis)) | loi de grammaire fibrée FiberedMZEqM (⟺ RH par fiberedMZEqM_iff_riemannHypothesis) |
| `ScientificRebuild20260829.riemannHypothesis_mirrorGapClosure_of_fiberedMZEqM` | `ScientificRebuild20260829.SemanticMasterTerminal` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (loi de grammaire fibrée FiberedMZEqM (⟺ RH) ; nom dupliqué avec le théorème de MirrorGapTerminalClosure) | loi de grammaire fibrée FiberedMZEqM (⟺ RH) ; nom dupliqué avec le théorème de MirrorGapTerminalClosure |
| `ScientificRebuild20260829.terminalSocket_is_rh_strength` | `ScientificRebuild20260829.TerminalSocketForceAudit` | P ⟺ RH | ÉQUIVALENTE À RH (FiberedMZEqM) | FiberedMZEqM — La prise terminale FiberedMZEqM est de force RH (certificat réutilisé). |
| `riemannHypothesis_of_universal_mirrorBranchCoincidence` | `SemanticProofSpine` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (coïncidence de branche miroir pour tout partenariat canonique (⟺ RH par universal_mirrorBranchCoincidence_iff_rh)) | coïncidence de branche miroir pour tout partenariat canonique (⟺ RH par universal_mirrorBranchCoincidence_iff_rh) |
| `universal_mirrorBranchCoincidence_iff_rh` | `SemanticProofSpine` | P ⟺ RH | ÉQUIVALENTE À RH (coïncidence de branche miroir universelle) | coïncidence de branche miroir universelle |
| `terminalImplicationForceAccounting` | `SemanticProofSpine` | P ⟺ RH | ÉQUIVALENTE À RH (coïncidence de branche miroir universelle) | coïncidence de branche miroir universelle |
| `SemanticTransportClosure20260821.riemannHypothesis_of_masterR12Producer` | `SemanticTransportClosure20260821.MasterSemanticClosure` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (producteur R12 maître (⟺ RH par masterR12Producer_iff_riemannHypothesis) ; conclusion RiemannHypothesis) | producteur R12 maître (⟺ RH par masterR12Producer_iff_riemannHypothesis) ; conclusion RiemannHypothesis |
| `SemanticTransportClosure20260821.masterR12Producer_of_riemannHypothesis` | `SemanticTransportClosure20260821.MasterSemanticClosure` | RH ⟹ P (RH en hypothèse) | CONFIRMÉE | la prémisse est RH elle-même (non déchargée) ; le théorème établit seulement que la propriété nommée découle de RH (sens facile de la caractérisation) |
| `SemanticTransportClosure20260821.masterR12Producer_iff_riemannHypothesis` | `SemanticTransportClosure20260821.MasterSemanticClosure` | P ⟺ RH | ÉQUIVALENTE À RH (prémisse nommée (cf. gloss)) | prémisse nommée (cf. gloss) |
| `SemanticTransportClosure20260821.r1ThroughR11ProducesR12_iff_riemannHypothesis` | `SemanticTransportClosure20260821.MasterSemanticClosure` | P ⟺ RH | ÉQUIVALENTE À RH (prémisse nommée (cf. gloss)) | prémisse nommée (cf. gloss) |
| `SemanticTransportClosure20260821.riemannHypothesis_of_firstReturnEndpointAssemblyProducer` | `SemanticTransportClosure20260821.PreR12MemberSensitiveAssemblyBoundary` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (producteur universel d'extrémités de premier retour (⟺ RH par firstReturnEndpointAssemblyProducer_iff_riemannHypothesis) ; conclusion RiemannHypothesis) | producteur universel d'extrémités de premier retour (⟺ RH par firstReturnEndpointAssemblyProducer_iff_riemannHypothesis) ; conclusion RiemannHypothesis |
| `SemanticTransportClosure20260821.firstReturnEndpointAssemblyProducer_of_riemannHypothesis` | `SemanticTransportClosure20260821.PreR12MemberSensitiveAssemblyBoundary` | RH ⟹ P (RH en hypothèse) | CONFIRMÉE | la prémisse est RH elle-même (non déchargée) ; le théorème établit seulement que la propriété nommée découle de RH (sens facile de la caractérisation) |
| `SemanticTransportClosure20260821.firstReturnEndpointAssemblyProducer_iff_riemannHypothesis` | `SemanticTransportClosure20260821.PreR12MemberSensitiveAssemblyBoundary` | P ⟺ RH | ÉQUIVALENTE À RH (prémisse nommée (cf. gloss)) | prémisse nommée (cf. gloss) |
| `SemanticTransportClosure20260821.riemannHypothesis_of_P0` | `SemanticTransportClosure20260821.ProgressiveFiberedFirstReturnClosure` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (P0 (FirstReturnMemberSensitiveFidelityP0, ⟺ RH par P0_iff_riemannHypothesis) ; conclusion RiemannHypothesis) | P0 (FirstReturnMemberSensitiveFidelityP0, ⟺ RH par P0_iff_riemannHypothesis) ; conclusion RiemannHypothesis |
| `SemanticTransportClosure20260821.P0_of_riemannHypothesis` | `SemanticTransportClosure20260821.ProgressiveFiberedFirstReturnClosure` | RH ⟹ P (RH en hypothèse) | CONFIRMÉE | la prémisse est RH elle-même (non déchargée) ; le théorème établit seulement que la propriété nommée découle de RH (sens facile de la caractérisation) |
| `SemanticTransportClosure20260821.P0_iff_riemannHypothesis` | `SemanticTransportClosure20260821.ProgressiveFiberedFirstReturnClosure` | P ⟺ RH | ÉQUIVALENTE À RH (prémisse nommée (cf. gloss)) | prémisse nommée (cf. gloss) |
| `SemanticTransportClosure20260821.riemannHypothesis_of_P1` | `SemanticTransportClosure20260821.ProgressiveFiberedFirstReturnClosure` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (P1 (⟺ P0 ⟺ RH) ; conclusion RiemannHypothesis) | P1 (⟺ P0 ⟺ RH) ; conclusion RiemannHypothesis |
| `SemanticTransportClosure20260821.P1_of_riemannHypothesis` | `SemanticTransportClosure20260821.ProgressiveFiberedFirstReturnClosure` | RH ⟹ P (RH en hypothèse) | CONFIRMÉE | la prémisse est RH elle-même (non déchargée) ; le théorème établit seulement que la propriété nommée découle de RH (sens facile de la caractérisation) |
| `SemanticTransportClosure20260821.P1_iff_riemannHypothesis` | `SemanticTransportClosure20260821.ProgressiveFiberedFirstReturnClosure` | P ⟺ RH | ÉQUIVALENTE À RH (prémisse nommée (cf. gloss)) | prémisse nommée (cf. gloss) |
| `SemanticTransportClosure20260821.riemannHypothesis_of_P2` | `SemanticTransportClosure20260821.ProgressiveFiberedFirstReturnClosureP2` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (fidélité P2/P3 (⟺ P0 ⟺ RH) ; conclusion RiemannHypothesis) | fidélité P2/P3 (⟺ P0 ⟺ RH) ; conclusion RiemannHypothesis |
| `SemanticTransportClosure20260821.P2_of_riemannHypothesis` | `SemanticTransportClosure20260821.ProgressiveFiberedFirstReturnClosureP2` | RH ⟹ P (RH en hypothèse) | CONFIRMÉE | la prémisse est RH elle-même (non déchargée) ; le théorème établit seulement que la propriété nommée découle de RH (sens facile de la caractérisation) |
| `SemanticTransportClosure20260821.P2_iff_riemannHypothesis` | `SemanticTransportClosure20260821.ProgressiveFiberedFirstReturnClosureP2` | P ⟺ RH | ÉQUIVALENTE À RH (fidélité P2/P3 (⟺ P0 ⟺ RH)) | fidélité P2/P3 (⟺ P0 ⟺ RH) |
| `SemanticTransportClosure20260821.riemannHypothesis_of_P3` | `SemanticTransportClosure20260821.ProgressiveFiberedFirstReturnClosureP3` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (fidélité P2/P3 (⟺ P0 ⟺ RH) ; conclusion RiemannHypothesis) | fidélité P2/P3 (⟺ P0 ⟺ RH) ; conclusion RiemannHypothesis |
| `SemanticTransportClosure20260821.P3_of_riemannHypothesis` | `SemanticTransportClosure20260821.ProgressiveFiberedFirstReturnClosureP3` | RH ⟹ P (RH en hypothèse) | CONFIRMÉE | la prémisse est RH elle-même (non déchargée) ; le théorème établit seulement que la propriété nommée découle de RH (sens facile de la caractérisation) |
| `SemanticTransportClosure20260821.P3_iff_riemannHypothesis` | `SemanticTransportClosure20260821.ProgressiveFiberedFirstReturnClosureP3` | P ⟺ RH | ÉQUIVALENTE À RH (fidélité P2/P3 (⟺ P0 ⟺ RH)) | fidélité P2/P3 (⟺ P0 ⟺ RH) |
| `SemanticTransportClosure20260821.riemannHypothesis_of_partneredNaturality` | `SemanticTransportClosure20260821.TrueZeroClosure` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (TrueZeroPartneredNaturality (⟺ RH) ; conclusion RiemannHypothesis) | TrueZeroPartneredNaturality (⟺ RH) ; conclusion RiemannHypothesis |
| `SemanticTransportClosure20260821.partneredNaturality_of_riemannHypothesis` | `SemanticTransportClosure20260821.TrueZeroClosure` | RH ⟹ P (RH en hypothèse) | CONFIRMÉE | la prémisse est RH elle-même (non déchargée) ; le théorème établit seulement que la propriété nommée découle de RH (sens facile de la caractérisation) |
| `SemanticTransportClosure20260821.partneredNaturality_iff_riemannHypothesis` | `SemanticTransportClosure20260821.TrueZeroClosure` | P ⟺ RH | ÉQUIVALENTE À RH (TrueZeroPartneredNaturality) | TrueZeroPartneredNaturality — Comptabilité de force : l'interface du producteur universel a la force de RH ; cela ne fait pas d'un producteur indépendant un théorème. |
| `riemannHypothesis_of_unifiedCommonE44ContactProducer` | `TrueZeroCommonContactProducerAudit` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (producteur commun de contact E44 (⟺ RH par unifiedCommonE44ContactProducer_iff_riemannHypothesis) ; conclusion RiemannHypothesis) | producteur commun de contact E44 (⟺ RH par unifiedCommonE44ContactProducer_iff_riemannHypothesis) ; conclusion RiemannHypothesis |
| `unifiedCommonE44ContactProducer_of_riemannHypothesis` | `TrueZeroCommonContactProducerAudit` | RH ⟹ P (RH en hypothèse) | CONFIRMÉE | la prémisse est RH elle-même (non déchargée) ; le théorème établit seulement que la propriété nommée découle de RH (sens facile de la caractérisation) |
| `unifiedCommonE44ContactProducer_iff_riemannHypothesis` | `TrueZeroCommonContactProducerAudit` | P ⟺ RH | ÉQUIVALENTE À RH (UnifiedCommonE44ContactProducer) | UnifiedCommonE44ContactProducer — Certificat de force cible exact : producteur commun ⟺ RH. |
| `unifiedKnownConstraintsProduceR12_iff_riemannHypothesis` | `UnifiedTrueZeroConstraintClosure` | P ⟺ RH | ÉQUIVALENTE À RH (UnifiedKnownConstraintsProduceR12) | UnifiedKnownConstraintsProduceR12 — Certificat de force exact du paquet même-objet entier connu : « contraintes connues ⟹ R12 » ⟺ RH. |
| `noCertifiedMirrorOffSignature_of_riemannHypothesis` | `XiAGCertifiedMirrorOffSignature` | RH ⟹ P (RH en hypothèse) | CONFIRMÉE | la prémisse est RH elle-même (non déchargée) ; le théorème établit seulement que la propriété nommée découle de RH (sens facile de la caractérisation) |
| `riemannHypothesis_of_noCertifiedMirrorOffSignature` | `XiAGCertifiedMirrorOffSignature` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (NoCertifiedMirrorOffSignature (⟺ RH) ; conclusion RiemannHypothesis) | NoCertifiedMirrorOffSignature (⟺ RH) ; conclusion RiemannHypothesis |
| `noCertifiedMirrorOffSignature_iff_riemannHypothesis` | `XiAGCertifiedMirrorOffSignature` | P ⟺ RH | ÉQUIVALENTE À RH (NoCertifiedMirrorOffSignature) | NoCertifiedMirrorOffSignature — Certificat d'anti-circularité : interdire la signature OFF certifiée complète est exactement RH. |
| `allConcreteRightHalfCountsZero_of_riemannHypothesis` | `XiAGTerminalClosureEquivalences` | RH ⟹ P (RH en hypothèse) | CONFIRMÉE | la prémisse est RH elle-même (non déchargée) ; le théorème établit seulement que la propriété nommée découle de RH (sens facile de la caractérisation) |
| `riemannHypothesis_of_allConcreteRightHalfCountsZero` | `XiAGTerminalClosureEquivalences` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (AllConcreteRightHalfCountsZero (⟺ RH) ; conclusion RiemannHypothesis) | AllConcreteRightHalfCountsZero (⟺ RH) ; conclusion RiemannHypothesis |
| `allConcreteRightHalfCountsZero_iff_riemannHypothesis` | `XiAGTerminalClosureEquivalences` | P ⟺ RH | ÉQUIVALENTE À RH (AllConcreteRightHalfCountsZero) | AllConcreteRightHalfCountsZero — Classification exacte de la formulation par comptes nuls bruts : ⟺ RH. |
| `eventually_subunit_of_riemannHypothesis` | `XiAGTerminalClosureEquivalences` | RH ⟹ P (RH en hypothèse) | CONFIRMÉE | la prémisse est RH elle-même (non déchargée) ; le théorème établit seulement que la propriété nommée découle de RH (sens facile de la caractérisation) |
| `eventuallyConcreteRightHalfCountSubunit_iff_riemannHypothesis` | `XiAGTerminalClosureEquivalences` | P ⟺ RH | ÉQUIVALENTE À RH (EventuallyConcreteRightHalfCountSubunit) | EventuallyConcreteRightHalfCountSubunit — Classification exacte de la formulation par quantification entière : ⟺ RH. |
| `strictRightDecayCertificate_of_riemannHypothesis` | `XiAGTerminalClosureEquivalences` | RH ⟹ P (RH en hypothèse) | CONFIRMÉE | la prémisse est RH elle-même (non déchargée) ; le théorème établit seulement que la propriété nommée découle de RH (sens facile de la caractérisation) |
| `strictRightDecayCertificate_iff_riemannHypothesis` | `XiAGTerminalClosureEquivalences` | P ⟺ RH | ÉQUIVALENTE À RH (StrictRightDecayCertificate) | StrictRightDecayCertificate — La prise brute de décroissance actuelle a exactement la force de RH. |
| `rawRightHalfContourDecayCertificate_iff_riemannHypothesis` | `XiAGTerminalClosureEquivalences` | P ⟺ RH | ÉQUIVALENTE À RH (RawRightHalfContourDecayCertificate) | RawRightHalfContourDecayCertificate — Classification finale : l'énoncé de décroissance de contour de moitié droite exact est lui-même équivalent à RH. |
| `RiemannHypothesisProof.RiemannHypothesis_proved_of_samePassageComposition` | `RiemannHypothesisProof.RiemannHypothesis` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (SamePassageGrammaticalRelationIsPreserved (⟺ RH) ; conclusion RiemannHypothesis) | SamePassageGrammaticalRelationIsPreserved (⟺ RH) ; conclusion RiemannHypothesis |
| `RiemannHypothesisProof.RiemannHypothesis_of_SamePassageGrammaticalRelationIsPreserved` | `RiemannHypothesisProof.SamePassageGrammar` | P ⟹ RH | IMPLIQUE RH SOUS PRÉMISSE (SamePassageGrammaticalRelationIsPreserved (⟺ RH) ; conclusion RiemannHypothesis) | SamePassageGrammaticalRelationIsPreserved (⟺ RH) ; conclusion RiemannHypothesis |
| `RiemannHypothesisProof.SamePassageGrammaticalRelationIsPreserved_of_RiemannHypothesis` | `RiemannHypothesisProof.SamePassageGrammar` | RH ⟹ P (RH en hypothèse) | CONFIRMÉE | la prémisse est RH elle-même (non déchargée) ; le théorème établit seulement que la propriété nommée découle de RH (sens facile de la caractérisation) |
| `RiemannHypothesisProof.SamePassageGrammaticalRelationIsPreserved_iff_RiemannHypothesis` | `RiemannHypothesisProof.SamePassageGrammar` | P ⟺ RH | ÉQUIVALENTE À RH (SamePassageGrammaticalRelationIsPreserved) | SamePassageGrammaticalRelationIsPreserved — Certificat de force : composition même-passage ⟺ RiemannHypothesis (non utilisé dans la preuve terminale). |

### B. Conclusion « tout zéro non trivial est de partie réelle 1/2 » sans le terme `RiemannHypothesis` (forme dépliée de RH ; 24 théorèmes)

| théorème | module | statut | prémisse en mots |
|---|---|---|---|
| `ScientificRebuild20260828.E44VonMangoldtPivotInjection.allNontrivialZerosCritical_of_reflectionSamePivot` | `ScientificRebuild20260828.E44LocalVonMangoldtPivot` | IMPLIQUE RH SOUS PRÉMISSE | injection de pivots E44 avec « même pivot pour le miroir de même hauteur » (ReflectionSameE44Pivot) ; conclusion ∀ρ non trivial, β=1/2 = forme dépliée de RH |
| `ScientificRebuild20260828.E44VonMangoldtPivotInjection.allNontrivialZerosCritical_of_heightDetermined` | `ScientificRebuild20260828.E44LocalVonMangoldtPivot` | IMPLIQUE RH SOUS PRÉMISSE | indice de pivot déterminé par la hauteur ; conclusion ∀ρ non trivial, β=1/2 = forme dépliée de RH |
| `ScientificRebuild20260828.RH_of_FINAL_SEMANTIC_LOCK` | `ScientificRebuild20260828.FinalClosureTarget` | IMPLIQUE RH SOUS PRÉMISSE | FINAL_SEMANTIC_LOCK (⟺ RH) ; « RH » du projet |
| `ScientificRebuild20260828.memberReturnLock_forces_all_true_zeros_critical` | `ScientificRebuild20260828.GrammarReturnFracture` | IMPLIQUE RH SOUS PRÉMISSE | verrou « von Mangoldt force le retour membre » (VonMangoldtForcesMemberReflectionReturn) ; conclusion β=1/2 pour tout zéro non trivial (forme dépliée de RH) |
| `ScientificRebuild20260828.allNontrivialZeros_beta_eq_half_of_sameEventLocalization` | `ScientificRebuild20260828.SemanticZeroPrimePivotContactProof` | IMPLIQUE RH SOUS PRÉMISSE | loi de localisation même-événement (SameEventLocalizationLaw) ; conclusion ∀ρ non trivial, β=1/2 (forme dépliée de RH) |
| `ScientificRebuild20260828.critical_of_reflectionInvariant_injective` | `ScientificRebuild20260828.ZeroFamilyCriticalityForcing` | IMPLIQUE RH SOUS PRÉMISSE | observable injectif F sur les zéros non triviaux invariant par la réflexion canonique ; conclusion ∀ρ non trivial, β=1/2 (forme dépliée de RH) |
| `ScientificRebuild20260828.allNontrivialZerosCritical_of_zeroHeight_injective_on_every_constellation` | `ScientificRebuild20260828.ZeroFamilyCriticalityForcing` | IMPLIQUE RH SOUS PRÉMISSE | zeroHeight injectif sur chaque constellation bornée ; conclusion ∀ρ non trivial, β=1/2 (forme dépliée de RH) |
| `ScientificRebuild20260828.allNontrivialZerosCritical_of_contactSignature_reflectionInvariant` | `ScientificRebuild20260828.ZeroFamilyCriticalityForcing` | IMPLIQUE RH SOUS PRÉMISSE | signature de contact invariante par réflexion pour tout zéro ; conclusion ∀ρ non trivial, β=1/2 (forme dépliée de RH) |
| `ScientificRebuild20260828.allNontrivialZerosCritical_of_contactSignature_heightDetermined` | `ScientificRebuild20260828.ZeroFamilyCriticalityForcing` | IMPLIQUE RH SOUS PRÉMISSE | signature de contact déterminée par la hauteur (HeightDetermined) ; conclusion ∀ρ non trivial, β=1/2 (forme dépliée de RH) |
| `ScientificRebuild20260829.false_of_positive_offline_of_fiberedMZEqM` | `ScientificRebuild20260829.ActualFiberedGrammar` | IMPLIQUE RH SOUS PRÉMISSE | loi de grammaire fibrée FiberedMZEqM (⟺ RH par fiberedMZEqM_iff_riemannHypothesis) ; conclusion : aucun représentant positif hors ligne à aucune hauteur (forme dépliée de RH) |
| `ScientificRebuild20260829.positiveRepresentative_beta_eq_half_of_fiberedMZEqM` | `ScientificRebuild20260829.ActualFiberedGrammar` | IMPLIQUE RH SOUS PRÉMISSE | loi de grammaire fibrée FiberedMZEqM (⟺ RH) ; conclusion : tout représentant positif est critique (forme dépliée de RH) |
| `ScientificRebuild20260829.false_of_true_offline_mirror_gap` | `ScientificRebuild20260829.MirrorGapTerminalClosure` | IMPLIQUE RH SOUS PRÉMISSE | loi de grammaire fibrée FiberedMZEqM (⟺ RH) ; conclusion : aucun représentant positif hors ligne (forme dépliée de RH) |
| `ScientificRebuild20260829.positiveRepresentative_beta_eq_half_of_mirrorGap` | `ScientificRebuild20260829.MirrorGapTerminalClosure` | IMPLIQUE RH SOUS PRÉMISSE | loi de grammaire fibrée FiberedMZEqM (⟺ RH) ; conclusion : tout représentant positif est critique (forme dépliée de RH) |
| `ScientificRebuild20260829.semanticMaster_no_positive_offline` | `ScientificRebuild20260829.SemanticMasterTerminal` | IMPLIQUE RH SOUS PRÉMISSE | loi de grammaire fibrée FiberedMZEqM (⟺ RH) ; conclusion : aucun représentant positif hors ligne (forme dépliée de RH) |
| `ScientificRebuild20260829.semanticMaster_positive_beta_eq_half` | `ScientificRebuild20260829.SemanticMasterTerminal` | IMPLIQUE RH SOUS PRÉMISSE | loi de grammaire fibrée FiberedMZEqM (⟺ RH) ; conclusion : tout représentant positif est critique (forme dépliée de RH) |
| `SemanticTransportClosure20260821.all_nontrivial_zeros_critical_of_partneredNaturality` | `SemanticTransportClosure20260821.TrueZeroClosure` | IMPLIQUE RH SOUS PRÉMISSE | TrueZeroPartneredNaturality (⟺ RH par partneredNaturality_iff_riemannHypothesis) ; conclusion ∀ρ vrai zéro non trivial, β=1/2 (forme dépliée de RH) |
| `positive_height_critical_of_noCertifiedMirrorOffSignature` | `XiAGCertifiedMirrorOffSignature` | IMPLIQUE RH SOUS PRÉMISSE | NoCertifiedMirrorOffSignature (⟺ RH) ; conclusion : tout zéro non trivial de hauteur > 0 est critique (forme dépliée de RH sur les hauteurs positives) |
| `positive_height_nontrivial_critical_of_concrete_decay_bound` | `XiAGConcreteRightHalfDegree` | IMPLIQUE RH SOUS PRÉMISSE | borne brute décroissante du compte concret de moitié droite (⟺ RH) ; conclusion : tout zéro non trivial de hauteur > 0 est critique (forme dépliée de RH sur les hauteurs positives) |
| `positive_height_nontrivial_critical_of_primeDensity_raw_bound` | `XiAGConcreteRightHalfDegree` | IMPLIQUE RH SOUS PRÉMISSE | borne brute par la densité première (⟺ RH) ; conclusion : tout zéro non trivial de hauteur > 0 est critique (forme dépliée de RH sur les hauteurs positives) |
| `bounded_critical_line_gives_global` | `ZeroPrimeIntruderExclusion` | IMPLIQUE RH SOUS PRÉMISSE | tout membre de toute constellation bornée est sur la ligne (bornée-critique universelle) ; conclusion ∀ρ non trivial, β=1/2 (forme dépliée de RH) |
| `capture_defect_preservation_everywhere_gives_rh` | `ZeroPrimeIntruderExclusion` | IMPLIQUE RH SOUS PRÉMISSE | conservation du défaut par la capture pour toute constellation bornée (⟺ bornée-critique ⟺ RH) ; conclusion ∀ρ non trivial, β=1/2 (forme dépliée de RH) |
| `RiemannHypothesisProof.NonCentralFunctionalMirrorContradiction_of_samePassageComposition` | `RiemannHypothesisProof.RiemannHypothesis` | IMPLIQUE RH SOUS PRÉMISSE | SamePassageGrammaticalRelationIsPreserved (⟺ RH par SamePassageGrammaticalRelationIsPreserved_iff_RiemannHypothesis) ; conclusion pointwise : tout zéro non trivial est critique (forme dépliée de RH) |
| `RiemannHypothesisProof.ZeroNonTrivialIsCentral_proved_of_samePassageComposition` | `RiemannHypothesisProof.RiemannHypothesis` | IMPLIQUE RH SOUS PRÉMISSE | SamePassageGrammaticalRelationIsPreserved (⟺ RH) ; conclusion ZeroNonTrivialIsCentral (∀ρ non trivial, β=1/2 : forme dépliée de RH) |
| `RiemannHypothesisProof.ZeroNonTrivialIsCentral_of_SamePassageGrammaticalRelationIsPreserved` | `RiemannHypothesisProof.SamePassageGrammar` | IMPLIQUE RH SOUS PRÉMISSE | SamePassageGrammaticalRelationIsPreserved (⟺ RH) ; conclusion ZeroNonTrivialIsCentral (forme dépliée de RH) |

### C. Théorèmes du lot dont le type porte une prémisse nommée prouvée équivalente à RH (ailleurs dans le projet), sans contenir `RiemannHypothesis` (39 théorèmes)

Prémisse → théorème `↔ RiemannHypothesis` qui l'établit équivalente à RH (`prem.json`, tout le projet). Statut = statut du théorème.

| théorème | prémisse (théorème d'équivalence) | statut |
|---|---|---|
| `ScientificRebuild20260828.LegacyP0Audit.p0_definition_exact` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP0` (`SemanticTransportClosure20260821.P0_iff_riemannHypothesis`) | CONFIRMÉE |
| `ScientificRebuild20260828.FINAL_SEMANTIC_LOCK_exact` | `ScientificRebuild20260828.FINAL_SEMANTIC_LOCK` (`ScientificRebuild20260829.routeD_universal_memberReturn_iff_RH`) | CONFIRMÉE |
| `ScientificRebuild20260828.FullyAligned.contradiction_of_FINAL_SEMANTIC_LOCK` | `ScientificRebuild20260828.FINAL_SEMANTIC_LOCK` (`ScientificRebuild20260829.routeD_universal_memberReturn_iff_RH`) | RÉFUTATION COMPILÉE |
| `ScientificRebuild20260828.RH_of_FINAL_SEMANTIC_LOCK` | `ScientificRebuild20260828.FINAL_SEMANTIC_LOCK` (`ScientificRebuild20260829.routeD_universal_memberReturn_iff_RH`) | IMPLIQUE RH SOUS PRÉMISSE |
| `ScientificRebuild20260829.false_of_positive_offline_of_fiberedMZEqM` | `ScientificRebuild20260829.FiberedMZEqM` (`ScientificRebuild20260829.terminalSocket_is_rh_strength`) | IMPLIQUE RH SOUS PRÉMISSE |
| `ScientificRebuild20260829.positiveRepresentative_beta_eq_half_of_fiberedMZEqM` | `ScientificRebuild20260829.FiberedMZEqM` (`ScientificRebuild20260829.terminalSocket_is_rh_strength`) | IMPLIQUE RH SOUS PRÉMISSE |
| `ScientificRebuild20260829.false_of_true_offline_mirror_gap` | `ScientificRebuild20260829.FiberedMZEqM` (`ScientificRebuild20260829.terminalSocket_is_rh_strength`) | IMPLIQUE RH SOUS PRÉMISSE |
| `ScientificRebuild20260829.positiveRepresentative_beta_eq_half_of_mirrorGap` | `ScientificRebuild20260829.FiberedMZEqM` (`ScientificRebuild20260829.terminalSocket_is_rh_strength`) | IMPLIQUE RH SOUS PRÉMISSE |
| `ScientificRebuild20260829.semanticMaster_no_positive_offline` | `ScientificRebuild20260829.FiberedMZEqM` (`ScientificRebuild20260829.terminalSocket_is_rh_strength`) | IMPLIQUE RH SOUS PRÉMISSE |
| `ScientificRebuild20260829.semanticMaster_positive_beta_eq_half` | `ScientificRebuild20260829.FiberedMZEqM` (`ScientificRebuild20260829.terminalSocket_is_rh_strength`) | IMPLIQUE RH SOUS PRÉMISSE |
| `SemanticTransportClosure20260821.r1ThroughR11ProducesR12_iff_masterR12Producer` | `SemanticTransportClosure20260821.R1ThroughR11ProducesR12` (`SemanticTransportClosure20260821.r1ThroughR11ProducesR12_iff_riemannHypothesis`); `SemanticTransportClosure20260821.MasterR12Producer` (`SemanticTransportClosure20260821.masterR12Producer_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.P1_of_P0` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP0` (`SemanticTransportClosure20260821.P0_iff_riemannHypothesis`); `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP1` (`SemanticTransportClosure20260821.P1_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.P0_of_P1` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP0` (`SemanticTransportClosure20260821.P0_iff_riemannHypothesis`); `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP1` (`SemanticTransportClosure20260821.P1_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.P1_iff_P0` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP0` (`SemanticTransportClosure20260821.P0_iff_riemannHypothesis`); `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP1` (`SemanticTransportClosure20260821.P1_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.P1_of_P2` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP1` (`SemanticTransportClosure20260821.P1_iff_riemannHypothesis`); `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP2` (`SemanticTransportClosure20260821.P2_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.P2_of_P1` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP1` (`SemanticTransportClosure20260821.P1_iff_riemannHypothesis`); `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP2` (`SemanticTransportClosure20260821.P2_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.P2_iff_P1` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP1` (`SemanticTransportClosure20260821.P1_iff_riemannHypothesis`); `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP2` (`SemanticTransportClosure20260821.P2_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.P0_of_P2` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP0` (`SemanticTransportClosure20260821.P0_iff_riemannHypothesis`); `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP2` (`SemanticTransportClosure20260821.P2_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.P2_of_P0` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP0` (`SemanticTransportClosure20260821.P0_iff_riemannHypothesis`); `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP2` (`SemanticTransportClosure20260821.P2_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.P2_iff_P0` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP0` (`SemanticTransportClosure20260821.P0_iff_riemannHypothesis`); `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP2` (`SemanticTransportClosure20260821.P2_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.P2_of_P3` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP2` (`SemanticTransportClosure20260821.P2_iff_riemannHypothesis`); `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP3` (`SemanticTransportClosure20260821.P3_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.P3_of_P2` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP2` (`SemanticTransportClosure20260821.P2_iff_riemannHypothesis`); `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP3` (`SemanticTransportClosure20260821.P3_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.P3_iff_P2` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP2` (`SemanticTransportClosure20260821.P2_iff_riemannHypothesis`); `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP3` (`SemanticTransportClosure20260821.P3_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.P1_of_P3` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP1` (`SemanticTransportClosure20260821.P1_iff_riemannHypothesis`); `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP3` (`SemanticTransportClosure20260821.P3_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.P0_of_P3` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP0` (`SemanticTransportClosure20260821.P0_iff_riemannHypothesis`); `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP3` (`SemanticTransportClosure20260821.P3_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.P3_iff_P1` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP1` (`SemanticTransportClosure20260821.P1_iff_riemannHypothesis`); `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP3` (`SemanticTransportClosure20260821.P3_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.P3_iff_P0` | `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP0` (`SemanticTransportClosure20260821.P0_iff_riemannHypothesis`); `SemanticTransportClosure20260821.FirstReturnMemberSensitiveFidelityP3` (`SemanticTransportClosure20260821.P3_iff_riemannHypothesis`) | CONFIRMÉE |
| `SemanticTransportClosure20260821.all_nontrivial_zeros_critical_of_partneredNaturality` | `SemanticTransportClosure20260821.TrueZeroPartneredNaturality` (`SemanticTransportClosure20260821.partneredNaturality_iff_riemannHypothesis`) | IMPLIQUE RH SOUS PRÉMISSE |
| `masterR12Producer_of_unifiedCommonE44ContactProducer` | `SemanticTransportClosure20260821.MasterR12Producer` (`SemanticTransportClosure20260821.masterR12Producer_iff_riemannHypothesis`); `UnifiedCommonE44ContactProducer` (`unifiedCommonE44ContactProducer_iff_riemannHypothesis`) | CONFIRMÉE |
| `unifiedKnownConstraintsProduceR12_iff_masterR12Producer` | `SemanticTransportClosure20260821.MasterR12Producer` (`SemanticTransportClosure20260821.masterR12Producer_iff_riemannHypothesis`); `UnifiedKnownConstraintsProduceR12` (`unifiedKnownConstraintsProduceR12_iff_riemannHypothesis`) | CONFIRMÉE |
| `positive_height_critical_of_noCertifiedMirrorOffSignature` | `NoCertifiedMirrorOffSignature` (`noCertifiedMirrorOffSignature_iff_riemannHypothesis`) | IMPLIQUE RH SOUS PRÉMISSE |
| `allConcreteRightHalfCountsZero_of_eventually_subunit` | `EventuallyConcreteRightHalfCountSubunit` (`eventuallyConcreteRightHalfCountSubunit_iff_riemannHypothesis`); `AllConcreteRightHalfCountsZero` (`allConcreteRightHalfCountsZero_iff_riemannHypothesis`) | CONFIRMÉE |
| `allConcreteRightHalfCountsZero_of_decayCertificate` | `AllConcreteRightHalfCountsZero` (`allConcreteRightHalfCountsZero_iff_riemannHypothesis`); `StrictRightDecayCertificate` (`strictRightDecayCertificate_iff_riemannHypothesis`) | CONFIRMÉE |
| `strictRightDecayCertificate_of_rawContour` | `RawRightHalfContourDecayCertificate` (`rawRightHalfContourDecayCertificate_iff_riemannHypothesis`); `StrictRightDecayCertificate` (`strictRightDecayCertificate_iff_riemannHypothesis`) | CONFIRMÉE |
| `rawContourDecayCertificate_of_strictRight` | `RawRightHalfContourDecayCertificate` (`rawRightHalfContourDecayCertificate_iff_riemannHypothesis`); `StrictRightDecayCertificate` (`strictRightDecayCertificate_iff_riemannHypothesis`) | CONFIRMÉE |
| `rawRightHalfContourDecayCertificate_iff_strictRightDecayCertificate` | `RawRightHalfContourDecayCertificate` (`rawRightHalfContourDecayCertificate_iff_riemannHypothesis`); `StrictRightDecayCertificate` (`strictRightDecayCertificate_iff_riemannHypothesis`) | CONFIRMÉE |
| `RiemannHypothesisProof.NonCentralFunctionalMirrorContradiction_of_samePassageComposition` | `RiemannHypothesisProof.SamePassageGrammaticalRelationIsPreserved` (`RiemannHypothesisProof.SamePassageGrammaticalRelationIsPreserved_iff_RiemannHypothesis`) | IMPLIQUE RH SOUS PRÉMISSE |
| `RiemannHypothesisProof.ZeroNonTrivialIsCentral_proved_of_samePassageComposition` | `RiemannHypothesisProof.SamePassageGrammaticalRelationIsPreserved` (`RiemannHypothesisProof.SamePassageGrammaticalRelationIsPreserved_iff_RiemannHypothesis`) | IMPLIQUE RH SOUS PRÉMISSE |
| `RiemannHypothesisProof.ZeroNonTrivialIsCentral_of_SamePassageGrammaticalRelationIsPreserved` | `RiemannHypothesisProof.SamePassageGrammaticalRelationIsPreserved` (`RiemannHypothesisProof.SamePassageGrammaticalRelationIsPreserved_iff_RiemannHypothesis`) | IMPLIQUE RH SOUS PRÉMISSE |

## 1. Table vérité → théorèmes

Pour chaque vérité Vi touchée par le lot : nombre de théorèmes, statut le plus fort atteint, puis la liste des noms (statut différent de CONFIRMÉE signalé par un suffixe : `†` sous condition, `‡` équivalente/implique RH, `§` réfutation compilée). Le rattachement « Vi » n'est posé que lorsque le type instancie ou établit la vérité ; sinon `AJOUT`.

- **V6** (23 ; plus fort : CONFIRMÉE ; C 23) : `ScientificRebuild20260828.EventContext.trueMember`, `ScientificRebuild20260828.genuineNontrivialZeroData`, `ScientificRebuild20260828.NontrivialZeroProfile.zerohood`, `ScientificRebuild20260828.NontrivialZeroProfile.not_trivial`, `ScientificRebuild20260828.NontrivialZeroProfile.not_pole`, `ScientificRebuild20260828.nontrivialZero_complete_profile`, `ScientificRebuild20260828.trivialZero_notNontrivial`, `ScientificRebuild20260829.TrustedZetaSeam.zerohood`, `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.trueMember`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1_trueZero`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11.r1`, `SemanticTransportClosure20260821.actualProjectZero_isTrueNontrivialZero`, `zetaZero_trivial_or_nontrivial`, `trivialZetaZero_not_nontrivial`, `zetaPerron_trivial_disjoint_nontrivial`, `RiemannHypothesisProof.trueZero_is_source_member`, `RiemannHypothesisProof.trivial_nontrivial_disjoint`, `RiemannHypothesisProof.ZeroNonTrivial.isZero`, `RiemannHypothesisProof.ZeroNonTrivial.notZeroTrivial`, `RiemannHypothesisProof.ZeroNonTrivial.ne_one`, `RiemannHypothesisProof.ZeroNonTrivial.ne_neg_nat`, `RiemannHypothesisProof.ZeroNonTrivialIsNotZeroTrivial`, `RiemannHypothesisProof.ZeroTrivialAndZeroNonTrivialAreDisjoint`
- **V7** (34 ; plus fort : CONFIRMÉE ; C 34) : `ScientificRebuild20260828.EventContext.openStrip`, `ScientificRebuild20260828.EventContext.positiveHeight`, `ScientificRebuild20260828.boundaryZeroGammaPositive`, `ScientificRebuild20260828.NontrivialZeroProfile.beta_positive`, `ScientificRebuild20260828.NontrivialZeroProfile.beta_lt_one`, `ScientificRebuild20260828.NontrivialZeroProfile.gamma_nonzero`, `ScientificRebuild20260828.OffLineQuartetProfile.seed_gamma_nonzero`, `ScientificRebuild20260828.nontrivialZero_complete_foundation`, `ScientificRebuild20260828.nontrivialZero_beta_openUnit`, `ScientificRebuild20260828.nontrivialInterior_gamma_ne_zero`, `ScientificRebuild20260829.TrustedZetaSeam.open_strip`, `ScientificRebuild20260829.TrustedZetaSeam.height_nonzero`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_positiveHeight`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_beta_ne_zero`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_gamma_ne_zero`, `TrueZeroQuartet.seed_im_ne_zero`, `UnifiedPositiveOfflineCase.positiveHeight`, `nontrivial_zeta_zero_im_ne_zero`, `Backlund.zeta_zero_re_mem_of_im_pos`, `zeta_zero_re_mem_of_im_pos`, `isNontrivialZetaZero_re_mem_Ioo`, `RiemannHypothesisProof.re_lt_one_of_zeta_eq_zero`, `RiemannHypothesisProof.ZeroTrivial_of_riemannZeta_eq_zero_of_re_nonpos`, `RiemannHypothesisProof.inStrip_of_mathlib`, `RiemannHypothesisProof.ZeroNonTrivial_of_riemannZeta_eq_zero`, `RiemannHypothesisProof.TrueNontrivialZero.isTrue`, `RiemannHypothesisProof.TrueNontrivialZero.gamma_pos`, `RiemannHypothesisProof.ZeroNonTrivial.re_pos`, `RiemannHypothesisProof.ZeroNonTrivial.re_lt_one`, `RiemannHypothesisProof.ZeroNonTrivial.mk'`, `RiemannHypothesisProof.ZeroNonTrivialBetaPositive`, `RiemannHypothesisProof.ZeroNonTrivialBetaLessThanOne`, `RiemannHypothesisProof.ZeroNonTrivial.im_ne_zero`, `RiemannHypothesisProof.ZeroNonTrivialGammaNonZero`
- **V8** (1 ; plus fort : CONFIRMÉE ; C 1) : `orderedPositiveRepresentatives_height_mono`
- **V9** (1 ; plus fort : CONFIRMÉE ; C 1) : `RiemannHypothesisProof.ZeroTrivialHasNoContactGeometry`
- **V12** (7 ; plus fort : CONFIRMÉE ; C 7) : `zetaZeroMultiplicity_conj`, `tendsto_mul_logDeriv_riemannZeta_zero`, `zetaZeroMultiplicity_zetaReflect`, `riemannZeta_order_eq_zetaZeroMultiplicity`, `zetaZeroMultiplicity_pos`, `RiemannHypothesisProof.ZeroNonTrivialMultiplicityPositive'`, `RiemannHypothesisProof.ZeroNonTrivialMultiplicityPositive`
- **V16** (3 ; plus fort : CONFIRMÉE ; C 3) : `ScientificRebuild20260901.TripleTransitionRigidity.left_span_law`, `ScientificRebuild20260901.TripleTransitionRigidity.right_span_law`, `ScientificRebuild20260829.towerHeightSpanOnPrimeEdge_eq_log_one_add_gap`
- **V17** (7 ; plus fort : CONFIRMÉE ; C 7) : `ScientificRebuild20260828.trueZero_contactWidth_from_height`, `ScientificRebuild20260828.SameEventPivotContactLocalization.member_contact_width`, `ScientificRebuild20260828.SameEventPivotContactLocalization.mirror_contact_width`, `ScientificRebuild20260828.NontrivialZeroProfile.contact_width_from_height`, `ScientificRebuild20260829.towerHeightSpanOnPrimeEdge_sub`, `ScientificRebuild20260829.tangentStageRight_eq_contact_mul`, `e44Delta_tangentStage`
- **V20** (3 ; plus fort : CONFIRMÉE ; C 3) : `RiemannHypothesisProof.trueContacts_exactly_two`, `RiemannHypothesisProof.trueContacts_ordered`, `RiemannHypothesisProof.trueContactCell_unique`
- **V28** (3 ; plus fort : CONFIRMÉE ; C 3) : `ScientificRebuild20260828.tourPivotPrime_eq`, `ScientificRebuild20260829.canonicalEventAxisPrime_eq`, `RiemannHypothesisProof.CanonicalPrimeEvent.centerPrime_ofTwoTransitionStart`
- **V45** (70 ; plus fort : CONFIRMÉE ; C 68, CC 2) : `ScientificRebuild20260901.ZeroGapConstraintCage.contact_pair_recovers_member`, `ScientificRebuild20260828.FullyAligned.fracturedMember_coordinates`, `ScientificRebuild20260828.EventContext.contactPairRecoversSameZero`, `ScientificRebuild20260828.E44SelectedPrimePivotCell.recovers_gamma`, `ScientificRebuild20260828.E44SelectedPrimePivotCell.recovers_beta`, `ScientificRebuild20260828.trueZero_beta_from_height_and_leftContact`, `ScientificRebuild20260828.trueZero_height_beta_contact_coupling`, `ScientificRebuild20260828.localContactSatisfiesCorrectedE44`, `ScientificRebuild20260828.localContactRecoversGamma`, `ScientificRebuild20260828.localContactRecoversBeta`, `ScientificRebuild20260828.localContactBetaFormula`, `ScientificRebuild20260828.PrimeLocatedTangentCell.recovers_height`, `ScientificRebuild20260828.PrimeLocatedTangentCell.recovers_beta`, `ScientificRebuild20260828.trueZeroContactCellSatisfiesCorrectedE44`, `ScientificRebuild20260828.trueZeroContactCellRecoversGamma`, `ScientificRebuild20260828.RealObjectBoundaryState.contactCellIsSameZeroE44`, `ScientificRebuild20260828.SameEventPivotContactLocalization.member_beta_readout`, `ScientificRebuild20260828.SameEventPivotContactLocalization.mirror_beta_readout`, `ScientificRebuild20260828.trueZero_beta_from_contact`, `ScientificRebuild20260828.trueZero_gamma_from_contact_pair`, `ScientificRebuild20260828.trueZero_corrected_E44`, `ScientificRebuild20260828.trueZero_beta_from_contact_pair`, `ScientificRebuild20260828.NontrivialZeroProfile.beta_from_height_and_left_contact`, `ScientificRebuild20260828.NontrivialZeroProfile.contact_pair_recovers_height`, `ScientificRebuild20260828.NontrivialZeroProfile.contact_pair_recovers_beta`, `ScientificRebuild20260828.nontrivialContactSignature_recoversGamma`, `ScientificRebuild20260828.nontrivialContactSignature_satisfiesCorrectedE44`, `ScientificRebuild20260828.nontrivialContactSignature_recoversBeta`, `ScientificRebuild20260828.nontrivialInterior_recovers_actual_beta`, `ScientificRebuild20260828.nontrivialInterior_recovers_actual_gamma`, `ScientificRebuild20260828.nontrivialRelation_recovers_beta`, `ScientificRebuild20260828.nontrivialRelation_recovers_height`, `ScientificRebuild20260829.FiberedMirrorGapEntry.contact_pair_recovers_member`, `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.recovers_gamma`, `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.recovers_beta`, `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.recovers_gamma`, `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.recovers_beta`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_beta_eq_gamma_div_tan_contact`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_gamma_recovered_from_contact_pair`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_contact_pair_satisfies_corrected_E44`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_beta_recovered_from_contact_pair`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_contact_pair_recovers_beta_gamma`, `tangentContact_phase_exact`, `tangentContact_equation`, `beta_eq_gamma_div_tan_tangentContact`, `e44RecoveredGamma_tangentStage`, `e44TangentEliminatedLaw_of_contact_width`, `tangentStage_satisfies_E44TangentEliminatedLaw`, `e44TangentRecoveredBeta_eq`, `trueZero_tangentStage_satisfies_corrected_E44`, `trueZero_tangentStage_one_satisfies_legacy_E44`, `UnifiedPositiveOfflineCase.E44Attachment.law`, `RiemannHypothesisProof.ContactsRecoverGamma`, `RiemannHypothesisProof.ContactsRecoverBeta`, `RiemannHypothesisProof.ContactsRecoverZeroIdentity`, `RiemannHypothesisProof.ContactsRecoverIndividualZeroData`, `RiemannHypothesisProof.HarmonicTowerPreservesIndividualZeroReading`, `RiemannHypothesisProof.ZeroIdentityIsPreservedAcrossWholeProof`, `RiemannHypothesisProof.HarmonicTowerPreservesSameZeroAcrossFirstReturn`, `RiemannHypothesisProof.FirstReturnContactsRecoverSameGamma`, `RiemannHypothesisProof.FirstReturnContactsRecoverSameBeta`, `RiemannHypothesisProof.FirstReturnContactsRecoverSameZero`, `RiemannHypothesisProof.trueContacts_recover_gamma`, `RiemannHypothesisProof.trueContacts_recover_beta`, `RiemannHypothesisProof.trueContacts_recover_member`, `RiemannHypothesisProof.tower_preserves_member`, `RiemannHypothesisProof.tower_preserves_gamma`, `RiemannHypothesisProof.tower_preserves_beta`, `RiemannHypothesisProof.tower_no_recentering`†, `RiemannHypothesisProof.NonCentralMirrorSameEventContactsRecoverMember`†
- **V46** (13 ; plus fort : CONFIRMÉE ; C 13) : `ScientificRebuild20260828.beta_eq_of_same_height_and_same_leftContact`, `ScientificRebuild20260828.nontrivial_family_contact_pair_injective`, `ScientificRebuild20260828.verified_dual_rigidities`, `ScientificRebuild20260828.nontrivialContactSignature_injective`, `ScientificRebuild20260829.transformedZeroGapOnPrimeEdge_ne_zero_of_distinct_trueZeros`, `ScientificRebuild20260829.transformedZeroGapOnVonMangoldtEdge_ne_zero_of_distinct_trueZeros`, `ScientificRebuild20260829.canonicalPrimeEdgeVoiceSignature_injective`, `ScientificRebuild20260829.distinct_trueZeros_separated_on_every_canonicalPrimeEdge`, `ScientificRebuild20260829.distinct_trueZeros_separated_on_every_vonMangoldtPrimeEdge`, `ScientificRebuild20260829.preOff_zeroPrimeEdge_rigidity`, `RiemannHypothesisProof.SameRealContactPairGivesSameZero`, `RiemannHypothesisProof.IndividualZeroReadingRequiresContactRecoverability`, `RiemannHypothesisProof.trueContacts_member_injective`
- **V48** (222 ; plus fort : CONFIRMÉE ; C 216, CC 6) : `ScientificRebuild20260901.ZeroGapConstraintCage.vonMangoldt_prime_gap_exact`, `ScientificRebuild20260901.reconstructedTransitionLabel_eq_canonical`, `ScientificRebuild20260901.reconstructedTransitionOccurrence_eq_canonical`, `ScientificRebuild20260901.reconstructedTripleTransitionPair_eq_canonical`, `ScientificRebuild20260901.TripleTransitionRigidity.transition_pair_lock`, `ScientificRebuild20260901.passageReconstructedTransitionOccurrence_eq_canonical`, `ScientificRebuild20260901.passageOccurrence_vonMangoldt_locks`, `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.vonMangoldt_first_position_lock`, `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.vonMangoldt_pivot_position_lock`, `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.vonMangoldt_third_position_lock`, `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.vonMangoldt_incoming_gap_lock`, `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.vonMangoldt_outgoing_gap_lock`, `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.vonMangoldt_incoming_occurrence_lock`, `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.vonMangoldt_outgoing_occurrence_lock`, `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.vonMangoldt_two_edge_grammar_lock`, `ScientificRebuild20260828.EventContext.vonMangoldtGrammarLockOnBlock`, `ScientificRebuild20260828.EventContext.MZ_eq_M`, `ScientificRebuild20260828.vonMangoldt_local_psi_lock`, `ScientificRebuild20260828.localVonMangoldtForcesExactPrimeGap`, `ScientificRebuild20260828.localVonMangoldtForcesExactPrimeEndpoints`, `ScientificRebuild20260828.localVonMangoldtForcesExactDeltaPsi`, `ScientificRebuild20260828.deltaPsiLocal_exact`, `ScientificRebuild20260828.tourPivot_vonMangoldt_position_lock`, `ScientificRebuild20260828.tourPivot_vonMangoldt_gap_lock`, `ScientificRebuild20260828.AUDIT_prime_grammar_immutable`, `ScientificRebuild20260828.SameEventPivotContactLocalization.pivot_vonMangoldt_position_exact`, `ScientificRebuild20260828.SameEventPivotContactLocalization.pivot_vonMangoldt_gap_exact`, `ScientificRebuild20260828.SameEventPivotContactLocalization.local_deltaPsi_exact`, `ScientificRebuild20260828.vonMangoldt_weighted_count_lock`, `ScientificRebuild20260828.vonMangoldt_real_prime_count_lock`, `ScientificRebuild20260828.vonMangoldt_prime_count_lock`, `ScientificRebuild20260828.vonMangoldt_prime_position_lock`, `ScientificRebuild20260828.vonMangoldt_prime_gap_lock`, `ScientificRebuild20260828.vonMangoldt_grammar_lock`, `ScientificRebuild20260828.vonMangoldt_grammar_positions_lock`, `ScientificRebuild20260828.vonMangoldt_grammar_gaps_lock`, `ScientificRebuild20260828.vonMangoldt_grammar_transitions_lock`, `ScientificRebuild20260828.vonMangoldt_grammar_pattern_lock`, `ScientificRebuild20260828.vonMangoldt_grammar_family_lock`, `ScientificRebuild20260828.vonMangoldt_grammar_boundary_lock`, `ScientificRebuild20260828.vonMangoldt_grammar_order_lock`, `ScientificRebuild20260828.vonMangoldt_cell_lock`, `ScientificRebuild20260828.prime_grammar_is_not_free`, `ScientificRebuild20260829.FiberedMirrorGapEntry.encodedZeroSource_eq_canonicalPrimeGrammar`, `ScientificRebuild20260829.FiberedMirrorGapEntry.reconstructedGrammar_eq_primeGrammar`, `ScientificRebuild20260829.FiberedMirrorGapEntry.vonMangoldt_prime_gap_exact`, `ScientificRebuild20260829.transformedZeroGapOnVonMangoldtEdge_eq_canonical`, `ScientificRebuild20260829.vonMangoldtPrimeEdgeVoiceSignature_eq_canonical`, `ScientificRebuild20260829.vonMangoldt_consecutivePrimeEdge_lock`, `ScientificRebuild20260829.selectedEncZCell_eq_gnat`, `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.vonMangoldt_axis_position_lock`, `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.vonMangoldt_axis_gap_lock`, `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.vonMangoldt_event_position`, `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.vonMangoldt_event_gap`, `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.encZ_eq_M_on_event_block`, `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.eventEncZCell_eq_gnat`, `ScientificRebuild20260829.TrueEventSingletonPassageRaccord.encZ_eq_M_on_trueEvent`, `ScientificRebuild20260829.encodeTrueEvent_encZRealization`, `zero_prime_patternFamilyAt_eq`, `zero_prime_metaPatternView_eq`, `zero_prime_patternOccupationProfile_eq`, `zero_prime_primitiveFamilyOccupationProfile_eq`, `PrimeZeroSemanticHierarchyCoverage.patternFamilyTransport`†, `PrimeZeroSemanticHierarchyCoverage.metaPatternTransport`†, `PrimeZeroSemanticHierarchyCoverage.patternOccupationTransport`†, `PrimeZeroSemanticHierarchyCoverage.primitiveFamilyOccupationTransport`†, `primeZeroSemanticHierarchyCoverage_holds`, `MirrorPairPrimeJunction.reconstructedGrammar_eq_activePrimeBlock`, `MirrorPairPrimeJunction.canonicalZeroSource_encodes_activePrimeBlock`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.finalObject_primeSide_eq_M`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.finalObject_primeSide_eq_MZ`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameBlock_primeGrammar_eq_zeroReconstructedGrammar`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.reconstructs_same_prime_block`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.MZ_eq_M_same_prime_block`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.capture_primeSide_eq_M`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.capture_primeSide_eq_MZ`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R6_samePrimeGrammar`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11.r6`, `SemanticTransportClosure20260821.FiberedFirstReturnClosureP2At.primeSideEqM`, `SemanticTransportClosure20260821.FiberedFirstReturnClosureP2At.primeSideEqMZ`, `completeGrammarBlock_pattern_eq_canonical`, `completeGrammarBlock_transitions_eq_pattern_relation`, `prime_completeGrammarBlock_entry_eq_blockEntryState`, `prime_completeGrammarBlock_exit_eq_blockExitState`, `zero_completeGrammarBlock_entry_eq_zeroReconstructedBlockEntryState`, `zero_completeGrammarBlock_exit_eq_zeroReconstructedBlockExitState`, `prime_completeGrammarBlock_globalDensity_eq_rank`, `prime_completeGrammarBlock_globalDensityTheta_eq_thetaM`, `zero_completeGrammarBlock_globalDensityTheta_eq_zeroReconstructedTheta`, `zero_completeGrammarBlock_eq_prime_completeGrammarBlock`, `zero_prime_positions_eq_all_positions`, `zero_prime_gaps_eq_all_positions`, `zero_prime_transitions_eq_all_positions`, `zero_prime_pattern_object_eq_all_positions_all_lengths`, `zero_prime_shape_eq_all_positions_all_lengths`, `zero_prime_family_eq_all_positions_all_lengths`, `zero_prime_entry_eq`, `zero_prime_exit_eq`, `zero_prime_transition_order_eq`, `zero_prime_pattern_order_eq`, `zero_prime_family_order_eq`, `zero_prime_global_density_eq`, `zero_prime_global_density_theta_eq`, `zero_prime_transitionSuccession_eq`, `zero_prime_familySuccession_eq`, `zero_prime_patternSuccession_eq`, `zero_prime_patternShape_eq`, `zero_prime_complete_grammar_bridge`, `zero_prime_pattern_occurrence_set_eq`, `zero_prime_pattern_occurrence_iff`, `zero_prime_family_occurrence_set_eq`, `zero_prime_family_occurrence_iff`, `zero_prime_transition_occurrence_set_eq`, `zero_prime_grammar_occurrence_set_eq`, `zero_prime_pattern_occurrence_initial_segment_eq`, `zero_prime_pattern_occurrence_count_eq`, `zero_prime_pattern_occurrence_order_eq`, `zero_prime_family_occurrence_initial_segment_eq`, `zero_prime_family_occurrence_count_eq`, `zero_prime_family_occurrence_order_eq`, `zero_prime_entry_exit_eq_at_every_occurrence`, `zero_prime_pattern_infinite_occurrence_iff`, `zero_prime_family_infinite_occurrence_iff`, `zero_prime_grammar_infinite_occurrence_iff`, `zero_prime_finite_ordered_succession_eq`, `zero_prime_complete_grammar_occurrence_bridge`, `zero_reconstructed_first_fifteen_positions_eq_canonical`, `zero_reconstructed_experiment_positions_eq_canonical`, `zero_reconstructed_experiment_gaps_eq_canonical`, `zero_reconstructed_experiment_complete_grammar_eq`, `prime_completeGrammarBlock_gaps_getElem`, `prime_completeGrammarBlock_positions_getElem`, `sourcePsiRecovered_canonical`, `sourcePiMangoldt_canonical`, `sourcePrimeCountReal_canonical`, `sourcePrimeCount_canonical`, `sourcePrimePosition_canonical`, `sourcePrimeGap_canonical`, `encodeZeroGrammar_canonical_eq_prime_grammar`, `capture_compatible_with_MZ_eq_M`, `capture_compatible_with_prime_determined_zero_grammar`, `capture_encodes_canonical_prime_grammar`, `capture_preserves_transitions`, `capture_preserves_transition_succession`, `capture_preserves_patterns`, `capture_preserves_shape`, `capture_preserves_pattern_order`, `capture_preserves_families`, `capture_preserves_family_order`, `capture_preserves_entry`, `capture_preserves_exit`, `capture_preserves_positions`, `capture_preserves_gaps`, `capture_preserves_occurrences`, `pi_from_PiWeighted_moebius`, `posOfCount_piCount_eq_p`, `reconstruction_positions_of_counting_eq`, `reconstruction_gaps_of_counting_eq`, `zeros_weighted_count_eq_arithmetic_weighted_count`, `zerosWeightedCount_eq_PiWeighted_of_admissible_cutoff`, `zerosPrimeCountReal_eq_piReal`, `zeros_prime_count_eq_prime_count`, `zeros_prime_positions_eq_prime_positions`, `zeros_prime_gaps_eq_prime_gaps`, `zero_reconstructed_any_derived_object_eq`, `zero_reconstructed_any_count_position_gap_object_eq`, `zero_reconstructed_pattern_object_eq`, `zero_reconstructed_family_classifier_eq`, `zero_reconstructed_order_eq`, `zero_reconstructed_order_constructor_eq`, `zero_reconstructed_density_fields_eq`, `zero_reconstructed_pair_classes_eq`, `zero_reconstructed_pair_classes_and_energy_eq`, `zero_reconstructed_cycle_relations_eq`, `zero_reconstructed_cycle_relation_prop_eq`, `LSeriesSummable_vonMangoldt_of_one_lt_re`, `negLogDeriv_riemannZeta_eq_LSeries_vonMangoldt`, `vonMangoldt_term_mul_perronKernel`, `neg_logDeriv_mul_perronKernel_eq_tsum`, `smoothed_mangoldt_weight_difference`, `smoothed_mangoldt_new_weight`, `smoothedMangoldtPrimitive_nat_difference`, `smoothedZeroPrimitive_eq_arithmetic`, `smoothedZeroPrimitive_nat_difference`, `psiRecoveredFromZeros_eq_psi`, `PiMangoldtFromZeros_eq_PiMangoldt`, `smoothed_formula_recovers_weighted_prime_count`, `RiemannHypothesisProof.CanonicalPrimeEvent.vonMangoldt_position_lock`, `RiemannHypothesisProof.CanonicalPrimeEvent.vonMangoldt_incomingGap_lock`, `RiemannHypothesisProof.CanonicalPrimeEvent.vonMangoldt_outgoingGap_lock`, `RiemannHypothesisProof.CanonicalPrimeEvent.reconstructedGrammar_eq_eventGrammar`, `RiemannHypothesisProof.VonMangoldtRelationDeterminesPrimePresence`, `RiemannHypothesisProof.VonMangoldtRelationDeterminesPrimePosition`, `RiemannHypothesisProof.ChebyshevRelationDeterminesLocalArithmeticVariation`, `RiemannHypothesisProof.VonMangoldtReconstructsPrimeCount`, `RiemannHypothesisProof.VonMangoldtReconstructsPrimePosition`, `RiemannHypothesisProof.VonMangoldtReconstructsGapForPrime`, `RiemannHypothesisProof.VonMangoldtReconstructsWholePrimeGrammar`, `RiemannHypothesisProof.VonMangoldtReconstructsPrimeGrammarGap`, `RiemannHypothesisProof.VonMangoldtReconstructsPrimeGrammarTransition`, `RiemannHypothesisProof.VonMangoldtReconstructsPrimeGrammarPattern`, `RiemannHypothesisProof.VonMangoldtReconstructsPrimeGrammarFamily`, `RiemannHypothesisProof.VonMangoldtRelationRigidifiesPrimeHistory`, `RiemannHypothesisProof.CentralPrimeDeterminesSameEncZAndMEvent`, `RiemannHypothesisProof.ZerosReconstructWeightedPrimeCount`, `RiemannHypothesisProof.ZerosReconstructPrimeCount`, `RiemannHypothesisProof.ZerosReconstructPrimePositions`, `RiemannHypothesisProof.ZerosReconstructGapForPrime`, `RiemannHypothesisProof.ZerosReconstructWholePrimeGrammar`, `RiemannHypothesisProof.PrimeHistoryFromZerosEqualsPrimeHistory`, `RiemannHypothesisProof.ZerosReconstructTransitionForPrime`, `RiemannHypothesisProof.ZerosReconstructPatternForPrime`, `RiemannHypothesisProof.ZerosReconstructFamilyForPrime`, `RiemannHypothesisProof.ZerosReconstructTransitionOrderForPrime`, `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_leftPrime_lock`, `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_pivot_lock`, `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_rightPrime_lock`, `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_incomingGap_lock`, `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_outgoingGap_lock`, `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_occurrence_pair_lock`, `RiemannHypothesisProof.NonCentralMirrorSameEventVonMangoldtGapLock`†, `RiemannHypothesisProof.NonCentralMirrorSameEventPrimeGrammarIsCanonical`†
- **V50** (4 ; plus fort : CONFIRMÉE ; C 4) : `orderedHeightFiber_sandwich`, `orderedHeightFiber_internal_gap_zero`, `orderedHeightFiber_internal_gap_zero_constellationGaps`, `orderedHeightFiber_internal_zero_gap_forall`
- **V59** (5 ; plus fort : CONFIRMÉE ; C 4, IM 1) : `ScientificRebuild20260828.critical_on_heightConstellation_of_zeroHeight_injective`, `ScientificRebuild20260828.allNontrivialZerosCritical_of_zeroHeight_injective_on_every_constellation`‡, `zeroConstellationWindowGaps_getElem`, `zeroConstellationWindowHeights_canonical_full`, `zeroConstellationWindowGaps_canonical_full`
- **V61** (5 ; plus fort : CONFIRMÉE ; C 5) : `ScientificRebuild20260828.tourPivotPrime_unique`, `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.primeIndex_unique`, `LocalizedMirrorPairPrimeWeldCase.assemblyPivot_unique`, `LocalizedMirrorPairPrimeWeldCase.PairAssemblyWindowCoverage.pivotUnique`, `RiemannHypothesisProof.TwoTransitionPrimeBlockHasUniqueCentralPrime`
- **V62** (21 ; plus fort : CONFIRMÉE ; CC 16, C 5) : `ScientificRebuild20260828.offLineSuppliesDistinctSameHeightPair`†, `ScientificRebuild20260828.realObjectBoundaryStateExists`†, `ScientificRebuild20260829.trueOffMirror_positive_distinct_sameHeight`†, `ScientificRebuild20260829.fiberedMirrorGapEntry_exists`†, `ScientificRebuild20260829.sameEventSingletonPassageRaccord_exists`†, `ScientificRebuild20260829.seamMirrorPairSelection_card`†, `ScientificRebuild20260829.seam_is_constructible_without_rh`†, `ScientificRebuild20260829.trustedZetaSeam`, `fullNonterminalSemanticAlignment_exists`†, `MemberMirrorGeometry.pairOccupiesSameHeightFiber`, `mirrorPairOrderedTroublePrimeCase_exists`†, `SemanticTransportClosure20260821.alignedLeftZeroFinset_image_reflect_eq_right`, `SemanticTransportClosure20260821.fullyAlignedSameEventContext_exists`†, `SemanticTransportClosure20260821.masterOffLineSemanticCase_exists`†, `SemanticTransportClosure20260821.masterOffLineSemanticCase_exists_same_zero`†, `unifiedPositiveOfflineCase_exists`†, `hasCertifiedMirrorOffSignature_of_positive_offline`†, `riemannZeta_zetaReflect_eq_zero`, `P4_4e.left_vertical_negLogDeriv_functional_identity`, `RiemannHypothesisProof.off_member_ne_mirror`†, `RiemannHypothesisProof.NonCentralFunctionalMirrorIsDistinct`†
- **V63** (94 ; plus fort : CONFIRMÉE ; C 88, CC 6) : `ScientificRebuild20260901.ZeroGapConstraintCage.quartet_card_four`, `ScientificRebuild20260901.ZeroGapConstraintCage.quartet_all_multiplicities_equal`, `ScientificRebuild20260828.EventContext.quartetIdentity`, `ScientificRebuild20260828.offLineSuppliesFullQuartet`†, `ScientificRebuild20260828.RealObjectBoundaryState.quartet_seed`, `ScientificRebuild20260828.NontrivialZeroProfile.conjugate_nontrivial`, `ScientificRebuild20260828.NontrivialZeroProfile.reflection_nontrivial`, `ScientificRebuild20260828.OffLineQuartetProfile.seed_zero`, `ScientificRebuild20260828.OffLineQuartetProfile.same_height_mirror_zero`, `ScientificRebuild20260828.OffLineQuartetProfile.conjugate_zero`, `ScientificRebuild20260828.OffLineQuartetProfile.opposite_height_mirror_zero`, `ScientificRebuild20260828.OffLineQuartetProfile.conjugate_gamma`, `ScientificRebuild20260828.OffLineQuartetProfile.opposite_height_mirror_gamma`, `ScientificRebuild20260828.OffLineQuartetProfile.conjugate_beta`, `ScientificRebuild20260828.OffLineQuartetProfile.opposite_height_mirror_beta`, `ScientificRebuild20260828.OffLineQuartetProfile.four_members_distinct`, `ScientificRebuild20260828.OffLineQuartetProfile.orbit_card_four`, `ScientificRebuild20260828.OffLineQuartetProfile.multiplicities_equal`, `ScientificRebuild20260828.offlineQuartet_complete_profile`, `ScientificRebuild20260828.nontrivialZero_conjugate_isNontrivial`, `ScientificRebuild20260829.FiberedMirrorGapEntry.mirror_is_genuine`, `ScientificRebuild20260829.quartet_transport_vonMangoldt_edge_lock`, `ScientificRebuild20260829.TrustedZetaSeam.conjugate_is_nontrivial`, `ScientificRebuild20260829.TrustedZetaSeam.mirror_is_nontrivial`, `MirrorPairPrimeJunction.rows_are_exact_mirror_pair`, `LocalizedMirrorPairPrimeWeldCase.pairRows_and_sourceDefect`, `MemberMirrorGeometry.mirrorIsTrueZero`, `MirrorPairOrderedTroublePrimeCase.exactMirrorRows_form_heightCollision`, `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.mirrorTrueMember`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.finalObject_mirror_mem_capture`, `SemanticTransportClosure20260821.negative_offLine_zero_gives_fullyAligned_case`†, `SemanticTransportClosure20260821.alignedLeftMultiplicityNat_eq_right`, `SemanticTransportClosure20260821.alignedTotalMultiplicityNat_eq_line_add_two_right`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.trueQuartet_seed`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.trueQuartet_sameHeightMirror`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.mirror_mem_capture`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R2_trueMirror`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11.r2`, `SemanticTransportClosure20260821.negative_offLine_zero_gives_master_case`†, `SemanticTransportClosure20260821.FiberedFirstReturnClosureP2At.sameMirrorInCapture`, `TrueZeroQuartet.conjugateMember_coe`, `TrueZeroQuartet.sameHeightMirror_coe`, `TrueZeroQuartet.oppositeHeightMirror_coe`, `TrueZeroQuartet.conjugateMember_im`, `TrueZeroQuartet.oppositeHeightMirror_im`, `TrueZeroQuartet.conjugateMember_re`, `TrueZeroQuartet.oppositeHeightMirror_re`, `TrueZeroQuartet.seed_ne_sameHeightMirror`, `TrueZeroQuartet.seed_ne_conjugateMember`, `TrueZeroQuartet.seed_ne_oppositeHeightMirror`, `TrueZeroQuartet.conjugateMember_ne_oppositeHeightMirror`, `TrueZeroQuartet.sameHeightMirror_ne_oppositeHeightMirror`, `TrueZeroQuartet.conjugateMember_ne_sameHeightMirror`, `TrueZeroQuartet.four_members_pairwise_distinct`, `TrueZeroQuartet.members_card_eq_four`, `TrueZeroQuartet.conjugate_multiplicity`, `TrueZeroQuartet.sameHeightMirror_multiplicity`, `TrueZeroQuartet.oppositeHeightMirror_multiplicity`, `TrueZeroQuartet.all_four_multiplicities_equal`, `TrueZeroQuartet.sameHeight_half_not_conjugation_closed`, `UnifiedPositiveOfflineCase.quartet_seed`, `UnifiedPositiveOfflineCase.quartet_card_four`, `UnifiedPositiveOfflineCase.KnownConstraintPacket.quartet`, `permanent_rightHalf_footprint_of_positive_offline`†, `centeredQuartetFirstMoment_eq_zero`, `quartetRadialSecondMoment_eq`, `riemannZeta_eq_conjRiemannZetaConj`, `riemannZeta_conj`, `riemannZeta_conj_eq_zero_of_zero`, `analyticOrderNatAt_conjRiemannZetaConj_eq_riemannZeta_conj`, `analyticOrderNatAt_riemannZeta_eq_conjRiemannZetaConj`, `zetaConjugationReflectionOrbit_zero`, `zetaConjugationReflectionOrbit_multiplicity_eq`, `isTrivialZetaZero_conj_iff`, `isNontrivialZetaZero_conj_iff`, `zetaPerronNontrivialZeroSet_conj_iff`, `zetaPerron_residue_conj`, `zetaPerron_conjugate_orbit_pairing`, `analyticOrderAt_completedZeta_zetaReflect`, `nontrivialZetaZerosByHeightFinset_conj`, `RiemannHypothesisProof.off_quartet_four_distinct`†, `RiemannHypothesisProof.off_quartet_multiplicity_lock`, `RiemannHypothesisProof.FunctionalQuartetDoesNotModifyZeroTrivialFamily`, `RiemannHypothesisProof.ConjugateForZeroPreservesBeta`, `RiemannHypothesisProof.ConjugateForZeroOpposesGamma`, `RiemannHypothesisProof.FunctionalMirrorForZeroIsZeroNonTrivial`, `RiemannHypothesisProof.FunctionalMirrorPreservesMultiplicity`, `RiemannHypothesisProof.ConjugateForZeroIsZeroNonTrivial`, `RiemannHypothesisProof.ConjugateForZeroPreservesMultiplicity`, `RiemannHypothesisProof.ConjugateForZeroIsDistinctFromZeroNonTrivial`, `RiemannHypothesisProof.NonCentralFunctionalQuartetHasFourDistinctZeros`†, `RiemannHypothesisProof.riemannZeta_conj`, `RiemannHypothesisProof.analyticOrderAt_zeta_conj`, `RiemannHypothesisProof.analyticOrderAt_zeta_one_sub`
- **V64** (4 ; plus fort : CONFIRMÉE ; C 4) : `positive_true_zero_mem_orderedPositiveRepresentatives`, `positive_true_mirror_mem_orderedPositiveRepresentatives`, `orderedPositiveMirrorPairWitness_exists`, `positiveMirrorPair_localContext_and_orderedView`
- **V65** (38 ; plus fort : CONFIRMÉE ; C 36, CC 2) : `OrderedPositiveMirrorPairWitness.same_height`, `ScientificRebuild20260901.ZeroGapConstraintCage.mirror_same_height`, `ScientificRebuild20260901.ZeroGapConstraintCage.mirror_complementary_re`, `ScientificRebuild20260901.ZeroGapConstraintCage.mirror_same_multiplicity`, `ScientificRebuild20260828.RealObjectBoundaryState.hasDistinctSameHeightZeros`, `ScientificRebuild20260828.NontrivialZeroProfile.reflection_same_height`, `ScientificRebuild20260828.NontrivialZeroProfile.reflection_complementary_beta`, `ScientificRebuild20260828.NontrivialZeroProfile.reflection_same_multiplicity`, `ScientificRebuild20260828.OffLineQuartetProfile.same_height_mirror_gamma`, `ScientificRebuild20260828.OffLineQuartetProfile.same_height_mirror_beta`, `ScientificRebuild20260828.nontrivialZero_reflection_foundation`, `ScientificRebuild20260829.FiberedMirrorGapEntry.mirror_same_height`, `ScientificRebuild20260829.FiberedMirrorGapEntry.mirror_complementary_re`, `ScientificRebuild20260829.seamMirrorPairSelection_same_height`, `ScientificRebuild20260829.TrustedZetaSeam.mirror_same_height`, `ScientificRebuild20260829.TrustedZetaSeam.mirror_complementary_re`, `ScientificRebuild20260829.TrustedZetaSeam.mirror_multiplicity`, `ScientificRebuild20260829.trustedMirrorProfile`, `MemberMirrorGeometry.mirrorSharesHeight`, `MemberMirrorGeometry.mirrorHasReflectedRadialPosition`, `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.sameHeight`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R3_sameHeight`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11.r3`, `SemanticTransportClosure20260821.mirrorPoint_re`, `SemanticTransportClosure20260821.mirrorPoint_im`, `SemanticTransportClosure20260821.FiberedFirstReturnClosureP3At.sameHeight`, `SemanticTransportClosure20260821.mirrorPoint_eq_projectMirror`, `SemanticTransportClosure20260821.fullyAlignedSameEventContextOf_mirror`†, `TrueZeroQuartet.sameHeightMirror_im`, `TrueZeroQuartet.sameHeightMirror_re`, `trueZeroBeta_mirror`, `trueZeroGamma_mirror`, `zetaReflect_re`, `RiemannHypothesisProof.functionalMirror_trueNontrivialZero_gamma`, `RiemannHypothesisProof.functionalMirror_trueNontrivialZero_beta`, `RiemannHypothesisProof.off_upperPair_sameHeight_distinctBeta`†, `RiemannHypothesisProof.FunctionalMirrorPreservesGamma`, `RiemannHypothesisProof.FunctionalMirrorComplementsBeta`
- **V74** (2 ; plus fort : CONFIRMÉE ; C 2) : `SemanticTransportClosure20260821.mirrorPoint_ne_self_iff`, `RiemannHypothesisProof.FirstReturnPreservesFunctionalMirrorDifference`
- **V77** (4 ; plus fort : CONFIRMÉE ; C 4) : `ScientificRebuild20260828.NontrivialZeroProfile.reflection_fixed_iff_central`, `ScientificRebuild20260829.TrustedZetaSeam.mirror_fixed_iff_critical`, `SemanticTransportClosure20260821.mirrorPoint_eq_self_iff`, `RiemannHypothesisProof.FunctionalMirrorEqualsZeroIffCentral`
- **V80** (2 ; plus fort : CONFIRMÉE ; C 2) : `zetaReflect_im`, `zetaReflect_deriv_ne_zero`
- **V100** (15 ; plus fort : CONFIRMÉE ; C 15) : `residue_unsmoothedZetaPerronIntegrand_at_zero`, `exp_cpow_zero_mode_identity`, `explicit_formula_zero_mode`, `exact_modal_projection_from_explicit_formula`, `tendsto_mul_neg_logDeriv_riemannZeta_zero`, `norm_nontrivialZeroResidueTerm_le_weighted`, `zetaPerron_residue_at_zeta_zero`, `zetaPerron_trivial_zero_residue_sum`, `zetaPerron_nontrivial_zero_residue_sum`, `neg_logDeriv_riemannZeta_sub_principal_zero_isBigO`, `meromorphicOrderAt_neg_logDeriv_riemannZeta_zero`, `residue_neg_logDeriv_riemannZeta_zero`, `residue_perronZetaIntegrand_zero`, `tour22_decomposition_instantiated`, `tour22_remainder_eq_explicit_formula_remainder`
- **V101** (1 ; plus fort : CONFIRMÉE ; C 1) : `explicit_formula_zero_mode_amplitude_ne_zero`
- **V102** (23 ; plus fort : CONFIRMÉE ; C 23) : `ScientificRebuild20260828.FullyAligned.normalizedMemberReflectionNorm`, `ScientificRebuild20260828.norm_memberGrammarReflection`, `ScientificRebuild20260828.NontrivialZeroProfile.tower_unitary_iff_central`, `ScientificRebuild20260828.nontrivialZero_tower_unitary_iff_critical`, `SemanticTransportClosure20260821.actualSameZeroReturnPartnership_radialDefect`, `SemanticTransportClosure20260821.ActualSameZeroReturnContext.sameRadialDefect`, `SemanticTransportClosure20260821.actualPartneredDefect_eq_zeroRadial`, `SemanticTransportClosure20260821.DefectAnchoredReturnData.blockOperator_radial`, `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.sameBlockRadialOperator`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.identifiedRightHalf_re_sub_half_eq_abs_radial`, `blockRadialMetricDefect_oppositeSigns`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.radialDefect_ne_zero`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.blockMetricDefect_oppositeSigns`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.blockOperator_radial`, `SemanticTransportClosure20260821.radialDefect_mirrorPoint`, `SemanticTransportClosure20260821.FiberedFirstReturnClosureP3At.radialDefectSameZero`, `SemanticTransportClosure20260821.FiberedFirstReturnClosureP3At.mirrorRadialOpposite`, `SemanticTransportClosure20260821.radialDefect_eq_actualPartnershipDefect`, `trueZeroDelta_mirror`, `UnifiedPositiveOfflineCase.trueZeroDelta_ne_zero`, `UnifiedPositiveOfflineCase.e44RadialDefect_ne_zero`, `UnifiedPositiveOfflineCase.KnownConstraintPacket.e44AllStages`, `centeredSameHeightFirstMoment_eq`
- **V121** (33 ; plus fort : CONFIRMÉE ; C 33) : `ScientificRebuild20260828.EventContext.sameZeroVonMangoldtQuartet`, `ScientificRebuild20260829.selection_rest_tsum_decomposition`, `ScientificRebuild20260829.offlineOrbit_tsum_decomposition_is_selection_instance`, `ScientificRebuild20260829.selection_Pi_rest_decomposition`, `ScientificRebuild20260829.seam_psi_rest_decomposition`, `FullNonterminalSemanticAlignment.collectivePrimeBridgeOnSameColumn`, `MirrorPairPrimeJunction.collectivePrimeBridge`, `LocalizedMirrorPairPrimeWeldCase.collectivePrimeBridge_on_partnershipBlock`, `MirrorPairOrderedTroublePrimeCase.collectivePrimeBridge_at_pairSensitiveColumn`, `TrueZeroQuartet.nontrivialZeroChannel_eq_quartet_add_rest`, `TrueZeroQuartet.smoothedVonMangoldtSum_eq_fixed_add_trivial_add_quartet_add_rest`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_smoothedVonMangoldt_quartet_decomposition`, `sourceZeroChannel_canonical`, `sourceSmoothedZeroFormula_canonical`, `sourceSmoothedZeroPrimitive_canonical`, `encodeZeroGrammar_reads_source`, `nontrivial_zero_residue_series_summable`, `nontrivial_zero_height_finset_bridge`, `nontrivial_height_complex_sum_eq_subtype_sum`, `nontrivial_zero_residue_series_symmetric_convergent`, `P5_complete`, `zetaPerron_finite_rectangle_residue_identity`, `smoothedVonMangoldtSum_eq_finite_residues_and_boundary_terms`, `zetaPerron_finite_residue_decomposition`, `smoothedVonMangoldtSum_eq_classified_residues_and_boundary_terms`, `verticalIntegral'_eq_smoothedVonMangoldtSum`, `exists_height_smoothed_formula_with_explicit_remainder`, `smoothedVonMangoldtSum_eq_height_truncated_main_add_boundaryRemainder`, `smoothedVonMangoldtSum_eq_height_truncated_residues_and_boundary_terms`, `smoothedVonMangoldtSum_eq_fixed_left_boundary_limit`, `smoothed_riemann_explicit_formula`, `smoothedZeroFormula_eq_smoothedVonMangoldtSum`, `smoothedZeroFormula_sub_background`
- **V140** (96 ; plus fort : CONFIRMÉE ; CC 1, EQ 18, IM 8, C 53, RF 16) : `OffLineCellModel.field33_fails_offLine`†, `separation_32_cannot_produce_33`‡, `unconditional_law_produces_field33_iff_rh`‡, `Q1_is_generic_control`‡, `Q5_two_orientation_compatibility_iff_rh`‡, `ScientificRebuild20260829.false_of_positive_offline_of_fiberedMZEqM`‡, `ScientificRebuild20260829.positiveRepresentative_beta_eq_half_of_fiberedMZEqM`‡, `ScientificRebuild20260829.routeA_universal_fiberedMZEqM_iff_RH`‡, `ScientificRebuild20260829.fiberedMZEqM_of_riemannHypothesis`, `ScientificRebuild20260829.fiberedMZEqM_iff_riemannHypothesis`‡, `ScientificRebuild20260829.false_of_true_offline_mirror_gap`‡, `ScientificRebuild20260829.positiveRepresentative_beta_eq_half_of_mirrorGap`‡, `ScientificRebuild20260829.semanticMaster_no_positive_offline`‡, `ScientificRebuild20260829.semanticMaster_positive_beta_eq_half`‡, `ScientificRebuild20260829.terminalSocket_is_rh_strength`‡, `mirrorBranchCoincidence_iff_critical`, `mirrorBranchCoincidence_fails_in_offLine_case`§, `universal_mirrorBranchCoincidence_iff_rh`‡, `terminalImplicationForceAccounting`‡, `MirrorPairOrderedTroublePrimeCase.terminalMirrorBranchCoincidence_fails`§, `SemanticTransportClosure20260821.actualGrammarReversalNaturality_iff_mirroredOperator_eq`, `SemanticTransportClosure20260821.actualGrammarReversalNaturality_iff_orientedEntries`, `SemanticTransportClosure20260821.actualGrammarReversalNaturality_iff_critical`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R12MatrixNaturality_iff_critical`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.not_R12MatrixNaturality_from_offLine`§, `SemanticTransportClosure20260821.actualPartneredNaturality_iff_critical`, `SemanticTransportClosure20260821.actualPartneredNaturality_fails_offLine`§, `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.not_internalNaturality`§, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.not_internalNaturality`§, `SemanticTransportClosure20260821.knownRigidities_admit_nonzero_defect`, `SemanticTransportClosure20260821.knownReturnRigidities_do_not_force_naturality`§, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R12Naturality_iff_critical`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.not_R12_from_offLine`§, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.contradiction_of_R12MatrixNaturality`§, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11_and_not_R12MatrixNaturality`, `SemanticTransportClosure20260821.masterR12Producer_of_riemannHypothesis`, `SemanticTransportClosure20260821.masterR12Producer_iff_riemannHypothesis`‡, `SemanticTransportClosure20260821.r1ThroughR11ProducesR12_iff_riemannHypothesis`‡, `SemanticTransportClosure20260821.canonicalMirrorResidualAgreement_forces_critical`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.contradiction_of_P0`§, `SemanticTransportClosure20260821.P0_of_riemannHypothesis`, `SemanticTransportClosure20260821.P0_iff_riemannHypothesis`‡, `SemanticTransportClosure20260821.P1_of_P0`, `SemanticTransportClosure20260821.P0_of_P1`, `SemanticTransportClosure20260821.P1_iff_P0`, `SemanticTransportClosure20260821.P1_of_riemannHypothesis`, `SemanticTransportClosure20260821.P1_iff_riemannHypothesis`‡, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.contradiction_of_P1`§, `SemanticTransportClosure20260821.P1_of_P2`, `SemanticTransportClosure20260821.P2_of_P1`, `SemanticTransportClosure20260821.P2_iff_P1`, `SemanticTransportClosure20260821.P0_of_P2`, `SemanticTransportClosure20260821.P2_of_P0`, `SemanticTransportClosure20260821.P2_iff_P0`, `SemanticTransportClosure20260821.P2_of_riemannHypothesis`, `SemanticTransportClosure20260821.P2_iff_riemannHypothesis`‡, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.contradiction_of_P2`§, `SemanticTransportClosure20260821.P2_of_P3`, `SemanticTransportClosure20260821.P3_of_P2`, `SemanticTransportClosure20260821.P3_iff_P2`, `SemanticTransportClosure20260821.P1_of_P3`, `SemanticTransportClosure20260821.P0_of_P3`, `SemanticTransportClosure20260821.P3_iff_P1`, `SemanticTransportClosure20260821.P3_iff_P0`, `SemanticTransportClosure20260821.P3_of_riemannHypothesis`, `SemanticTransportClosure20260821.P3_iff_riemannHypothesis`‡, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.contradiction_of_P3`§, `SemanticTransportClosure20260821.zeroRadialNaturality_iff_actualPartneredNaturality`, `SemanticTransportClosure20260821.reflectionAccumulationRatio_eq_iff_blockHolonomy_eq`, `SemanticTransportClosure20260821.reflectionAccumulationRatio_two_eq_four_iff_crossTransport_entries`, `SemanticTransportClosure20260821.crossTransport_entries_eq_iff_crossOperator_entries`, `SemanticTransportClosure20260821.reflectionAccumulationRatio_two_eq_four_iff_critical`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R12MatrixNaturality_iff_reflectionAccumulationRatio_baseIndependent`, `SemanticTransportClosure20260821.transformedReturnCase_natural_iff_defect_zero`, `SemanticTransportClosure20260821.cumulative_rigidities_admit_offline_case`, `SemanticTransportClosure20260821.cumulativeKnownRigidity_does_not_force_naturality`§, `SemanticTransportClosure20260821.naturalUnderReversal_iff_entries_eq`, `SemanticTransportClosure20260821.radial_entries_eq_iff_defect_zero`, `SemanticTransportClosure20260821.radial_naturality_iff_defect_zero`, `SemanticTransportClosure20260821.return_does_not_force_naturality`, `SemanticTransportClosure20260821.stage_naturality_iff_defect_zero`, `SemanticTransportClosure20260821.critical_of_zeroRadialTransport_natural`, `SemanticTransportClosure20260821.all_nontrivial_zeros_critical_of_partneredNaturality`‡, `SemanticTransportClosure20260821.partneredNaturality_of_riemannHypothesis`, `SemanticTransportClosure20260821.partneredNaturality_iff_riemannHypothesis`‡, `masterR12Producer_of_unifiedCommonE44ContactProducer`, `unifiedCommonE44ContactProducer_of_riemannHypothesis`, `unifiedCommonE44ContactProducer_iff_riemannHypothesis`‡, `UnifiedPositiveOfflineCase.not_R12`§, `UnifiedPositiveOfflineCase.KnownConstraintPacket.r12Fails`, `unifiedKnownConstraintsProduceR12_iff_masterR12Producer`, `unifiedKnownConstraintsProduceR12_iff_riemannHypothesis`‡, `false_of_independent_R12`§, `noCertifiedMirrorOffSignature_of_riemannHypothesis`, `allConcreteRightHalfCountsZero_of_riemannHypothesis`, `RiemannHypothesisProof.NonCentralFunctionalMirrorContradiction_of_samePassageComposition`‡
- **V145** (13 ; plus fort : CONFIRMÉE ; C 13) : `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.reconstructed_left_count_eq_startRank`, `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.reconstructed_local_count_three`, `ScientificRebuild20260828.E44SelectedPrimePivotCell.exact_local_prime_count`, `ScientificRebuild20260828.E44SelectedPrimePivotCell.exact_local_psi`, `ScientificRebuild20260828.PrimeLocatedTangentCell.localPrimeCount_exact`, `ScientificRebuild20260828.PrimeLocatedTangentCell.localDeltaPsi_exact`, `ScientificRebuild20260829.trueEvent_contactCell_exact_readout`, `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_left_count_lock`, `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_midpoint_count_lock`, `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_right_count_lock`, `RiemannHypothesisProof.CanonicalContactCell.vonMangoldt_local_count_lock`, `RiemannHypothesisProof.CanonicalContactCell.startRank_eq_floor_piReal_left`, `RiemannHypothesisProof.CanonicalContactCell.left_zero_count_floor_eq_startRank`
- **V149** (2 ; plus fort : CONFIRMÉE ; C 2) : `ScientificRebuild20260828.E44VonMangoldtPivotInjection.oneToOne`, `ScientificRebuild20260828.E44VonMangoldtPivotInjection.pivotIndex_injective`
- **V161** (4 ; plus fort : CONFIRMÉE ; C 4) : `distinct_central_trueZeros_have_distinct_heights`, `ordered_central_pair_heightGap_pos`, `critical_line_gives_no_captured_zero_gap_defect`, `captured_gaps_pos_iff_critical_line`
- **V162** (38 ; plus fort : CONFIRMÉE ; CC 12, C 26) : `off_trueZero_gives_actual_ordered_zeroGap_constructive`†, `off_mirror_zeroHeightGap_but_lossless_primeEdgeGap_nonzero`†, `ScientificRebuild20260901.zeroGapConstraintCage_of_off`†, `ScientificRebuild20260828.offLineForcesOrderedZeroGap`†, `ScientificRebuild20260829.FiberedMirrorGapEntry.actualZeroGapReadout_eq_zero`, `ScientificRebuild20260829.FiberedMirrorGapEntry.mirrorZeroGap_is_entry_of_actualZeroGrammar`, `ScientificRebuild20260829.FiberedMirrorGapEntry.zeroEntryIsNull`, `ScientificRebuild20260829.trueOffMirror_forces_zero_constellation_gap`†, `ScientificRebuild20260829.trueOffMirror_forces_zero_ordered_gap`†, `ScientificRebuild20260829.trueOffQuartet_forces_zero_ordered_gap`†, `ScientificRebuild20260829.FiberedMirrorGapEntry.zeroGap`, `ScientificRebuild20260829.MirrorFiberPassageWitness.actual_GZ_gap_eq_zero`, `ScientificRebuild20260829.MirrorFiberPassageWitness.orderedGap_eq_zero`, `ScientificRebuild20260829.mirrorFiberPassageWitness_exists`†, `ScientificRebuild20260829.SingletonPassageCrosswalk.leftInternalGap_eq_zero`, `ScientificRebuild20260829.encodeSingletonPassage_zeroRealization`, `ScientificRebuild20260829.seam_two_realizations`, `ScientificRebuild20260829.zeroEntry_always_null`, `ScientificRebuild20260829.TrueEventSingletonPassageRaccord.orderedGap_eq_zero`, `ScientificRebuild20260829.TrueEventCrosswalk.leftInternalGap_eq_zero`, `ScientificRebuild20260829.encodeTrueEvent_zeroRealization`, `ScientificRebuild20260829.quartet_upper_rawHeightGap_zero_but_transformedGap_nonzero`, `ScientificRebuild20260829.quartet_lower_rawHeightGap_zero_but_transformedGap_nonzero`, `FullNonterminalSemanticAlignment.orderedCollectiveTrouble`, `FullNonterminalSemanticAlignment.radialSeparationNonzero`, `LocalizedMirrorPairPrimeWeldCase.radial_nonzero`, `LocalizedMirrorPairPrimeWeldCase.orderedTrouble_and_pairPrimeDefect_coexist`, `OffLineMirrorTroubleCase.radial_nonzero`, `MirrorPairOrderedTroublePrimeCase.scientificBoundary`, `SemanticTransportClosure20260821.ProvedActualPartneredRigidities.orderedTrouble`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R4_exactOrderedTrouble`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.radialDefect_ne_zero`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11.r4`, `UnifiedPositiveOfflineCase.pairSensitiveScientificBoundary`, `intruder_gives_captured_zero_gap_defect`†, `RiemannHypothesisProof.NonCentralFunctionalMirrorCreatesActualZeroGrammarNullPassage`†, `RiemannHypothesisProof.NonCentralFunctionalMirrorCreatesActualZeroGapReadout`†, `RiemannHypothesisProof.NonCentralMirrorHasActualNullZeroPassageAndPositivePrimePlace`†
- **V163** (28 ; plus fort : CONFIRMÉE ; C 18, CC 5, RF 5) : `ScientificRebuild20260901.ZeroGapConstraintCage.mirror_contact_distinct`, `ScientificRebuild20260828.EventContext.contactFracture`, `ScientificRebuild20260828.beta_eq_half_of_reflection_sameEvent_leftContact`, `ScientificRebuild20260828.localOffLineMirrorContactsDistinct`, `ScientificRebuild20260828.offLineSplitsTrueMirrorContact`†, `ScientificRebuild20260828.no_sameEventPivotContactLocalization_of_off`§, `ScientificRebuild20260828.trueOffLine_contact_ne_mirror`†, `ScientificRebuild20260828.beta_forced_half_of_same_reflected_contact_signature`, `ScientificRebuild20260828.nontrivialContactSignature_reflect_eq_iff_critical`, `ScientificRebuild20260829.FiberedMirrorGapEntry.true_contacts_distinct`, `ScientificRebuild20260829.FiberedMirrorGapEntry.routeB_samePrimeCocycles_coexist_with_distinctContacts`, `ScientificRebuild20260829.trueOffline_center_ne_mirror_center`†, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_offLine_contact_ne_mirror`, `false_of_common_E44_contact_on_unified_offline`§, `e44_same_contacts_for_mirror_force_half`, `trueZero_same_E44_contacts_force_critical`, `trueOffline_no_common_E44_contact_pair`§, `critical_of_independent_common_E44_contact`, `tangentContact_eq_mirror_iff_half`, `trueZeroTangentContact_eq_mirror_iff_critical`, `trueOffline_tangentContact_ne_mirror`†, `UnifiedPositiveOfflineCase.no_common_E44_contact_pair`§, `UnifiedPositiveOfflineCase.E44Attachment.criticalDefect_ne_zero`, `UnifiedPositiveOfflineCase.KnownConstraintPacket.noCommonContact`, `RiemannHypothesisProof.NonCentralFunctionalMirrorCannotShareSameContacts`§, `RiemannHypothesisProof.sameHeight_distinctBeta_contacts_ne`, `RiemannHypothesisProof.sameHeight_not_contact_identity`, `RiemannHypothesisProof.tower_preserves_off_distinction`†
- **V174** (18 ; plus fort : CONFIRMÉE ; C 18) : `transition_residue_coboundary_v2`, `lifted_gap_coboundary_v2`, `PrimeGrammarCoverage.gapTransitionProjection`, `PrimeGrammarCoverage.transitionsAreFiniteGraphEdges`, `SemanticTransportClosure20260821.sigma_eq_of_prime_residue_eq`, `SemanticTransportClosure20260821.DefectAnchoredReturnData.changeFamily`, `SemanticTransportClosure20260821.prime_residue_ne_of_change_family`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.startChangeFamily`, `transformOf_edge_correspondence`, `transform_exhaustive_unique`, `transform_partition`, `gap_transition_residue_exists`, `completeGrammarBlock_family_is_the_canonical_family`, `zero_reconstructed_relations_eq`, `zero_reconstructed_patterns_eq`, `zero_reconstructed_patterns_eq_of_object`, `zero_reconstructed_families_eq`, `zero_reconstructed_complete_metapattern_eq`
- **V182** (4 ; plus fort : CONFIRMÉE ; C 4) : `RiemannHypothesisProof.CanonicalPrimeEvent.eq_of_centerPrime_eq`, `RiemannHypothesisProof.CanonicalPrimeEvent.same_centerPrime_rigidifies_environment`, `RiemannHypothesisProof.SameCentralPrimeDeterminesSamePrimeEvent`, `RiemannHypothesisProof.SameCentralPrimeDeterminesSamePrimeEnvironment`
- **O7 (point ouvert touché : aucun terme inconditionnel de type RH ; ces théorèmes n'établissent RH que sous prémisse, ou l'équivalence)** (23 ; plus fort : CONFIRMÉE ; IM 21, C 1, EQ 1) : `ScientificRebuild20260828.riemannHypothesis_of_FINAL_SEMANTIC_LOCK`‡, `ScientificRebuild20260828.RH_of_FINAL_SEMANTIC_LOCK`‡, `ScientificRebuild20260829.riemannHypothesis_of_fiberedMZEqM`‡, `ScientificRebuild20260829.riemannHypothesis_mirrorGapClosure_of_fiberedMZEqM`‡, `ScientificRebuild20260829.semanticMaster_riemannHypothesis`‡, `ScientificRebuild20260829.riemannHypothesis_mirrorGapClosure_of_fiberedMZEqM`‡, `riemannHypothesis_of_universal_mirrorBranchCoincidence`‡, `SemanticTransportClosure20260821.riemannHypothesis_of_masterR12Producer`‡, `SemanticTransportClosure20260821.riemannHypothesis_of_firstReturnEndpointAssemblyProducer`‡, `SemanticTransportClosure20260821.riemannHypothesis_of_P0`‡, `SemanticTransportClosure20260821.riemannHypothesis_of_P1`‡, `SemanticTransportClosure20260821.riemannHypothesis_of_P2`‡, `SemanticTransportClosure20260821.riemannHypothesis_of_P3`‡, `SemanticTransportClosure20260821.riemannHypothesis_of_partneredNaturality`‡, `riemannHypothesis_of_unifiedCommonE44ContactProducer`‡, `riemannHypothesis_of_noCertifiedMirrorOffSignature`‡, `riemannHypothesis_of_allConcreteRightHalfCountsZero`‡, `RiemannHypothesisProof.ZeroNonTrivialIsCentral_proved_of_samePassageComposition`‡, `RiemannHypothesisProof.RiemannHypothesis_proved_of_samePassageComposition`‡, `RiemannHypothesisProof.ZeroNonTrivialIsCentral_of_SamePassageGrammaticalRelationIsPreserved`‡, `RiemannHypothesisProof.RiemannHypothesis_of_SamePassageGrammaticalRelationIsPreserved`‡, `RiemannHypothesisProof.SamePassageGrammaticalRelationIsPreserved_of_RiemannHypothesis`, `RiemannHypothesisProof.SamePassageGrammaticalRelationIsPreserved_iff_RiemannHypothesis`‡
- **AJOUT** (1535 théorèmes sans Vi) : voir tables par module (colonne « Vi / AJOUT »).

## 2. Ajouts proposés

Vérités nouvelles, rédigées comme le maître les écrirait, avec les théorèmes du lot qui les établissent (statut = celui de la table par module ; les conditions sont dites dans la phrase).

1. L'objet de grammaire complet reconstruit depuis les zéros par le canal de Chebyshev/von Mangoldt (positions, écarts, transitions, motifs, familles, entrée et sortie, successions ordonnées de transitions, de motifs et de familles, densités) est égal, champ par champ et pour tout rang n et toute longueur k, à l'objet construit depuis l'histoire première ; les ensembles, les comptes, les listes ordonnées et l'infinité des apparitions d'un motif, d'une famille ou d'une succession coïncident (M^Z = M complet, inconditionnel). Cette hiérarchie (motifs, familles, méta-pattern), dite « descriptive et jamais portée » dans RHV6Fresh (V176, O13), est ici compilée dans une base séparée.
   - Théorèmes : `patternBlockOf_toShape`, `completeGrammarBlock_pattern_eq_canonical`, `completeGrammarBlock_transitions_eq_pattern_relation`, `completeGrammarBlock_shape_eq_pattern_shape`, `prime_completeGrammarBlock_entry_eq_blockEntryState`, `prime_completeGrammarBlock_exit_eq_blockExitState`, `zero_completeGrammarBlock_entry_eq_zeroReconstructedBlockEntryState`, `zero_completeGrammarBlock_exit_eq_zeroReconstructedBlockExitState`, `completeGrammarBlock_family_is_the_canonical_family`, `prime_completeGrammarBlock_globalDensity_eq_rank`, `prime_completeGrammarBlock_globalDensityTheta_eq_thetaM`, `zero_completeGrammarBlock_globalDensityTheta_eq_zeroReconstructedTheta`, `zero_completeGrammarBlock_eq_prime_completeGrammarBlock`, `zero_prime_positions_eq_all_positions`, `zero_prime_gaps_eq_all_positions`, `zero_prime_transitions_eq_all_positions`, `zero_prime_pattern_object_eq_all_positions_all_lengths`, `zero_prime_shape_eq_all_positions_all_lengths`, `zero_prime_family_eq_all_positions_all_lengths`, `zero_prime_entry_eq`, `zero_prime_exit_eq`, `zero_prime_transition_order_eq`, `zero_prime_pattern_order_eq`, `zero_prime_family_order_eq`, `zero_prime_global_density_eq`, `zero_prime_global_density_theta_eq`, `zero_prime_transitionSuccession_eq`, `zero_prime_familySuccession_eq`, `zero_prime_patternSuccession_eq`, `zero_prime_patternShape_eq`, `zero_prime_completeGrammar_positions_strictMono`, `zero_prime_block_positions_strictMono`, `zero_prime_complete_grammar_bridge`, `zero_prime_pattern_occurrence_set_eq`, `zero_prime_pattern_occurrence_iff`, `zero_prime_family_occurrence_set_eq`, `zero_prime_family_occurrence_iff`, `zero_prime_transition_occurrence_set_eq`, `zero_prime_grammar_occurrence_set_eq`, `zero_prime_pattern_occurrence_initial_segment_eq`, `zero_prime_pattern_occurrence_count_eq`, `zero_prime_pattern_occurrence_order_eq`, `zero_prime_family_occurrence_initial_segment_eq`, `zero_prime_family_occurrence_count_eq`, `zero_prime_family_occurrence_order_eq`, `zero_prime_entry_exit_eq_at_every_occurrence`, `zero_prime_pattern_infinite_occurrence_iff`, `zero_prime_family_infinite_occurrence_iff`, `zero_prime_grammar_infinite_occurrence_iff`, `zero_prime_finite_ordered_succession_eq`, `zero_prime_complete_grammar_occurrence_bridge`, `encodeZeroGrammar_canonical_eq_prime_grammar`, `capture_compatible_with_MZ_eq_M`, `capture_compatible_with_prime_determined_zero_grammar`, `ZeroPrimeGrammarCapture.zeroSide_eq`, `ZeroPrimeGrammarCapture.primeSide_eq`, `capture_encodes_canonical_prime_grammar`, `capture_preserves_member_order`, `capture_preserves_window`, `capture_preserves_transitions`, `capture_preserves_transition_succession`, `capture_preserves_patterns`, `capture_preserves_shape`, `capture_preserves_pattern_order`, `capture_preserves_families`, `capture_preserves_family_order`, `capture_preserves_entry`, `capture_preserves_exit`, `capture_preserves_positions`, `capture_preserves_gaps`, `capture_preserves_occurrences`, `zero_reconstructed_pattern_object_eq`, `zero_reconstructed_order_eq`, `zero_reconstructed_complete_metapattern_eq`
2. Toute construction déterministe d'un objet à partir des suites (comptage, positions, écarts) reconstruites depuis les zéros redonne la même valeur que depuis l'histoire première : la différence d'un zéro hors ligne ne peut passer par aucune telle construction (classificateurs de famille, de paires, d'ordre, de cycle).
   - Théorèmes : `zero_reconstructed_any_derived_object_eq`, `zero_reconstructed_any_count_position_gap_object_eq`, `zero_reconstructed_family_classifier_eq`, `zero_reconstructed_order_constructor_eq`, `zero_reconstructed_pair_classes_eq`, `zero_reconstructed_pair_classes_and_energy_eq`, `zero_reconstructed_cycle_relations_eq`, `zero_reconstructed_cycle_relation_prop_eq`
3. L'histoire première reconstruite depuis les zéros redonne exactement le comptage, les positions et les écarts (préfixes expérimentaux de 15 et 46 positions compris), avec inversion exacte du comptage et inversion de Möbius exacte du compte pondéré.
   - Théorèmes : `zero_reconstructed_first_fifteen_positions_eq_canonical`, `zero_reconstructed_experiment_positions_eq_canonical`, `zero_reconstructed_experiment_gaps_eq_canonical`, `zero_reconstructed_experiment_complete_grammar_eq`, `piCount_le_one`, `piReal_rpow_eq_zero_of_log_lt`, `PiWeighted_truncation_stable`, `rpow_one_div_mul`, `sum_divisors_moebius_eq_ite`, `pi_from_PiWeighted_moebius`, `piCount_p`, `piCount_lt_p`, `posOfCount_piCount_eq_p`, `reconstruction_positions_of_counting_eq`, `reconstruction_gaps_of_counting_eq`, `primes_determine_zeta_in_halfplane`, `zeros_weighted_count_eq_arithmetic_weighted_count`, `canonicalPiCutoff_eq_natLogFloor`, `canonicalPiCutoff_one_le`, `canonicalPiCutoff_mono`, `mem_canonicalPiCutoff_iff_pow_le`, `Icc_canonicalPiCutoff_subset`, `rpow_one_div_ge_two_of_mem_canonical_cutoff`, `canonicalPiCutoff_rpow_le`, `zerosWeightedCount_eq_PiWeighted_of_admissible_cutoff`, `zerosPrimeCountReal_eq_piReal`, `zeros_prime_count_eq_prime_count`, `zeros_prime_positions_eq_prime_positions`, `zeros_prime_gaps_eq_prime_gaps`, `psiRecoveredFromZeros_eq_psi`, `PiMangoldtFromZeros_eq_PiMangoldt`, `smoothed_formula_recovers_weighted_prime_count`, `RiemannHypothesisProof.ZerosReconstructWeightedPrimeCount`, `RiemannHypothesisProof.ZerosReconstructPrimeCount`, `RiemannHypothesisProof.ZerosReconstructPrimePositions`, `RiemannHypothesisProof.ZerosReconstructGapForPrime`, `RiemannHypothesisProof.ZerosReconstructWholePrimeGrammar`, `RiemannHypothesisProof.PrimeHistoryFromZerosEqualsPrimeHistory`
4. Un membre hors ligne force un écart de hauteur nul dans la constellation ordonnée (son miroir de même hauteur), alors que tout écart premier canonique est strictement positif ; tous les écarts capturés sont strictement positifs si et seulement si tous les membres de la constellation sont sur la ligne critique, et aucun encodeur de la grammaire des zéros vers la grammaire première ne transporte le défaut d'écart nul.
   - Théorèmes : `distinct_central_trueZeros_have_distinct_heights`, `ordered_central_pair_heightGap_pos`, `ordered_adjacent_zeroHeightGap_zero_forces_off`, `off_trueZero_gives_actual_ordered_zeroGap_constructive`, `off_mirror_zeroHeightGap_but_lossless_primeEdgeGap_nonzero`, `ScientificRebuild20260828.offLineForcesOrderedZeroGap`, `ScientificRebuild20260828.canonicalPrimeGapPositive`, `ScientificRebuild20260828.canonicalPrimeGapNonzero`, `ScientificRebuild20260829.trueOffMirror_forces_zero_constellation_gap`, `ScientificRebuild20260829.trueOffMirror_forces_zero_ordered_gap`, `ScientificRebuild20260829.trueOffQuartet_forces_zero_ordered_gap`, `gnat_pos`, `gnat_no_defect`, `canonical_prime_grammar_has_no_captured_zero_gap_defect`, `capture_prime_side_has_no_defect`, `intruder_gives_captured_zero_gap_defect`, `critical_line_gives_no_captured_zero_gap_defect`, `captured_gaps_pos_iff_critical_line`, `capture_defect_preservation_iff_critical_line`, `capture_prime_side_is_intruder_insensitive`, `no_encoder_transports_the_defect`, `defect_transporting_encoder_breaks_capture`, `RiemannHypothesisProof.PrimeGrammarGapIsStrictlyPositive`, `RiemannHypothesisProof.PrimeGrammarExcludesNullGap`, `RiemannHypothesisProof.PrimeGrammarBlockGapIsStrictlyPositive`, `RiemannHypothesisProof.DistinctPrimeHistoryPositionsHavePositiveSeparation`, `RiemannHypothesisProof.PrimeGrammarIsImmutableAndExcludesNullity`, `RiemannHypothesisProof.PrimeHistoryFromZerosInheritsStrictPositivity`
5. Les rigidités de retour connues (R1 à R11, retour grammatical fini, pivot, orientations opposées, support par étage, retour radial réciproque à tout étage) tiennent pour tout défaut radial, y compris hors ligne, et ne forcent pas la naturalité par renversement ; celle-ci équivaut exactement à β = 1/2 et échoue sur tout cas hors ligne (contre-modèle à d = 1).
   - Théorèmes : `SemanticTransportClosure20260821.actualGrammarReversalNaturality_iff_orientedEntries`, `SemanticTransportClosure20260821.actualGrammarReversalNaturality_iff_critical`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R12MatrixNaturality_iff_critical`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.not_R12MatrixNaturality_from_offLine`, `SemanticTransportClosure20260821.actualPartneredNaturality_iff_critical`, `SemanticTransportClosure20260821.actualPartneredNaturality_fails_offLine`, `SemanticTransportClosure20260821.knownReturnRigidities_hold`, `SemanticTransportClosure20260821.knownRigidities_admit_nonzero_defect`, `SemanticTransportClosure20260821.knownReturnRigidities_do_not_force_naturality`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11_holds`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R12Naturality_iff_critical`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.not_R12_from_offLine`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R1ThroughR11_and_not_R12MatrixNaturality`, `SemanticTransportClosure20260821.reflectionAccumulationRatio_two_eq_four_iff_critical`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.R12MatrixNaturality_iff_reflectionAccumulationRatio_baseIndependent`, `SemanticTransportClosure20260821.cumulativeKnownRigidity_holds`, `SemanticTransportClosure20260821.transformedReturnCase_natural_iff_defect_zero`, `SemanticTransportClosure20260821.cumulative_rigidities_admit_offline_case`, `SemanticTransportClosure20260821.cumulativeKnownRigidity_does_not_force_naturality`, `SemanticTransportClosure20260821.radial_returnProduct_eq_one`, `SemanticTransportClosure20260821.naturalUnderReversal_iff_entries_eq`, `SemanticTransportClosure20260821.radial_entries_eq_iff_defect_zero`, `SemanticTransportClosure20260821.radial_naturality_iff_defect_zero`, `SemanticTransportClosure20260821.return_does_not_force_naturality`, `SemanticTransportClosure20260821.stage_returnProduct_eq_one`, `SemanticTransportClosure20260821.stage_naturality_iff_defect_zero`
6. Aucune paire exacte de contacts E44 (à étage positif) ne décode à la fois un zéro hors ligne et son miroir de même hauteur ; deux contacts tangents communs à un zéro et à son miroir imposent β = 1/2 ; les centres des paires de contacts d'un membre et de son miroir diffèrent hors ligne.
   - Théorèmes : `ScientificRebuild20260901.ZeroGapConstraintCage.no_common_E44_contact`, `ScientificRebuild20260828.beta_eq_half_of_reflection_sameEvent_leftContact`, `ScientificRebuild20260828.beta_forced_half_of_same_reflected_contact_signature`, `ScientificRebuild20260829.trueContactCenter_eq_mirror_iff_critical`, `ScientificRebuild20260829.trueOffline_center_ne_mirror_center`, `false_of_common_E44_contact_on_unified_offline`, `e44_same_contacts_for_mirror_force_half`, `trueZero_same_E44_contacts_force_critical`, `trueOffline_no_common_E44_contact_pair`, `critical_of_independent_common_E44_contact`, `tangentContact_eq_mirror_iff_half`, `trueZeroTangentContact_eq_mirror_iff_critical`, `trueOffline_tangentContact_ne_mirror`, `UnifiedPositiveOfflineCase.no_common_E44_contact_pair`, `UnifiedPositiveOfflineCase.E44Attachment.criticalDefect_ne_zero`
7. Les zéros triviaux n'ont pas de géométrie de Tour : hauteur nulle, contact tangent dégénéré égal à 1, β récupéré nul différent de leur partie réelle, loi E44 corrigée non satisfaite aux étages positifs, caractère de Tour jamais unitaire ; la famille triviale est fixe, de multiplicité 1, et n'est jamais modifiée par un quartet non trivial.
   - Théorèmes : `ScientificRebuild20260828.TrivialZeroProfile.triviality`, `ScientificRebuild20260828.TrivialZeroProfile.beta_exact`, `ScientificRebuild20260828.TrivialZeroProfile.beta_negative`, `ScientificRebuild20260828.TrivialZeroProfile.gamma_zero`, `ScientificRebuild20260828.TrivialZeroProfile.multiplicity_one`, `ScientificRebuild20260828.TrivialZeroProfile.conjugation_fixed`, `ScientificRebuild20260828.TrivialZeroProfile.functional_reflection_not_zero`, `ScientificRebuild20260828.TrivialZeroProfile.completed_zeta_nonzero`, `ScientificRebuild20260828.TrivialZeroProfile.boundary_beta_recovery`, `ScientificRebuild20260828.TrivialZeroProfile.tower_nonunitary`, `ScientificRebuild20260828.trivialZero_complete_profile`, `ScientificRebuild20260828.trivialZero_re`, `ScientificRebuild20260828.trivialZero_im`, `ScientificRebuild20260828.trivialZero_re_lt_zero`, `ScientificRebuild20260828.trivialZero_isTrivial`, `ScientificRebuild20260828.trivialZero_notNontrivial`, `ScientificRebuild20260828.trivialZero_complete_foundation`, `ScientificRebuild20260828.trivialZero_conj_eq_self`, `ScientificRebuild20260828.trivialZero_functionalReflect_not_zetaZero`, `ScientificRebuild20260828.tangentContact_zeroHeight`, `ScientificRebuild20260828.tangentStageRight_zeroHeight`, `ScientificRebuild20260828.trivialZero_tangentContact_eq_one`, `ScientificRebuild20260828.trivialZero_tangentStageRight_eq_one`, `ScientificRebuild20260828.trivialZero_contactDelta_eq_zero`, `ScientificRebuild20260828.trivialZero_contactRecoveredGamma_eq_zero`, `ScientificRebuild20260828.trivialZero_contactRecoveredBeta_eq_zero`, `ScientificRebuild20260828.trivialZero_contactRecoveredBeta_ne_realPart`, `ScientificRebuild20260828.trivialZero_no_positiveStage_correctedE44`, `ScientificRebuild20260828.trivialZero_tower_not_unitary`, `ScientificRebuild20260828.zeroFamily_tool_separation`, `RiemannHypothesisProof.ZeroTrivialAtIndex_eq`, `RiemannHypothesisProof.ZeroTrivialMultiplicityIsOne`, `RiemannHypothesisProof.ZeroTrivialFamilyIsFixedUnitBackground`, `RiemannHypothesisProof.ZeroTrivialHasNoContactGeometry`, `RiemannHypothesisProof.ZeroTrivialMirrorStaysAtZeroHeight`, `RiemannHypothesisProof.FunctionalQuartetDoesNotModifyZeroTrivialFamily`, `RiemannHypothesisProof.EveryCompensatingZeroMustBelongToCompleteNonTrivialZeroSource`, `RiemannHypothesisProof.ZeroTrivialHasRealNegativeCoordinate`, `RiemannHypothesisProof.ZeroTrivialHasZeroGamma`, `RiemannHypothesisProof.ZeroTrivialIsFixedByConjugation`, `RiemannHypothesisProof.ZeroTrivialFamilyIsFixed`
8. La réalité analytique de zêta (ζ(conj s) = conj ζ(s) hors du pôle, par réflexion de Schwarz), la stabilité des zéros par conjugaison et la conservation exacte de la multiplicité analytique sous conjugaison et sous réflexion fonctionnelle (orbite de quatre zéros à multiplicités égales) sont des théorèmes sans RH.
   - Théorèmes : `natCast_arg_ne_pi`, `conj_natCast_cpow`, `conj_one_div_natCast_cpow`, `riemannZeta_conj_eq_of_one_lt_re`, `conj_ne_one_iff`, `differentiableAt_conjRiemannZetaConj`, `analyticOnNhd_conjRiemannZetaConj`, `riemannZeta_eq_conjRiemannZetaConj_of_one_lt_re`, `riemannZeta_eventuallyEq_conjRiemannZetaConj`, `riemannZeta_eq_conjRiemannZetaConj`, `riemannZeta_conj`, `riemannZeta_conj_eq_zero_of_zero`, `iteratedDeriv_conj_conj`, `analyticOrderNatAt_conjRiemannZetaConj_eq_riemannZeta_conj`, `analyticOrderNatAt_riemannZeta_eq_conjRiemannZetaConj`, `zetaZeroMultiplicity_conj`, `zetaConjugationReflectionOrbit_zero`, `zetaConjugationReflectionOrbit_multiplicity_eq`, `zetaReflect_deriv_ne_zero`, `analyticOrderAt_completedZeta_zetaReflect`, `zetaZeroMultiplicity_zetaReflect`, `RiemannHypothesisProof.zeta_conj_of_one_lt_re`, `RiemannHypothesisProof.riemannZeta_conj`, `RiemannHypothesisProof.tendsto_conj_nhds`, `RiemannHypothesisProof.analyticAt_conj_conj`, `RiemannHypothesisProof.analyticOrderAt_conj_conj`, `RiemannHypothesisProof.analyticOrderAt_zeta_conj`, `RiemannHypothesisProof.analyticOrderAt_zeta_one_sub`
9. Le canal des zéros, la fenêtre de constellation et le comptage par hauteur sont aveugles à la multiplicité et à l'adjonction d'un point de multiplicité nulle ; le canal et l'encodeur ne sont pas injectifs sur les sources ; une source normalisée est déterminée par sa multiplicité.
   - Théorèmes : `sourceZeroResidueTerm_eq_zero_of_mult_eq_zero`, `sourceZeroChannel_adjoin_null_member`, `adjoin_null_member_ne`, `encodeZeroGrammar_adjoin_null_member`, `sourceZeroChannel_not_injective`, `encodeZeroGrammar_not_injective`, `isNormalizedZeroSource_canonical`, `normalized_eq_of_mult_eq`, `adjoin_null_member_not_normalized`, `zeroHeightSet_ignores_mult`, `zeroOrderedMembers_ignores_mult`, `zeroConstellationWindow_blind_to_multiplicity`, `zeroConstellationWindowHeights_blind_to_multiplicity`, `zeroConstellationWindowGaps_blind_to_multiplicity`, `zeroCountUpTo_blind_to_multiplicity`, `isNormalizedZeroSource_double_mult`
10. ζ n'a aucun zéro réel dans le segment ouvert ]0,1[ (série êta appariée) ; un zéro non trivial est de partie réelle strictement entre 0 et 1 et de partie imaginaire non nulle.
   - Théorèmes : `dirichletEtaPairedTerm_pos`, `dirichletEtaPairedTerm_le`, `dirichletEtaPairedTerm_summable`, `dirichletEtaPaired_pos`, `dirichletEtaPairedTermC_le`, `dirichletEtaPairedTermC_summable`, `dirichletEtaPairedC_differentiableAt`, `dirichletEtaPairedC_eq_of_one_lt_re`, `dirichletEtaPairedC_eq_of_mem_Ioo`, `dirichletEtaPairedC_ofReal`, `riemannZeta_real_neg_Ioo_zero_one`, `riemannZeta_real_ne_zero_Ioo_zero_one`, `riemannZeta_real_ne_zero_of_not_trivial_nonpos`, `nontrivial_zeta_zero_im_ne_zero`, `int_one_le_of_real_le_neg_one`, `isTrivialZetaZero_of_real_cos_eq_zero`, `riemannZeta_ne_zero_of_real_nontrivial_left`, `isNontrivialZetaZero_re_mem_Ioo`, `RiemannHypothesisProof.re_lt_one_of_zeta_eq_zero`, `RiemannHypothesisProof.ZeroTrivial_of_riemannZeta_eq_zero_of_re_nonpos`, `RiemannHypothesisProof.inStrip_of_mathlib`, `RiemannHypothesisProof.ZeroNonTrivial_of_riemannZeta_eq_zero`, `RiemannHypothesisProof.four_le_one_div_add_one_div_one_sub`, `RiemannHypothesisProof.noRealZetaZeroInOpenUnitSegment_of_completedZeta₀_norm_lt_four`, `RiemannHypothesisProof.noRealZetaZeroInOpenUnitSegment`
11. Le résidu de l'intégrande de Perron en un zéro de zêta est −m(ρ)·K_x(ρ) (m = multiplicité) ; −ζ'/ζ a un pôle exactement simple en chaque zéro et en 1 (résidus −m(ρ) et +1) ; la somme lissée de von Mangoldt admet la formule explicite avec séries de zéros triviaux et non triviaux ; la série des zéros se scinde de façon exacte et inconditionnelle en une sélection finie de zéros (orbite d'une paire, quartet) et un reste : la formule ne contraint que la somme, l'isolement d'un terme n'est pas borné.
   - Théorèmes : `ScientificRebuild20260829.selection_rest_tsum_decomposition`, `ScientificRebuild20260829.offlineOrbit_tsum_decomposition_is_selection_instance`, `ScientificRebuild20260829.selection_Pi_rest_decomposition`, `ScientificRebuild20260829.selection_primitive_rest_decomposition`, `ScientificRebuild20260829.selection_psi_rest_decomposition`, `ScientificRebuild20260829.selection_weighted_count_rest_decomposition`, `ScientificRebuild20260829.selection_prime_count_rest_decomposition`, `ScientificRebuild20260829.seamPairPrimitivePart_reads_both_members`, `ScientificRebuild20260829.seam_psi_rest_decomposition`, `ScientificRebuild20260829.seam_weighted_count_rest_decomposition`, `ScientificRebuild20260829.seam_prime_count_rest_decomposition`, `TrueZeroQuartet.nontrivialZeroChannel_eq_quartet_add_rest`, `TrueZeroQuartet.smoothedVonMangoldtSum_eq_fixed_add_trivial_add_quartet_add_rest`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_smoothedVonMangoldt_quartet_decomposition`, `negLogDeriv_riemannZeta_eq_LSeries_vonMangoldt`, `tendsto_mul_logDeriv_riemannZeta_zero`, `tendsto_mul_neg_logDeriv_riemannZeta_zero`, `tendsto_mul_logDeriv_riemannZeta_pole`, `tendsto_mul_neg_logDeriv_riemannZeta_pole`, `zetaPerron_residue_at_zeta_zero`, `zetaPerron_trivial_zero_residue_sum`, `zetaPerron_nontrivial_zero_residue_sum`, `neg_logDeriv_riemannZeta_sub_principal_zero_isBigO`, `meromorphicOrderAt_neg_logDeriv_riemannZeta_zero`, `meromorphicOrderAt_neg_logDeriv_riemannZeta_pole`, `residue_neg_logDeriv_riemannZeta_zero`, `residue_neg_logDeriv_riemannZeta_pole`, `residue_perronZetaIntegrand_zero`, `smoothed_riemann_explicit_formula`
12. Chacune des prémisses suivantes est équivalente à RH, donc aucune ne décharge une partie de RH : FINAL_SEMANTIC_LOCK (retour du membre par réflexion), la loi de grammaire fibrée FiberedMZEqM, le producteur d'extrémités de premier retour, la fidélité P0/P1/P2/P3, la coïncidence de branche miroir universelle, la naturalité partenariée, le producteur R12 maître, le producteur de contact E44 commun, la loi « contraintes connues ⟹ R12 », la double localisation universelle du quartet hors ligne, l'égalité de Laurent à deux bases, la signature OFF certifiée exclue, les comptes concrets de moitié droite nuls, le certificat de décroissance de moitié droite, et la composition même-passage de la bibliothèque `RiemannHypothesisProof`.
   - Théorèmes : `separation_32_cannot_produce_33`, `unconditional_law_produces_field33_iff_rh`, `Q1_is_generic_control`, `Q5_two_orientation_compatibility_iff_rh`, `twoBaseReflectedLaurentEquality_iff_rh`, `ScientificRebuild20260901.fullQuartetOffDoubleTransitionLocalization_iff_riemannHypothesis`, `ScientificRebuild20260828.FINAL_SEMANTIC_LOCK_iff_riemannHypothesis`, `ScientificRebuild20260828.finalSemanticLockIsTerminalStrength`, `ScientificRebuild20260829.routeA_universal_fiberedMZEqM_iff_RH`, `ScientificRebuild20260829.routeD_universal_memberReturn_iff_RH`, `ScientificRebuild20260829.routeD_endpointAssemblyProducer_iff_RH`, `ScientificRebuild20260829.fiberedMZEqM_iff_riemannHypothesis`, `ScientificRebuild20260829.terminalSocket_is_rh_strength`, `universal_mirrorBranchCoincidence_iff_rh`, `terminalImplicationForceAccounting`, `SemanticTransportClosure20260821.masterR12Producer_iff_riemannHypothesis`, `SemanticTransportClosure20260821.r1ThroughR11ProducesR12_iff_riemannHypothesis`, `SemanticTransportClosure20260821.firstReturnEndpointAssemblyProducer_iff_riemannHypothesis`, `SemanticTransportClosure20260821.P0_iff_riemannHypothesis`, `SemanticTransportClosure20260821.P1_iff_riemannHypothesis`, `SemanticTransportClosure20260821.P2_iff_riemannHypothesis`, `SemanticTransportClosure20260821.P3_iff_riemannHypothesis`, `SemanticTransportClosure20260821.partneredNaturality_iff_riemannHypothesis`, `unifiedCommonE44ContactProducer_iff_riemannHypothesis`, `unifiedKnownConstraintsProduceR12_iff_riemannHypothesis`, `noCertifiedMirrorOffSignature_iff_riemannHypothesis`, `allConcreteRightHalfCountsZero_iff_riemannHypothesis`, `eventuallyConcreteRightHalfCountSubunit_iff_riemannHypothesis`, `strictRightDecayCertificate_iff_riemannHypothesis`, `rawRightHalfContourDecayCertificate_iff_riemannHypothesis`, `RiemannHypothesisProof.SamePassageGrammaticalRelationIsPreserved_iff_RiemannHypothesis`
13. Les théorèmes qui concluent False (ou une négation) sur un contexte hors ligne (nullité fidèle, R12, contacts E44 communs, P0 à P3, égalité des membres aux extrémités, placement déterminé par la hauteur avec inverse, retour du membre par réflexion) réfutent la propriété correspondante dans ce contexte, sans réfuter RH : ils disent seulement que la propriété universelle ne tient que s'il n'existe aucun contexte hors ligne.
   - Théorèmes : `ScientificRebuild20260901.false_of_upper_double_transition_localization`, `ScientificRebuild20260828.FullyAligned.contradiction_of_FINAL_SEMANTIC_LOCK`, `ScientificRebuild20260828.EventContext.offMemberReflectionDoesNotReturn`, `ScientificRebuild20260828.trueOffLine_memberReflection_doesNotReturn`, `ScientificRebuild20260828.offLine_refutes_unjustified_memberReturnLock`, `ScientificRebuild20260828.no_sameEventPivotContactLocalization_of_off`, `ScientificRebuild20260829.FiberedMirrorGapEntry.false_of_fiberedGapNullityFidelity`, `ScientificRebuild20260829.FiberedMirrorGapEntry.routeA_nullityFidelity_contradiction`, `ScientificRebuild20260829.FiberedMirrorGapEntry.routeC_no_heightDetermined_leftInverse`, `ScientificRebuild20260829.FiberedMirrorGapEntry.routeD_localMemberReturn_refuted`, `ScientificRebuild20260829.fiberedGapNullityFidelity_iff_false`, `mirrorBranchCoincidence_fails_in_offLine_case`, `MirrorPairOrderedTroublePrimeCase.terminalMirrorBranchCoincidence_fails`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.not_R12MatrixNaturality_from_offLine`, `SemanticTransportClosure20260821.actualPartneredNaturality_fails_offLine`, `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.not_internalNaturality`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.not_internalNaturality`, `SemanticTransportClosure20260821.knownReturnRigidities_do_not_force_naturality`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.not_R12_from_offLine`, `SemanticTransportClosure20260821.MasterOffLineSemanticCase.contradiction_of_R12MatrixNaturality`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.not_firstReturnEndpointMemberEquality`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.contradiction_of_P0`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.contradiction_of_P1`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.contradiction_of_P2`, `SemanticTransportClosure20260821.FullyAlignedSameEventContext.contradiction_of_P3`, `SemanticTransportClosure20260821.cumulativeKnownRigidity_does_not_force_naturality`, `false_of_common_E44_contact_on_unified_offline`, `trueOffline_no_common_E44_contact_pair`, `UnifiedPositiveOfflineCase.not_R12`, `UnifiedPositiveOfflineCase.no_common_E44_contact_pair`, `UnifiedPositiveOfflineCase.no_heightDetermined_leftInverse`, `false_of_independent_R12`, `no_encoder_transports_the_defect`, `defect_transporting_encoder_breaks_capture`, `RiemannHypothesisProof.NonCentralFunctionalMirrorCannotShareSameContacts`, `RiemannHypothesisProof.False_of_SamePassageNullityFidelity`
14. Le premier central d'un événement premier (départ à deux transitions) est l'unique premier entre les bords de la fenêtre ; il identifie l'événement de façon injective ; la paire de contacts vrais d'un zéro a un centre strictement entre les contacts, qui pointe un premier canonique seulement sous la prémisse nommée « le centre atteint un premier canonique » (`TrueContactCenterHitsCanonicalPrime`, le théorème manquant).
   - Théorèmes : `ScientificRebuild20260829.canonicalEventAxisPrime_eq`, `ScientificRebuild20260829.canonicalEventAxisPrime_isPrime`, `ScientificRebuild20260829.canonicalEventAxis_rigid`, `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.axis_eq_tourPivotPrime`, `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.vonMangoldt_axis_position_lock`, `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.vonMangoldt_axis_gap_lock`, `ScientificRebuild20260829.TrueContactCanonicalAxisPrimeEventCell.canonical_axis_gap_pos`, `ScientificRebuild20260829.trueContactCenter_congr`, `ScientificRebuild20260829.trueContactCenter_eq_contact_mul_stageFactor`, `ScientificRebuild20260829.trueContactCenter_pos`, `ScientificRebuild20260829.contact_lt_stageRight`, `ScientificRebuild20260829.trueContactCenter_strictly_between`, `ScientificRebuild20260829.trueContactCenter_eq_mirror_iff_critical`, `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.center_eq_prime`, `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.primeIndex_unique`, `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.event_prime_isPrime`, `ScientificRebuild20260829.TrueContactCenterPrimeEventCell.event_prime_strictly_inside`, `ScientificRebuild20260829.trueContactCenterPrimeEventCell_of_hit`, `ScientificRebuild20260829.trueEventSingletonPassageRaccord_of_hit`, `LocalizedMirrorPairPrimeWeldCase.assemblyPivot_unique`, `LocalizedMirrorPairPrimeWeldCase.PairAssemblyWindowCoverage.pivotUnique`, `RiemannHypothesisProof.CanonicalPrimeEvent.centerPrime_ofTwoTransitionStart`, `RiemannHypothesisProof.CanonicalPrimeEvent.centerPrime_isPrime`, `RiemannHypothesisProof.CanonicalPrimeEvent.eq_of_centerPrime_eq`, `RiemannHypothesisProof.CanonicalPrimeEvent.same_centerPrime_rigidifies_environment`, `RiemannHypothesisProof.TwoTransitionPrimeBlockHasUniqueCentralPrime`, `RiemannHypothesisProof.SameCentralPrimeDeterminesSamePrimeEvent`, `RiemannHypothesisProof.SameCentralPrimeDeterminesSamePrimeEnvironment`
15. Dans une fenêtre bornée, le degré concret de moitié droite (nombre de zéros non triviaux hors ligne côté droit) vaut le compteur analytique N'(1/2,T), est monotone, est nul si et seulement si tout zéro non trivial de hauteur < T est critique, et une borne brute décroissante de ce compte entraîne sa nullité à toute hauteur (équivalent à RH).
   - Théorèmes : `concreteRightHalfDegree_cast_eq_nprime`, `concreteRightHalfDegree_mono`, `concreteRightHalfDegree_eq_neg_rectangle_re`, `concreteRightHalfDegree_eq_zero_iff_bounded_critical_line`, `concreteRightHalfDegree_all_zero_of_eventually_zero`, `concreteRightHalfDegree_all_zero_of_decay_bound`, `positive_height_nontrivial_critical_of_concrete_decay_bound`, `positive_height_nontrivial_critical_of_primeDensity_raw_bound`, `allConcreteRightHalfCountsZero_of_eventually_subunit`, `allConcreteRightHalfCountsZero_of_decayCertificate`, `bounded_critical_line_gives_global`, `capture_defect_preservation_everywhere_gives_rh`

## 3. Cascades

Théorèmes les plus utilisés du lot (dépendances inverses sur tout `rh_gap_criterion.jsonl`, `deps_project`). « Conséquences » = théorèmes dont la preuve utilise le théorème ; l'énoncé d'un dépendant n'est donné que s'il appartient à ce lot.

- **`isNontrivialZetaZero_re_mem_Ioo`** (`ZetaZeroHeightTruncation`) — Cette vérité est confirmée : Tout zéro non trivial local est dans la bande critique ouverte 0 < β < 1. [CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé)] et provoque la série de conséquences suivantes (62 théorèmes) : `projectNontrivialZero_to_trusted` (module `Audit.TrustedNativeBridge`, hors lot) ; `isNontrivialZetaZero_one_sub` (module `LiZeroSideAmplification`, hors lot) ; `nontrivialZetaZero_ne_one` (module `LiZeroSideAmplification`, hors lot) ; `nontrivialZetaZero_ne_zero` (module `LiZeroSideAmplification`, hors lot) ; `offline_orbit_internal_defect_ge_two` (module `Round26ARRelationalRigidityRecovery`, hors lot) ; `offline_orbit_internal_defect_cofinal` (module `Round26ATCompiledTerminalJunctionAudit`, hors lot) ; `exists_strictMonoOn_reflectedNormSqProfile` (module `Round26AVReflectedDifferenceClosedForm`, hors lot) ; `nontrivialZero_add_one_ne_zero` (module `Round26AVReflectedDifferenceClosedForm`, hors lot) ; `nontrivialZero_ne_zero` (module `Round26AVReflectedDifferenceClosedForm`, hors lot) ; `complexPsiDisturbance_exists` (module `Round26AWMultiLevelDisturbanceLadder`, hors lot) ; et 52 autres.
- **`zero_reconstructed_any_derived_object_eq`** (`ZeroReconstructedMetaPattern`) — Cette vérité est confirmée : Transport universel : toute construction déterministe F des deux suites (positions, écarts) donne la même valeur sur les suites reconstruites et sur (p, gnat). [CONFIRMÉE] et provoque la série de conséquences suivantes (26 théorèmes) : `zero_reconstructed_diagonal_increment_mass_eq` (module `Round26AGSignedCrossDecomposition`, hors lot) ; `zero_reconstructed_signed_correlation_eq` (module `Round26AGSignedCrossDecomposition`, hors lot) ; `offline_member_leaves_reconstructed_grammar_unchanged` (module `Round26B4ConstellationGapElementLocalisation`, hors lot) ; `derived_object_invariant_under_any_zero_hypothesis` (module `Round26B4GrammaticalInsensitivityClosure`, hors lot) ; `lock_two_grammatical_route_closed_negatively` (module `Round26B4GrammaticalInsensitivityClosure`, hors lot) ; `offline_difference_stays_outside_the_grammar` (module `Round26B4GrammaticalInsensitivityClosure`, hors lot) ; `zero_reconstructed_grammatical_property_iff` (module `Round26B4GrammaticalInsensitivityClosure`, hors lot) ; `zero_reconstructed_innovationJ_eq` (module `Round26M56ZeroMetaPatternScaleRigidity`, hors lot) ; `zero_reconstructed_normalized_innovation_window_energy_eq` (module `Round26M56ZeroMetaPatternScaleRigidity`, hors lot) ; `zero_reconstructed_scale_block_pair_energy_eq_canonical` (module `Round26M57ScaleInjectionEnergy`, hors lot) ; et 16 autres.
- **`nontrivial_zeta_zero_im_ne_zero`** (`ZetaRealAxisNonvanishing`) — Cette vérité est confirmée : Un zéro non trivial a une partie imaginaire non nulle (V7 exige γ > 0 pour les membres ; ici seulement γ ≠ 0). [CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé)] et provoque la série de conséquences suivantes (26 théorèmes) : `offline_zero_orbit_mode_eq_orbit_finset_sum` (module `OfflineZeroOrbitDecomposition`, hors lot) ; `nontrivialZero_ne_conj` (module `Round26AXPsiConjugationRigidity`, hors lot) ; `conjugateMate_ne_self` (module `Round26B4OrderedConstellationView`, hors lot) ; `heightConstellation_eq_pos_union_neg` (module `Round26B4OrderedConstellationView`, hors lot) ; `heightConstellation_mem_ordered_or_conjugate` (module `Round26B4OrderedConstellationView`, hors lot) ; `grammarZeroModeEnergy_cannot_separate_conjugate_zeros` (module `Round26B4VoiceIdentityAnchor`, hors lot) ; `im_reflectedPoleProduct_ne_zero` (module `Round26BGCorrectivePhaseCandidate`, hors lot) ; `zeroRow_contactRatio_eq_one_iff_critical_line` (module `Round26CXTowerCarrierBridge`, hors lot) ; `ScientificRebuild20260828.trueZero_beta_from_height_and_leftContact` (β est fixé exactement par la hauteur et le contact gauche : β = γ / tan(γ·log contact).) ; `ScientificRebuild20260828.trueZero_contactWidth_from_height` (La hauteur fixe la largeur logarithmique de la cellule de contact vraie : e44Delta = mπ/γ.) ; et 16 autres.
- **`zeros_prime_positions_eq_prime_positions`** (`ZeroPrimeTerminalReconstruction`) — Cette vérité est confirmée : La position première reconstruite égale p n. [CONFIRMÉE] et provoque la série de conséquences suivantes (23 théorèmes) : `e44_certified_prime_position` (module `E44VonMangoldtGrammarBridge`, hors lot) ; `InverseSignatureConcrete.exact_meta_reconstruction_identity` (module `InverseSignatureConcrete`, hors lot) ; `round23_zero_prime_gap_reconstruction` (module `Round23TerminalClosure`, hors lot) ; `zeroReconstructedCorrectedTAtPrime_eq_correctedTAtPrime` (module `Round25G2CCorrectedTEmbedding`, hors lot) ; `zeroReconstructedTChebyshevBoundaryCorrection_eq` (module `Round25G2CCorrectedTEmbedding`, hors lot) ; `zeroReconstructedRelationOf_eq` (module `Round25G2CGrammarBridge`, hors lot) ; `zeroReconstructed_blockEntryState_eq` (module `Round26B4GrammaticalInsensitivityClosure`, hors lot) ; `zeroReconstructed_blockExitState_eq` (module `Round26B4GrammaticalInsensitivityClosure`, hors lot) ; `ScientificRebuild20260828.localVonMangoldtForcesExactPrimeEndpoints` (Les deux positions premières reconstruites sont exactement les premiers consécutifs canoniques.) ; `ScientificRebuild20260828.vonMangoldt_prime_position_lock` (La position première reconstruite au rang n est p n.) ; et 13 autres.
- **`zeros_prime_gaps_eq_prime_gaps`** (`ZeroPrimeTerminalReconstruction`) — Cette vérité est confirmée : L'écart premier reconstruit égale gnat n. [CONFIRMÉE] et provoque la série de conséquences suivantes (23 théorèmes) : `e44_certified_prime_gap` (module `E44VonMangoldtGrammarBridge`, hors lot) ; `InverseSignatureConcrete.exact_meta_reconstruction_identity` (module `InverseSignatureConcrete`, hors lot) ; `round23_zero_prime_gap_reconstruction` (module `Round23TerminalClosure`, hors lot) ; `decoder_prime_gaps_are_canonical` (module `Round26B4CollectiveDecoderAbsorptionAudit`, hors lot) ; `zeroReconstructed_changeCount_eq` (module `Round26B4GrammaticalInsensitivityClosure`, hors lot) ; `zeroReconstructed_change_skeleton_alternates` (module `Round26B4GrammaticalInsensitivityClosure`, hors lot) ; `ScientificRebuild20260828.localVonMangoldtForcesExactPrimeGap` (Champ/état de bord d'objet réel : la reconstruction depuis les zéros redonne l'écart premier consécutif exact.) ; `ScientificRebuild20260828.vonMangoldt_prime_gap_lock` (L'écart premier reconstruit au rang n est gnat n.) ; `ScientificRebuild20260829.encodedPrimeGapOfPassage_eq_gnat` (Le même écart premier est gnat au rang premier sélectionné par le raccord.) ; `ScientificRebuild20260829.selectedEncZCell_eq_gnat` (EncZ = M sur la cellule sélectionnée : la cellule reconstruite est l'écart premier canonique gnat.) ; et 13 autres.
- **`zetaZeroMultiplicity_pos`** (`ZetaZeroMultiplicity`) — Cette vérité est confirmée : Chaque zéro de ζ a une multiplicité strictement positive. [CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé)] et provoque la série de conséquences suivantes (23 théorèmes) : `offline_zero_mode_amplitude_ne_zero` (module `OfflineZeroIncompatibility`, hors lot) ; `offline_zero_orbit_contribution` (module `OfflineZeroIncompatibility`, hors lot) ; `psi_mellin_subexponential_excludes_right_nontrivial_zeros` (module `Round25M53MellinZetaIdentity`, hors lot) ; `reflectedRowCoeff_ne_zero` (module `Round26AVReflectedDifferenceClosedForm`, hors lot) ; `canonicalScaleFourThetaZeroAmplitude_ne_zero` (module `Round26B4GrammarSpectralSectors`, hors lot) ; `explicitNonzeroScaleFourResidue_ne_zero` (module `Round26B4GrammarSpectralSectors`, hors lot) ; `nontrivialZeroResidueTerm_ne_zero` (module `Round26B4RealBlockVoiceExhibition`, hors lot) ; `im_reflectedPhaseProduct_ne_zero` (module `Round26BGCorrectivePhaseCandidate`, hors lot) ; `logDerivBoundedNear_forces_ne_zero` (module `Round26DVChebyshevPoleObstruction`, hors lot) ; `residueBelowOne_forces_ne_zero` (module `Round26DWResidueThresholdBridge`, hors lot) ; et 13 autres.
- **`isNontrivialZetaZero_conj_iff`** (`ZetaPerronFiniteResidues`) — Cette vérité est confirmée : Le conjugué d'un zéro non trivial est un zéro non trivial ⟺ ρ l'est. [CONFIRMÉE] et provoque la série de conséquences suivantes (21 théorèmes) : `isNontrivialZetaZero_one_sub` (module `LiZeroSideAmplification`, hors lot) ; `offlineOrbitMode_eq_offlineOrbitModeFromP5` (module `OfflineOrbitModeTraceability`, hors lot) ; `offline_zero_orbit_contribution` (module `OfflineZeroIncompatibility`, hors lot) ; `offlineOrbitEnergy_eq_weighted_P5_projection_energy` (module `OfflineZeroOrbitDecomposition`, hors lot) ; `offlineZeroOrbitFinset_sum_of_im_ne_zero` (module `OfflineZeroOrbitDecomposition`, hors lot) ; `offline_zero_channel_orbit_rest_expansion_of_im_ne_zero` (module `OfflineZeroOrbitDecomposition`, hors lot) ; `offline_zero_orbit_mode_eq_orbit_finset_sum_of_im_ne_zero` (module `OfflineZeroOrbitDecomposition`, hors lot) ; `isNontrivialZetaZero_reflectConj` (module `Round26B4ConstellationGapPattern`, hors lot) ; `collective_projection_conj_invariant` (module `Round26B4ConstellationRefinementTable`, hors lot) ; `conjugate_rows_distinct` (module `Round26B4ConstellationRefinementTable`, hors lot) ; et 11 autres.
- **`zero_completeGrammarBlock_eq_prime_completeGrammarBlock`** (`ZeroPrimeCompleteGrammarBridge`) — Cette vérité est confirmée : Théorème central : l'objet de grammaire complet construit depuis les suites reconstruites des zéros égale celui construit depuis l'histoire première (M^Z = M complet, tous n, k). [CONFIRMÉE] et provoque la série de conséquences suivantes (20 théorèmes) : `zero_completeGrammarBlock_rigid` (module `Round26ANGrammarRigidityRestoration`, hors lot) ; `relational_rigidity_recovery` (module `Round26ARRelationalRigidityRecovery`, hors lot) ; `offline_member_leaves_complete_grammar_unchanged` (module `Round26B4CompleteGrammarOfflineBlindness`, hors lot) ; `ScientificRebuild20260828.vonMangoldt_grammar_lock` (Verrou de grammaire : la grammaire reconstruite via zéros/von Mangoldt égale la grammaire première canonique.) ; `zero_prime_complete_grammar_bridge` (Paquet terminal (Tour 10S) : conjonction du théorème central, des égalités champ par champ (positions, écarts, transitio) ; `zero_prime_entry_eq` (L'entrée de bord reconstruite égale la première.) ; `zero_prime_exit_eq` (La sortie de bord reconstruite égale la première.) ; `zero_prime_family_eq_all_positions_all_lengths` (La famille reconstruite égale la famille première.) ; `zero_prime_family_order_eq` (La succession ordonnée des familles reconstruite égale la première.) ; `zero_prime_gaps_eq_all_positions` (Les écarts coïncident.) ; et 10 autres.
- **`gnat_pos`** (`ZeroPrimeIntruderExclusion`) — Cette vérité est confirmée : Tout écart entre deux premiers consécutifs est strictement positif. [CONFIRMÉE] et provoque la série de conséquences suivantes (18 théorèmes) : `ScientificRebuild20260901.tripleTransitionRigidity` (Constructeur universel : le paquet de rigidité de triplet de transitions existe pour tous T0,T1,T2,n.) ; `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.contact_interval_three_prime_certificate` (Certificat compact : adresse issue du compte gauche, comptage local 3, pivot premier, deux écarts positifs, deux occurre) ; `ScientificRebuild20260901.ContactAlgebraicThreePrimeInterval.two_gaps_positive` (Champ : les deux écarts entrant et sortant sont strictement positifs.) ; `ScientificRebuild20260828.localForcedPrimeGapPositive` (L'écart premier forcé est strictement positif.) ; `ScientificRebuild20260828.RealObjectBoundaryState.hasZeroGapAndPositivePrimeGap` (Un état de bord contient à la fois l'écart nul côté zéros et un écart premier canonique positif.) ; `ScientificRebuild20260828.canonicalPrimeGapPositive` (Tout écart premier consécutif canonique est strictement positif.) ; `ScientificRebuild20260828.weldedCasePrimeGapPositive` (Sur la colonne première sélectionnée d'un cas soudé, l'écart premier canonique est strictement positif.) ; `ScientificRebuild20260829.FiberedMirrorGapEntry.canonicalPrimeGapPositive` (L'écart premier canonique à l'entrée est strictement positif.) ; `ScientificRebuild20260829.preOff_twoChannel_zeroPrimeGap_rigidity` (Pré-OFF : pour deux vrais zéros distincts, l'arête première est > 0, de largeur log > 0, et l'écart transformé est non n) ; `ScientificRebuild20260829.preOff_zeroPrimeEdge_rigidity` (Certificat de rigidité pré-OFF : écart reconstruit exact, positif, et signature de voix distincte pour deux zéros distin) ; et 8 autres.
- **`riemannZeta_analyticOrderAt_ne_top`** (`ZetaZeroMultiplicity`) — Cette vérité est confirmée : L'ordre analytique de ζ en un zéro est fini. [CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé)] et provoque la série de conséquences suivantes (16 théorèmes) : `Kadiri.riemannZeta_eventually_ne_zero_punctured_nontrivialZero` (module `P4Port.IEANTN.KadiriZeroCounting`, hors lot) ; `Kadiri.riemannZeta_eventually_ne_zero_punctured_positiveHeightZero` (module `P4Port.IEANTN.KadiriZeroCounting`, hors lot) ; `Kadiri.riemannZeta_meromorphicOrderAt_ne_top_nontrivialZero` (module `P4Port.IEANTN.KadiriZeroCounting`, hors lot) ; `Kadiri.riemannZeta_meromorphicOrderAt_ne_top_positiveHeightZero` (module `P4Port.IEANTN.KadiriZeroCounting`, hors lot) ; `Kadiri.riemannZeta_order_conj` (module `P4Port.IEANTN.KadiriZeroCounting`, hors lot) ; `psi_mellin_subexponential_excludes_right_nontrivial_zeros` (module `Round25M53MellinZetaIdentity`, hors lot) ; `meromorphicOrderAt_neg_logDeriv_zeta_mul_eq_neg_one` (module `Round26DKCombinedChannelNoCancellation`, hors lot) ; `existsUnique_zetaLogDerivRegularDatum` (module `Round26FNPrimeChannelRegularPart`, hors lot) ; `eventually_riemannZeta_ne_zero_punctured` (module `Round26FORegularPartReflection`, hors lot) ; `analyticAt_zetaLogDerivRegularized` (module `Round26FPRegularPartFirstJet`, hors lot) ; et 6 autres.
- **`zetaZero_ne_one`** (`ZetaZeroMultiplicity`) — Cette vérité est confirmée : Un zéro de ζ n'est pas le pôle 1. [CONFIRMÉE (domaine : hypothèses analytiques ou numériques de l'énoncé)] et provoque la série de conséquences suivantes (15 théorèmes) : `residue_scaleFourThetaMellinContinuation_of_boundary_vanishing` (module `Round26B4GrammarSpectralClosure`, hors lot) ; `zetaLogDerivRegularDatum_conj` (module `Round26FORegularPartReflection`, hors lot) ; `isNontrivialZetaZero_zetaReflect` (module `Round26Round27RHClosure`, hors lot) ; `analyticOrderNatAt_conjRiemannZetaConj_eq_riemannZeta_conj` (L'ordre analytique de conj ∘ ζ ∘ conj en ρ égale celui de ζ en conj ρ.) ; `riemannZeta_conj_eq_zero_of_zero` (Si ρ est un zéro de ζ, conj ρ en est un aussi : les zéros sont stables par conjugaison (hypothèse : ρ zéro).) ; `zetaZeroMultiplicity_conj` (Conservation exacte de la multiplicité analytique sous conjugaison : m(ρ̄) = m(ρ) pour tout zéro ρ de ζ.) ; `riemannZeta_zetaReflect_eq_zero` (La formule fonctionnelle transporte tout zéro de partie réelle positive vers le zéro réfléchi 1−ρ.) ; `isNontrivialZetaZero_conj_iff` (Le conjugué d'un zéro non trivial est un zéro non trivial ⟺ ρ l'est.) ; `isTrivialZetaZero_ne_one` (Un zéro trivial n'est pas 1.) ; `zetaPerron_special_disjoint_trivial` (Points spéciaux et zéros triviaux du rectangle sont disjoints.) ; et 5 autres.
- **`SemanticTransportClosure20260821.CompleteOfflineDiscoveryBundle.offLine`** (`SemanticTransportClosure20260821.CompleteDiscoverySemanticSpine`) — Cette vérité est confirmée : Champ : le zéro est hors ligne. [CONFIRMÉE] et provoque la série de conséquences suivantes (14 théorèmes) : `ScientificRebuild20260828.EventContext.offLine` (Champ d'EventContext : ce zéro est hors ligne (β ≠ 1/2), propriété du même zéro.) ; `ScientificRebuild20260829.riemannHypothesis_of_fiberedMZEqM` (FiberedMZEqM ⟹ RiemannHypothesis (conséquence de la loi littérale du maître sémantique de l'époque).) ; `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.not_internalNaturality` (Hors ligne, la naturalité interne correctement typée est fausse sur le même bloc sélectionné.) ; `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.sameBlockLiftDoesNotReturn` (Le même retour grammatical n'efface pas la déformation radiale hors ligne (norme fin ≠ norme début).) ; `SemanticTransportClosure20260821.ExhaustiveSameObjectOfflineContext.trueZero_and_offLine` (Le paquet exhaustif concerne un vrai zéro non trivial hors ligne unique.) ; `SemanticTransportClosure20260821.exhaustiveSameObjectOfflineContext_exists` (Tout vrai zéro positif hors ligne engendre le contexte exhaustif même-objet avec les seules conséquences déjà prouvées.) ; `SemanticTransportClosure20260821.FullyAlignedSameEventContext.sameZero_offLine_contact_ne_mirror` (Sur le même membre hors ligne et son miroir de même hauteur, les contacts tangents au même indice diffèrent.) ; `SemanticTransportClosure20260821.FullyAlignedSameEventContext.identifiedRadialContribution_pos` (Le terme borne inférieure est strictement positif sous la seule hypothèse hors ligne.) ; `SemanticTransportClosure20260821.FullyAlignedSameEventContext.radialDefect_ne_zero` (Le défaut radial β−1/2 du zéro d'un contexte pleinement aligné (hors ligne) est non nul.) ; `SemanticTransportClosure20260821.FullyAlignedSameEventContext.identifiedRightHalfRepresentative_exists` (La même paire hors ligne fournit un représentant de moitié droite identifié.) ; et 4 autres.

## 4. Points ouverts touchés et tensions

Sans les résoudre.

- **O6 / O9 (théorème d'isolement ; la formule explicite ne contraint que la somme)** : `selection_rest_tsum_decomposition`, `selection_Pi_rest_decomposition`, `selection_primitive_rest_decomposition`, `selection_psi_rest_decomposition`, `selection_weighted_count_rest_decomposition`, `selection_prime_count_rest_decomposition`, `nontrivialZeroChannel_eq_quartet_add_rest`, `smoothedVonMangoldtSum_eq_fixed_add_trivial_add_quartet_add_rest`, `sameZero_smoothedVonMangoldt_quartet_decomposition`, `seam_*_rest_decomposition` scindent exactement la série des zéros en une sélection finie (orbite d'une paire, quartet) et un reste. Ils isolent les termes de la sélection mais ne bornent ni ne comparent ces termes au reste : le théorème d'isolement de O6 n'est pas établi ; la décomposition n'en est que l'énoncé algébrique préalable.
- **O5 / O8 / O10 / O17 / O18 / O21 (prémisses restantes)** : les 31 théorèmes `ÉQUIVALENTE À RH` du lot (section RH, A) confirment que chaque formulation de producteur, de fidélité ou de loi de retour est équivalente à RH ; `strictRightDecayCertificate_iff_riemannHypothesis` et `noCertifiedMirrorOffSignature_iff_riemannHypothesis` sont les formes atomiques (un compte concret de moitié droite ; une signature) équivalentes à RH.
- **O13 (hiérarchie motifs/familles/méta-pattern non portée dans RHV6Fresh)** : `zero_completeGrammarBlock_eq_prime_completeGrammarBlock` et les théorèmes de `ZeroPrimeCompleteGrammarBridge`, `ZeroPrimeCompleteGrammarOccurrences`, `ZeroReconstructedMetaPattern` établissent M^Z = M pour motifs, familles, successions ordonnées et occurrences dans la base `rh_gap_criterion` ; le point reste ouvert pour RHV6Fresh (base hors hiérarchie d'autorité).
- **O11 / T5 / T8 (seconde Tour, lecture)** : sans objet dans ce lot (aucune seconde Tour) ; les cas hors ligne y sont traités par le partenariat et les contacts tangents, non par la Tour inversée.
- **T9 (somme contre terme isolé)** : le lot contient à la fois le terme individuel d'un zéro (`zetaPerron_residue_at_zeta_zero`, résidu −m(ρ)K_x(ρ) ; `explicit_formula_zero_mode`) et la décomposition exacte sélection/reste de la somme ; il éclaire la tension (un terme est bien un objet isolé, sa contribution à la somme n'est pas bornée).
- **T17 (« seule question ouverte »)** : la liste de prémisses distinctes prouvées chacune équivalente à RH (fidélité, retour, naturalité, contacts communs, passage nul, degré de moitié droite…) éclaire que « ce qui reste » se formule en de multiples énoncés équivalents.
- **T20 / V (vérification)** : sans objet ici.
- **Vocabulaire (hors T1…T20)** : homonymie `zetaReflect` entre bases et emploi de « capture » pour la capture zéros/premiers (voir Incidents).
- **T4 (conclusion RH vs statut)** : les 42 théorèmes `IMPLIQUE RH SOUS PRÉMISSE` du lot sont conditionnels à une prémisse non déchargée ; aucun n'est un terme fermé (V119, O7). Pour 33 d'entre eux la prémisse est prouvée équivalente à RH par un théorème du projet (mention « ⟺ RH » dans le statut) ; pour les 9 autres l'équivalence avec RH n'est pas établie par un théorème de ce lot : `ScientificRebuild20260828.E44VonMangoldtPivotInjection.allNontrivialZerosCritical_of_reflectionSamePivot`, `ScientificRebuild20260828.E44VonMangoldtPivotInjection.allNontrivialZerosCritical_of_heightDetermined`, `ScientificRebuild20260828.memberReturnLock_forces_all_true_zeros_critical`, `ScientificRebuild20260828.allNontrivialZeros_beta_eq_half_of_sameEventLocalization`, `ScientificRebuild20260828.critical_of_reflectionInvariant_injective`, `ScientificRebuild20260828.allNontrivialZerosCritical_of_zeroHeight_injective_on_every_constellation`, `ScientificRebuild20260828.allNontrivialZerosCritical_of_contactSignature_reflectionInvariant`, `ScientificRebuild20260828.allNontrivialZerosCritical_of_contactSignature_heightDetermined`, `bounded_critical_line_gives_global`.

## 5. Incidents

- **Axiome hors standard (`native_decide`)** : 4 théorèmes du lot (statut `HORS STANDARD`) : `ScientificRebuild20260828.constraintEvidenceCoverage_length`, `ScientificRebuild20260828.allConstraints_length`, `ScientificRebuild20260828.allConstraints_nodup`, `ScientificRebuild20260828.constraintPhaseCoverage_length`. Axiomes : `RhGap.ScientificRebuild20260828.constraintEvidenceCoverage_length._native.native_decide.ax_1_1`, `RhGap.ScientificRebuild20260828.allConstraints_length._native.native_decide.ax_1_1`, `RhGap.ScientificRebuild20260828.allConstraints_nodup._native.native_decide.ax_1_1`, `RhGap.ScientificRebuild20260828.constraintPhaseCoverage_length._native.native_decide.ax_1_1`. Les trois autres théorèmes hors standard du projet (`master_99_constraints_nodup`, `master_has_exactly_99_constraints`, `master_has_exactly_99_evidence_rows`, module `MasterLeanE58TotalTripleRoute`) sont hors de ce lot. Aucun `sorryAx` dans le lot ; aucun axiome ajouté (aucune déclaration `axiom` dans le projet, cf. SUMMARY).
- **Terme RH fermé** : aucun (aucun type du lot n'est exactement `RiemannHypothesis`). Les théorèmes de conclusion `RiemannHypothesis` sont tous sous prémisse (section RH, A) ; ceux de la bibliothèque `RiemannHypothesisProof` (`RiemannHypothesis_proved_of_samePassageComposition`, `RiemannHypothesis_of_SamePassageGrammaticalRelationIsPreserved`) dépendent de `SamePassageGrammaticalRelationIsPreserved`, prouvée équivalente à RH (`SamePassageGrammaticalRelationIsPreserved_iff_RiemannHypothesis`). Le nom `RiemannHypothesis_proved_of_samePassageComposition` (« proved ») est plus fort que son type (implication sous prémisse).
- **Nom dupliqué entre modules** : `riemannHypothesis_mirrorGapClosure_of_fiberedMZEqM` déclaré à la fois dans `MirrorGapTerminalClosure` et `SemanticMasterTerminal` (même type `FiberedMZEqM → RiemannHypothesis`) ; 2 noms dupliqués dans le lot au total : `ScientificRebuild20260829.riemannHypothesis_mirrorGapClosure_of_fiberedMZEqM`, `gnat_pos`. Les décomptes « entraîne » de ces noms sont cumulés. La docstring de la seconde occurrence annonce le remplacement par un alias inconditionnel : le type reste conditionnel (docstring ≠ état du type).
- **Modules extraits dans une ronde séparée** (SUMMARY : noms de théorèmes dupliqués ou conflit d'import) : `SemanticMasterTerminal`, `ZeroPrimeIntruderExclusion`, `E44LocalVonMangoldtPivot` (dont le groupe de 18 modules) ; la présence de leurs théorèmes dans le jsonl est vérifiée par le contrôle de complétude.
- **Champ `mentions_RH` pollué** : 259 lignes du lot marquées, 195 uniquement à cause du nom de namespace `RiemannHypothesisProof` ; recomptage par mot isolé : 64.
- **Consigne du lot vs données** : les 20 modules `RiemannHypothesisProof.*` du lot sont compilés d'après `rh_gap_criterion_modules.tsv` (contrairement à la consigne « non compilés ») ; les 15 modules non compilés de la bibliothèque sont listés plus haut et ne sont pas dans le lot.
- **Nom qui promet plus que le type** : `trueZero_individual_identity` (`RiemannHypothesisProof.RHV2ZeroIdentity` : type `ρ = ρ`) ; `FirstReturnPreservesRadialDeformationForZero` (type `x = x`, aucun contenu sur le premier retour) ; `FirstReturnPreservesFunctionalMirrorDifference` et `NonCentralFirstReturnCannotEraseRadialDeformation` (indices de retour `s`, `t` non utilisés par le type : la conclusion ne dépend pas d'un retour) ; `FirstReturnContactsRecoverSameZero` (compare deux Tours du même ρ) ; `full_meta_pattern_scale_recomposition` (implication tautologique H → H) ; `RiemannHypothesis_proved_of_samePassageComposition` (voir ci-dessus).
- **Docstring ≠ type** : relevé partiel, uniquement lorsque la lecture du type l'a fait apparaître : docstring de `riemannHypothesis_mirrorGapClosure_of_fiberedMZEqM` (SemanticMasterTerminal) évoquant le remplacement futur par un alias inconditionnel (voir plus haut) ; docstring de `noRealZetaZeroInOpenUnitSegment` affirmant que le fait est absent de Mathlib v4.31.0 (affirmation sur Mathlib non vérifiée ici, non contredite par le type). Aucune comparaison systématique docstring/type sur les 2399 théorèmes n'a été faite.
- **Homonymies de vocabulaire avec RHV6Fresh** : `zetaReflect` (`1 − ρ` ici, `1 − conj ρ` dans RHV6Fresh) ; « capture » (capture découplée zéros/premiers ici, rayon miroir posé sur le rayon, V185, dans le maître) ; « partenariat », « soudure », « constellation » sont propres à cette base.
- **Vérité V7 partiellement rattachée** : `nontrivial_zeta_zero_im_ne_zero` établit `γ ≠ 0` (V7 dit `γ > 0` pour les membres de l'énumération) ; rattaché à V7 avec cette réserve. Les états `CONFIRMÉE (domaine : paquet …)` désignent des paquets de propriétés dont un théorème `_holds` (cité dans le statut quand il existe) établit qu'ils sont toujours réalisés ; pour les paquets sans `_holds` cité, la réalisation universelle n'a pas été vérifiée par le relecteur.
- **Théorèmes privés** : 71 théorèmes du lot sont privés (noms internes) ; ils sont inclus.

## 6. Contrôle de complétude

- Modules du lot (`lots/C4c.txt`) : 181 ; sections de module dans les tables : 181.
- Théorèmes du lot dans `data/rh_gap_criterion.jsonl` (module ∈ lot) : 2399 ; entrées des tables par module : 2399 ; noms distincts (nom, module) : 2399.
- Correspondance exacte multiensemble (module, nom) tables = jsonl : OUI.
- Contrôle : 2399 lignes de théorème dans les tables = 2399 lignes du lot dans le jsonl : CONFORME.
