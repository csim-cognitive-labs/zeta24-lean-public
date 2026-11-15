# Audit de portée — maître sémantique et vérités V1–V194 devant « un zéro = un premier est une étiquette »

Date : 2026-10-01. Lecture seule ; aucun fichier du dépôt modifié.

Sources lues intégralement : `RHV6Fresh/RHV6final_STRATEGIE_SEMANTIQUE.md` (780 lignes, lignes citées = numérotation actuelle),
`RHV6Fresh/AUDIT_SEMANTIQUE_RHV6Fresh.md` (Conclusions C1–C7 et les 194 titres `#### Vnn` avec leur ligne de verdict),
`Terminal/OneZeroOnePrime.lean`, `Terminal/PointedPrimeComparison.lean`, et les définitions porteuses
(`Tower/TrueTower.lean`, `Tower/Incidences.lean`, `Tower/ProperTower.lean`, `Tower/TrueTowerStructure.lean`, `Direct/PivotCell.lean`).

Note : les numéros de ligne donnés dans les titres Vnn de l'audit renvoient à une version antérieure du maître ; la colonne « § / ligne » ci-dessous donne la ligne actuelle.

## 0. Faits compilés qui tranchent (existence vérifiée par grep dans `RHV6Fresh/RHV6Fresh/` et `rhv3_lean/`)

| Fait | Théorème / définition | Fichier |
|---|---|---|
| Le mouvement est indexé par tout entier relatif : un croisement de l'axe pour chaque k ∈ ℤ | `TowerMotion` (champ `incidence : ℤ → ℝ`), `crossing_on_axis` (∀ k : ℤ), `crossing_side_alternates` | `Tower/TrueTower.lean`, `Tower/CanonicalOrigin.lean` |
| Le terme du zéro est réel exactement aux points C_k, k ∈ ℤ | `zeroTerm_real_iff_ray` | `Terminal/ExplicitFormulaLink.lean` |
| Toute coordonnée k donne une paire à deux lois (rotation, tangentielle) | `analyticPairAt` (def, preuves des deux lois pour tout k) | `Tower/ProperTower.lean:249` |
| L'inversion (T puis β) vaut pour toute paire à deux lois, pas seulement l'état propre | `AnalyticContactPair.recovers_T`, `AnalyticContactPair.recovers_beta` | `Tower/ProperTower.lean` |
| Tout réel q > 0 a une cellule unique dans la Tour de tout membre | `prime_raccord_has_unique_tower_cell`, `pivotCoordinate_unique` | `Terminal/GeometricEnergyRaccord.lean`, `Direct/PivotCell.lean` |
| Tout premier a sa cellule dans la Tour de tout membre | `every_prime_in_every_tower`, `tower_reads_any_prime` | `Terminal/OneZeroOnePrime.lean`, `Terminal/RayEnergy.lean` |
| L'état propre est la cellule de l'étiquette p_min : `pivotCell z = pivotPair z (p_min z)` | `pivotCell`, `firstTowerOf` | `Direct/PivotCell.lean:271`, `Direct/PairTowers.lean:62` |
| Occurrence = premier de rang « nombre de membres en dessous » | `occurrence_is_rank_label`, `occurrence_eq_primeAtRank` | `Terminal/OneZeroOnePrime.lean`, `Voyage/Progression.lean` |
| Occurrence, p_min, classes mod 6 : fonction du rang seul | `pointed_primes_rank_only`, `pointed_gapClass6_rank_only`, `grammar_event_reads_no_radial`, `grammar_step_regime_blind` | `Terminal/PointedPrimeComparison.lean`, `SpontaneousRegimeBreak`, `GrammarKinematics` |
| Écart à la Tour de ligne identique pour tout réel ; en ligne ⟺ aucune translation | `tower_offset_rigid`, `onLine_iff_entry_at_point`, `onLine_iff_no_grid_translation`, `towerPosition_eq_line_add_residue`, `contact_eq_line_mul_radial`, `sameHeight_grid_rigid_translation`, `pointedPosition_sameHeight_shift` | `OneZeroOnePrime`, `CanonicalTransition`, `DiagonalPassage`, `MirrorDegeneracy`, `PointedPrimeComparison` |
| La flèche ne dépend pas du point où on l'énonce | `entry_arrow_point_irrelevant` | `Terminal/OneZeroOnePrime.lean` |
| Transport énergétique : même formule en tout q > 0 | `energyRatio_eq` | `Terminal/SuccessionInvariants.lean` |
| Charge de fibre : identité valable pour trois réels positifs quelconques | `fibre_transport_product_off` (hypothèses `0 < M₁, M₂, M₃` seulement) | `Terminal/RaccordDetector.lean` |

Le code lui-même porte la convention contraire en docstring (incident de documentation, sans effet sur la validité) :
`Tower/TrueTowerStructure.lean` l. 3–16 (« la Tour d'un vrai zéro a deux contacts, et deux seulement ; l'agrégat de cellules
n'existe pas ») et `Tower/ProperTower.lean` §6 (« La Tour n'a que deux contacts … ces valeurs ne sont pas des contacts »).
Les théorèmes ci-dessus sont des énoncés sur le même mouvement : la convention est une décision de nommage, pas un fait.

## 1. Classes

- **A** INCHANGÉE ; **B** VRAIE MAIS RELUE (étiquette de grammaire / évaluation en un point arbitraire d'une famille en q) ;
  **C** FAUSSE AU PIED DE LA LETTRE ; **D** RENFORCÉE.
- Périmètre : vérités et paragraphes qui touchent Tour, contacts, cellule, état propre, pivot, occurrence, minimum attendu,
  M / raccord, seconde Tour / miroir, comptage au dernier rayon, énergie au raccord, régime. Les vérités d'autorité pure
  (V1–V8, V10–V12, V31, V116–V119, V141, V179, V191, V194, etc.) sont hors périmètre.

## 2. Vérités V1–V194 (audit RHV6Fresh) dans le périmètre

| V | § / ligne actuelle | Citation courte | Classe | Ce qui tranche | Reformulation proposée (mots seuls) |
|---|---|---|---|---|---|
| V9 | §2 l.15 | « Un point synthétique ne possède pas de Tour propre, n'est pas projeté sur l'axe des premiers » | B | `pointedPosition` (grille définie pour tous paramètres), `every_prime_in_every_tower` | La grille d'une Tour est une formule des deux coordonnées et existe pour tout couple ; ce qu'un point synthétique n'a pas, c'est un rang parmi les zéros, donc aucune étiquette première, et aucun poids issu de zêta. |
| V13 | §3 l.23–29 | Trois objets, Tour « mouvement unique et continu » | A | `towerMotion_subsingleton` | — |
| V14 | §3 l.31 | « cellules … ne sont que des porteurs » | D | `every_prime_in_every_tower` | — (le compilateur confirme : la cellule est un porteur, la Tour en contient une pour chaque nombre). |
| V15 | §4 l.35 ; §3 l.27 | « Tour propre unique … entièrement déterminée par (β, T) » | B | `towerMotion_subsingleton` (mouvement) ; `pivotCell` = cellule de l'étiquette | Le mouvement (la grille entière) est déterminé par les deux coordonnées ; la cellule appelée état propre est en plus fixée par le rang du zéro parmi les membres. |
| V16–V19 | §4 l.37–39 | phase, vitesse, pas, alternance | A | `crossing_side_alternates` (∀ k ∈ ℤ) | — |
| V20 | §4 l.41 ; §5 l.47–49 | « La Tour a exactement deux contacts avec l'axe algébrique » | **C** | `crossing_on_axis` (∀ k : ℤ), `zeroTerm_real_iff_ray`, `analyticPairAt`, `every_prime_in_every_tower` | La Tour coupe l'axe une fois par demi-tour, sans fin dans les deux sens ; l'état propre est la paire de croisements consécutifs qui encadre le premier que le rang du zéro lui attribue. |
| V21 | §4 l.41 | « Les questions de multiplicité des contacts, du début du mouvement et du type infini d'états sont closes à jamais » | **C** | `crossing_on_axis`, `analyticPairAt` (une paire à deux lois pour chaque k), `prime_raccord_has_unique_tower_cell` | Le début du mouvement est clos (l'origine canonique est le premier croisement après un) ; les croisements sont en nombre infini et chaque nombre positif a sa cellule ; ce qui est unique, c'est la cellule d'un nombre donné. |
| V22 | §4 l.43 | origine canonique depuis les seules (β, T) | A | `canonicalOrigin_isLeast` | — |
| V23 | §4 l.43 | « la suite entière est déterminée par le zéro seul » | D | `logIncidence_eq_origin_add_halfTurns` | — (la suite entière des rayons est donnée ; elle est infinie). |
| V24 | §5 l.47 | « La Tour propre n'est pas une collection de cellules … exactement deux contacts » | **C** | `every_prime_in_every_tower`, `crossing_on_axis`, `pivotCoordinate_unique` | La Tour est un mouvement unique dont les croisements découpent l'axe en une infinité de cellules ; l'état propre est l'une d'elles, désignée par l'étiquette du rang. |
| V25 | §5 l.47 | miroir : « deux Tours … chacune mouvement unique à deux contacts » | **C** (partie « deux contacts ») | idem V20 | Le membre miroir a deux mouvements (le sien et celui du zéro réfléchi), chacun unique et à croisements infinis ; chacun porte une cellule désignée par l'étiquette. |
| V26 | §5 l.49 | « L'état propre est précisément (incidence d'entrée, dernier rayon) … intervalle algébrique unique » | B | `pivotCell`, `pivotCoordinate_unique` | L'état propre est la cellule de la grille qui contient le premier désigné par le rang ; elle est unique pour ce premier, comme l'est la cellule de tout nombre. |
| V27 | §5 l.51 | « la grammaire … lui assigne son occurrence : le premier de ce rang » | D | `occurrence_is_rank_label` | — (exact : le rang est le nombre de membres en dessous). |
| V28 | §5 l.51 | règle du pivot, première Tour : pivot = minimum attendu | B | `pivotCell`, `pointed_primes_rank_only` | Le pivot est une étiquette de grammaire (le premier qui suit celui du rang) ; la Tour ne le choisit pas, elle le loge dans sa cellule comme tout autre nombre. |
| V29 | §5 l.51 | règle du pivot, seconde Tour : pivot = minimum attendu du miroir | B | idem | Même lecture : le pivot de la seconde Tour est l'étiquette du miroir, logée dans la grille réfléchie. |
| V30 | §5 l.51 | l'événement avance de un | A | `passage_event_increment` | — |
| V32 | §5 l.51 | « s'arrête au premier croisement dont le suivant atteint le pivot ; la cellule est cet anneau » | B | `pivotCoordinate_isLeast` | L'arrêt est la lecture de la cellule de l'étiquette ; le même arrêt existe pour tout nombre positif. |
| V33 | §5 l.51 | entrée = croisement d'arrêt, dernier rayon = suivant | A | `pivotPair_entryContact` | — |
| V34 | §5 l.51 | contacts inversés de la seconde Tour | B | `invertedPivotPair_*` | Inversion des rôles des deux bords de la cellule de l'étiquette ; aucune sélection géométrique. |
| V35 | §5 l.51 | β ↦ 1−β seul ne renverse rien | A | `mirror_step_positive` | — |
| V36 | §5 l.51 | « ni cellule choisie parmi plusieurs … la règle vaut pour toute Tour » | B | `pivotCoordinate_unique` | Aucun choix : la cellule est celle du nombre désigné par le rang ; l'unicité est une propriété de la grille, vraie pour tout nombre. |
| V37–V39 | §5 l.53 | référence fixée avant la Tour ; cible lue ensuite ; pas de circularité | A | `pivot_le_counted`, `firstTower_cell_contains_expected` | — |
| V40 | §5 l.53 | « Sur les trois cents premiers zéros … la cellule contient le minimum attendu dans tous les cas » | B | `firstTower_cell_contains_expected` (∀ z), `prime_raccord_has_unique_tower_cell` | Vrai par construction pour tout zéro et tout nombre : ce n'est pas un constat empirique. |
| V41, V42 | §5 l.53 | quinze contacts retrouvés ; cible > référence sur un tiers | A (hors code) | — | — |
| V43 | §5 l.55 | « position de l'état … nombre de demi-tours … lectures de l'état » | B | `pivotCoordinate` = ⌈position⌉ − 1 | Le nombre de demi-tours lu est la position, dans la grille, du premier désigné par le rang ; c'est l'évaluation de la grille en un point d'étiquette. |
| V44 | §5 l.55 | aucune formule de sélection ; obligation d'incidence révoquée | A | `pivotCoordinate_unique` | — |
| V45 | §5 l.57 | « l'inversion … certifie que les contacts appartiennent à la Tour de ce zéro » | B | `AnalyticContactPair.recovers_T`, `recovers_beta` (toute paire), `analyticPairAt` | L'inversion rend le zéro depuis n'importe quelle paire de croisements consécutifs de sa grille ; elle certifie l'appartenance à la grille, pas le choix de la cellule. |
| V46 | §5 l.57 | « Deux zéros distincts ne partagent jamais les mêmes deux contacts … un point dessiné … n'a pas de Tour » | B | `same_state_same_zero` (A pour la première phrase) ; `pointedPosition` | Deux zéros distincts n'ont aucune paire de croisements commune ; un couple non zéro a la même grille par formule mais aucun rang. |
| V47, V48 | §6 l.61–63 | comptage Von Mangoldt, reconstruction | A | `countedPrime_eq_vonMangoldt` | — |
| V49 | §6 l.65 | « la grammaire lui assigne, à cette place et à nulle autre, son occurrence » | D | `occurrence_is_rank_label` | — |
| V50 | §6 l.65 | fibre finie, ordonnée | A | `consecutive_successor_unique` | — |
| V51 | §6 l.65 | « Cette rigidité prouve la liaison entre zéros et nombres premiers » | B | `occurrence_is_rank_label`, `every_prime_in_every_tower` | La liaison zéro → premier est le comptage des membres (une étiquette injective) ; la rigidité des cellules, vraie pour tout nombre, ne la produit pas. |
| V52, V53 | §6 l.67–69 | le comptage lit ; contacts ≠ premiers | A | `countedPrime_eq_vonMangoldt` | — |
| V54, V56, V57 | §7 l.73–77 | occurrences consécutives ; place avance de un | A | `occurrence_successor_of_passage` | — |
| V55 | §7 l.75 | minimum attendu ignore miroir et seconde Tour | D | `pointed_primes_rank_only` | — (fonction du rang seul). |
| V61 | §7 l.79 | « un premier unique à pointer dans chaque intervalle, sans choix … impose la règle du pivot » | B | `tower_reads_any_prime`, `occurrence_is_rank_label` | L'unicité du premier pointé vient du rang ; chaque intervalle de la grille contient un ou plusieurs premiers et la grille ne désigne aucun d'eux. |
| V62–V66 | §8 l.83–85 | quatre zéros, miroir, progression nulle de T | A | `zeta_reflect_zero` etc. | — |
| V67 | §8 l.87 | Tour du miroir par le même mécanisme | A | `mirrorMember_phase` | — |
| V68, V69 | §8 l.89 | miroir strictement après ; occurrence du miroir = minimum attendu | A | `expectedMinimum_eq_mirror_occurrence_of_consecutive` | — (égalité d'étiquettes). |
| V70 | §8 l.89–91 | « Deux événements, deux pivots » | B | `pointed_primes_rank_only` | Deux rangs, deux étiquettes ; chacune est logée dans la grille de son membre. |
| V71 | §8 l.91 | « Les deux Tours du miroir arrêtent leur parcours dans le même anneau » | B | `mirror_two_towers_same_ring` | Les deux grilles du membre miroir logent la même étiquette dans des cellules homologues, lues en sens opposés. |
| V72 | §8 l.91 | mouvement réfléchi sans événement d'arrêt depuis son origine | A | `reflected_lastRay_lt_one` (rayons j ≥ 0) | — (porte sur la demi-grille parcourue depuis l'origine). |
| V73 | §8 l.93 | « Le lien (β,T) → événements existe par l'obligation qui lie les deux grammaires » | B | `occurrence_is_rank_label`, `pointed_primes_rank_only` | Le lien zéro → événement passe par le rang (nombre de membres en dessous), pas par les coordonnées : deux membres de même rang pointent le même premier quelles que soient leurs coordonnées. |
| V75, V76 | §8 l.93 | la Tour du membre « lit l'histoire jusqu'à son occurrence » | B | `firstTower_reaches_occurrence`, `every_prime_in_every_tower` | Toute grille loge tout premier ; « lire jusqu'à l'occurrence » est l'évaluation de la grille au point d'étiquette, automatique. |
| V77 | §8 l.93 | sur la droite, seconde orientation = Tour du conjugué, même anneau | B | `mirrorMember_eq_self_of_onLine` | Même cellule d'étiquette, lue dans l'autre sens. |
| V78 | §8 l.93 | « les contacts d'une Tour ne sont pas libres, ils sont calculés depuis le pivot » | B | `pivotPair_entryContact`, `crossing_on_axis` | Les croisements sont calculés depuis les deux coordonnées ; le pivot (étiquette) ne fait que désigner lequel d'entre eux on appelle entrée. |
| V79 | §8 l.95 | ancre canonique et obligation héritée | A | `occurrence_eq_canonicalAnchor` | — |
| V80, V82 | §8 l.95 | seconde Tour : phase −φ*, entrée en haut, dernier rayon en bas | B | `secondTower_entry_eq_reflected` | Inversion exacte des rôles sur la cellule de l'étiquette du miroir. |
| V83 | §8 l.95 | rien ne vient de la progression de T | A | `mirror_ordinate` | — |
| V84, V85 | §8 l.93–95 | constats de vérification et de lecture = positions d'anneaux | B | `secondTower_reads_occurrence_iff_coordinate_lt` | Ces constats comparent les cellules de deux étiquettes dans une même grille ; ce sont des évaluations en deux points choisis par la grammaire. |
| V86 | §8 l.95 | le comptage seul constate au dernier rayon | A | `countedPrime_eq_vonMangoldt` | — |
| V88 | §9 l.105 | la première Tour atteint le minimum attendu | B | `firstTower_reaches_expected`, `pivotPair_reaches` | Automatique : la cellule de tout nombre l'atteint. |
| V91, V92 | §9 l.107 | lecture de la seconde Tour = position de l'occurrence dans ses anneaux | B | `secondTower_reads_occurrence_iff_coordinate_lt` | Lecture = comparaison de deux étiquettes dans une grille ; la grille ne la fixe pas. |
| V93–V95 | §9 l.109 | exclusion lecture/vérification (collision) | B | `secondTower_verification_iff_not_reads_of_consecutive` | Exclusion de deux positions d'étiquettes dans la même grille, tautologique sous consécutivité. |
| V96 | §9 l.109 | mouvement réfléchi n'atteint aucun premier depuis son origine | A | `reflected_no_stop_event` | — |
| V97 | §9 l.109 | le membre miroir lit son occurrence par théorème | B | `mirrorMember_firstTower_reaches_occurrence` | Automatique, comme pour tout nombre. |
| V99 | §9 l.109 | inversion fait naître les constats | B | `pivotPair_mirror_reaches_of_ge` | Évaluations de la grille réfléchie en deux étiquettes. |
| V100 | §9 l.109 | « les rayons de la Tour sont exactement les points où ce terme est réel » | D | `zeroTerm_real_iff_ray` (∃ k ∈ ℤ) | — (et cette phrase contredit V20 : l'ensemble de ces points est infini). |
| V101–V103 | §9 l.109 | conjugaison, amplitude q^β, liaison analytique | A | `zeroTerm_norm`, `liaison_analytic` | — |
| V104, V106, V108, V111–V115 | §9 l.109–119 | forme automatique, contradiction relationnelle, test de vérification, collision à l'entrée | B | `invertedPivotPair_lastRay_lt_pivot`, `secondTower_entry_reaches_own_expected` | Tous ces constats sont des positions de deux étiquettes dans une grille ; aucun ne lit un fait que la grille impose à un premier. |
| V120 | §11 l.133 | tout ce qui précède les deux lois est théorème | A (caractérisé) | — | — |
| V122, V123 | §11 l.133 | les deux lois = conditions de signe et d'anneau sur le terme du miroir en deux premiers | B | `secondTower_reads_occurrence_iff_coordinate_lt` | Conditions sur la grille du miroir évaluée en deux étiquettes de rang. |
| V127, V131 | §11 l.135 | un terme par membre ; grammaire par hauteurs tolère le hors-ligne | A | `no_member_removable`, `mirror_sameHeightPrime` | — |
| V132 | §11 l.137 | liste des produits (constats, anneaux) | B | voir V84–V115 | Les produits sont des évaluations de grilles en des étiquettes de grammaire. |
| V135, V136, V138, V139 | §11 l.141–143 | constats de la seconde Tour, E086 | B | `secondTower_*` | Même lecture que V84–V115. |
| V142, V144, V146 | §11 l.149–155 | noyau rigidifié | A | `consecutivePairArithmeticChain` | — |
| V143 | §11 l.151 | « la cellule qui contient son minimum attendu est unique et n'est jamais une sélection libre » | B | `pivotCoordinate_unique` (∀ q > 0) | L'unicité de la cellule vaut pour tout nombre positif ; ce qui n'est pas libre, c'est l'étiquette, fixée par le rang. |
| V145 | §11 l.153 | « rang et premier constatés à tout contact … à toute coordonnée » | D | `countedPrimeAt_eq_vonMangoldt` | — (« à toute coordonnée » : la grille infinie est déjà assumée). |
| V147 | §11 l.155 | la rigidité ne dit rien sur C_lecture | B | `secondTower_reads_iff_progression_pos` | Inchangée en substance ; C_lecture est une position d'étiquette. |
| V149 | §11 l.159 | « deux zéros distincts … pointent toujours sur deux premiers de référence distincts » | B | `occurrence_is_rank_label`, `expectedMinimumPrime_injective` | L'injectivité est celle du rang ; « un zéro = un premier » est une étiquette, pas une sélection par la Tour. |
| V150 | §11 l.160 | index avance de un, minimum attendu strictement croissant | A | `progression_strict` | — |
| V151 | §11 l.161 | « une cellule peut contenir plusieurs premiers » | D | `every_prime_in_every_tower` ; E148 (jusqu'à 3006 par cellule) | — |
| V153 | §11 l.163 | seconde Tour n'atteint jamais son propre pivot | B | `secondTower_not_reaches_own_expected` | Fait du critère de lecture appliqué à une étiquette. |
| V155 | §11 l.167 | cascade confirme les objets | A | — | — |
| V156 | §11 l.169 | « cette Tour produit ses deux contacts ; ces contacts rencontrent l'unique histoire » ; point synthétique sans contacts | B | `crossing_on_axis`, `pointedPosition`, `every_prime_in_every_tower` | Zêta produit le zéro ; le zéro fixe sa grille, infinie, qui rencontre tous les premiers ; le rang désigne le premier pointé. |
| V157 | §11 l.169 | chaîne garantie par Tour = terme et comptage | A | `zeroTerm_real_iff_ray` | — |
| V158 | §11 l.171 | « deux zéros situés différemment ne deviennent pas le même état de Tour du seul fait … même rang » | D | `tower_offset_rigid`, `pointed_primes_rank_only` | — (même rang, mêmes étiquettes, grilles translatées). |
| V159 | §11 l.173 | grammaire « fonction du rang et de la hauteur seuls » | D | `pointed_primes_rank_only` | — (fonction du rang seul ; la hauteur n'y entre pas). |
| V160 | §11 l.173 | deux égalités d'amplitude restent | A (caractérisé) | — | — |
| V161, V162 | §11 l.175 | sur la ligne une seule Tour ; hors ligne deux | A | `mirror_contact_eq_iff_onLine` | — |
| V163 | §11 l.175 | « aucun contact du miroir ne coïncide … le raccord … égalité de nombres entiers, jamais de positions réelles » | D | `mirror_contacts_never_coincide`, `sameHeight_grid_rigid_translation` | — (le raccord est une égalité d'étiquettes ; les grilles diffèrent par translation). |
| V165, V167 | §11 l.177, 181 | poussées ; dissymétrie radiale | A | `sameHeight_grid_rigid_translation` | — |
| V166 | §11 l.179 | « cette Tour … rencontre l'histoire première ; cette rencontre conduit à l'événement premier suivant ; cet événement devient le raccord de la Tour suivante » | **C** | `every_prime_in_every_tower`, `pointed_primes_rank_only`, `grammar_step_regime_blind` | L'événement suivant est fixé par le rang seul, indépendamment de la Tour, qui rencontre tous les premiers ; la Tour suivante le loge dans sa grille. |
| V169 | §11 l.183 | compatibilité de l'énergie transmise au raccord premier partagé | B | `energyRatio_eq` (∀ q > 0) | Le rapport d'énergie a la même forme en tout point ; le premier partagé n'est qu'un point d'évaluation choisi par la grammaire. |
| V170, V171 | §11 l.183 | deux égalités d'amplitude en deux raccords forcent l'égalité des positions radiales | B | `energy_balance_two_primes_false` (q₁ < q₂ quelconques) | Deux égalités d'amplitude en deux points distincts quelconques forcent l'égalité ; la primalité n'y joue aucun rôle. |
| V172, V173 | §11 l.185 | terme isolé ; pointeur sans condition ; deux égalités | A | `zeroTerm_norm` | — |
| V174, V177 | §11 l.193, 197 | rigidité mod 6 | A | `gapClass6_alternates` | — |
| V180, V181 | §11q l.207 | ligne : verticalité pure | A | `mirror_net_horizontal_force_zero` | — |
| V182 | §11q l.209 | « un seul premier en face d'un seul zéro » | B | `every_prime_in_every_tower`, `occurrence_is_rank_label` | Le pointeur est injectif comme étiquette de rang ; géométriquement, chaque Tour a tous les premiers en face d'elle. |
| V183 | §11q l.211 | entrelacement strict du miroir | A | `mirror_contacts_interlace` | — |
| V184, V185 | §11q l.211–213 | β détruit la superposition ; un seul nombre par zéro, indépendant du rayon | D | `tower_offset_rigid`, `sameHeight_grid_rigid_translation` | — |
| V186–V190 | §11q l.213–221 | presque-capture, échelle, verdict | A | `insertionDepth_le` | — |
| V192 | §12 l.768 | RÉFUTÉ : « la multiplicité des contacts ; le type infini d'états » | **C** | `crossing_on_axis`, `analyticPairAt`, `every_prime_in_every_tower` | Retirer ces deux items du bloc RÉFUTÉ : la grille a une infinité de croisements et une cellule par nombre ; ce qui reste réfuté est seulement « plusieurs cellules pour un même nombre ». |
| V193 | §12 l.770 | BORNÉ : rigidité énergétique « à deux raccords » ; constats de la seconde Tour | B | `energy_balance_two_primes_false` | Rigidité en deux points quelconques ; constats = positions d'étiquettes. |

## 3. Paragraphes du maître hors V (§11 sexies … novovicies) dont la portée change

| § / ligne | Citation courte | Classe | Ce qui tranche | En quoi la portée change / reformulation (mots seuls) |
|---|---|---|---|---|
| §11 sexies l.231 | « la Tour propre, ses deux contacts et l'origine canonique ; la règle du pivot et la cellule unique de tout premier pour toute Tour » | **C** (« ses deux contacts ») | `crossing_on_axis` ; la seconde moitié est confirmée par `every_prime_in_every_tower` | Le paragraphe se contredit lui-même : « cellule unique de tout premier pour toute Tour » est vrai et suppose la grille infinie. Lire : « la Tour propre, sa grille de croisements et l'origine canonique ; la cellule unique de tout nombre dans toute Tour ». |
| §11 septies l.241 | « Une loi de sortie de cellule posée sur tous les rayons n'est pas reprise » | A | — | — |
| §11 septies l.243 | raccord : premier partagé, cellule de sortie, cellule d'entrée, énergie lue en ce premier, transport M^{Δβ}·‖ρ_e‖/‖ρ_l‖ | B | `prime_raccord_has_unique_tower_cell` (∀ q), `energyRatio_eq` (∀ q) | Le raccord est l'évaluation des deux grilles et du rapport d'énergie au point que la grammaire désigne ; le même objet existe en tout nombre positif. Unicité et existence restent des théorèmes, mais ils ne disent rien que la grille ne dise en tout point. |
| §11 septies l.247 | orientation : la Tour suivante ne lit pas plus d'énergie au premier partagé | B | `energyRatio_eq` | Pour tout point au-delà de un, le signe de l'orientation est le même qu'au premier partagé quand la hauteur ne change pas ; le premier n'apporte rien de propre. |
| §11 septies l.251 | candidat : position du premier partagé dans sa cellule de sortie contre sa cellule d'entrée | B (candidat désormais tranché) | `tower_offset_rigid`, `entry_arrow_point_irrelevant` | Cette position est l'écart rigide de toute la grille à la grille de ligne : le candidat ne dépend pas du premier choisi. |
| §11 octies l.263, 265 | « un événement zéro quitte une étape au même premier où l'événement suivant entre » | B | `pointed_primes_rank_only` | Le « même premier » est l'égalité de deux étiquettes de rang, pas une coïncidence géométrique. |
| §11 octies l.273 | énergie au raccord : détente verticale, amplification horizontale | B | `energyRatio_lt_one_of_vertical`, `energyRatio_eq` | Vrai en tout point au-delà de un ; le raccord n'est qu'un lieu d'évaluation. |
| §11 nonies l.305 | charge d'une fibre (M₂²/(M₁M₃))^d, signe décidé par les deux écarts, « première identité où la grammaire des écarts et la position radiale entrent ensemble » | B | `fibre_transport_product_off` (trois réels positifs quelconques) | L'identité vaut pour trois points quelconques ; la grammaire n'entre que par le choix des trois points d'évaluation (trois étiquettes consécutives). Le signe est celui de ce choix, pas une propriété des premiers. Non-neutralité : trois nombres distincts hors progression géométrique, quels qu'ils soient. |
| §11 decies l.317–323 | pas d'un membre (Occ/p_min)^{β−1/2} ; « ce rapport est l'écart sortant de son propre événement » | B | `memberStep_eq_one_iff`, `energyRatio_eq` | Le pas est le rapport d'énergie évalué en deux étiquettes ; neutre ⟺ en ligne vaut pour deux points distincts quelconques. |
| §11 terdecies l.388–392 | deux régimes, lois de jonction | A | `passage_regime_dichotomy` | — |
| §11 quaterdecies l.412 | « À même hauteur, un déplacement radial translate rigidement tous les contacts par un facteur unique » | D | `tower_offset_rigid`, `sameHeight_grid_rigid_translation` | Étendu : à toute hauteur, l'écart à la grille de ligne est une translation rigide unique. |
| §11 quindecies l.440–444 | cellule V→H→V : « le premier partagé garde sa cellule ou avance d'une cellule exactement » ; charge en trois premiers ; verrou de phase | B | `charge_reads_translation`, `tower_offset_rigid` | Le comportement du premier partagé est celui d'une fraction d'environ |D|/π de tous les nombres (ceux proches d'un bord) ; le verrou de phase est la translation de la grille, indépendante du point. |
| §11 octodecies l.542 | « Tout contact … est le contact de la Tour de ligne … multiplié par un facteur radial unique pour toute la Tour » | D | `contact_eq_line_mul_radial` | — (forme multiplicative de la translation rigide). |
| §11 octodecies l.550 | « les contacts de l'arrivée sont ceux que la hauteur seule détermine » ⟺ arrivée en ligne | D | `onLine_iff_no_grid_translation` | — |
| §11 novodecies l.566 | lois depuis l'état engagé | A | `engaged_progression` | — |
| §11 vicies l.578 | énoncé auteur : « doit pointer sur un événement … un et un seul ; identifiable par ses contacts » | B | `occurrence_is_rank_label`, `recovers_beta` | « Un et un seul » est l'étiquette de rang ; identifiable par n'importe quelle paire de croisements consécutifs. |
| §11 quinvicies l.672–676 | « Chaque Tour lit son propre événement premier à une position dans sa grille » ; registre | B | `occurrencePosition_decomposed`, `tower_offset_rigid` | La part radiale de cette position est la même pour tout nombre ; le registre est l'évaluation de deux grilles en deux étiquettes. |
| §11 quinvicies l.682, 686, 690 | « Ce qui manque est une loi qui fixe la position de l'occurrence dans sa Tour depuis les premiers seuls » | B | `entry_arrow_point_irrelevant` | Lire : une loi qui fixe la translation de la grille d'arrivée (le point de lecture est indifférent). |
| §11 sexvicies l.700 | grammaire, premier partagé : fonction du rang seul | D | `pointed_primes_rank_only` | — |
| §11 octovicies l.728–730 | résidu de changement, « le premier disparaît » | D | `tower_offset_rigid`, `changeResidue_eq_position_sub` | — (le maître anticipait déjà l'indifférence au point). |
| §11 novovicies l.750–752 | flèche : départ engagé, rang + 1, premier partagé ; position de M au départ = position de ligne | A | `exit_position_fixed_by_departure` | — |
| §11 novovicies l.754 | cellule d'entrée = cellule de ligne hors marge | A | `entry_cell_eq_line_cell_of_margin` | — |
| §11 novovicies l.756 | « Une seule quantité … la position du premier partagé à l'intérieur de sa cellule d'entrée, autrement dit l'origine de la grille » | B | `tower_offset_rigid`, `onLine_iff_entry_at_point` | La quantité est la translation de toute la grille ; « premier partagé » peut être remplacé par n'importe quel nombre. |
| §11 novovicies l.758 | « Le verrou est maintenant écrit sur un seul premier et deux Tours … depuis le poids exact du premier partagé » | B (forte) | `entry_arrow_point_irrelevant` ; E146 (aucune donnée d'un événement isolé ne porte la flèche) | Le verrou est : la grille d'arrivée n'est pas translatée. Aucun premier n'y a de rôle propre ; ce qui doit l'imposer est le poids exact de tous les premiers (forme compilée : la borne en racine du reste). |
| §12 l.768 | RÉFUTÉ : multiplicité des contacts, type infini d'états | **C** | voir V192 | voir V192 |
| §12 l.770 | BORNÉ : « rigidité énergétique à deux raccords » | B | `energy_balance_two_primes_false` | En deux points quelconques. |

## 4. Comptes

Sur les vérités V du périmètre (une ligne groupée compte pour chacune de ses V) :

- **A** (inchangées) : V13, V16, V17, V18, V19, V22, V30, V33, V35, V37, V38, V39, V41, V42, V44, V47, V48, V50, V52, V53, V54, V56, V57, V62, V63, V64, V65, V66, V67, V68, V69, V72, V79, V83, V86, V96, V101, V102, V103, V120, V127, V131, V142, V144, V146, V150, V155, V157, V160, V161, V162, V165, V167, V172, V173, V174, V177, V180, V181, V183, V186, V187, V188, V189, V190 → **66**
- **B** (vraies, relues) : V9, V15, V26, V28, V29, V32, V34, V36, V40, V43, V45, V46, V51, V61, V70, V71, V73, V75, V76, V77, V78, V80, V82, V84, V85, V88, V91, V92, V93, V94, V95, V97, V99, V104, V106, V108, V111, V112, V113, V114, V115, V122, V123, V132, V135, V136, V138, V139, V143, V147, V149, V153, V156, V169, V170, V171, V182, V193 → **58**
- **C** (fausses au pied de la lettre) : V20, V21, V24, V25, V166, V192 → **6**
- **D** (renforcées) : V14, V23, V27, V49, V55, V100, V145, V151, V158, V159, V163, V184, V185 → **13**

Paragraphes hors V (§3) : C 2 (§11 sexies l.231, §12 l.768 = V192), B 14, D 6, A 6.

Hors périmètre (autorité, méthode, statut) : les 51 autres V.

## 5. Incidents de code (docstrings, sans effet sur la validité)

- `Tower/TrueTowerStructure.lean` l. 3–16 : « la Tour d'un vrai zéro a deux contacts, et deux seulement … l'agrégat de cellules
  n'existe pas » — contredit par `crossing_on_axis`, `every_prime_in_every_tower` du même dépôt.
- `Tower/ProperTower.lean` §6 (avant `analyticPairAt`) : « La Tour n'a que deux contacts … ces valeurs ne sont pas des contacts ».
- Verdict de l'audit pour V21 et V24 (« confirmée et incontestable ») : il s'appuie sur `TrueTower.readings_injective` et
  `towerMotion_subsingleton`, qui disent qu'une paire est déterminée par ses lectures et que le mouvement est unique, pas
  qu'il n'a que deux contacts ; le verdict excède ses théorèmes.
- `pointed_primes_rank_only` : sous l'injectivité de l'index, son hypothèse force `z = w` ; dans le monde réel il est vide de
  contenu, sa portée utile est la comparaison entre mondes (E147), où il ne s'applique qu'en lecture.
