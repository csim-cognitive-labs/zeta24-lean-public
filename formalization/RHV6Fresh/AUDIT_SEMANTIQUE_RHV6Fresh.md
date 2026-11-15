# Audit sémantique de RHV6Fresh — vérités du maître, théorèmes compilés, conséquences

**Date** : 2026-09-29. **HEAD** : `63cbfbec`. **Dépôt** : `formalization/RHV6Fresh/`.

**Périmètre.** Tout le projet RHV6Fresh : 742 théorèmes/lemmes utilisateur extraits, répartis sur 62 modules compilés (plus la bibliothèque `RHV6Demonstration` et le module `Audit`, qui ne contient aucun théorème) ; 141 définitions/structures/inductifs ; `lake build` (cibles par défaut) : PASS, 3895 jobs, 0 erreur ; 0 déclaration `sorryAx` ; aucun axiome ajouté ; axiomes de tous les théorèmes dans {`propext`, `Classical.choice`, `Quot.sound`} (un théorème, `forward_and_backward_false`, n'en utilise aucun). 43 théorèmes mentionnent `RiemannHypothesis` dans leur type (26 équivalences, 10 conclusions RH sous prémisse, 7 où RH est antécédent ou apparaît ailleurs) ; aucun ne prouve RH sans prémisse. Le grep `theorem|lemma` du source donne 720 sur les modules compilés contre 742 extraits (l'écart n'est pas expliqué davantage par les données ; 10 des théorèmes extraits sont privés) ; ce sont les 742 de l'extracteur qui font foi.

**Méthode.** (1) Extracteur Lean (`experiments/audit_semantique/DumpTheorems.lean`) exécuté sur les modules compilés : nom, module, type, docstring, dépendances de preuve dans le projet (`deps_project`) et dans la base (`deps_base`), axiomes (`collectAxioms`), `sorry`, mention de RH, nombre d'hypothèses Prop. (2) Graphe de dépendances compilé : « A entraîne B » signifie « la preuve de B utilise A » ; rien n'est inventé. (3) Statut unique par théorème, décidé mécaniquement puis vérifié à la lecture du type : CONFIRMÉE, CONFIRMÉE SOUS CONDITION, ÉQUIVALENTE À RH, IMPLIQUE RH SOUS PRÉMISSE, RÉFUTATION COMPILÉE ; un théorème sans phrase correspondante dans le maître porte l'étiquette AJOUT. (4) Correctif de contrôle n°1 : « sous condition » est réservé à une restriction substantielle du domaine (côté bas, hors ligne, consécutivité stricte, passage particulier, prémisse nommée) ; injectivité, unicité, implication entre deux notions de la vérité et caractérisation sont CONFIRMÉE, l'hypothèse étant l'antécédent de la relation énoncée. (5) Les 194 vérités V1…V194, les 24 points ouverts O1…O24 et les 20 tensions T1…T20 viennent de `VERITES_MAITRE.md` (lecture du maître sémantique `RHV6final_STRATEGIE_SEMANTIQUE.md`). (6) Lots : B1 Foundation/Tower/Voyage/Direct/Grammar/CleanTerminal ; B2 Terminal A–L ; B3 Terminal M–Z ; B4 Demonstration, Audit et six pistes parquées.

**Rôles.** Collecte et production : Sonnet (extraction, fragments B1–B4, assemblage B5). Plans, contrôle et conclusions : Fable. Aucun théorème n'est créé ni modifié, aucun fichier `.lean` du projet n'est touché ; l'audit relie et qualifie ce qui existe. Les sections de ce document ne contiennent que ce que les fragments validés, `VERITES_MAITRE.md` et les données extraites établissent.

## Conclusions (Fable)

*Rédigées par Fable après contrôle des fragments B1–B4, de l'assemblage B5 et de la révision B6.*

**C1. Le socle est entier, inconditionnel et sans faille.** 742 théorèmes compilés, 0 `sorryAx`,
axiomes standard seuls. Les 194 vérités du maître se répartissent ainsi : 123 confirmées sans
condition, 22 confirmées sous condition (presque toujours la consécutivité stricte ou le côté bas
`β < 1/2`), 13 seulement caractérisées (équivalentes à RH ou l'impliquant sous prémisse), 34 hors code
(autorité, méthode, constats numériques), 2 non transcrites (V107 : nature « relationnelle » de la
contradiction, aucun énoncé ; V124 : seule la somme ψ est compilée, jamais un terme isolé de la
somme).

**C2. La chaîne de la démonstration est confirmée maillon par maillon, depuis zêta jusqu'au raccord.**
Cette série de vérités est confirmée et incontestable, et chacune provoque la suivante (graphe de
dépendances compilé) :
1. *Un zéro, une place* : deux zéros distincts ont deux places distinctes, l'ordre des places est
   strict (`thm_zeroSourceIndex_injective`, `thm_zeroSourceIndex_strictMono`, base rhv3).
2. *Un zéro, un premier pointé* : le minimum attendu est le premier qui suit la place ; deux zéros
   distincts pointent deux premiers distincts (`expectedMinimumPrime_injective`) ; hors ligne, le
   miroir pointe un autre premier (`mirror_expectedMinimum_ne`).
3. *Un premier pointé, une cellule, deux contacts* : la Tour propre place ce premier dans une cellule
   unique, qui est la plus petite qui l'atteint, jamais choisie (`firstTower_cell_contains_expected`,
   `firstTower_contactPair_unique`, `pivotCoordinate_isLeast`), pour tout `β`.
4. *Le comptage lit la cellule* : le premier compté au dernier rayon est celui du comptage de Von
   Mangoldt/Tchebychev (`countedPrime_eq_vonMangoldt`).
5. *Le passage raccorde* : sur tout passage, la place avance de un, l'occurrence du suivant est le
   minimum attendu du précédent, le suivant pointe `p_{n+2}` et sa cellule le contient
   (`passage_event_increment`, `passage_raccords`, `regime_captive_of_prime`) ; la progression des
   minimums attendus est stricte (`expectedMinimumPrime_succ_of_passage`).
6. *Le miroir est un membre* : hors ligne, le miroir est un vrai zéro distinct, postérieur, et sous
   consécutivité stricte son occurrence EST le minimum attendu du zéro original
   (`mirrorMember_ne`, `expectedMinimum_eq_mirror_occurrence_of_consecutive`).
7. *La Tour est le terme explicite* : l'amplitude du terme d'un zéro en q est `q^β/‖ρ‖`
   (`zeroTerm_norm`), ses rayons sont les points où il est réel, de signe alterné.

**C3. La corrélation centrale : toute l'information β-visible est compilée, et elle est propre à la
paire, jamais à la succession.** Trois familles de théorèmes voient `β` : (a) l'entrelacement strict du
miroir dans chaque cellule et la profondeur d'insertion `D ≠ 0` (`mirror_contacts_interlace`,
`insertionDepth_eq_zero_iff`, `superposed_xor_strictlyInterlaced`) ; (b) l'amplitude `q^β`
(`zeroTerm_norm`, `energyRatio_eq`, `mirror_verticalEnergy_pos`) ; (c) la position radiale dans
l'ordre des membres (second disjoint lexicographique). **Les zéros sont liés entre eux par théorème**
(rectification après objection de l'auteur, 2026-09-29 ; la formulation antérieure « aucun théorème ne
relie les rayons d'un zéro à ceux du zéro qui le précède » était fausse et est retirée) :
(i) *liaison de tous les zéros* — la formule explicite (`smoothed_riemann_explicit_formula`,
`psiRecoveredFromZeros_eq_psi`, base rhv3) établit le reste exact de ψ comme somme des contributions
de tous les zéros non triviaux ; chaque contribution est nécessaire, aucune ne peut être retirée, et
la Tour de chaque zéro est la géométrie de sa contribution (`zeroTerm_norm`, ses rayons sont les points
où elle est réelle) ; (ii) *entrelacement des rayons* — `mirror_contacts_interlace` : les rayons de `z*`
s'insèrent strictement entre les rayons consécutifs de `z`, pour tout `k` ; sous consécutivité
stricte, `z*` est le successeur de `z` (`mirror_sourceIndex_of_consecutive`), c'est donc un théorème qui
relie les rayons d'un zéro à ceux du zéro qui le précède ; (iii) *raccord* — sur tout passage, le
premier partagé ordonne les contacts : `C⁻(e) < p_min(e) = Occ(l) < p_min(l) ≤ C⁺(l)`
(`firstTower_cell_contains_expected`, `passage_raccords`). C'est exactement le résidu mesuré par la sonde P11 (verticalité de `e`,
entrelacement de `l`, premier pointé : `⊢ False` non résolu). La captivité « par le premier pointé »
est un théorème ; la captivité « par le zéro précédent » n'en a aucun.

**C4. Toutes les routes de fermeture convergent vers une seule prémisse atomique.** Les 32
théorèmes équivalents à RH et les 9 qui l'impliquent sous prémisse forment un seul faisceau :
absence de passage nul (`PNoNullPassage`) ⟺ exclusion horizontale ⟺ superposition des rayons
⟺ `D ≡ 0` ⟺ grammaire par hauteurs (`grammarsAgree_iff_riemannHypothesis`) ⟺ excès inter-Tours
strictement positif ⟺ équilibre énergétique aux deux raccords ⟺ poussée verticale énergétique ⟺
accord des deux horloges ⟺ capture de régime (modulo le plus bas zéro sur la ligne) ⟺ lecture
énergétique locale (modulo `T ≥ 2` hors ligne) ⟺ lecture réfléchie ⟺ absence de côté bas ⟺ RH
(`premise_ladder_tfae`, `noNullPassage_iff_riemannHypothesis`, `riemannHypothesis_iff_noLowerSide`).
Chaque reformulation, même la plus locale (un réel par zéro, un raccord par passage), retombe sur
« deux membres consécutifs à la même hauteur n'existent pas ». Aucun théorème β-visible n'en décharge
une partie pour un zéro hors ligne.

**C5. Réfutations compilées (17) : elles bornent les pistes, elles ne ferment rien.** Le mouvement
réfléchi depuis sa propre origine n'atteint jamais le minimum attendu du miroir (d'où la vacuité de
`hReaches`) ; aucun contact du miroir ne coïncide avec un contact du zéro ; deux égalités d'amplitude
à deux premiers distincts forcent `β_e = β_l` ; l'identité d'événement miroir, le transport miroir,
l'équivariance réfléchie et la positivité de Weil par configuration sont réfutés (pistes parquées).

**C6. Le maître doit être réaligné sur quatre points** (le code prime, §2 de CLAUDE.md) : la ligne 115
conclut RH sans théorème ; les vérités attribuées à `PairHeightGap.lean` et `InversionClosure.lean`
(fichiers retirés) ne tiennent plus que sous consécutivité stricte ; `CriticalityCharacterization` est
cité « compilé » alors qu'il est parqué ; la seconde Tour est décrite à la fois comme atteignant et
n'atteignant jamais son pivot — ce sont deux objets distincts, tous deux compilés
(`secondTower_entry_reaches_own_expected`, `reflectedFromOrigin_never_reaches_expectedMinimum`).

**C7. Incidents à corriger dans le code, sans effet sur la validité** : docstrings « même hauteur »
sans hypothèse de hauteur dans le type (`sameHeight_horizontal_dominates`, `amplitude_ratio_sameHeight`,
`horizontal_energy_action`) ; noms plus forts que le type (`terminalCollision_conditional_on_reflectedObligation`,
`remaining_open_question_is_readout_only`) ; hypothèse `β = 1/2` inutilisée
(`control_two_onLine_towers_unique`) ; dépendance active sur une piste parquée
(`mirror_heightEventIndex_eq` → `mirror_sameHeightIndex`) ; docstring de `RHV6Demonstration` citant
des fichiers retirés ; 51 `.olean` orphelins.

**Verdict.** Tout ce que le maître affirme comme construction (zéro, Tour, contacts, cellule, pointeur,
raccord, miroir, amplitude) est théorème. Ce qui ferait de cette construction une démonstration de RH
est, sous toutes ses formes compilées, équivalent à RH. `RH_FOUND=FALSE`.


## 2. Statistiques

Table statut × lot (entrées de l'annexe A ; un théorème = une entrée).

| Statut | B1 | B2 | B3 | B4 | Total |
|---|---:|---:|---:|---:|---:|
| CONFIRMÉE | 306 | 79 | 94 | 90 | 569 |
| CONFIRMÉE SOUS CONDITION | 29 | 23 | 39 | 24 | 115 |
| ÉQUIVALENTE À RH | 0 | 15 | 8 | 9 | 32 |
| IMPLIQUE RH SOUS PRÉMISSE | 0 | 3 | 6 | 0 | 9 |
| RÉFUTATION COMPILÉE | 3 | 3 | 0 | 11 | 17 |
| **Total** | **338** | **123** | **147** | **134** | **742** |

- Vérités V touchées (au moins un théorème les rattache dans le champ Vérités) : **116** sur 194 ; en plus, 1 vérité(s) sans rattachement direct dont la formulation cite un théorème existant (V190) ; le reste (77) n'est rattaché à aucun théorème.
- Théorèmes marqués AJOUT (aucune Vi) : **191** (dont 85 repris dans un item d'ajout de la section 5, 106 lemmes de support ou trop locaux non repris).
- Verdicts sur les 194 vérités (révision B6) : confirmée 123 ; confirmée sous condition 22 ; caractérisée seulement (équivalente à RH ou impliquant RH) 13 ; réfutation compilée 0 ; NON TRANSCRITE 2 ; hors code 34. Avant révision B6 : confirmée 104 ; confirmée sous condition 8 ; caractérisée seulement 5 ; réfutation compilée 0 ; NON TRANSCRITE 41 ; hors code 36.
- Points ouverts O1…O24 : 24 ; tensions T1…T20 : 20.

## 3. Vérités du maître, une par une

Pour chaque Vi : la reformulation du maître (avec sa section), puis le verdict décidé sur les statuts des théorèmes rattachés (le statut le plus fort l'emporte ; les théorèmes équivalents à RH sont toujours mentionnés). Les conséquences sont les théorèmes dont la preuve utilise les théorèmes de la vérité (graphe `deps_project`), avec leur énoncé en mots.

#### V1 — Le code Lean compilé sous `RHV6Fresh/RHV6Fresh/` (base RHV3Lean, port zeta23) est la première autorité ; un théorème compilé est vrai et ne se conteste pas. (§1, l. 5)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V2 — Le port zeta23 est validé par Lean et par des mathématiciens. (§1, l. 5)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `isNontrivialZero_iff`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve).

#### V3 — Le maître, le maître mathématique et le maître Lean sont alignés sur le code après coup, peuvent contenir des erreurs, et sont corrigés dès qu'un théorème compilé les contredit. (§1, l. 5)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V4 — Aucune interdiction du maître ne prévaut contre un énoncé compilé. (§1, l. 5 (répété §10, l. 121))
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V5 — Le projet a un seul objectif : un terme compilé, inconditionnel, de type `RiemannHypothesis`. (§1, l. 5)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V6 — On ne travaille qu'avec les vrais zéros non triviaux de zêta, dont l'existence est garantie par la théorie analytique. (§2, l. 9)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V7 — Chaque zéro considéré a partie réelle strictement entre 0 et 1, partie imaginaire strictement positive, et existence issue de la seule théorie analytique de zêta. (§2, l. 11)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `isNontrivialZero_iff`, `analyticOrderAt_riemannZeta_ne_top`, `multiplicity_ne_top`, `zetaZeroConfig_carrier`, `zeroPoint_re_pos`) et provoque la série de conséquences suivantes : `allNontrivial_onLine_iff_riemannHypothesis` (« Tous les zéros non triviaux de la configuration zetaZeroConfig ont Re = 1/2 » équivaut à RiemannH…) ; `one_le_zeroMult` (Tout vrai zéro (zeta23) a multiplicité au moins 1.) ; `zeroPoint_add_one_ne_zero` (`ρ + 1` est non nul pour tout zéro.) ; `zeroPoint_isNontrivial` (Le point `ρ` de tout membre est un zéro non trivial au sens de la formule explicite compilée de la…) ; `zeroPoint_ne_zero` (Le point `ρ` d'un zéro est non nul.).

#### V8 — L'ensemble des vrais zéros est ordonné par partie imaginaire croissante puis partie réelle croissante ; cet ordre est celui de l'énumération et n'est jamais un argument scientifique de la preuve. (§2, l. 13)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `consecutive_successor_unique`, `passage_height_le`, `height_pos_of_precedes`, `exists_consecutive_predecessor`, `passage_trichotomy_ABC`, `passage_deltaT_nonneg`) et provoque la série de conséquences suivantes : `allOnLine_of_regimeCapture` (Sous PLowestZeroOnLine et PRegimeCapture, tout zéro est sur la ligne (récurrence forte sur l'index).) ; `fiberSuccessor_eq_mirror_of_noInterposition` (Sans membre intercalé entre z et son miroir, le successeur consécutif d'un zéro de côté bas est le…) ; `heightProgression_of_horizontalExclusion` (Sous l'exclusion horizontale, tout passage progresse strictement en hauteur (poussée verticale comm…) ; `interTowerExcess_nonneg` (L'excès inter-Tours est toujours positif ou nul.) ; `interTowerExcess_pos_iff_riemannHypothesis` (Exiger un excès inter-Tours strictement positif sur tout passage est équivalent à RH.) ; `offPassages_interTowerExcess_pos_iff_riemannHypothesis` (La même exigence sur les seuls passages à extrémité hors ligne est encore équivalente à RH.) ; et 2 autre(s) : `succession_invariants`, `verticalEnergyPush_of_riemannHypothesis`. Cas restreints, confirmés sous condition (passage dont les deux extrémités sont sur la ligne critique) : `passage_height_lt_of_onLine`.

#### V9 — Un point synthétique ne possède pas de Tour propre, n'est pas projeté sur l'axe des premiers ; il faut passer par zêta. (§2, l. 15 (repris §11, l. 165))
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V10 — Aucun raisonnement ne se fait sur des points synthétiques ; aucune expérience synthétique ne vaut. (§2, l. 15)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V11 — Tout contrôle numérique utilise exclusivement les zéros publiés par Odlyzko, n'a jamais valeur de preuve, ne peut que réfuter une implémentation, jamais un énoncé sémantique du maître. (§2, l. 17)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V12 — Personne ne sait calculer un zéro hors de la droite critique ; il n'est jamais calculé, approché ni synthétisé ; sa représentation est le port du projet compilé et validé (jamais l'import), portant la réflexion zêta (équation fonctionnelle), la conservation de multiplicité et les fenêtres finies d'ordonnées. (§2, l. 19)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `isNontrivialZero_iff`, `zeroMult_eq_toNat_multiplicity`, `zetaReflect_eq_mirrorSupport`, `analyticOrderAt_zeta_conj`, `analyticOrderAt_zeta_one_sub`, `zeta_mult_reflect`, `multiplicity_ne_top`, `one_le_zeroMult`, `riemannZeta_zeros_locallyFinite`, `zeta_window_finite`, `ZeroConfig.one_le_mult`, `ZeroConfig.strip`, `ZeroConfig.reflect_mem`, `ZeroConfig.mult_reflect`, `ZeroConfig.finite_window`, `zetaZeroConfig_carrier`, `zetaZeroConfig_mult`, `zeroSupport_mem_zetaZeroConfig`, `zeta_mult_functionalReflect`) et provoque la série de conséquences suivantes : `analyticOrderAt_zeta_reflect` (L'ordre d'annulation de zêta en 1−ρ̄ égale celui en ρ (bande ouverte).) ; `allNontrivial_onLine_iff_riemannHypothesis` (« Tous les zéros non triviaux de la configuration zetaZeroConfig ont Re = 1/2 » équivaut à RiemannH…) ; `zeroSideWindow_nonneg_of_onLine` (Sous la condition « tous les points de la configuration C sont sur la droite » : la forme côté zéro…).

#### V13 — La démonstration porte sur trois objets et trois seulement : (i) l'ensemble ordonné des vrais zéros, (ii) la Tour propre intrinsèque de chaque zéro (mouvement géométrique unique et continu), (iii) l'unique histoire ordonnée des premiers reconstruite depuis la source des zéros par Chebyshev/Von Mangoldt, avec sa grammaire complète (rangs, occurrences, primalité, écarts, progression). (§3, l. 23–29)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V14 — Aucun objet supplémentaire ne crée une seconde histoire première, une seconde famille de Tours ou une seconde notion de progression ; cellules, coordonnées internes, états intermédiaires, comptages locaux ne sont que des porteurs. (§3, l. 31)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) (théorèmes : `towerMotion_subsingleton`, `TrueTower.ext_pair`, `expectedMinimumPrime_injective`, `secondTower_ring_eq_mirror_firstTower`) : principe de méthode (interdiction d'objets supplémentaires), aucun théorème ne peut porter une interdiction ; instances compilées : `Subsingleton (TowerMotion z)` (une seule Tour par zéro), `expectedMinimumPrime z1 = expectedMinimumPrime z2 → z1 = z2`, `(secondTowerOf z).properState.upright = (firstTowerOf (mirrorMember z)).properState` (la seconde Tour n'est pas une seconde famille) (révision B6)

#### V15 — Chaque vrai zéro possède une Tour propre unique et déterministe, entièrement déterminée par (β, T). (§4, l. 35)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `firstTowerOf_properState`, `canonicalOrigin_eq`, `TrueTower.phase_eq_motion`, `TrueTower.incidence_eq_motion`, `TowerMotion.phase_eq`, `towerMotion_phase`, `towerMotion_incidence`, `towerMotion_subsingleton`, `TrueTower.toTowerMotion_eq`, `TrueTower.ext_pair`, `TrueTower.readings_injective`, `control_two_onLine_towers_unique`, `off_pair_towers_unique_like_control`, `zeroPoint_norm_sq`) et provoque la série de conséquences suivantes : `contactMinusAt_eq_exp` (Le rayon k de z vaut exp((arctan(T/β) + kπ)/T).) ; `contactMinus_eq_iff_radial_eq` (Deux zéros de même hauteur ont le même contact `C_k` si et seulement si leurs positions radiales co…) ; `cos_phase_eq` (cos(phase de la Tour) = β/‖ρ‖.) ; `grids_never_coincide` (Aucun étage de la Tour d'un zéro ne coïncide avec aucun étage de la Tour d'un autre zéro de même ha…) ; `mirror_contacts_interlace` (Pour β < 1/2 et tout k : C_{k−1}(z) < C_k(z*) < C_k(z).) ; `contactAt_tangent_minus` (Au contact inférieur de toute cellule consécutive, tan(T·log C) = T/β : le contact certifie (T,β) p…) ; et 17 autre(s) : `contactAt_tangent_plus`, `crossing_argument`, `incidence_neg_one_lt_one`, `insertionDepth_eq`, `mirrorMember_contactMinusAt`, `mirrorMember_contactPlusAt`, `mirrorMember_phase`, `mirror_contact_ratio_const`, `mirror_phase`, `mirror_relative_position`, `mirror_verticalEnergy_eq_zero_iff`, `mirror_verticalEnergy_pos`, `one_lt_canonicalOrigin`, `sameHeight_amplitude_inverts_at_primes`, `zeroPoint_eq_of_phase_norm_eq`, `zeroPoint_norm_eq_of_eq`, `zeroPoint_norm_lt_of_height_lt`.

#### V16 — La Tour porte une phase (déduite de β et T) et une vitesse de rotation fixée par T seul ; c'est une spirale (éloignement croissant, argument avançant avec le log de l'abscisse à la vitesse fixée par T, décalé de la phase). (§4, l. 37)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `towerMotion_phase_pos`, `towerMotion_phase_lt_pi_div_two`, `towerMotion_incidence_mono`, `towerMotion_incidence_lt_iff`, `logIncidence_eq_origin_add_halfTurns`, `halfTurn_logStep`, `crossing_argument`, `AnalyticContactPair.tangentLaw`, `TrueTower.phase_eq_motion`, `TowerMotion.phase_eq`, `TowerMotion.logIncidence_eq`, `TowerMotion.incidence_eq`, `towerMotion_phase`, `towerMotion_incidence`, `towerMotion_incidence_positive`, `towerMotion_incidence_strictOrder`, `pi_mul_towerPosition`, `phase_identity`, `contactMinusAt_eq_exp`, `cos_phase_eq`, `phase_identity_cos`, `towerPosition_sub`) et provoque la série de conséquences suivantes : `TrueTower.incidence_eq_motion` (Les rayons portés par une Tour propre sont ceux du mouvement canonique du zéro.) ; `grids_never_coincide` (Aucun étage de la Tour d'un zéro ne coïncide avec aucun étage de la Tour d'un autre zéro de même ha…) ; `contactAt_tangent_minus` (Au contact inférieur de toute cellule consécutive, tan(T·log C) = T/β : le contact certifie (T,β) p…) ; `contactAt_tangent_plus` (Idem au contact supérieur : les deux extrémités certifient le même rapport T/β.) ; `zeroTerm_re_eq_cos_towerPosition` (Pour q > 0, Re(terme du zéro en q) = q^β·cos(π·position de Tour en q)/‖ρ‖.) ; `abs_insertionDepth_lt_half` (|D| < 1/2 pour tout zéro.) ; et 46 autre(s) : `canonicalOrigin_lt_iff_zero_le_pivotCoordinate`, `contactMinus_eq_iff_radial_eq`, `incidence_neg_one_lt_one`, `mirror_contacts_interlace`, `pivotCoordinate_mirror_mem`, `towerMotion_consecutive_width`, `towerPosition_shift_abs_lt_half`, `zeroTerm_im_eq_sin_towerPosition`, `AnalyticContactPair.entryReading_isInt`, `AnalyticContactPair.recovers_beta`, `canonicalOrigin_eq`, `canonicalOrigin_pos`, `contactAt_ordered`, `contactMinusAt_positive`, `contactPlusAt_positive`, `contact_lt_mirror_iff`, `coordinate_lt_of_gap_ge_pi`, `countedPrimeAt_mono_oriented`, `crossing_on_axis`, `crossing_side`, `crossing_side_abs`, `entry_separates_in_fiber`, `insertionDepth_eq`, `mirrorMember_contactMinusAt` ….

#### V17 — Le pas de log-rayon entre deux croisements consécutifs ne dépend que de T ; il n'est pas un écart entre nombres premiers. (§4, l. 37)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `logIncidence_eq_origin_add_halfTurns`, `halfTurn_logStep`, `contactAt_consecutive_logWidth`, `TowerMotion.logIncidence_eq`, `towerMotion_consecutive_width`, `towerMotion_ringJump_logWidth`, `sameHeight_pitch_invariant`, `sameRadial_height_changes_pitch`, `ray_energy_growth`, `sameRing_imp_gap_lt_pi`, `coordinate_lt_of_gap_ge_pi`, `span_eq_on_sameHeight_fiber`) et provoque la série de conséquences suivantes : `TrueTower.incidence_eq_motion` (Les rayons portés par une Tour propre sont ceux du mouvement canonique du zéro.) ; `contactAt_tangent_minus` (Au contact inférieur de toute cellule consécutive, tan(T·log C) = T/β : le contact certifie (T,β) p…) ; `contactAt_tangent_plus` (Idem au contact supérieur : les deux extrémités certifient le même rapport T/β.) ; `mirror_step_positive` (Le pas de log-rayon du miroir supérieur (1−β,T) vaut +π/T : β ↦ 1−β seul ne renverse rien.) ; `pivotPair_stageReading` (Le nombre d'étages lu sur la paire du pivot vaut un.) ; `reflectedLogIncidence_eq` (Le log-rayon de coordonnée j du mouvement réfléchi est celui de la Tour propre à la coordonnée −j (…) ; et 3 autre(s) : `reflected_lastRay_lt_one`, `secondTower_reads_of_gap_ge_pi`, `towerMotion_incidence`. Touchée aussi (sans l'établir) par : `phase_increment_eq_of_sameHeight`.

#### V18 — À chaque rayon où la courbe traverse l'axe algébrique réel, le passage change de côté (positif-négatif-positif en alternance stricte, une traversée par demi-tour). (§4, l. 39)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `crossing_argument`, `crossing_on_axis`, `crossing_side`, `crossing_side_alternates`, `crossing_side_abs`, `ray_energy`, `ray_energy_alternates`, `geometry_of_tower`) et provoque la série de conséquences suivantes : `ray_zeroTerm_eq` (Le terme sur un rayon est exactement son énergie signée (partie imaginaire nulle).) ; `succession_invariants` (Paquet sur tout passage : trichotomie, formule de R_E, constance ⟺ Δβ = 0, raccords, cellules conte…). Touchée aussi (sans l'établir) par : `oddFactor_sign_alternates`.

#### V19 — Cette alternance est vérifiée exactement sur tous les zéros publiés. (§4, l. 39)
- Verdict : Cette vérité est confirmée (théorèmes : `crossing_side_alternates`, `crossing_side`, `crossing_on_axis`) : `cos (T·log (incidence (k+1)) - phase) = -cos (T·log (incidence k) - phase)` et `cos (…) = (-1)^k` pour tout zéro et tout `k` : l'alternance stricte est un théorème (a fortiori exact sur les zéros publiés) ; le constat numérique lui-même reste hors code (révision B6)

#### V20 — La Tour a exactement deux contacts avec l'axe algébrique : l'incidence d'entrée et le dernier rayon ; ils délimitent l'unique cellule de l'état propre, contenant un ou plusieurs premiers. (§4, l. 41 (aussi §5, l. 47–49))
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `AnalyticContactPair.cell_nonempty`, `reaches_analyticPairAt_iff`, `lastRayContact_eq_contactPlusAt`, `contactAt_consecutive_logWidth`, `contactAt_ordered`, `contactMinusAt_positive`, `contactPlusAt_positive`, `contactAt_tangent_minus`, `contactAt_tangent_plus`, `InvertedContactPair.entryContact_pos`, `InvertedContactPair.lastRayContact_pos`, `AnalyticContactPair.entryContact_pos`, `AnalyticContactPair.lastRayContact_pos`, `AnalyticContactPair.ordered`, `AnalyticContactPair.rotationLaw`, `AnalyticContactPair.tangentLaw`, `AnalyticContactPair.entryReading_isInt`, `AnalyticContactPair.entryContact_eq_incidence`, `AnalyticContactPair.lastRayContact_eq_incidence`, `AnalyticContactPair.contacts_of_one_stage`, `analyticPairAt_entryContact`, `analyticPairAt_lastRayContact`, `TrueTower.properState_entryContact`, `TrueTower.properState_lastRayContact`) et provoque la série de conséquences suivantes : `pivotPair_stageReading` (Le nombre d'étages lu sur la paire du pivot vaut un.) ; `AnalyticContactPair.ext_readings` (Une paire de contacts est déterminée par ses deux lectures (coordonnée d'entrée, nombre d'étages).) ; `AnalyticContactPair.logDiameter_positive` (Le diamètre logarithmique de la cellule (log C_dernier − log C_entrée) est strictement positif.) ; `countedPrime_le_lastRay` (Le premier compté est au plus le dernier rayon (comptage inclusif).) ; `pivotCell_amplitude_brackets` (Pour `q > 0`, l'amplitude du terme en `q` est strictement supérieure à celle au contact d'entrée de…) ; `prime_raccord_has_unique_tower_cell` (Pour tout zéro et `q > 0`, le premier `q` est encadré par les deux contacts de la cellule de sa coo…) ; et 27 autre(s) : `AnalyticContactPair.entryCoordinate_cast`, `AnalyticContactPair.eq_analyticPairAt_of_one_stage`, `AnalyticContactPair.recovers_beta`, `AnalyticContactPair.stageReading_isInt`, `InvertedContactPair.entryContact_eq_incidence`, `InvertedContactPair.lastRayContact_eq_incidence`, `InvertedContactPair.reaches_primeAtRank_iff`, `canonicalOrigin_lt_iff_zero_le_pivotCoordinate`, `contactPlusAt_lt_primeAtRank_counted`, `countedPrime_eq_countedPrimeAt_lastRay`, `countedPrime_lt_expected_of_lastRay`, `countedRank_eq_countedRankAt_lastRay`, `countedRank_eq_succ_iff`, `countedRank_eq_zero_iff`, `entry_separates_in_fiber`, `pivotCoordinate_le_of_le_contactPlus`, `pivotPair_entryContact`, `pivotPair_lastRayContact`, `pivot_le_contactPlus_pivotCoordinate`, `ray_energy`, `ray_energy_alternates`, `ray_energy_growth`, `ray_zeroTerm_real`, `reaches_iff_readCoordinates` …. Touchée aussi (sans l'établir) par : `pivotCell_entry_zeroTerm_real`, `pivotCell_lastRay_zeroTerm_real`.

#### V21 — Les questions de multiplicité des contacts, du début du mouvement et du type infini d'états sont closes à jamais. (§4, l. 41)
- Verdict : Cette vérité est confirmée (théorèmes : `canonicalOrigin_isLeast`, `one_lt_incidence_iff`, `TrueTower.readings_injective`, `AnalyticContactPair.contacts_of_one_stage`, `AnalyticContactPair.stageReading_isNat`, `towerMotion_subsingleton`) : début du mouvement : `IsLeast {k | 1 < (towerMotionOf z).incidence k} 0` ; multiplicité : l'état est fixé par `(entryCoordinate, stageCount)` (`readings_injective`), deux contacts `entryContact < lastRayContact` ; type d'états : `∃ m, 0 < m ∧ stageReading = ↑m` ; « closes à jamais » = statut (hors code) (révision B6)

#### V22 — L'origine canonique est le premier croisement de l'axe algébrique après l'abscisse un, point de départ unique obtenu sans premier, rang ni comptage, depuis les seuls (β, T). (§4, l. 43)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `canonicalOrigin_lt_iff_zero_le_pivotCoordinate`, `canonicalOrigin_eq`, `canonicalOrigin_pos`, `one_lt_canonicalOrigin`, `incidence_neg_one_lt_one`, `one_lt_incidence_iff`, `canonicalOrigin_isLeast`, `geometry_of_tower`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve).

#### V23 — Le mouvement commence à l'origine canonique et avance d'un demi-tour à chaque croisement ; la suite entière est déterminée par le zéro seul, il n'y a rien à produire pour obtenir les rayons. (§4, l. 43)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `towerMotion_incidence_mono`, `towerMotion_incidence_lt_iff`, `logIncidence_eq_origin_add_halfTurns`, `InvertedContactPair.rotationLaw`, `AnalyticContactPair.rotationLaw`, `TrueTower.incidence_eq_motion`, `towerMotion_incidence`, `contactMinusAt_eq_exp`, `geometry_of_tower`) et provoque la série de conséquences suivantes : `canonicalOrigin_lt_iff_zero_le_pivotCoordinate` (La référence est devant l'origine canonique exactement quand la coordonnée d'arrêt est ≥ 0 (le parc…) ; `AnalyticContactPair.stageReading_isInt` (Le nombre d'étages lu est un entier (loi de rotation).) ; `canonicalOrigin_eq` (L'origine canonique vaut exp(phase/T) : elle ne dépend que de (β,T), sans premier ni rang.) ; `contactMinus_eq_iff_radial_eq` (Deux zéros de même hauteur ont le même contact `C_k` si et seulement si leurs positions radiales co…) ; `contact_lt_mirror_iff` (C_j(z) < C_k(z*) ⟺ j − k < −D (hypothèse de notation c = j − k).) ; `crossing_argument` (L'argument du mouvement au croisement k vaut kπ.) ; et 11 autre(s) : `grids_never_coincide`, `incidence_neg_one_lt_one`, `mirrorMember_contactMinusAt`, `mirrorMember_contactPlusAt`, `mirror_contact_lt_iff`, `mirror_contact_ratio_const`, `mirror_contacts_interlace`, `mirror_relative_position`, `one_lt_incidence_iff`, `pivotCoordinate_le_of_le_contactPlus`, `secondTower_reads_occurrence_iff_coordinate_lt`. Touchée aussi (sans l'établir) par : `towerPosition_contactMinusAt`.

#### V24 — La Tour propre n'est pas une collection de cellules ; c'est un mouvement géométrique unique à exactement deux contacts. (§5, l. 47)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `towerMotion_subsingleton`, `TrueTower.toTowerMotion_eq`) et provoque la série de conséquences suivantes : `TrueTower.ext_pair` (Une Tour propre est déterminée par sa paire de contacts.).

#### V25 — Le zéro miroir hors ligne possède deux Tours distinctes (première Tour dans le sens croissant, seconde Tour de la paire dans le sens opposé), chacune mouvement unique à deux contacts. (§5, l. 47)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `off_pair_towers_unique_like_control`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve).

#### V26 — L'état propre est précisément (incidence d'entrée, dernier rayon) ; ce sont des rayons, pas des premiers ; ils délimitent un intervalle algébrique unique contenant un ou plusieurs premiers. (§5, l. 49)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `AnalyticContactPair.cell_nonempty`, `reaches_of_mem_cell`, `crossing_on_axis`, `contactAt_ordered`, `InvertedTower.properState_entryContact`, `InvertedTower.properState_lastRayContact`, `AnalyticContactPair.ordered`, `AnalyticContactPair.logDiameter_positive`, `TrueTower.properState_entryContact`, `TrueTower.properState_lastRayContact`, `AnalyticContactPair.ext_contacts`, `cell_contains_expected`, `expected_mem_cell`) et provoque la série de conséquences suivantes : `AnalyticContactPair.eq_analyticPairAt_of_one_stage` (À un seul étage, la paire est la valeur des formules à sa coordonnée lue (analyticPairAt).) ; `AnalyticContactPair.ext_readings` (Une paire de contacts est déterminée par ses deux lectures (coordonnée d'entrée, nombre d'étages).) ; `AnalyticContactPair.recovers_T` (Inversion : T = m·π/(log C_dernier − log C_entrée) : les deux contacts redonnent exactement T par l…) ; `AnalyticContactPair.stageReading_positive` (Le nombre d'étages lu est strictement positif.) ; `InvertedContactPair.logDiameter_positive` (Le diamètre logarithmique de la cellule inversée est strictement positif.). Touchée aussi (sans l'établir) par : `prime_raccord_has_unique_tower_cell`.

#### V27 — Le zéro a un rang dans la source des zéros ; la grammaire première reconstruite lui assigne son occurrence (le premier de ce rang) ; ce lien est établi et n'est pas un choix. (§5, l. 51)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `occurrence_eq_canonicalAnchor`, `InvertedContactPair.reaches_occurrence_iff`, `occurrence_prime`, `occurrence_pos`, `reaches_occurrence_iff`, `countedPrime_eq_occurrence_iff`, `countedPrime_eq_occurrence_iff_rank_succ`, `expectedMinimum_eq_succ_occurrence`, `occurrence_eq_primeAtRank`, `clock_pn_eq`, `clock_ph_eq`) et provoque la série de conséquences suivantes : `clock_ph_le_pn` (Le premier de l'horloge des hauteurs est inférieur ou égal à celui de l'horloge des membres.) ; `countedPrime_eq_occurrence_iff_cell` (C_lecture en forme cellule : premier compté = occurrence ⟺ Occ(w) ≤ C⁺ < p_min(w).) ; `mirror_continuous_progression_pos` (La progression continue du second événement du miroir (de son occurrence à son minimum attendu) est…) ; `off_consecutive_continuous_progression_eq_span` (Sous consécutivité stricte, la progression continue du second événement du miroir vaut exactement `…) ; `InvertedContactPair.countedRank_pos_of_reaches_occurrence` (Le rang compté est positif dès que l'occurrence est atteinte.) ; `countedPrime_eq_occurrence_iff_of_lt_two` (Pour un dernier rayon < 2, le premier compté est l'occurrence ⟺ l'index zéro-source est nul.) ; et 26 autre(s) : `expectedMinimum_le_mirror_occurrence`, `horizontalRaccords_amplitude_brackets`, `localReading_modeA`, `localReading_of_riemannHypothesis`, `memberHeightTransport_iff_index`, `memberTransition_eq_canonical`, `mirror_occurrence_strict`, `mirror_sourceIndex_of_consecutive`, `occurrence_lt_expectedMinimumPrime`, `occurrence_strict_of_passage`, `occurrence_successor_of_passage`, `occurrences_agree_iff_riemannHypothesis`, `off_mirror_two_grammars`, `passage_double_constraint`, `passage_raccords`, `passage_span_eq_log_occurrences`, `progression_nonneg`, `reaches_occurrence_iff_readCoordinates`, `reflected_blocked_onLine`, `reflected_mirror_reads_nothing`, `riemannHypothesis_of_energyBalance`, `sameHeight_amplitude_inverts_at_raccords`, `secondTower_reads_occurrence_iff_coordinate_lt`, `secondTower_reads_of_gap_ge_pi` ….

#### V28 — Règle du pivot, cas droite/première Tour : pour tout zéro de la droite et pour la première Tour d'une paire hors ligne, le parcours va dans le sens croissant et le pivot est le premier qui suit immédiatement l'occurrence, i.e. le minimum attendu. (§5, l. 51)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `firstTowerOf_properState`, `pivotPair_entryContact`, `pivotPair_lastRayContact`) et provoque la série de conséquences suivantes : `entry_lt_pivot` (L'incidence d'entrée de la paire du pivot est strictement sous la référence.) ; `pivotPair_entryReading` (La coordonnée d'entrée lue sur la paire du pivot est la coordonnée calculée par la règle.) ; `pivot_le_lastRay` (La référence est au plus égale au dernier rayon de sa paire de pivot.). Cas restreints, confirmés sous condition (zéro sur la droite critique (β=1/2)) : `firstTowerOf_eq_lineTowerOf`, `lineTowerOf_properState`, `lineTower_reaches_expected`.

#### V29 — Règle du pivot, seconde Tour : c'est la Tour du zéro réfléchi par l'équation fonctionnelle, parcours en sens opposé, pivot propre = minimum attendu du miroir (premier qui suit l'occurrence du miroir). (§5, l. 51 (aussi l. 89))
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `invertedPivotPair_entryContact`, `invertedPivotPair_lastRayContact`, `secondTowerOf_properState`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve).

#### V30 — La seconde Tour est la Tour d'un autre zéro dont la partie réelle diffère ; son événement dans la grammaire des zéros est le suivant de celui du zéro original (l'événement avance de un) ; elle ne peut pas avoir le même événement que la première. (§5, l. 51 (aussi l. 135))
- Verdict : Cette vérité est confirmée sous condition (théorèmes : `mirror_sourceIndex_of_consecutive`, `mirrorMember_distinct_member`, `mirror_occurrence_strict`, `mirror_event_identity_refuted`, `mirror_expectedMinimum_ne`, `passage_event_increment`) : sous β<1/2 : `mirrorMember z ≠ z ∧ PZeroMemberPrecedes z (mirrorMember z)`, `occurrence z < occurrence (mirrorMember z)`, `¬occurrence (mirrorMember z) = occurrence z` (pas le même événement) ; l'avance exacte de un est `nZeroSourceIndex (mirrorMember z) = nZeroSourceIndex z + 1` sous consécutivité stricte ; sur tout passage : `nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1` (révision B6)

#### V31 — Le « pivot commun » de la seconde Tour (énoncé du 2026-09-24) est retiré : il donnait à la seconde Tour l'événement de la première et aucun événement d'arrêt propre. (§5, l. 51 (aussi l. 135, l. 137, l. 225))
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V32 — Le parcours part de l'origine canonique, avance d'un demi-tour par croisement, s'arrête au premier croisement dont le suivant atteint le pivot ; la cellule est cet anneau ; le nombre d'étages vaut un. (§5, l. 51)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `invertedPivotPair_stageCount`, `pivotPair_entryContact`, `pivotPair_lastRayContact`, `pivotPair_entryReading`, `pivotPair_entryCoordinate`, `pivotPair_stageReading`, `pivotPair_stageCount`, `pivotCoordinate_le_of_le_contactPlus`, `pivot_le_contactPlus_pivotCoordinate`, `pivotCoordinate_isLeast`, `canonicalOrigin_lt_iff_zero_le_pivotCoordinate`, `AnalyticContactPair.eq_analyticPairAt_of_one_stage`, `countedPrime_of_one_stage`, `AnalyticContactPair.stageReading_isInt`, `AnalyticContactPair.stageCount_positive`, `AnalyticContactPair.contacts_of_one_stage`, `sameRing_imp_gap_lt_pi`, `pivotCoordinate_mono`, `stop_event`, `readings`) et provoque la série de conséquences suivantes : `firstTower_readings` (La première Tour a pour coordonnée d'entrée celle du pivot de p_min(z) et un étage.) ; `invertedPivotPair_entryCoordinate` (La coordonnée d'entrée de la paire inversée du pivot est celle du rayon du haut, k+1.) ; `lineTower_readings` (Sur la droite, la coordonnée d'entrée est celle du pivot de p_min(z) et le nombre d'étages vaut 1.) ; `secondTower_reads_occurrence_iff_coordinate_lt` (C_lecture : la seconde Tour lit l'occurrence du miroir ssi Occ(z*) tombe dans un anneau strictement…) ; `AnalyticContactPair.stageReading_isNat` (Le nombre d'étages lu est un naturel strictement positif.) ; `InvertedContactPair.stageCount_positive` (Le nombre d'étages d'une paire inversée est strictement positif.) ; et 4 autre(s) : `entry_lt_pivot`, `pivot_le_lastRay`, `progression_nonneg`, `secondTower_readings`. Cas restreints, confirmés sous condition (zéro sur la droite critique (β=1/2)) : `lineTower_readings`.

#### V33 — Orientation croissante : l'incidence d'entrée est le croisement d'arrêt, le dernier rayon est le suivant. (§5, l. 51)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `pivotPair_entryContact`, `pivotPair_lastRayContact`, `stop_event`) et provoque la série de conséquences suivantes : `entry_lt_pivot` (L'incidence d'entrée de la paire du pivot est strictement sous la référence.) ; `pivotPair_entryReading` (La coordonnée d'entrée lue sur la paire du pivot est la coordonnée calculée par la règle.) ; `pivot_le_lastRay` (La référence est au plus égale au dernier rayon de sa paire de pivot.).

#### V34 — Seconde Tour : les contacts sont inversés (incidence d'entrée = croisement au-dessus du pivot ; dernier rayon = croisement au-dessous). (§5, l. 51 (aussi l. 95, l. 133, l. 137))
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `invertedPivotPair_entryContact`, `invertedPivotPair_lastRayContact`, `invertedPivotPair_upright`, `invertedPivotPair_cell_contains`, `secondTower_entry_eq_reflected`, `secondTower_lastRay_eq_reflected`, `InvertedContactPair.entryContact_pos`, `InvertedContactPair.lastRayContact_pos`, `InvertedContactPair.ordered`, `InvertedContactPair.rotationLaw`, `InvertedContactPair.tangentLaw`, `InvertedContactPair.upright_entryContact`, `InvertedContactPair.upright_lastRayContact`, `InvertedContactPair.logDiameter_positive`, `InvertedContactPair.recovers_T`, `InvertedContactPair.recovers_beta`, `InvertedContactPair.entryContact_eq_incidence`, `InvertedContactPair.lastRayContact_eq_incidence`, `invertedPairAt_entryContact`, `invertedPairAt_lastRayContact`, `invertedPairAt_upright`, `InvertedTower.properState_entryContact`, `InvertedTower.properState_lastRayContact`, `reflectedLogIncidence_eq`, `reflectedIncidence_eq`, `reflectedIncidence_antitone`, `reflected_entry_eq_contactPlus`, `reflected_lastRay_eq_contactMinus`, `invertedPairAt_eq_reflected`, `reflectedMotion_incidence`, `secondTower_inversion_is_unconditional`, `reflection_reverses_existing_ring`, `reflected_presents_via_functional_reflect`) et provoque la série de conséquences suivantes : `InvertedContactPair.entryReading_isInt` (La coordonnée d'entrée lue sur une paire inversée est un entier (loi tangentielle).) ; `InvertedContactPair.reaches_primeAtRank_iff` (Dualité rang/contact au dernier rayon inversé : le premier de rang r est atteint ssi r < rang compt…) ; `invertedPivotPair_entryCoordinate` (La coordonnée d'entrée de la paire inversée du pivot est celle du rayon du haut, k+1.) ; `invertedPivotPair_stageCount` (Le nombre d'étages de la paire inversée du pivot vaut un.) ; `reflected_lastRay_lt_one` (Depuis son origine (j ≥ 1), le dernier rayon du mouvement réfléchi est strictement sous l'abscisse…) ; `secondTower_cell_contains_own_expected` (La seconde Tour atteint l'anneau de son pivot propre p_min(z*) : dernier rayon strictement sous lui…) ; et 1 autre(s) : `trajectory_reversal`.

#### V35 — Le seul changement de partie réelle (β ↦ 1−β) ne renverse rien ; le renversement vient de l'équation fonctionnelle et de la conjugaison (1−ρ). (§5, l. 51 ; §8, l. 95 ; §11, l. 137 ; §12, l. 225)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `reflectedPhase_eq_neg`, `reflected_step`, `mirror_step_positive`) et provoque la série de conséquences suivantes : `reflectedIncidence_antitone` (Les rayons du zéro réfléchi décroissent strictement avec sa coordonnée (orientation opposée).) ; `reflectedLogIncidence_eq` (Le log-rayon de coordonnée j du mouvement réfléchi est celui de la Tour propre à la coordonnée −j (…). Touchée aussi (sans l'établir) par : `completedZeta_zetaReflect`.

#### V36 — La détermination de la cellule n'admet rien d'autre : ni cellule choisie parmi plusieurs, ni formule arbitraire de coordonnée, ni lecture de l'autre Tour, ni argument tiré de la partie imaginaire commune ; la règle vaut pour toute Tour, sur la droite ou hors d'elle. (§5, l. 51)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `firstTower_contactPair_unique`, `pivotCoordinate_unique`, `pivotCoordinate_eq_of_same_cell`, `geometry_selects_raccord_prime`, `tower_reads_any_prime`) et provoque la série de conséquences suivantes : `control_two_onLine_towers_unique` (Pour deux zéros de la ligne, toute coordonnée dont la cellule contient le minimum attendu du zéro e…) ; `off_pair_towers_unique_like_control` (Pour un zéro et son miroir, toute coordonnée dont la cellule contient le minimum attendu est la coo…). Touchée aussi (sans l'établir) par : `prime_raccord_has_unique_tower_cell`.

#### V37 — La référence est le pivot, fixé par la progression première avant toute Tour ; la cible constatée est le dernier premier atteint par le comptage au dernier rayon, lue après. (§5, l. 53)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `pivot_le_lastRay`, `pivotPair_reaches`, `pivotPair_reaches_of_le`, `pivot_countedRank_pos`, `pivot_le_counted`, `R1_iff_expected_le_counted`, `reaches_iff_le_countedPrime`, `reaches_expected_of_le_lastRay`, `expectedMinimum_le_stateReadout_iff`, `stateReadout_lt_expectedMinimum_iff`, `expected_le_counted`) et provoque la série de conséquences suivantes : `cell_contains_expected` (Pour tout zéro, la cellule de l'état propre de la première Tour contient le minimum attendu : incid…) ; `expectedMinimum_le_produced_iff` (À compte positif, le premier produit atteint p_min(a) exactement quand le contact supérieur l'attei…) ; `firstTower_cell_contains_expected` (Pour tout zéro et tout β, la cellule de la première Tour contient le minimum attendu (C⁻ < p_min(z)…) ; `firstTower_reaches_expected` (La première Tour de tout zéro atteint le minimum attendu de son zéro (par la règle du pivot).) ; `invertedPivotPair_cell_contains` (Le pivot est dans la cellule inversée : dernier rayon (bas) strictement sous lui, entrée (haut) au…) ; `lineTower_cell_contains_expected` (Sur la droite, C⁻ < p_min(z) ≤ C⁺ : le minimum attendu est dans la cellule.) ; et 7 autre(s) : `lineTower_expected_le_counted`, `lineTower_reaches_expected`, `lock_imp_counted_lt_occurrence`, `pivotPair_mirror_reaches_of_ge`, `pivot_le_contactPlus_pivotCoordinate`, `prime_raccord_has_unique_tower_cell`, `produced_lt_expectedMinimum_iff`. Touchée aussi (sans l'établir) par : `lastPrimeAtStateUpper_le_contact`.

#### V38 — La cible peut dépasser la référence (sauts de l'histoire première) ; elle ne descend jamais sous elle. (§5, l. 53)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `InvertedContactPair.reaches_iff_le_countedPrime`, `pivot_le_counted`, `occurrence_lt_expectedMinimumPrime`, `expected_le_counted`) et provoque la série de conséquences suivantes : `consecutivePairArithmeticChain` (Sous consécutivité stricte d'un zéro de côté bas et de son miroir : la place du miroir est celle du…) ; `expectedMinimumPrime_succ_of_passage` (Sur tout passage, le minimum attendu du membre antérieur est strictement inférieur à celui du posté…) ; `expectedMinimum_lt_mirror_expectedMinimum` (Pour un zéro de côté bas, le minimum attendu de z est strictement sous celui du miroir.) ; `firstTower_reaches_occurrence` (La première Tour de tout zéro lit son occurrence (théorème).) ; `lineTower_expected_le_counted` (Sur la droite, la cible constatée est au moins le minimum attendu.) ; `lineTower_reaches_occurrence` (Sur la droite, la Tour du zéro lit son occurrence (Occ(z) < p_min(z)).) ; et 7 autre(s) : `pivotCell_mirror_reaches_expected`, `progression_nonneg`, `reads_expected_imp_ne_previous_expected`, `reads_expected_imp_not_occurrence`, `riemannHypothesis_of_energyBalance`, `secondTower_entry_reaches_mirror_occurrence`, `upright_presents_forward`. Cas restreints, confirmés sous condition (zéro sur la droite critique (β=1/2)) : `lineTower_expected_le_counted`.

#### V39 — Il n'y a pas de circularité : la règle fixe la cellule depuis la référence, la cible s'y lit ensuite. (§5, l. 53)
- Verdict : Cette vérité est confirmée (théorèmes : `secondTowerOf_properState`, `firstTowerOf_properState`, `pivotCoordinate_isLeast`, `firstTower_cell_contains_expected`, `expected_le_counted`) : `(secondTowerOf z).properState = invertedPivotPair (mirrorMember z) ↑(expectedMinimumPrime (mirrorMember z))` : la définition ne contient ni `occurrence z` ni `expectedMinimumPrime z` (pas de circularité) ; la cellule est fixée par le pivot (`IsLeast {k | q ≤ contactPlusAt z k} (pivotCoordinate z q)`) et la cible se lit après (`expectedMinimumPrime z ≤ countedPrime (firstTowerOf z).properState`, elle ne descend jamais sous la référence) (révision B6)

#### V40 — Sur les 300 premiers zéros publiés, la cellule contient le minimum attendu dans tous les cas. (§5, l. 53)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `firstTower_cell_contains_expected`, `entry_lt_pivot`, `pivot_le_lastRay`, `cell_contains_expected`) et provoque la série de conséquences suivantes : `invertedPivotPair_cell_contains` (Le pivot est dans la cellule inversée : dernier rayon (bas) strictement sous lui, entrée (haut) au…) ; `lineTower_cell_contains_expected` (Sur la droite, C⁻ < p_min(z) ≤ C⁺ : le minimum attendu est dans la cellule.) ; `prime_raccord_has_unique_tower_cell` (Pour tout zéro et `q > 0`, le premier `q` est encadré par les deux contacts de la cellule de sa coo…) ; `canonicalOrigin_lt_iff_zero_le_pivotCoordinate` (La référence est devant l'origine canonique exactement quand la coordonnée d'arrêt est ≥ 0 (le parc…) ; `grammar_determines_stop_ray` (Sous la grammaire par hauteurs, sur tout passage, le membre postérieur est sur la ligne, sa hauteur…) ; `invertedPivotPair_lastRay_lt_pivot` (Le dernier rayon inversé est strictement sous le pivot.) ; et 5 autre(s) : `pivotCoordinate_le_of_le_contactPlus`, `pivotPair_reaches`, `pivot_le_contactPlus_pivotCoordinate`, `properTowerOfMirror_and_reflectedMotion_coexist`, `regime_captive_of_prime`. Cas restreints, confirmés sous condition (zéro sur la droite critique (β=1/2)) : `lineTower_cell_contains_expected`.

#### V41 — Sur ces 300 zéros, les quinze contacts historiques sont exactement retrouvés. (§5, l. 53)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V42 — Sur ces 300 zéros, la cible dépasse la référence sur près d'un tiers. (§5, l. 53)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V43 — La position de l'état dans la suite des croisements (nombre de demi-tours depuis l'origine canonique) et le nombre d'étages sont des lectures de l'état, jamais des entrées ni des paramètres. (§5, l. 55)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `invertedPivotPair_entryCoordinate`, `invertedPivotPair_stageCount`, `firstTower_readings`, `secondTower_readings`, `pivotPair_entryReading`, `pivotPair_entryCoordinate`, `pivotPair_stageReading`, `pivotPair_stageCount`, `reaches_iff_readCoordinates`, `not_reaches_iff_readCoordinates`, `reaches_occurrence_iff_readCoordinates`, `AnalyticContactPair.eq_analyticPairAt_of_one_stage`, `lastRayContact_eq_contactPlusAt`, `InvertedContactPair.stageReading_isNat`, `InvertedContactPair.stageCount_positive`, `InvertedContactPair.stageCount_cast`, `InvertedContactPair.entryReading_isInt`, `AnalyticContactPair.entryReading_isInt`, `AnalyticContactPair.stageReading_isInt`, `AnalyticContactPair.stageReading_positive`, `AnalyticContactPair.stageReading_isNat`, `AnalyticContactPair.entryCoordinate_cast`, `AnalyticContactPair.stageCount_positive`, `AnalyticContactPair.stageCount_cast`, `AnalyticContactPair.ext_readings`, `TrueTower.readings_injective`, `readings`) et provoque la série de conséquences suivantes : `AnalyticContactPair.lastRayContact_eq_incidence` (Le dernier rayon est le rayon de coordonnée (entrée + nombre d'étages).) ; `lineTower_readings` (Sur la droite, la coordonnée d'entrée est celle du pivot de p_min(z) et le nombre d'étages vaut 1.) ; `secondTower_coordinate_eq_unique_mirrorContactPair` (La coordonnée de la seconde Tour moins un est la coordonnée unique de la première Tour du membre mi…) ; `AnalyticContactPair.entryContact_eq_incidence` (L'incidence d'entrée est le rayon de coordonnée d'entrée de la Tour du zéro.) ; `AnalyticContactPair.same_state_same_zero` (Deux états propres de même nombre d'étages et mêmes contacts appartiennent au même zéro : les conta…) ; `countedPrime_eq_countedPrimeAt_lastRay` (Le premier compté d'un état est le premier constaté indexé à la coordonnée du dernier rayon (k+m−1).) ; et 5 autre(s) : `countedPrime_le_lastRay`, `countedPrime_lt_expected_of_lastRay`, `countedRank_eq_countedRankAt_lastRay`, `firstTower_contactPair_unique`, `stop_event`. Cas restreints, confirmés sous condition (zéro sur la droite critique (β=1/2)) : `lineTower_readings`.

#### V44 — Aucune formule de sélection de la coordonnée n'est cherchée ; l'obligation dite d'incidence d'entrée est révoquée et jamais rouverte. (§5, l. 55)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `pivotCoordinate_unique`, `pivotCoordinate_isLeast`) et provoque la série de conséquences suivantes : `firstTower_contactPair_unique` (Toute coordonnée k dont la cellule contient p_min(z) est la coordonnée d'entrée de la première Tour…) ; `geometry_selects_raccord_prime` (Sur tout passage (hauteurs positives : condition de domaine), l'occurrence du membre postérieur est…) ; `pivotCoordinate_eq_of_same_cell` (Deux références de la même cellule donnent la même coordonnée de pivot : la règle est aveugle au pr…) ; `stop_event` (Pour tout zéro, la coordonnée d'entrée de la première Tour est le plus petit croisement dont le con…).

#### V45 — Propriété centrale, l'inversion : les deux contacts redonnent exactement T par leur rapport, puis β par la loi tangentielle ; elle certifie que les contacts appartiennent à la Tour de ce zéro. (§5, l. 57 (repris l. 167, l. 165))
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `mirrorMember_contactMinusAt`, `mirrorMember_contactPlusAt`, `contactAt_tangent_minus`, `contactAt_tangent_plus`, `InvertedContactPair.tangentLaw`, `InvertedContactPair.recovers_T`, `InvertedContactPair.recovers_beta`, `InvertedContactPair.entryContact_eq_incidence`, `InvertedContactPair.lastRayContact_eq_incidence`, `AnalyticContactPair.tangentLaw`, `AnalyticContactPair.recovers_T`, `AnalyticContactPair.recovers_beta`, `AnalyticContactPair.entryContact_eq_incidence`, `AnalyticContactPair.lastRayContact_eq_incidence`, `AnalyticContactPair.same_state_same_zero`, `inversion`) et provoque la série de conséquences suivantes : `AnalyticContactPair.contacts_of_one_stage` (À un seul étage, les deux contacts sont la paire consécutive (contactMinusAt, contactPlusAt) à la c…) ; `AnalyticContactPair.ext_readings` (Une paire de contacts est déterminée par ses deux lectures (coordonnée d'entrée, nombre d'étages).) ; `AnalyticContactPair.entryReading_isInt` (La coordonnée d'entrée lue est un entier (loi tangentielle).) ; `InvertedContactPair.entryReading_isInt` (La coordonnée d'entrée lue sur une paire inversée est un entier (loi tangentielle).) ; `contact_lt_mirror_iff` (C_j(z) < C_k(z*) ⟺ j − k < −D (hypothèse de notation c = j − k).) ; `entry_separates_in_fiber` (Deux zéros de même hauteur dont les états propres ont la même incidence d'entrée sont le même zéro…) ; et 4 autre(s) : `lastRayContact_eq_contactPlusAt`, `mirror_contact_lt_iff`, `mirror_contacts_interlace`, `reaches_iff_readCoordinates`.

#### V46 — Deux zéros distincts ne partagent jamais les mêmes deux contacts ; un même couple est le même zéro ; un point dessiné avec le même couple sans être zéro n'a pas de Tour ; il n'existe pas plusieurs résultats. (§5, l. 57)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `firstTower_contactPair_unique`, `AnalyticContactPair.same_state_same_zero`, `entry_separates_in_fiber`, `AnalyticContactPair.ext_contacts`, `AnalyticContactPair.ext_readings`, `TrueTower.ext_pair`, `contactMinus_eq_iff_radial_eq`, `zeroPoint_eq_of_phase_norm_eq`, `phase_norm_ne_of_ne`) et provoque la série de conséquences suivantes : `TrueTower.readings_injective` (Les lectures (coordonnée d'entrée, nombre d'étages) identifient une Tour propre.) ; `AnalyticContactPair.eq_analyticPairAt_of_one_stage` (À un seul étage, la paire est la valeur des formules à sa coordonnée lue (analyticPairAt).) ; `control_two_onLine_towers_unique` (Pour deux zéros de la ligne, toute coordonnée dont la cellule contient le minimum attendu du zéro e…) ; `mirror_contact_eq_iff_onLine` (Le contact `C_k` du membre miroir coïncide avec celui de `z` si et seulement si `z` est sur la lign…) ; `off_pair_towers_unique_like_control` (Pour un zéro et son miroir, toute coordonnée dont la cellule contient le minimum attendu est la coo…) ; `onLine_of_mirror_phase_shift_eq_zero` (Si Δφ = 0 alors β = 1/2.). Touchée aussi (sans l'établir) par : `grids_never_coincide`.

#### V47 — On applique le comptage de Von Mangoldt et Chebyshev à l'unique histoire première. (§6, l. 61)
- Verdict : Cette vérité est confirmée (théorèmes : `countedPrime_eq_vonMangoldt`, `countedRank_eq_vonMangoldt`, `occurrence_eq_primeAtRank`) : `countedRank S = nPrimeCountingFromJ rChebyshevJNat ⌊S.lastRayContact⌋₊` et `countedPrime S = fnPrimeAtRank (…- 1)` : le comptage de Chebyshev/Von Mangoldt est appliqué à l'unique histoire première (`fnPrimeAtRank`) (révision B6)

#### V48 — La première partie de la démonstration reconstruit la grammaire première depuis les zéros : le canal Chebyshev/Von Mangoldt redonne exactement l'unique histoire (poids, primalité, comptage, rangs, écarts), composante par composante. (§6, l. 63)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `countedRank_eq_vonMangoldt`, `countedPrime_eq_vonMangoldt`, `liaison_analytic`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve).

#### V49 — Cette reconstruction rigidifie la relation zéros/premiers : chaque zéro porte sa place dans l'ordre des zéros ; la grammaire lui assigne à cette place et à nulle autre son occurrence. (§6, l. 65)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `InvertedContactPair.reaches_occurrence_iff`, `reaches_occurrence_iff`, `occurrence_eq_primeAtRank`) et provoque la série de conséquences suivantes : `InvertedContactPair.countedRank_pos_of_reaches_occurrence` (Le rang compté est positif dès que l'occurrence est atteinte.) ; `countedPrime_eq_occurrence_iff` (Le premier compté sur l'état de w est l'occurrence de w ⟺ le rang compté moins un vaut l'index zéro…) ; `countedPrime_eq_occurrence_iff_cell` (C_lecture en forme cellule : premier compté = occurrence ⟺ Occ(w) ≤ C⁺ < p_min(w).) ; `expectedMinimum_le_mirror_occurrence` (Pour un zéro de côté bas, l'occurrence du miroir est au moins le minimum attendu de z (progression…) ; `memberTransition_eq_canonical` (Pour tout membre w, sa transition (Occ(w), p_min(w)) est la transition canonique de son index n(w)…) ; `mirror_continuous_progression_pos` (La progression continue du second événement du miroir (de son occurrence à son minimum attendu) est…) ; et 5 autre(s) : `mirror_occurrence_strict`, `mirror_sourceIndex_of_consecutive`, `occurrence_prime`, `off_consecutive_continuous_progression_eq_span`, `passage_raccords`.

#### V50 — Lorsque plusieurs zéros partagent la même partie imaginaire, la fibre de cette partie imaginaire est finie, ordonne ces zéros et fournit leur passage consécutif. (§6, l. 65)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `consecutive_successor_unique`, `zeta_window_finite`, `entry_separates_in_fiber`, `span_eq_on_sameHeight_fiber`) et provoque la série de conséquences suivantes : `fiberSuccessor_eq_mirror_of_noInterposition` (Sans membre intercalé entre z et son miroir, le successeur consécutif d'un zéro de côté bas est le…). Cas restreints, confirmés sous condition (zéro de côté bas) (autres hypothèses : antécédents de la relation énoncée ou conditions de domaine : z' consécutif à z; zéro de côté bas (β<1/2); pour un zéro hors ligne) : `fiberSuccessor_ordinate_eq`, `fiberSuccessor_eq_mirror_or_precedes`, `exists_fiberSuccessor`, `off_event_increment_without_height`.

#### V51 — Cette rigidité prouve la liaison entre zéros et premiers et prouve la progression obligatoire. (§6, l. 65)
- Verdict : Cette vérité est confirmée (théorèmes : `pivotCoordinate_unique`, `firstTower_contactPair_unique`, `countedPrime_eq_vonMangoldt`, `countedRank_eq_vonMangoldt`, `liaison_analytic`, `progression_occurrence`, `expectedMinimumPrime_succ_of_passage`, `expectedMinimumPrime_injective`) : les conclusions sont compilées : liaison `countedPrime S = fnPrimeAtRank (nPrimeCountingFromJ rChebyshevJNat ⌊S.lastRayContact⌋₊ - 1)`, `psiRecoveredFromZeros x = Chebyshev.psi x`, progression `PZeroMembersConsecutive a b → occurrence b = expectedMinimumPrime a`, injectivité du pointeur ; la rigidité est `k = pivotCoordinate z q` (unicité). Le lien de cause « prouvé PAR cette rigidité » n'est pas un théorème unique (les résultats sont indépendants dans le graphe) (révision B6)

#### V52 — Le comptage s'effectue depuis le début de l'histoire jusqu'au dernier rayon de l'état propre ; le dernier premier inclus est celui effectivement constaté ; le comptage lit, il ne sélectionne jamais. (§6, l. 67)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `InvertedContactPair.not_reaches_iff`, `InvertedContactPair.reaches_of_le`, `InvertedContactPair.not_reaches_of_lastRay_lt`, `InvertedContactPair.countedPrime_prime`, `InvertedContactPair.countedRank_eq_vonMangoldt`, `InvertedContactPair.reaches_primeAtRank_iff`, `InvertedContactPair.reaches_iff_le_countedPrime`, `InvertedContactPair.countedPrime_lt_of_not_reaches_succ`, `InvertedContactPair.countedRank_pos_of_reaches_occurrence`, `countedPrimeAt_eq_vonMangoldt`, `countedPrimeAt_eq_primeAtRank`, `contactPlusAt_lt_primeAtRank_counted`, `countedPrimeAt_lt_expected_of_contact`, `vonMangoldt_channel_reflectionFixed`, `countedPrimeAt_of_contactPlus_eq`, `countedPrimeAt_mono_oriented`, `pivot_countedRank_pos`, `pivot_le_counted`, `R1_iff_expected_le_counted`, `reaches_iff_readCoordinates`, `not_reaches_iff_readCoordinates`, `reaches_occurrence_iff_readCoordinates`, `not_reaches_iff`, `reaches_of_le`, `reaches_of_mem_cell`, `reaches_primeAtRank_iff`, `reaches_iff_le_countedPrime`, `reaches_of_le_lastRay`, `not_reaches_of_lastRay_lt`, `reaches_analyticPairAt_iff`, `countedRank_eq_zero_iff`, `one_le_countedRank_of_two_le`, `countedPrime_eq_occurrence_iff_of_lt_two`, `countedRank_eq_succ_iff`, `countedPrime_prime`, `countedPrime_eq_countedPrimeAt_lastRay`, `countedRank_eq_countedRankAt_lastRay`, `countedPrime_lt_expected_of_lastRay`, `countedPrime_le_lastRay`, `producedPrime_eq_vonMangoldt`, `producedPrime_prime`, `primeCountAtStateUpper_mono`, `producedPrime_mono`, `primeCountAtStateUpper_pos_of_two_le`, `count_pos_of_reaches`, `expectedMinimum_le_produced_iff`, `produced_lt_expectedMinimum_iff`, `primeCountAtStateUpper_eq_vonMangoldt`, `lastPrimeAtStateUpper_le_contact`) et provoque la série de conséquences suivantes : `InvertedContactPair.reaches_occurrence_iff` (L'occurrence du zéro est atteinte sur une paire inversée exactement quand le rang compté dépasse l'…) ; `countedPrime_eq_expected_iff_rank_succ` (Pour un dernier rayon ≥ 2, premier compté = minimum attendu ⟺ rang compté = index + 2.) ; `countedPrime_eq_occurrence_iff_cell` (C_lecture en forme cellule : premier compté = occurrence ⟺ Occ(w) ≤ C⁺ < p_min(w).) ; `countedPrime_eq_occurrence_iff_rank_succ` (Pour un dernier rayon ≥ 2, premier compté = occurrence ⟺ rang compté = index + 1.) ; `countedPrime_of_one_stage` (À un seul étage, le premier compté est le premier constaté à la coordonnée d'entrée.) ; `expected_le_counted` (Pour tout zéro, la cible constatée (dernier premier compté au dernier rayon) est au moins la référe…) ; et 13 autre(s) : `firstTower_reaches_occurrence`, `invertedPivotPair_not_reaches`, `invertedPivotPair_not_reaches_of_le`, `lineTower_expected_le_counted`, `lineTower_reaches_occurrence`, `lock_imp_counted_lt_occurrence`, `mirror_counted_lt_expected_iff`, `not_reaches_expected_of_lastRay_lt`, `pivotPair_reaches_of_le`, `reaches_expected_iff`, `reaches_occurrence_iff`, `secondTower_counted_lt_own_expected`, `secondTower_verification_iff_not_reads_of_consecutive`.

#### V53 — L'événement de comptage n'entre jamais dans la construction de l'état propre ; les deux contacts ne sont pas des premiers. (§6, l. 69)
- Verdict : Cette vérité est confirmée (théorèmes : `AnalyticContactPair.entryContact_eq_incidence`, `AnalyticContactPair.lastRayContact_eq_incidence`, `pivotPair_entryContact`, `pivotPair_lastRayContact`, `countedPrime_eq_vonMangoldt`, `countedPrime_le_lastRay`) : `entryContact = rTowerIncidence z entryCoordinate`, `lastRayContact = rTowerIncidence z (entryCoordinate + stageCount)` et `pivotPair_entryContact = exp ((phase + ↑(pivotCoordinate z q)·π)/T)` : les contacts sont des réels fonctions de `z` et de la coordonnée seules ; le comptage vient après (`countedPrime S = fnPrimeAtRank (… ⌊S.lastRayContact⌋₊ - 1)`, `↑(countedPrime S) ≤ S.lastRayContact`) (révision B6)

#### V54 — Pour deux zéros consécutifs, leurs occurrences dans l'unique histoire sont consécutives ; le premier suivant l'occurrence du zéro courant est le minimum que le zéro suivant doit nécessairement atteindre. (§7, l. 73)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `occurrence_successor_of_passage`, `expectedMinimumPrime_pos`, `reaches_expected_iff`, `reaches_expected_of_reaches_occurrence`, `countedPrime_eq_expected_iff`, `countedPrime_eq_expected_iff_rank_succ`, `expectedMinimumPrime_prime`, `occurrence_lt_expectedMinimumPrime`, `expectedMinimumPrime_eq_laterOccurrence`, `progression_occurrence`, `expectedMinimum_eq_succ_occurrence`, `count_pos_of_reaches`, `geometry_selects_raccord_prime`, `passage_event_increment`, `passage_double_constraint`, `regime_captive_of_prime`, `passage_raccords`, `succession_invariants`, `progression_nonneg`) et provoque la série de conséquences suivantes : `expectedMinimumPrime_succ_of_passage` (Sur tout passage, le minimum attendu du membre antérieur est strictement inférieur à celui du posté…) ; `reads_expected_imp_ne_previous_expected` (Si l'état de z' lit son propre minimum attendu, alors il ne lit pas p_min(z) sur un passage consécu…) ; `R1_iff_expected_le_counted` (Sur toute paire de contacts à compte positif, le minimum attendu est atteint ssi il ne dépasse pas…) ; `cell_contains_expected` (Pour tout zéro, la cellule de l'état propre de la première Tour contient le minimum attendu : incid…) ; `consecutivePairArithmeticChain` (Sous consécutivité stricte d'un zéro de côté bas et de son miroir : la place du miroir est celle du…) ; `countedPrime_ne_expected_iff_cell` (Forme cellule du constat de vérification au successeur z' de z : premier compté ≠ p_min(z) ⟺ C⁺(S')…) ; et 38 autre(s) : `expectedMinimum_eq_mirror_occurrence_of_consecutive`, `expectedMinimum_lt_mirror_expectedMinimum`, `expected_le_counted`, `firstTower_cell_contains_expected`, `firstTower_contactPair_unique`, `firstTower_reaches_expected`, `firstTower_reaches_occurrence`, `grammar_determines_stop_ray`, `grammar_hypotheses_of_passage`, `horizontalRaccords_amplitude_brackets`, `lineTower_cell_contains_expected`, `lineTower_expected_le_counted`, `lineTower_reaches_expected`, `lineTower_reaches_occurrence`, `lock_imp_counted_lt_occurrence`, `mirror_continuous_progression_pos`, `mirror_pivot_mono_of_consecutive`, `mirror_sourceIndex_of_consecutive`, `off_consecutive_continuous_progression_eq_span`, `off_event_increment_without_height`, `onLine_passage_shares_grammar_context`, `passage_span_eq_log_occurrences`, `pivotCell_mirror_reaches_expected`, `pivotPair_mirror_reaches_of_ge` …. Cas restreints, confirmés sous condition (zéro de côté bas (β<1/2); paire (z, miroir) strictement consécutive; selon l'énoncé : Sous la condition « a et b sont deux membres consécutifs ») : `expectedMinimum_le_mirror_occurrence`, `expectedMinimum_eq_mirror_occurrence_of_consecutive`, `mirror_sourceIndex_of_consecutive`, `reached_progression`. Touchée aussi (sans l'établir) par : `consecutivePairArithmeticChain`.

#### V55 — Le minimum attendu est une propriété de la progression universelle des premiers, établie par la rigidité ; sa définition ignore le miroir et la seconde Tour. (§7, l. 75)
- Verdict : Cette vérité est confirmée (théorèmes : `expectedMinimum_eq_succ_occurrence`, `expectedMinimumPrime_prime`, `expectedMinimumPrime_injective`, `occurrence_lt_expectedMinimumPrime`) : `expectedMinimumPrime a = fnPrimeSuccessor (nZeroSourceIndex ↑a)` : fonction du seul index du zéro dans la suite des premiers, énoncé sans `mirrorMember` ni `secondTowerOf` (révision B6)

#### V56 — Sur un passage consécutif, la place avance de un et l'occurrence avance du premier courant au premier suivant. (§7, l. 77)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `occurrence_strict_of_passage`, `occurrence_successor_of_passage`, `reaches_expected_of_reaches_occurrence`, `expectedMinimumPrime_eq_laterOccurrence`, `eventIndex_succ_of_passage`, `expectedMinimumPrime_succ_of_passage`, `progression_occurrence`, `progression_strict`, `passage_event_increment`, `rank_grammar_unconditional`, `later_sourceIndex_eq`, `grammar_hypotheses_of_passage`, `passage_double_constraint`, `passage_raccords`, `passage_span_eq_log_occurrences`) et provoque la série de conséquences suivantes : `countedPrime_ne_expected_iff_cell` (Forme cellule du constat de vérification au successeur z' de z : premier compté ≠ p_min(z) ⟺ C⁺(S')…) ; `expectedMinimum_eq_mirror_occurrence_of_consecutive` (Sous consécutivité stricte, l'occurrence du miroir égale exactement le minimum attendu de z.) ; `geometry_selects_raccord_prime` (Sur tout passage (hauteurs positives : condition de domaine), l'occurrence du membre postérieur est…) ; `grammar_determines_stop_ray` (Sous la grammaire par hauteurs, sur tout passage, le membre postérieur est sur la ligne, sa hauteur…) ; `interTowerExcess_pos_of_grammar_iff_riemannHypothesis` (Ajouter les trois hypothèses grammaticales à « excès strictement positif » ne change rien : l'énonc…) ; `mirror_sourceIndex_of_consecutive` (Sous consécutivité stricte de la paire (z, miroir), l'index zéro-source du miroir est celui de z pl…) ; et 8 autre(s) : `off_event_increment_without_height`, `onLine_clock_sync`, `onLine_passage_shares_grammar_context`, `reached_progression`, `reads_expected_imp_ne_previous_expected`, `regime_captive_of_prime`, `succession_invariants`, `verification_passes`. Cas restreints, confirmés sous condition (zéro de côté bas, β < 1/2 ; consécutivité stricte du zéro et de son miroir; consécutivité stricte du zéro et de son miroir; prémisse `PGrammarByHeight`, ⟺ RH par `grammarByHeight_iff_riemannHypothesis` ; hauteurs positives; selon l'énoncé : Sous la condition « a et b sont deux membres consécutifs ») : `consecutivePairArithmeticChain`, `consecutive_continuous_signature`, `grammar_determines_stop_ray`, `reached_progression`.

#### V57 — Compilé : la place avance de un et l'occurrence avance sur tout passage, que la hauteur avance ou non ; sur la ligne la hauteur avance. (§7, l. 77)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `eventIndex_succ_of_passage`, `passage_event_increment`, `rank_grammar_unconditional`, `grammar_hypotheses_of_passage`, `passage_heightEventIndex_dichotomy`) et provoque la série de conséquences suivantes : `onLine_clock_sync` (Sur un passage dont les deux extrémités sont sur la ligne critique, l'index de membre et l'index de…) ; `interTowerExcess_pos_of_grammar_iff_riemannHypothesis` (Ajouter les trois hypothèses grammaticales à « excès strictement positif » ne change rien : l'énonc…) ; `off_clock_slip` (Pour un zéro hors ligne, il existe un passage où l'horloge des membres avance de un, celle des haut…) ; `off_event_increment_without_height` (Un zéro hors ligne produit un passage réel de même hauteur, dont la place avance de un, dont l'occu…) ; `onLine_passage_shares_grammar_context` (Un passage ON partage toute la grammaire (place +1, raccord, occurrence croissante), sa hauteur pro…) ; `passage_double_constraint` (Sur tout passage : Occ(l) = p_min(e), Occ(e) < Occ(l), le later tient Occ(l) dans sa cellule, l'ear…) ; et 2 autre(s) : `passage_raccords`, `regime_captive_of_prime`. Cas restreints, confirmés sous condition (passage dont les deux extrémités sont sur la ligne critique; pour un zéro hors ligne; passage dont les deux extrémités sont sur la ligne ; hauteurs positives; selon l'énoncé : Sur un passage dont les deux extrémités sont sur la ligne critique) : `passage_height_lt_of_onLine`, `off_event_increment_without_height`, `rank_grammar_forces_no_displacement`, `offPassage_full_context`, `onLine_passage_shares_grammar_context`, `off_excess_zero`, `onLine_clock_sync`. Touchée aussi (sans l'établir) par : `passage_height_lt_of_riemannHypothesis`.

#### V58 — L'énoncé « la place avance donc la hauteur avance », pris sur tout passage ou sur les seuls passages à extrémité hors ligne, est RH elle-même. (§7, l. 77)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `passage_height_lt_of_riemannHypothesis`) et provoque la série de conséquences suivantes : `grammar_forces_mode_A` (Sous la grammaire par hauteurs, tout passage est en « mode A » (terme hors maître : hauteurs strict…) ; `heightProgression_iff_riemannHypothesis` (« La place avance donc la hauteur avance », sur tout passage de membres supérieurs, est équivalent…) ; `noNullPassage_iff_riemannHypothesis` (L'absence de passage nul est équivalente à RH.). Cas restreints, confirmés sous condition (prémisse `PGrammarByHeight` (index par membres = index par hauteurs pour tout zéro), ⟺ RH par `grammarByHeight_iff_riemannHypothesis` ; hauteurs positives; prémisse `PGrammarByHeight`, ⟺ RH par `grammarByHeight_iff_riemannHypothesis`; selon l'énoncé : Pour un zéro hors ligne) : `grammar_forces_displacement`, `grammar_forces_mode_A`, `off_clock_slip`. Équivalences/implications RH liées (caractérisations, jamais vérité acquise) : `heightProgression_iff_riemannHypothesis`, `offPassages_heightProgression_iff_riemannHypothesis`, `displacement_forced_iff_grammarByHeight`, `interTowerExcess_pos_iff_riemannHypothesis`, `offPassages_interTowerExcess_pos_iff_riemannHypothesis`, `interTowerExcess_pos_of_grammar_iff_riemannHypothesis`, `noNullPassage_iff_heightProgression`, `riemannHypothesis_of_PHeightProgression`. Touchée aussi (sans l'établir) par : `nullPassage_offLine`, `off_event_increment_without_height`, `rank_grammar_forces_no_displacement`.

#### V59 — La grammaire par hauteurs de la base (une hauteur, un événement) coïncide avec la grammaire par membres si et seulement si RH. (§7, l. 77)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `sourceIndex_eq_heightEventIndex_of_riemannHypothesis`, `passage_heightEventIndex_dichotomy`, `clock_h_le_n`, `clock_ph_eq`) et provoque la série de conséquences suivantes : `clock_ph_le_pn` (Le premier de l'horloge des hauteurs est inférieur ou égal à celui de l'horloge des membres.) ; `grammarsAgree_iff_riemannHypothesis` (Les deux grammaires (par membres, par hauteurs) coïncident sur tout zéro si et seulement si RH.) ; `off_clock_slip` (Pour un zéro hors ligne, il existe un passage où l'horloge des membres avance de un, celle des haut…) ; `onLine_clock_sync` (Sur un passage dont les deux extrémités sont sur la ligne critique, l'index de membre et l'index de…). Cas restreints, confirmés sous condition (pour un zéro hors ligne; prémisse `PGrammarByHeight` (index par membres = index par hauteurs pour tout zéro), ⟺ RH par `grammarByHeight_iff_riemannHypothesis` ; hauteurs positives; prémisse `PGrammarByHeight`, ⟺ RH par `grammarByHeight_iff_riemannHypothesis`; prémisse `PGrammarByHeight`, ⟺ RH par `grammarByHeight_iff_riemannHypothesis` ; hauteurs positives) : `off_heightEventIndex_lt_sourceIndex`, `grammar_forces_displacement`, `grammar_forces_mode_A`, `grammar_determines_stop_ray`. Équivalences/implications RH liées (caractérisations, jamais vérité acquise) : `grammarsAgree_iff_riemannHypothesis`, `occurrences_agree_iff_riemannHypothesis`, `displacement_forced_iff_grammarByHeight`, `grammarByHeight_iff_riemannHypothesis`, `clock_agree_iff_riemannHypothesis`, `grammarsAgree_all_iff_pastOnLine_all`, `pastOnLine_all_iff_riemannHypothesis`. Touchée aussi (sans l'établir) par : `heightEventIndex_le_sourceIndex`, `memberHeightTransport_iff_index`.

#### V60 — Il ne faut jamais décorréler la grammaire des zéros de la grammaire première : elles sont liées indéfectiblement. (§7, l. 79)
- Verdict : Cette vérité est caractérisée seulement (équivalente à RH ou impliquant RH) (théorèmes : `grammarsAgree_iff_riemannHypothesis`, `grammarsAgree_all_iff_pastOnLine_all`, `passage_event_increment`) : la liaison des deux grammaires comme égalité partout est `(∀ z, nZeroSourceIndex ↑z = nZeroHeightEventIndex (tZeroHeightEvent z)) ↔ RiemannHypothesis` ; sur tout passage la liaison par le rang tient (`passage_event_increment`) ; la partie normative (« il ne faut jamais ») reste hors code (révision B6)

#### V61 — Il y a des sauts mais un premier unique à pointer dans chaque intervalle, sans choix ; cette obligation fait que deux zéros doivent pointer des événements de la grammaire première et impose la règle du pivot pour tous les zéros. (§7, l. 79)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `tower_reads_any_prime`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve).

#### V62 — Hors droite critique, la symétrie fonctionnelle produit un second vrai zéro distinct ; les points clés sont ceux de zeta23. (§8, l. 83 (aussi l. 135))
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `zetaReflect_eq_mirrorSupport`, `zeta_reflect_zero`, `upperMirror_support_eq_reflect`, `zeta_functionalReflect_zero`, `reflectedZero_isZero`, `quartet_chain`, `radialOffset_eq_zero_iff_reflect_fixed`, `zetaReflect_eq_self_iff`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve).

#### V63 — D'un zéro hors ligne naissent quatre zéros de même multiplicité : ρ, son conjugué, son miroir fonctionnel (1 − conjugué), et le zéro réfléchi (1 − ρ, conjugué du miroir). (§8, l. 83 (aussi l. 135, l. 227))
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `analyticOrderAt_zeta_conj`, `analyticOrderAt_zeta_one_sub`, `zeta_reflect_zero`, `analyticOrderAt_zeta_reflect`, `zeta_mult_reflect`, `mirror_multiplicity`, `upperMirror_multiplicity`, `ZeroConfig.reflect_mem`, `ZeroConfig.mult_reflect`, `zetaFunctionalReflect_eq_conj_reflect`, `zetaFunctionalReflect_re`, `zetaFunctionalReflect_im`, `zeta_functionalReflect_zero`, `zeta_mult_functionalReflect`, `functionalReflect_support_eq_conj_mirror`, `functionalReflect_im_eq_neg_mirror`, `reflectedZero_support`, `reflectedZero_isZero`, `reflectedZero_re`, `reflectedZero_im`, `quartet_chain`) et provoque la série de conséquences suivantes : `functionalReflect_re_eq_mirror` (La partie réelle du zéro réfléchi est la position radiale (1−β) du miroir supérieur.) ; `reflectedZero_not_member` (Pour tout zéro, le zéro réfléchi 1 − ρ a une partie imaginaire strictement négative : il n'est jama…) ; `reflected_transition_content` (Sous la condition « z de côté bas » : le quartet, le trajet renversé, la transition canonique du mi…). Cas restreints, confirmés sous condition (selon l'énoncé : Sous la condition « z de côté bas ») : `reflected_transition_content`. Touchée aussi (sans l'établir) par : `conj_zetaReflect`, `zetaReflect_eq_conj`.

#### V64 — L'énumération de la source ne compte que les zéros de partie imaginaire positive ; parmi les quatre, deux sont membres (le zéro et son miroir) et portent deux événements distincts successifs ; les deux conjugués reprennent l'événement de leur membre. (§8, l. 83)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `reflectedZero_not_member`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve). Cas restreints, confirmés sous condition (selon l'énoncé : Pour un zéro hors ligne; selon l'énoncé : Sous consécutivité stricte; selon l'énoncé : Pour β < 1/2 et consécutivité stricte; selon l'énoncé : Sous la condition « z de côté bas ») : `off_mirror_same_frequency`, `off_mirror_same_frequency_of_consecutive`, `off_consecutive_translation_signature`, `mirror_consumes_member_index`.

#### V65 — Le miroir a la même partie imaginaire que le zéro, partie réelle complément à un, même multiplicité ; cette contrainte est créée par zêta et compilée. (§8, l. 85)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `mirrorMember_ordinate`, `mirrorMember_radial`, `mirrorMember_mirrorMember_radial`, `zetaReflect_eq_mirrorSupport`, `zetaReflect_re`, `zetaReflect_im`, `analyticOrderAt_zeta_reflect`, `zeta_mult_reflect`, `mirror_multiplicity`, `upperMirror_multiplicity`, `upperMirror_support_eq_reflect`, `functionalReflect_re_eq_mirror`, `mirror_ordinate`, `mirror_beta`, `mirror_radial_shift`, `mirror_radial_shift_eq_zero_iff`, `mirror_phase_increment_eq`, `mirror_span_eq`, `explicitIndex_mirror_im`) et provoque la série de conséquences suivantes : `fiberSuccessor_radial_le_mirror` (Un successeur consécutif de même hauteur ne dépasse pas le miroir (β(z') ≤ 1−β(z)).) ; `grammarsAgree_at_iff_onLine_below` (Pour tout zéro z : l'index par membres n(z) égale l'index par hauteurs h(z) si et seulement si tout…) ; `mirrorMember_eq_self_of_onLine` (Sur la droite critique, le membre miroir est le zéro lui-même.) ; `mirrorMember_phase` (La phase de la Tour propre du membre miroir est φ* = arctan(T/(1−β)).) ; `mirror_contact_eq_iff_onLine` (Le contact `C_k` du membre miroir coïncide avec celui de `z` si et seulement si `z` est sur la lign…) ; `mirror_phase` (La phase de la Tour propre du miroir supérieur est arctan(T/(1−β)) : mêmes formules appliquées à se…) ; et 26 autre(s) : `off_consecutive_translation_signature`, `off_mirror_same_frequency`, `radialOffset_eq_zero_iff_reflect_fixed`, `weilPairTerm_off_neg`, `weilPairTerm_test_eq`, `zetaReflect_centeredPoint`, `zetaReflect_eq_self_iff`, `consecutive_continuous_signature`, `exists_fiberSuccessor`, `fiberSuccessor_ordinate_eq`, `mirrorMember_contactMinusAt`, `mirrorMember_contactPlusAt`, `mirrorMember_ne`, `mirror_contact_ratio_const`, `mirror_degeneracy_of_onLine`, `mirror_degeneracy_tfae`, `mirror_grid_never_coincides`, `mirror_horizontal_tension_eq_zero_iff`, `mirror_net_horizontal_force_zero`, `mirror_phase_gap_eq_arctan`, `mirror_phase_lt`, `off_consecutive_continuous_progression_eq_span`, `onLine_mirror_trivial`, `reflectedZero_re` …. Cas restreints, confirmés sous condition (zéro de côté bas (β<1/2); consécutivité stricte du zéro et de son miroir) : `mirror_radial_gt`, `consecutive_continuous_signature`. Touchée aussi (sans l'établir) par : `mirror_radialOffset`, `mirror_radialOffset_sq`, `pair_same_conditions`.

#### V66 — Cette contrainte rend nulle la progression de T entre les deux zéros de la paire (le suivant d'un OFF est son miroir) et donne deux parties réelles dont l'une est un moins l'autre ; ce n'est pas une nullité de T mais de sa progression. (§8, l. 85)
- Verdict : Cette vérité est confirmée sous condition (zéro de côté bas) (autres hypothèses : antécédents de la relation énoncée ou conditions de domaine : z' consécutif à z; zéro de côté bas (β<1/2); pour un zéro hors ligne; selon l'énoncé : Pour un zéro hors ligne) (théorèmes : `fiberSuccessor_ordinate_eq`, `exists_fiberSuccessor`, `offPassage_full_context`, `off_clock_slip`) et provoque la série de conséquences suivantes : `radial_gt_of_consecutive_lowerSide` (Pour un zéro de côté bas, tout successeur consécutif a une position radiale strictement supérieure.) ; `radial_le_mirror_of_consecutive_lowerSide` (Pour un zéro de côté bas, tout successeur consécutif a une position radiale au plus 1−β.) ; `riemannHypothesis_of_verticalEnergyPush` (PVerticalEnergyPush (l'énergie du later n'excède jamais celle de l'earlier en q ≥ 1) entraîne RH.). Touchée aussi (sans l'établir) par : `nullPassage_offLine`, `off_event_increment_without_height`, `nullPassage_horizontal`, `off_excess_zero`.

#### V67 — Le miroir possède sa Tour propre par le même mécanisme que tout zéro (formules identiques appliquées à ses coordonnées) ; original et miroir = deux zéros, deux couples, deux Tours ; la Tour du miroir n'est jamais construite à partir de la première. (§8, l. 87)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `mirrorMember_phase`, `mirrorMember_contactMinusAt`, `mirrorMember_contactPlusAt`, `secondTower_ring_eq_mirror_firstTower`, `mirror_phase`) et provoque la série de conséquences suivantes : `contact_lt_mirror_iff` (C_j(z) < C_k(z*) ⟺ j − k < −D (hypothèse de notation c = j − k).) ; `insertionDepth_eq` (D(z) = (arctan(T/β) − arctan(T/(1−β)))/π.) ; `mirror_contact_lt_iff` (Comparaison du rayon k du miroir au rayon j de z : C_k(z*) < C_j(z) ⟺ −D < j − k (hypothèse de nota…) ; `mirror_contacts_interlace` (Pour β < 1/2 et tout k : C_{k−1}(z) < C_k(z*) < C_k(z).) ; `mirror_phase_gap_eq_arctan` (φ_z − φ_{z*} = arctan(T(1−2β)/(β(1−β) + T²)).).

#### V68 — Dans l'ordre d'énumération, le miroir vient strictement après le zéro original ; les deux zéros de la paire sont strictement consécutifs. (§8, l. 89)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `exists_consecutive_predecessor`) et provoque la série de conséquences suivantes : `allOnLine_of_regimeCapture` (Sous PLowestZeroOnLine et PRegimeCapture, tout zéro est sur la ligne (récurrence forte sur l'index).). Cas restreints, confirmés sous condition (zéro de côté bas (β<1/2); paire (z, miroir) strictement consécutive; zéro de côté bas) (autres hypothèses : antécédents de la relation énoncée ou conditions de domaine : z' consécutif à z; zéro de côté bas) (autres hypothèses : antécédents de la relation énoncée ou conditions de domaine : z' consécutif ; aucun membre intercalé entre z et le miroir) : `mirror_precedes`, `sourceIndex_lt_mirror`, `mirror_sourceIndex_of_consecutive`, `mirrorMember_distinct_member`, `fiberSuccessor_ordinate_eq`, `fiberSuccessor_eq_mirror_or_precedes`, `fiberSuccessor_eq_mirror_of_noInterposition`, `exists_fiberSuccessor`, `member_index_lt_of_lowerSide`, `off_member_index_lt_mirror`, `member_index_succ_of_consecutive`, `mirror_occurrence_strict`, `mirror_consumes_member_index`.

#### V69 — Donc l'occurrence du miroir est exactement le minimum attendu du premier zéro. (§8, l. 89 (aussi l. 105))
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `reaches_expected_of_reaches_occurrence`) et provoque la série de conséquences suivantes : `verification_passes` (Sous la condition « a précède b de façon consécutive » : le minimum attendu de a est atteint à l'ét…). Cas restreints, confirmés sous condition (paire (z, miroir) strictement consécutive; zéro de côté bas, β < 1/2 ; consécutivité stricte du zéro et de son miroir; selon l'énoncé : Sous consécutivité stricte) : `expectedMinimum_eq_mirror_occurrence_of_consecutive`, `consecutivePairArithmeticChain`, `off_mirror_same_frequency_of_consecutive`.

#### V70 — Deux événements, deux pivots : pivot de la première Tour = minimum attendu du zéro original = occurrence du miroir ; pivot de la seconde Tour = minimum attendu du miroir, qui suit. (§8, l. 89, l. 91)
- Verdict : Cette vérité est confirmée sous condition (théorèmes : `firstTower_readings`, `secondTowerOf_properState`, `expectedMinimum_eq_mirror_occurrence_of_consecutive`, `expectedMinimum_lt_mirror_expectedMinimum`, `secondTower_readings`) : pivot de la première Tour : `entryCoordinate = pivotCoordinate z ↑(expectedMinimumPrime z)` ; pivot de la seconde : `invertedPivotPair (mirrorMember z) ↑(expectedMinimumPrime (mirrorMember z))` ; sous consécutivité stricte `expectedMinimumPrime z = occurrence (mirrorMember z)` ; sous β<1/2 `expectedMinimumPrime z < expectedMinimumPrime (mirrorMember z)` (le pivot du miroir « suit ») (révision B6)

#### V71 — Les deux Tours du miroir arrêtent leur parcours dans le même anneau (celui du minimum attendu du miroir) et le lisent en sens opposés : la première a pour dernier rayon le croisement du haut, la seconde le croisement du bas. (§8, l. 91, l. 93)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `invertedPivotPair_upright`, `secondTower_ring_eq_mirror_firstTower`, `mirror_two_towers_same_ring`, `invertedPairAt_upright`, `trajectory_reversal`) et provoque la série de conséquences suivantes : `invertedPivotPair_entryCoordinate` (La coordonnée d'entrée de la paire inversée du pivot est celle du rayon du haut, k+1.) ; `invertedPivotPair_stageCount` (Le nombre d'étages de la paire inversée du pivot vaut un.).

#### V72 — Le mouvement réfléchi n'a aucun événement d'arrêt depuis sa propre origine, ses rayons descendant sous un dès le premier pas ; l'événement d'arrêt de la seconde Tour est celui du membre miroir sur son pivot ; l'orientation ne décide que du rôle des deux rayons. (§8, l. 91 (aussi l. 139 E086, l. 159))
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `reflected_lastRay_lt_one`, `reflected_no_stop_event`, `invertedPairAt_coordinate_le_zero`, `properTowerOfMirror_and_reflectedMotion_coexist`, `reflected_reads_no_prime`, `reflected_mirror_reads_nothing`, `reflection_creates_no_prime_event`) et provoque la série de conséquences suivantes : `reflectedFromOrigin_never_reaches_expectedMinimum` (Le mouvement réfléchi du membre miroir, suivi depuis son origine (j ≥ 1), n'atteint jamais le minim…) ; `reflectedReading_iff_noLowerSide` (Exiger de tout zéro de côté bas que le mouvement réfléchi de son miroir atteigne l'occurrence du mi…) ; `reflected_blocked_onLine` (Pour un zéro de la ligne, le mouvement réfléchi n'atteint pas son occurrence.). Cas restreints, confirmés sous condition (β = 1/2; zéro de côté bas ; consécutivité stricte du zéro et de son miroir) : `reflectedFromOrigin_never_reaches_expectedMinimum_beta_blind`, `arithmeticChain_and_reflectedFromOrigin_coexist`. Équivalences/implications RH liées (caractérisations, jamais vérité acquise) : `riemannHypothesis_of_hReaches_is_vacuous`. Réfutations compilées liées : `reflectedFromOrigin_never_reaches_expectedMinimum`, `reflectedStopSet_own_expectedMinimum_eq_empty`, `no_reflectedStopCoordinate_own_expectedMinimum`, `terminalCollision_conditional_on_reflectedObligation`.

#### V73 — Le lien (β,T) → événements existe par l'obligation liant les deux grammaires ; il n'est évaluable sur aucun zéro hors ligne (aucun ne se calcule), il est lu dans la chaîne jamais calculé. (§8, l. 93)
- Verdict : Cette vérité est caractérisée seulement (équivalente à RH ou impliquant RH) (théorèmes : `grammarsAgree_iff_riemannHypothesis`, `off_mirror_two_grammars`, `consecutivePairArithmeticChain`, `AnalyticContactPair.recovers_beta`) : l'obligation liant les deux grammaires est `(∀ z, nZeroSourceIndex ↑z = nZeroHeightEventIndex (tZeroHeightEvent z)) ↔ RiemannHypothesis` ; hors ligne les deux grammaires diffèrent (`occurrence (mirrorMember z) ≠ occurrence z` avec `nHeightEventMZOccurrence` égaux) ; `recovers_beta` : β est lu depuis les contacts ; la non-évaluabilité sur un zéro hors ligne est épistémique (hors code) (révision B6)

#### V74 — Hors ligne, le miroir est un membre authentique et distinct : vrai zéro, différent, strictement postérieur, d'index avancé, d'occurrence au moins le minimum attendu ; « tout cela est théorème ». (§8, l. 93)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `zeta_reflect_zero`) et provoque la série de conséquences suivantes : `zeta_functionalReflect_zero` (La réflexion ρ ↦ 1−ρ envoie un vrai zéro sur un vrai zéro (équation fonctionnelle et conjugaison) :…). Cas restreints, confirmés sous condition (zéro de côté bas (β<1/2); selon l'énoncé : Pour un zéro de côté bas (β < 1/2); selon l'énoncé : Pour un zéro hors ligne; selon l'énoncé : Sous la condition « z de côté bas ») : `mirror_precedes`, `sourceIndex_lt_mirror`, `expectedMinimum_le_mirror_occurrence`, `mirrorMember_ne`, `mirrorMember_distinct_member`, `member_index_lt_of_lowerSide`, `off_member_index_lt_mirror`, `mirror_occurrence_strict`, `mirror_consumes_member_index`.

#### V75 — Sa première Tour (sens croissant) lit l'histoire jusqu'à son occurrence : théorème, liaison portée par cette Tour. (§8, l. 93 (aussi l. 105, l. 107, l. 137))
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `firstTower_reaches_occurrence`, `mirrorMember_firstTower_reaches_occurrence`, `mirror_ownTower_reads`, `reaches_occurrence`, `upright_presents_forward`) et provoque la série de conséquences suivantes : `mirror_two_towers_same_ring` (Les deux Tours du membre miroir lisent le même anneau en sens opposés : la première lit son occurre…) ; `reached_progression` (Sous la condition « a et b sont deux membres consécutifs » : l'occurrence de b est le minimum atten…) ; `verification_passes` (Sous la condition « a précède b de façon consécutive » : le minimum attendu de a est atteint à l'ét…). Cas restreints, confirmés sous condition (zéro sur la droite critique (β=1/2)) : `lineTower_reaches_occurrence`.

#### V76 — La seconde Tour du miroir pivote sur le même pivot que sa première Tour (son propre minimum attendu) depuis l'orientation opposée ; les deux Tours du membre lisent le même anneau en sens opposés ; la seconde a pour dernier rayon le croisement du bas. (§8, l. 93)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `secondTowerOf_properState`, `secondTower_ring_eq_mirror_firstTower`, `secondTower_coordinate_eq_unique_mirrorContactPair`, `secondTower_cell_contains_own_expected`, `mirror_two_towers_same_ring`) et provoque la série de conséquences suivantes : `reflected_presents_reversed` (Pour tout zéro z, sur l'anneau du membre miroir, la seconde Tour a une entrée au moins égale à p_mi…) ; `secondTowerOwnContacts_meets_arithmeticChain` (Sous ces conditions, l'entrée de la seconde Tour de `z` dépasse strictement l'occurrence du miroir,…) ; `secondTower_entry_reaches_own_expected` (Dans la seconde orientation, le contact qui atteint le pivot propre est l'entrée (p_min(z*) ≤ entré…).

#### V77 — Sur la droite, le zéro et son miroir sont confondus ; la seconde orientation y est la Tour du conjugué, sur le même anneau, lue par le bas : rien ne se contredit. (§8, l. 93 (aussi l. 105))
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `radialOffset_eq_zero_iff_fixed`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve). Cas restreints, confirmés sous condition (zéro sur la droite critique (β=1/2); selon l'énoncé : Sur la ligne (β = 1/2); selon l'énoncé : Sur la ligne; selon l'énoncé : Pour un zéro de la ligne) : `mirrorMember_eq_self_of_onLine`, `firstTowerOf_eq_lineTowerOf`, `lineTowerOf_properState`, `mirror_phase_shift_eq_zero_of_onLine`, `mirror_contacts_eq_of_onLine`, `mirror_degeneracy_of_onLine`, `onLine_mirror_trivial`, `reflected_blocked_onLine`, `explicitIndex_mirror_eq_of_onLine`.

#### V78 — Aucune question n'est posée à la géométrie du miroir prise seule : les contacts d'une Tour ne sont pas libres, calculés depuis le pivot, qui est l'événement premier que le zéro doit pointer. (§8, l. 93)
- Verdict : Cette vérité est confirmée (théorèmes : `pivotPair_entryContact`, `pivotPair_lastRayContact`, `firstTower_contactPair_unique`, `pivotCoordinate_unique`, `secondTower_coordinate_eq_unique_mirrorContactPair`, `AnalyticContactPair.ext_readings`) : les contacts ne sont pas libres : `pivotPair_entryContact z q = exp ((phase + pivotCoordinate z q·π)/T)` et `contactMinusAt z k < q → q ≤ contactPlusAt z k → k = pivotCoordinate z q` ; la coordonnée de `secondTowerOf z` est celle de la Tour propre de `mirrorMember z` (`… entryCoordinate - 1 = (firstTowerOf (mirrorMember z)).properState.entryCoordinate`) (révision B6)

#### V79 — Deux informations distinctes au miroir : son ancre canonique (prochaine occurrence prévue, propre) et l'obligation de progression minimale (minimum attendu du précédent, héritée) ; elles sont ou ne sont pas égales, sans contradiction. (§8, l. 95)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `occurrence_eq_canonicalAnchor`) et provoque la série de conséquences suivantes : `clock_pn_eq` (Le premier lu par l'horloge des membres est le premier de rang n (ancre canonique).) ; `memberHeightTransport_iff_index` (Pour tout zéro w, le transport « occurrence membre = occurrence de l'événement de hauteur » en w éq…) ; `occurrence_eq_primeAtRank` (L'occurrence d'un zéro est le premier de rang égal à son index zéro-source.) ; `occurrence_lt_expectedMinimumPrime` (L'occurrence d'un zéro est strictement inférieure à son minimum attendu.) ; `occurrence_strict_of_passage` (Sur tout passage (membres supérieurs), l'occurrence du membre antérieur est strictement inférieure…) ; `occurrence_successor_of_passage` (Sur tout passage, l'occurrence du membre postérieur est le premier successeur de l'index zéro-sourc…) ; et 3 autre(s) : `occurrences_agree_iff_riemannHypothesis`, `off_mirror_two_grammars`, `passage_span_eq_log_occurrences`.

#### V80 — La seconde Tour est la Tour du zéro 1 − ρ = (1 − β, −T), conjugué du miroir supérieur ; mêmes formules tangentielles ⇒ phase −φ* et pas −π/T ; elle parcourt le même événement premier en orientation opposée ; ses contacts sont ceux du miroir supérieur, rôles échangés (entrée C_{k₂+1} en haut, dernier rayon C_{k₂} en bas). (§8, l. 95)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `invertedPivotPair_entryCoordinate`, `mirrorMember_phase`, `mirrorMember_contactMinusAt`, `mirrorMember_contactPlusAt`, `secondTower_entry_eq_incidence`, `secondTower_lastRay_eq_incidence`, `secondTower_entry_eq_reflected`, `secondTower_lastRay_eq_reflected`, `secondTower_readings`, `secondTower_coordinate_eq_unique_mirrorContactPair`, `zetaFunctionalReflect_eq_conj_reflect`, `zetaFunctionalReflect_re`, `zetaFunctionalReflect_im`, `functionalReflect_support_eq_conj_mirror`, `functionalReflect_re_eq_mirror`, `functionalReflect_im_eq_neg_mirror`, `mirror_phase`, `reflectedPhase_eq_neg`, `reflectedLogIncidence_eq`, `reflectedIncidence_eq`, `reflected_step`, `reflectedIncidence_antitone`, `reflected_entry_eq_contactPlus`, `reflected_lastRay_eq_contactMinus`, `invertedPairAt_eq_reflected`, `ReflectedMotion.phase_eq`, `ReflectedMotion.logIncidence_eq`, `ReflectedMotion.incidence_eq`, `reflectedMotion_incidence`, `reflectedZero_support`, `reflectedZero_re`, `reflectedZero_im`, `secondTower_inversion_is_unconditional`, `trajectory_reversal`, `reflection_reverses_existing_ring`, `reflected_presents_via_functional_reflect`) et provoque la série de conséquences suivantes : `zeta_functionalReflect_zero` (La réflexion ρ ↦ 1−ρ envoie un vrai zéro sur un vrai zéro (équation fonctionnelle et conjugaison) :…) ; `contact_lt_mirror_iff` (C_j(z) < C_k(z*) ⟺ j − k < −D (hypothèse de notation c = j − k).) ; `insertionDepth_eq` (D(z) = (arctan(T/β) − arctan(T/(1−β)))/π.) ; `mirror_contact_lt_iff` (Comparaison du rayon k du miroir au rayon j de z : C_k(z*) < C_j(z) ⟺ −D < j − k (hypothèse de nota…) ; `mirror_contacts_interlace` (Pour β < 1/2 et tout k : C_{k−1}(z) < C_k(z*) < C_k(z).) ; `mirror_phase_gap_eq_arctan` (φ_z − φ_{z*} = arctan(T(1−2β)/(β(1−β) + T²)).) ; et 5 autre(s) : `quartet_chain`, `reflectedZero_not_member`, `reflected_lastRay_lt_one`, `reflected_transition_content`, `zeta_mult_functionalReflect`. Cas restreints, confirmés sous condition (selon l'énoncé : Sous la condition « z de côté bas ») : `reflected_transition_content`.

#### V81 — Le miroir supérieur tourne dans le même sens (β ↦ 1−β seul ne renverse rien). (§8, l. 95)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `mirror_step_positive`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve).

#### V82 — La seconde Tour pivote sur son propre minimum attendu ; entrée = croisement au-dessus du pivot, dernier rayon = croisement au-dessous ; théorème. (§8, l. 95)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `invertedPivotPair_cell_contains`, `invertedPivotPair_lastRay_lt_pivot`, `invertedPivotPair_not_reaches`, `invertedPivotPair_not_reaches_of_le`, `secondTowerOf_properState`, `secondTower_entry_eq_incidence`, `secondTower_lastRay_eq_incidence`, `secondTower_cell_contains_own_expected`, `secondTower_entry_reaches_own_expected`, `InvertedContactPair.ordered`, `invertedPairAt_eq_reflected`, `secondTower_inversion_is_unconditional`, `reflected_presents_reversed`) et provoque la série de conséquences suivantes : `secondTowerOwnContacts_meets_arithmeticChain` (Sous ces conditions, l'entrée de la seconde Tour de `z` dépasse strictement l'occurrence du miroir,…) ; `secondTower_entry_eq_reflected` (L'entrée de la seconde Tour est l'entrée du zéro réfléchi à sa coordonnée −(k₂+1) : l'inversion est…) ; `secondTower_entry_reaches_mirror_occurrence` (À l'entrée, la seconde Tour atteint l'occurrence du membre miroir (Occ(z*) < p_min(z*) ≤ entrée), s…) ; `secondTower_lastRay_eq_reflected` (Le dernier rayon de la seconde Tour est le rayon suivant du zéro réfléchi à la coordonnée −(k₂+1)+1.) ; `secondTower_not_reaches_own_expected` (La seconde Tour, lue à son dernier rayon, n'atteint jamais son pivot propre p_min(z*).). Cas restreints, confirmés sous condition (zéro de côté bas ; consécutivité stricte du zéro et de son miroir) : `secondTowerOwnContacts_meets_arithmeticChain`.

#### V83 — Rien ne vient de la progression de T, nulle entre les deux zéros de la paire. (§8, l. 95)
- Verdict : Cette vérité est confirmée (théorèmes : `mirror_ordinate`, `off_consecutive_translation_signature`, `off_event_increment_without_height`, `mirror_sameHeightEvent`) : `rZeroHeight ↑(mirrorMember z) = rZeroHeight ↑z` (inconditionnel) ; sous consécutivité stricte et β<1/2 : hauteurs égales, `nZeroHeightEventIndex` égaux, `TowerPrimeGapSpan` égales, accroissements de phase égaux : aucune progression de T entre les deux zéros de la paire (révision B6)

#### V84 — Le constat de vérification (dernier rayon sous le minimum attendu du zéro original) est un constat lu ; il tient exactement lorsque le minimum attendu du zéro original tombe dans le même anneau du miroir que le minimum attendu du miroir. (§8, l. 95 (aussi l. 107, l. 137))
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `InvertedContactPair.not_reaches_iff`, `InvertedContactPair.not_reaches_of_lastRay_lt`, `mirror_counted_lt_expected_iff`, `countedPrimeAt_lt_expected_of_contact`, `authorForm_iff_counted_lt`, `lock_imp_pivot_lt_expected`, `not_reaches_iff`, `not_reaches_of_lastRay_lt`, `not_reaches_expected_of_lastRay_lt`, `countedPrime_ne_expected_iff_cell`, `reads_expected_imp_ne_previous_expected`, `countedPrime_lt_expected_of_lastRay`, `expectedMinimum_le_produced_iff`, `produced_lt_expectedMinimum_iff`) et provoque la série de conséquences suivantes : `invertedPivotPair_not_reaches` (Dans la seconde orientation, le pivot n'est jamais compté au dernier rayon (rayon du bas de son ann…) ; `secondTower_verification_iff_not_reads_of_consecutive` (Sous consécutivité stricte, le constat de vérification (dernier rayon < p_min(z)) équivaut à la nég…). Cas restreints, confirmés sous condition (paire (z, miroir) strictement consécutive; zéro de côté bas (β<1/2); zéro de côté bas) (autres hypothèses : antécédents de la relation énoncée ou conditions de domaine : rang compté > 0 ; la paire n'atteint pas p_min(z)) : `secondTower_verification_iff_not_reads_of_consecutive`, `pivotCell_mirror_reaches_expected`, `lock_imp_counted_lt_occurrence`.

#### V85 — Le constat de lecture (seconde Tour lit l'occurrence) tient exactement lorsque l'occurrence est dans un anneau strictement inférieur à celui du minimum attendu du miroir : constat lu, non un théorème (au sens lecture inconditionnelle). (§8, l. 93)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `secondTower_reads_occurrence_iff_coordinate_lt`, `mirror_two_towers_same_ring`, `countedPrime_eq_occurrence_iff_cell`, `reads_expected_imp_not_occurrence`, `reads_expected_imp_ne_previous_expected`, `remaining_open_question_is_readout_only`, `secondTower_reads_iff_progression_pos`) et provoque la série de conséquences suivantes : `countedPrime_ne_expected_iff_cell` (Forme cellule du constat de vérification au successeur z' de z : premier compté ≠ p_min(z) ⟺ C⁺(S')…) ; `secondTower_reads_of_gap_ge_pi` (Si π ≤ T·log(p_min(z*)/Occ(z*)), la seconde Tour lit l'occurrence du miroir (condition suffisante p…). Cas restreints, confirmés sous condition (selon l'énoncé : Si π ≤ T·log(p_min(z*)/Occ(z*))) : `secondTower_reads_of_gap_ge_pi`. Touchée aussi (sans l'établir) par : `secondTowerOwnContacts_meets_arithmeticChain`.

#### V86 — Le comptage seul décide et constate au dernier rayon le dernier premier atteint. (§8, l. 95)
- Verdict : Cette vérité est confirmée (théorèmes : `countedPrime_eq_vonMangoldt`, `reaches_iff_le_countedPrime`, `countedPrime_le_lastRay`, `not_reaches_iff`) : `countedPrime S = fnPrimeAtRank (nPrimeCountingFromJ rChebyshevJNat ⌊S.lastRayContact⌋₊ - 1)` (le comptage au dernier rayon) et `reaches S p ↔ p ≤ countedPrime S` ; `¬reaches S p ↔ S.lastRayContact < ↑p` (révision B6)

#### V87 — Pour chacune des deux Tours : produire les deux contacts par la règle du pivot, appliquer le comptage jusqu'au dernier rayon, confronter à la même référence (le minimum attendu du zéro original, défini par la seule progression première). (§9, l. 101)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V88 — Première Tour, référence effective : avec ses contacts propres, la Tour du zéro original atteint le minimum attendu ; conséquence de la règle du pivot ; la première Tour lit aussi l'histoire jusqu'à son occurrence. (§9, l. 103 (aussi l. 133))
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `firstTower_reaches_expected`, `firstTower_reaches_occurrence`, `pivotPair_reaches`, `pivotPair_reaches_of_le`, `reaches_expected_of_le_lastRay`, `mirror_ownTower_reads`, `reaches_expected`, `reaches_occurrence`, `upright_presents_forward`) et provoque la série de conséquences suivantes : `lineTower_reaches_expected` (Sur la droite, la Tour atteint le minimum attendu de son zéro (par construction de la règle).) ; `mirrorMember_firstTower_reaches_occurrence` (La première Tour du membre miroir lit son occurrence (la liaison portée par cette Tour).) ; `pivotPair_mirror_reaches_of_ge` (Toute référence q ≥ p_min(z) posée sur la Tour du miroir donne p_min(z) atteint.) ; `pivot_countedRank_pos` (Le rang compté au dernier rayon de la cellule d'une référence première est strictement positif.) ; `pivot_le_counted` (La cible constatée (dernier premier compté au dernier rayon) est au moins la référence : elle peut…) ; `reached_progression` (Sous la condition « a et b sont deux membres consécutifs » : l'occurrence de b est le minimum atten…) ; et 1 autre(s) : `verification_passes`. Cas restreints, confirmés sous condition (zéro sur la droite critique (β=1/2); selon l'énoncé : Sous la condition « a et b sont deux membres consécutifs »; selon l'énoncé : Sous la condition « a précède b de façon consécutive ») : `lineTower_reaches_expected`, `lineTower_reaches_occurrence`, `reached_progression`, `verification_passes`.

#### V89 — Sur les quinze zéros publiés, ce constat est vérifié pour chacun. (§9, l. 103)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V90 — Le miroir étant postérieur, son occurrence est le minimum attendu du premier zéro (ce que la progression impose). (§9, l. 105)
- Verdict : Cette vérité est confirmée sous condition (théorèmes : `expectedMinimum_eq_mirror_occurrence_of_consecutive`, `progression_occurrence`, `expectedMinimum_le_mirror_occurrence`, `consecutivePairArithmeticChain`) : `PZeroMembersConsecutive ↑z ↑(mirrorMember z) → expectedMinimumPrime z = occurrence (mirrorMember z)` (consécutivité stricte) ; sous β<1/2 seulement `expectedMinimumPrime z ≤ occurrence (mirrorMember z)` (révision B6)

#### V91 — La lecture de la seconde Tour n'est pas un théorème de la géométrie de la seconde Tour, qui la rend équivalente à une position de l'occurrence dans ses anneaux ; elle est imposée par la liaison des deux grammaires. (§9, l. 105)
- Verdict : Cette vérité est confirmée (théorèmes : `secondTower_reads_occurrence_iff_coordinate_lt`, `mirror_two_towers_same_ring`, `secondTower_reads_iff_progression_pos`, `remaining_open_question_is_readout_only`) : `(secondTowerOf z).properState.reaches (occurrence (mirrorMember z)) ↔ pivotCoordinate (mirrorMember z) ↑(occurrence (mirrorMember z)) < pivotCoordinate (mirrorMember z) ↑(expectedMinimumPrime (mirrorMember z))` : la lecture est exactement une position d'anneau. Partie « imposée par la liaison des deux grammaires » NON transcrite (aucun théorème ne force la lecture ; CLAUDE.md §4 ; sa forme universelle est `reflectedReading_iff_noLowerSide`, ⟺ RH) (révision B6)

#### V92 — Sur la droite, la seconde orientation est la Tour du conjugué sur le même anneau lu par le bas : rien ne l'oblige à lire. (§9, l. 105)
- Verdict : Cette vérité est confirmée sous condition (théorèmes : `mirrorMember_eq_self_of_onLine`, `secondTower_ring_eq_mirror_firstTower`, `secondTower_reads_occurrence_iff_coordinate_lt`, `reflected_blocked_onLine`) : sous β=1/2 : `mirrorMember z = z` ; `(secondTowerOf z).properState.upright = (firstTowerOf (mirrorMember z)).properState` (même anneau, lu à rebours) ; la lecture n'est équivalente qu'à une position d'anneau (rien ne l'oblige) ; la réflexion authentique sur la droite ne lit aucun `occurrence` (`reflected_blocked_onLine`) (révision B6)

#### V93 — Hors ligne, constat de lecture et constat de vérification s'excluent sur le contact terminal de la seconde Tour : théorème, et c'est la collision. (§9, l. 107 (aussi l. 133, l. 137, l. 227))
- Verdict : Cette vérité est confirmée sous condition (paire (z, miroir) strictement consécutive) (théorèmes : `secondTower_verification_iff_not_reads_of_consecutive`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve). Touchée aussi (sans l'établir) par : `expected_le_counted_lt_expected_false`.

#### V94 — Cette exclusion tient pour tout membre postérieur au zéro original, que la hauteur progresse ou non ; la nullité de la progression de T n'y entre que par l'ordre (le miroir est un membre postérieur). (§9, l. 107)
- Verdict : Cette vérité est confirmée sous condition (théorèmes : `countedPrime_ne_expected_iff_cell`, `reads_expected_imp_ne_previous_expected`, `secondTower_verification_iff_not_reads_of_consecutive`) : sous consécutivité (z, z') sans hypothèse sur β ni sur la hauteur : `countedPrime S' ≠ expectedMinimumPrime z ↔ ¬(↑(occurrence z') ≤ S'.lastRayContact ∧ S'.lastRayContact < ↑(expectedMinimumPrime z'))` ; pour la paire miroir : verification ↔ ¬lecture. La version « tout membre postérieur » (non consécutif) n'est pas compilée : `PairHeightGap` retiré (T1) (révision B6)

#### V95 — Sur la droite, le miroir est le membre lui-même : la vérification est un théorème, et la lecture tient exactement quand l'occurrence et le minimum attendu tombent dans deux anneaux distincts. (§9, l. 107)
- Verdict : Cette vérité est confirmée sous condition (théorèmes : `mirrorMember_eq_self_of_onLine`, `secondTower_cell_contains_own_expected`, `secondTower_not_reaches_own_expected`, `secondTower_reads_occurrence_iff_coordinate_lt`, `mirror_two_towers_same_ring`) : sous β=1/2 : `mirrorMember z = z` ; la vérification est automatique (`(secondTowerOf z).lastRayContact < ↑(expectedMinimumPrime (mirrorMember z))`, `¬ … reaches (expectedMinimumPrime (mirrorMember z))`) ; la lecture ↔ `pivotCoordinate … (occurrence …) < pivotCoordinate … (expectedMinimumPrime …)` (deux anneaux distincts) (révision B6)

#### V96 — Compilé : le mouvement réfléchi (zéro de hauteur négative) n'atteint aucun premier depuis son origine, pour tout zéro, sur la droite comme hors ligne ; ce zéro n'est jamais membre. (§9, l. 107)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `reflected_lastRay_lt_one`, `reflected_no_stop_event`, `properTowerOfMirror_and_reflectedMotion_coexist`, `reflected_reads_no_prime`, `reflected_mirror_reads_nothing`, `reflection_creates_no_prime_event`, `reflectedZero_not_member`) et provoque la série de conséquences suivantes : `reflectedFromOrigin_never_reaches_expectedMinimum` (Le mouvement réfléchi du membre miroir, suivi depuis son origine (j ≥ 1), n'atteint jamais le minim…) ; `reflectedReading_iff_noLowerSide` (Exiger de tout zéro de côté bas que le mouvement réfléchi de son miroir atteigne l'occurrence du mi…) ; `reflected_blocked_onLine` (Pour un zéro de la ligne, le mouvement réfléchi n'atteint pas son occurrence.). Cas restreints, confirmés sous condition (β = 1/2; selon l'énoncé : Pour un zéro de la ligne) : `reflectedFromOrigin_never_reaches_expectedMinimum_beta_blind`, `reflected_blocked_onLine`. Équivalences/implications RH liées (caractérisations, jamais vérité acquise) : `riemannHypothesis_of_hReaches_is_vacuous`. Réfutations compilées liées : `reflectedFromOrigin_never_reaches_expectedMinimum`, `reflectedStopSet_own_expectedMinimum_eq_empty`, `no_reflectedStopCoordinate_own_expectedMinimum`, `terminalCollision_conditional_on_reflectedObligation`.

#### V97 — Compilé : le membre miroir a sa Tour propre par la production uniforme et elle lit son occurrence par théorème ; porter sa lecture sur la réflexion et l'exiger de tout zéro de côté bas est RH. (§9, l. 107)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `mirror_ownTower_reads`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve). Équivalences/implications RH liées (caractérisations, jamais vérité acquise) : `reflectedReading_iff_noLowerSide`, `reflectedReading_iff_riemannHypothesis`.

#### V98 — Accord de l'auteur (2026-09-25) : la source de la contradiction est l'inversion (orientation opposée donnée par T opposée du zéro réfléchi), non la hauteur ni la position radiale. (§9, l. 107)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V99 — Compilé : avant l'inversion la Tour droite du miroir lit et la vérification est fausse (aucune collision) ; l'inversion échange les rayons et fait naître les deux constats et leur exclusion ; la même inversion sur la droite (conjugué) donne le même constat conditionnel ; les deux lois de l'inversion (liaison et vérification) donnent RH et lui sont équivalentes. (§9, l. 107)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `pivotPair_mirror_reaches_of_ge`) et provoque la série de conséquences suivantes : `lock_imp_pivot_lt_expected` (Si la pivotPair du miroir posée à q n'atteint pas p_min(z), alors q < p_min(z) (la vérification for…) ; `pivotCell_mirror_reaches_expected` (Pour un zéro de côté bas, la cellule du pivot propre du miroir atteint p_min(z) (p_min(z) ≤ Occ(z*)…). Cas restreints, confirmés sous condition (zéro de côté bas (β<1/2)) : `pivotCell_mirror_reaches_expected`.

#### V100 — Compilé : l'anneau du miroir n'est pas une géométrie posée à côté de zêta ; la Tour d'un zéro est la géométrie du terme que ce zéro porte dans la formule explicite de Riemann compilée dans la base ; la position de Tour est l'argument du terme ; les rayons sont exactement les points où le terme est réel. (§9, l. 107 (aussi l. 129, l. 165))
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `zeroTerm_im_eq_sin_towerPosition`, `zeroTerm_real_iff_sin`, `towerPosition_contactMinusAt`, `ray_zeroTerm_real`, `zeroTerm_real_iff_ray`, `explicit_term_of_member`, `zeroTerm_is_derivative_of_explicit_term`, `pivotCell_entry_zeroTerm_real`, `pivotCell_lastRay_zeroTerm_real`, `phase_increment_eq_pi_span`, `zeroTerm_re`, `phase_identity_cos`, `zeroTerm_re_eq_cos_towerPosition`, `ray_energy`, `ray_zeroTerm_eq`, `succession_invariants`) et provoque la série de conséquences suivantes : `consecutive_continuous_signature` (Sous consécutivité stricte : la place du miroir avance de un, la hauteur du miroir est celle du zér…) ; `explicit_term_derivative` (Pour `x > 0`, la dérivée du terme du membre dans le canal compilé est `−m(ρ)` fois le terme de la T…) ; `height_lower_bound_of_phase_quantum` (Si `c ≤ ΔΘ_n` pour un zéro et un rang donnés, alors `c / log(p_{n+1}/p_n) ≤ T` : borne inférieure l…) ; `interTowerExcess_eq` (L'excès inter-Tours `J(p)` (défini plus haut ; V155 ne le cite que par nom de fichier) vaut `(T_l −…) ; `off_consecutive_continuous_progression_eq_span` (Sous consécutivité stricte, la progression continue du second événement du miroir vaut exactement `…) ; `phase_increment_eq_of_sameHeight` (Deux zéros de même hauteur ont la même progression continue ΔΘ_n à tout rang `n` : elle ne dépend q…) ; et 4 autre(s) : `phase_increment_ge_height_mul_log_one_add_inv`, `phase_increment_ge_height_mul_log_one_add_two_div`, `phase_increment_pos`, `ray_energy_alternates`. Touchée aussi (sans l'établir) par : `zeroPoint_re`, `zeroPoint_im`, `pi_mul_towerPosition`, `cpow_zeroPoint_re`, `cpow_zeroPoint_im`, `zeroTerm_im`, `phase_identity`, `zeroPoint_isNontrivial`.

#### V101 — L'inversion est la conjugaison de ce terme (terme du conjugué = conjugué du terme, partie imaginaire opposée, somme réelle) : le nombre imaginaire, source de l'inversion. (§9, l. 107)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `conjugate_term_eq_conj`, `conjugate_term_im`, `pair_term_real`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve). Cas restreints, confirmés sous condition (selon l'énoncé : Sur la ligne) : `mirror_zeroTerm_eq_of_onLine`.

#### V102 — La position radiale entre dans l'amplitude du terme : hors ligne l'amplitude du miroir domine celle du zéro original ; sur la droite elles sont égales. (§9, l. 107)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `zeroTerm_norm`, `mirror_zeroTerm_norm`, `mirror_amplitude_ratio`, `amplitude_exponents_eq_iff_onLine`, `amplitude_ratio_sameHeight`, `horizontal_energy_action`, `ray_energy_growth`, `energyRatio_eq`, `energyRatio_const_of_deltaBeta_zero`, `energyRatio_const_iff`, `energyRatio_unbounded_of_deltaBeta_pos`, `succession_invariants`, `amplitude_inverts_of_radial_lt`, `passage_energy_sign_dichotomy`) et provoque la série de conséquences suivantes : `energy_balance_two_primes_false` (Si `β_e < β_l` et `q₁ < q₂`, les deux égalités de normes `‖terme(e,q₁)‖ = ‖terme(l,q₁)‖` et `‖terme…) ; `amplitude_le_iff_horizontal_le_vertical` (Pour `q > 0`, l'amplitude du terme du zéro postérieur est au plus celle du zéro antérieur si et seu…) ; `amplitude_lt_of_height_lt` (À même β, la Tour la plus haute porte strictement moins d'énergie en tout q > 0.) ; `energyRatio_lt_one_of_vertical` (Si β_e = β_l et T_e < T_l, le rapport énergétique est < 1 en tout q > 0.) ; `log_amplitude_ratio_eq` (Pour deux zéros `e`, `l` et `q > 0` (condition de domaine), `log‖terme(l,q)‖ − log‖terme(e,q)‖ = H…) ; `pivotCell_amplitude_brackets` (Pour `q > 0`, l'amplitude du terme en `q` est strictement supérieure à celle au contact d'entrée de…) ; et 1 autre(s) : `riemannHypothesis_of_verticalEnergyPush`. Cas restreints, confirmés sous condition (zéro de côté bas ; `q ≥ 1`; β = 1/2; selon l'énoncé : Sur la ligne; selon l'énoncé : Sous les conditions « z de côté bas » et x ≥ 1) : `mirror_amplitude_exponent_dominates`, `onLine_amplitude_exponents_equal`, `horizontal_energy_action_zero_of_onLine`, `sameHeight_amplitude_inverts_at_primes`, `sameHeight_amplitude_inverts_at_raccords`, `explicitFormula_counts_members`. Touchée aussi (sans l'établir) par : `log_amplitude_ratio_eq`, `cpow_reflect_product`.

#### V103 — La liaison des deux grammaires existe en forme analytique compilée : Tchebychev reconstruit depuis les zéros, et le terme de la Tour est la dérivée du terme du zéro dans cette reconstruction. (§9, l. 107)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `liaison_analytic`, `zeroTerm_is_derivative_of_explicit_term`, `explicit_term_derivative`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve).

#### V104 — La forme automatique du constat (croisement du bas sous un pivot posé égal au minimum attendu du zéro original) est retirée avec le pivot commun : elle ne testait rien. (§9, l. 107 (aussi l. 137, l. 225))
- Verdict : Cette vérité est confirmée (théorèmes : `invertedPivotPair_lastRay_lt_pivot`, `invertedPivotPair_not_reaches`, `secondTower_not_reaches_own_expected`) : `0 < q → (invertedPivotPair z q).lastRayContact < q` et `¬(invertedPivotPair z ↑p).reaches p` : le constat du bas sous un pivot posé est automatique (ne testait rien) ; le fait de son retrait est un statut (hors code) (révision B6)

#### V105 — Le substitut sur les ordonnées publiées (deux zéros consécutifs de la droite pris pour une paire) n'est jamais un zéro hors ligne ; il est indicatif seulement, ne prouve ni ne réfute rien. (§9, l. 109)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) (théorèmes : `control_two_onLine_towers_unique`) : énoncé de méthode numérique (statut d'un substitut sur ordonnées publiées : « indicatif, ne prouve ni ne réfute ») ; seul l'objet contrôle est compilé (`control_two_onLine_towers_unique`, unicité de la cellule pour deux zéros ON), il ne porte pas ce statut (révision B6)

#### V106 — La contradiction est relationnelle : la progression exige que la seconde Tour ait atteint le minimum ; ses contacts et son comptage disent qu'elle ne l'atteint pas ; la première l'atteint, la seconde non, alors que l'ordre la place après. (§9, l. 111)
- Verdict : Cette vérité est caractérisée seulement (équivalente à RH ou impliquant RH) (théorèmes : `terminalCollision_conditional_on_reflectedObligation`, `reflectedReading_iff_noLowerSide`, `secondTower_not_reaches_own_expected`, `firstTower_reaches_expected`, `mirror_precedes`) : les faits sont compilés : la première atteint (`reaches (firstTowerOf z).properState (expectedMinimumPrime z)`), la seconde non (`¬… reaches (expectedMinimumPrime (mirrorMember z))`), le miroir est postérieur (`PZeroMemberPrecedes`) ; mais « la progression exige que la seconde ait atteint » est l'obligation `hReaches` : `(∀ z, β<1/2 → ∃ j, … ≤ reflectedIncidence … (j+1)) ↔ ∀ z, ¬β<1/2` et `(∃ j, …) → False` ne donne que la conditionnelle ; contradiction inconditionnelle absente (révision B6)

#### V107 — Ce n'est pas une seule Tour dont un constat serait vrai et faux à la fois, ni une exigence d'égalité des derniers comptés. (§9, l. 111)
- Verdict : NON TRANSCRITE : aucun énoncé compilé sur la forme logique de la contradiction (« pas une seule Tour… ni égalité des derniers comptés ») ; seules existent les deux Tours distinctes (`secondTower_ring_eq_mirror_firstTower`) et la conditionnelle `terminalCollision_conditional_on_reflectedObligation` (voir V106) (révision B6)

#### V108 — Le test de vérification s'applique à tout zéro, sur ou hors de la droite : produire les contacts, compter, confronter ; le résultat est un constat, jamais une attente ni une hypothèse. (§9, l. 113)
- Verdict : Cette vérité est confirmée sous condition (selon l'énoncé : Sous la condition « a précède b de façon consécutive ») (théorèmes : `verification_passes`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve).

#### V109 — Quatre niveaux stricts : la géométrie (zéro → Tour → contacts) ; la lecture arithmétique (contacts → comptage) ; la contradiction ; l'universalisation, seule à faire apparaître RH. (§9, l. 113)
- Verdict : Cette vérité est caractérisée seulement : équivalente à RH ou impliquant RH sous prémisse (théorèmes : `riemannHypothesis_of_noOff`) ; aucune vérité acquise sans condition n'en sort. Conséquences dans le graphe : `allNontrivial_onLine_iff_riemannHypothesis` (« Tous les zéros non triviaux de la configuration zetaZeroConfig ont Re = 1/2 » équivaut à RiemannH…) ; `fixedLocusSelection_iff_riemannHypothesis` (Le « théorème candidat » `PFixedLocusSelection` (hors du lieu fixe, dans la bande, A = 0 ⟹ G ≠ 0) é…) ; `grammarsAgree_iff_riemannHypothesis` (Les deux grammaires (par membres, par hauteurs) coïncident sur tout zéro si et seulement si RH.) ; `heightProgression_iff_riemannHypothesis` (« La place avance donc la hauteur avance », sur tout passage de membres supérieurs, est équivalent…) ; `noNullPassage_iff_riemannHypothesis` (L'absence de passage nul est équivalente à RH.) ; `riemannHypothesis_of_energyBalance` (La prémisse d'équilibre énergétique aux deux raccords entraîne RH : un zéro hors ligne fournit un p…) ; et 5 autre(s) : `riemannHypothesis_of_localReading`, `riemannHypothesis_of_noLowerSide`, `riemannHypothesis_of_regimeCapture`, `riemannHypothesis_of_verticalEnergyPush`, `xiRealZeros_iff_riemannHypothesis`.

#### V110 — « Donc aucun zéro distinct ne peut exister hors de la droite critique. Tout vrai zéro a sa partie réelle égale à un demi. C'est l'hypothèse de Riemann. » (§9, l. 115)
- Verdict : Cette vérité est caractérisée seulement : équivalente à RH ou impliquant RH sous prémisse (théorèmes : `riemannHypothesis_of_noOff`, `riemannHypothesis_of_noLowerSide`) ; aucune vérité acquise sans condition n'en sort. Conséquences dans le graphe : `allNontrivial_onLine_iff_riemannHypothesis` (« Tous les zéros non triviaux de la configuration zetaZeroConfig ont Re = 1/2 » équivaut à RiemannH…) ; `fixedLocusSelection_iff_riemannHypothesis` (Le « théorème candidat » `PFixedLocusSelection` (hors du lieu fixe, dans la bande, A = 0 ⟹ G ≠ 0) é…) ; `grammarsAgree_iff_riemannHypothesis` (Les deux grammaires (par membres, par hauteurs) coïncident sur tout zéro si et seulement si RH.) ; `heightProgression_iff_riemannHypothesis` (« La place avance donc la hauteur avance », sur tout passage de membres supérieurs, est équivalent…) ; `mirrorEventIdentity_iff_riemannHypothesis` (La prémisse `PMirrorEventIdentity` (Cible C exigée de tout zéro de côté bas) équivaut à RiemannHypo…) ; `mirrorTransport_iff_riemannHypothesis` (La prémisse `PMirrorTransport` (transport au miroir exigé de tout zéro de côté bas) équivaut à Riem…) ; et 8 autre(s) : `noNullPassage_iff_riemannHypothesis`, `reflectedEquivariance_iff_riemannHypothesis`, `riemannHypothesis_iff_noLowerSide`, `riemannHypothesis_of_energyBalance`, `riemannHypothesis_of_localReading`, `riemannHypothesis_of_regimeCapture`, `riemannHypothesis_of_verticalEnergyPush`, `xiRealZeros_iff_riemannHypothesis`.

#### V111 — Collision typée à l'entrée (instruction 2026-09-24, implémentée et compilée) : la seconde Tour atteint son pivot et lit son occurrence à son entrée, par théorème, et hors ligne y atteint le minimum attendu du zéro original. (§9, l. 117)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `secondTower_entry_reaches_own_expected`, `secondTower_entry_reaches_mirror_occurrence`) et provoque la série de conséquences suivantes : `reflected_presents_reversed` (Pour tout zéro z, sur l'anneau du membre miroir, la seconde Tour a une entrée au moins égale à p_mi…).

#### V112 — À l'entrée, le premier compté est au moins le pivot, de sorte que la régression comptée est réfutée à l'entrée. (§9, l. 117)
- Verdict : Cette vérité est confirmée (théorèmes : `secondTower_entry_reaches_own_expected`, `pivot_le_counted`, `expected_le_counted`, `invertedPivotPair_entryContact`, `expected_le_counted_lt_expected_false`) : `↑(expectedMinimumPrime (mirrorMember z)) ≤ (secondTowerOf z).properState.entryContact` ; `q ≤ countedPrime (pivotPair z ↑q)` ; `pExpected ≤ pCounted → pCounted < pExpected → False` : à l'entrée le compté est au moins le pivot, la régression comptée est impossible (révision B6)

#### V113 — La collision lecture/vérification typée à l'entrée est réfutée ; la vérification typée à l'entrée, exigée de tout zéro de côté inférieur, est équivalente à RH. (§9, l. 117)
- Verdict : Cette vérité est confirmée sous condition (théorèmes : `secondTowerOwnContacts_meets_arithmeticChain`, `secondTower_entry_reaches_mirror_occurrence`, `secondTower_entry_reaches_own_expected`, `expectedMinimum_lt_mirror_expectedMinimum`, `riemannHypothesis_iff_noLowerSide`) : sous consécutivité stricte : `↑(occurrence (mirrorMember z)) < (secondTowerOf z).properState.entryContact` avec `occurrence (mirrorMember z) = expectedMinimumPrime z` : à l'entrée la lecture tient et la vérification (entrée < `p_min(z)`) est fausse, pas de collision. Sous β<1/2 sans consécutivité `p_min(z) < p_min(z*) ≤ entryContact` donne la même réfutation ; la moitié « vérification typée à l'entrée exigée de tout zéro de côté bas ⟺ RH » n'est PAS un théorème (prédicat d'entrée absent, `EntryCollision` retiré ; ingrédients seuls, avec `riemannHypothesis_iff_noLowerSide`) (révision B6)

#### V114 — La lecture à l'entrée et la vérification au dernier rayon tiennent ensemble sur la Tour produite et ne se contredisent pas ; aucun contact de la seconde Tour produite ne porte à la fois la lecture de son occurrence et la non-atteinte du minimum attendu du zéro original. (§ 9, l. 117)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `secondTower_entry_reaches_mirror_occurrence`) et provoque la série de conséquences suivantes : `reflected_presents_reversed` (Pour tout zéro z, sur l'anneau du membre miroir, la seconde Tour a une entrée au moins égale à p_mi…).

#### V115 — Ce verdict réfute la proposition d'une collision à l'entrée ; il ne réfute aucun énoncé des maîtres, qui placent les deux constats au dernier rayon. (§9, l. 117)
- Verdict : Cette vérité est confirmée sous condition (théorèmes : `secondTowerOwnContacts_meets_arithmeticChain`, `secondTower_entry_reaches_mirror_occurrence`, `secondTower_verification_iff_not_reads_of_consecutive`) : même réfutation de la collision à l'entrée que V113 (sous consécutivité stricte) ; les deux constats au dernier rayon sont compilés (`lastRayContact < ↑(expectedMinimumPrime z) ↔ ¬ … reaches (occurrence (mirrorMember z))`) ; la clause « ne réfute aucun énoncé des maîtres » est méta (révision B6)

#### V116 — Ce qui définit une preuve : terme final `RiemannHypothesis` dépendant des seuls axiomes standard, sans `sorry`, `admit`, axiome ajouté ni hypothèse non déchargée. (§10, l. 121)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V117 — Une hypothèse exigée de tout zéro de côté β < 1/2 dont le corps est insatisfiable est RH elle-même et ne ferme rien. (§10, l. 121)
- Verdict : Cette vérité est caractérisée seulement : équivalente à RH ou impliquant RH sous prémisse (théorèmes : `riemannHypothesis_iff_noLowerSide`, `reflectedReading_iff_noLowerSide`, `reflectedReading_iff_riemannHypothesis`, `mirrorEventIdentity_iff_riemannHypothesis`, `mirrorTransport_iff_riemannHypothesis`, `reflectedEquivariance_iff_riemannHypothesis`, `riemannHypothesis_of_noLowerSide`) ; aucune vérité acquise sans condition n'en sort. Conséquences dans le graphe : `zeroInsertionDepth_iff_riemannHypothesis` (D(z) = 0 pour tout zéro si et seulement si RH (via riemannHypothesis_iff_noLowerSide).).

#### V118 — Le statut du document est normatif pour le sens scientifique entier. (§11, l. 125)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V119 — Le statut Lean est distinct : RH n'est jamais certifiée Lean-vraie par le document seul ; seul un terme inconditionnel de type `RiemannHypothesis` le peut ; à ce jour aucun tel terme ne compile. (§11, l. 127 (aussi l. 143, l. 195, l. 231))
- Verdict : Cette vérité est caractérisée seulement : équivalente à RH ou impliquant RH sous prémisse (théorèmes : `regimeCapture_iff_riemannHypothesis`, `riemannHypothesis_of_regimeCapture`, `riemannHypothesis_of_PHeightProgression`) ; aucune vérité acquise sans condition n'en sort. Conséquences dans le graphe : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve).

#### V120 — Tout ce qui précède les deux lois de l'inversion est théorème : les quatre zéros, le miroir membre suivant, la production des deux Tours, l'inversion, la naissance des deux constats, leur exclusion, l'universalisation, et l'identité de la Tour avec le terme du zéro dans la formule explicite. (§11 « Ce qui reste », l. 129)
- Verdict : Cette vérité est caractérisée seulement : équivalente à RH ou impliquant RH sous prémisse (théorèmes : `riemannHypothesis_of_noOff`) ; aucune vérité acquise sans condition n'en sort. Conséquences dans le graphe : `allNontrivial_onLine_iff_riemannHypothesis` (« Tous les zéros non triviaux de la configuration zetaZeroConfig ont Re = 1/2 » équivaut à RiemannH…) ; `fixedLocusSelection_iff_riemannHypothesis` (Le « théorème candidat » `PFixedLocusSelection` (hors du lieu fixe, dans la bande, A = 0 ⟹ G ≠ 0) é…) ; `grammarsAgree_iff_riemannHypothesis` (Les deux grammaires (par membres, par hauteurs) coïncident sur tout zéro si et seulement si RH.) ; `heightProgression_iff_riemannHypothesis` (« La place avance donc la hauteur avance », sur tout passage de membres supérieurs, est équivalent…) ; `noNullPassage_iff_riemannHypothesis` (L'absence de passage nul est équivalente à RH.) ; `riemannHypothesis_of_energyBalance` (La prémisse d'équilibre énergétique aux deux raccords entraîne RH : un zéro hors ligne fournit un p…) ; et 5 autre(s) : `riemannHypothesis_of_localReading`, `riemannHypothesis_of_noLowerSide`, `riemannHypothesis_of_regimeCapture`, `riemannHypothesis_of_verticalEnergyPush`, `xiRealZeros_iff_riemannHypothesis`.

#### V121 — La fonction de Tchebychev, sa reconstruction exacte depuis les zéros et la formule explicite lissée qui l'exprime comme somme sur tous les zéros sont pleinement compilées ; la liaison des deux grammaires s'y appuie. (l. 129 (aussi l. 131, l. 227))
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `liaison_analytic`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve). Touchée aussi (sans l'établir) par : `zeroPoint_isNontrivial`.

#### V122 — Hors ligne les deux lois (liaison et vérification) s'excluent : aucune preuve de l'une n'est possible sans que l'autre soit fausse, sauf s'il n'existe aucun zéro de côté bas ; sous la loi de liaison (la question close), la loi de vérification est fausse en tout zéro de côté bas. (l. 129)
- Verdict : Cette vérité est confirmée sous condition (théorèmes : `secondTower_verification_iff_not_reads_of_consecutive`, `reflectedReading_iff_noLowerSide`, `riemannHypothesis_iff_noLowerSide`) : sous consécutivité stricte, vérification `↔ ¬` lecture sur la seconde Tour : les deux lois s'excluent exactement (tautologie de l'ordre) ; sous la loi de liaison en tout zéro de côté bas consécutif la loi de vérification est fausse en chacun ; la forme universelle de la liaison sur la réflexion est `… ↔ ∀ z, ¬rZeroRadialPosition ↑z < 1/2` (⟺ RH) ; l'énoncé universel sans consécutivité n'est pas compilé (révision B6)

#### V123 — Les deux lois sont des conditions de signe et d'anneau sur le terme du miroir en deux premiers (minimum attendu du zéro original et occurrence du miroir). (l. 129)
- Verdict : Cette vérité est confirmée sous condition (théorèmes : `secondTower_reads_occurrence_iff_coordinate_lt`, `secondTower_verification_iff_not_reads_of_consecutive`, `countedPrime_lt_expected_of_lastRay`, `mirror_counted_lt_expected_iff`) : sous consécutivité stricte : lecture = condition d'anneau sur `occurrence (mirrorMember z)` vs `expectedMinimumPrime (mirrorMember z)` ; vérification = `lastRayContact < ↑(expectedMinimumPrime z)` avec `expectedMinimumPrime z = occurrence (mirrorMember z)` : deux inégalités sur les deux mêmes premiers ; le mot « signe » n'a pas de théorème propre (révision B6)

#### V124 — La formule explicite compilée ne contraint que la somme de tous les termes de tous les zéros, jamais un terme isolé. (l. 129)
- Verdict : NON TRANSCRITE (théorèmes : `liaison_analytic`) : seule l'identité de somme `psiRecoveredFromZeros x = ↑(Chebyshev.psi x)` (`2 ≤ x`) est compilée ; l'énoncé négatif « jamais un terme isolé » n'a ni théorème d'isolement ni de non-isolement ; le terme d'un membre existe comme sommande (`explicit_term_of_member`) mais n'est pas isolé de la somme (CLAUDE.md §4, ExplicitFormulaLink) (révision B6)

#### V125 — Aucune hypothèse, aucun test sur zéros publiés, aucune loi posée sur tout zéro de côté bas ne remplace le théorème d'isolement. (l. 129)
- Verdict : Cette vérité est caractérisée seulement (équivalente à RH ou impliquant RH) (théorèmes : `reflectedReading_iff_noLowerSide`, `noNullPassage_iff_riemannHypothesis`, `energyBalance_iff_riemannHypothesis`, `localReading_iff_riemannHypothesis`, `regimeCapture_iff_riemannHypothesis`, `mirrorTransport_iff_riemannHypothesis`) : chaque loi posée sur tout zéro de côté bas est compilée comme équivalente à RH (`PNoNullPassage ↔ RiemannHypothesis`, `PEnergyBalanceAtRaccords ↔ RiemannHypothesis`, …) donc ne peut pas remplacer un théorème d'isolement non circulaire ; l'absence de substitut (méthode) reste hors code (révision B6)

#### V126 — Réorientation (acceptée 2026-09-25) : toutes les routes « un zéro hors ligne contredit la grammaire » ont fini sur une prémisse réfutée hors ligne ou équivalente à RH ; la cible devient la caractérisation de la droite critique. (l. 131)
- Verdict : Cette vérité est confirmée sous condition (selon l'énoncé : Sous la condition « z de côté bas ») (théorèmes : `reflected_transition_content`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve). Équivalences/implications RH liées (caractérisations, jamais vérité acquise) : `riemannHypothesis_iff_noLowerSide`, `mirrorEventIdentity_iff_riemannHypothesis`, `mirrorTransport_iff_riemannHypothesis`, `reflectedEquivariance_iff_riemannHypothesis`. Réfutations compilées liées : `mirror_event_identity_refuted`, `pair_transport_false`, `mirror_transport_refuted`, `forward_and_backward_false`, `reversedTransition_not_canonical`, `reflectedTransitionCanonical_refuted`, `reflectedHeightTransitionCanonical_refuted`, `reflected_equivariance_false`, `reflected_equivariance_false_onLine`.

#### V127 — Compilé : le côté premier de la formule explicite compte les membres et non les événements, un terme par zéro ; une paire hors ligne y est deux termes distincts à même fréquence, même événement de hauteur, deux amplitudes ; sur la droite un seul terme. (l. 131)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `mirror_heightEventIndex_eq`, `mirror_sameHeightEvent`, `mirror_no_new_height_event`, `explicitIndex_term`, `explicitIndex_injective`, `explicitIndex_mirror_im`) et provoque la série de conséquences suivantes : `off_consecutive_translation_signature` (Pour β < 1/2 et consécutivité stricte : n(z*) = n(z)+1, même hauteur, même événement de hauteur, mê…) ; `off_mirror_same_frequency` (Pour un zéro hors ligne, le miroir a même hauteur, même événement de hauteur, même portée première…) ; `onLine_mirror_trivial` (Sur la ligne, le miroir est le zéro lui-même : toutes les différences (hauteur, événement, portée,…). Cas restreints, confirmés sous condition (pour un zéro hors ligne; selon l'énoncé : Pour un zéro hors ligne; selon l'énoncé : Pour β < 1/2 et consécutivité stricte; selon l'énoncé : Sous la condition « z de côté bas ») : `off_mirror_two_grammars`, `off_mirror_same_frequency`, `off_consecutive_translation_signature`, `mirror_event_collision_content`, `explicitIndex_mirror_ne_of_off`, `explicitIndex_mirror_ne`, `explicitIndex_mirror_eq_of_onLine`, `explicitFormula_counts_members`. Touchée aussi (sans l'établir) par : `explicit_term_of_member`, `explicitIndex_val`.

#### V128 — Compilé : la caractéristique de la criticité est l'accord des deux grammaires (index par membres = index par hauteurs) ; globale : en un membre, elle tient ssi tout membre qui le précède est sur la droite ; position du membre lui-même sans effet. (l. 131)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `grammarsAgree_at_iff_onLine_below`, `grammarsAgree_at_iff_pastOnLine`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve). Cas restreints, confirmés sous condition (selon l'énoncé : Sous les conditions « z de côté bas » et « le passé de z est sur la droite ») : `grammarsAgree_at_lowSide_of_onLine_below`. Équivalences/implications RH liées (caractérisations, jamais vérité acquise) : `grammarsAgree_iff_riemannHypothesis`, `grammarByHeight_iff_riemannHypothesis`, `clock_agree_iff_riemannHypothesis`.

#### V129 — Compilé : un membre de côté bas au passé sur la droite a l'accord, son miroir à même hauteur ne l'a pas ; un seul membre hors ligne dans le passé détruit l'accord ; exigé de tout membre, l'accord est RH. (l. 131)
- Verdict : Cette vérité est confirmée sous condition (selon l'énoncé : Sous les conditions « z de côté bas » et « le passé de z est sur la droite »; selon l'énoncé : Sous la condition « z de côté bas »; selon l'énoncé : Sous les conditions « w précède z » et « w est hors ligne ») (théorèmes : `grammarsAgree_at_lowSide_of_onLine_below`, `mirror_heightEventIndex_lt_sourceIndex`, `pair_characteristic_splits`, `heightEventIndex_lt_sourceIndex_of_off_below`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve). Équivalences/implications RH liées (caractérisations, jamais vérité acquise) : `grammarsAgree_all_iff_pastOnLine_all`, `pastOnLine_all_iff_riemannHypothesis`.

#### V130 — La chaîne « progression, un événement par étape, miroir égal au membre, position radiale un demi » a pour maillon central « un membre par hauteur », qui est cet accord partout, donc RH. (l. 131)
- Verdict : Cette vérité est caractérisée seulement (équivalente à RH ou impliquant RH) (théorèmes : `grammarsAgree_iff_riemannHypothesis`, `heightProgression_iff_riemannHypothesis`, `noNullPassage_iff_riemannHypothesis`, `clock_agree_iff_riemannHypothesis`, `passage_event_increment`, `nullPassage_offLine`) : maillon central « un membre par hauteur » = accord des grammaires partout : `(∀ z, nZeroSourceIndex ↑z = nHeightEventIndex …) ↔ RiemannHypothesis` ; progression/un événement par étape : `passage_event_increment` ; hauteur stricte ↔ RH (`heightProgression_iff_riemannHypothesis`) (révision B6)

#### V131 — La grammaire par hauteurs est déjà la représentation non bifurquée et tolère un zéro hors ligne (même premier au membre et à son miroir) : la non-bifurcation ne force pas le miroir à être le membre. (l. 131)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `mirror_heightEventIndex_eq`, `mirror_sameHeightEvent`, `mirror_sameHeightIndex`, `mirror_sameHeightPrime`, `mirror_no_new_height_event`, `mirror_heightEventTransition_eq`) et provoque la série de conséquences suivantes : `off_consecutive_translation_signature` (Pour β < 1/2 et consécutivité stricte : n(z*) = n(z)+1, même hauteur, même événement de hauteur, mê…) ; `off_mirror_same_frequency` (Pour un zéro hors ligne, le miroir a même hauteur, même événement de hauteur, même portée première…) ; `onLine_mirror_trivial` (Sur la ligne, le miroir est le zéro lui-même : toutes les différences (hauteur, événement, portée,…). Cas restreints, confirmés sous condition (pour un zéro hors ligne; selon l'énoncé : Pour un zéro hors ligne; selon l'énoncé : Pour β < 1/2 et consécutivité stricte; selon l'énoncé : Sous la condition « z de côté bas ») : `off_mirror_two_grammars`, `off_mirror_same_frequency`, `off_consecutive_translation_signature`, `off_clock_slip`, `mirror_event_collision_content`. Touchée aussi (sans l'établir) par : `off_heightEventIndex_lt_sourceIndex`.

#### V132 — Produits et théorèmes (liste) : Tour propre des deux zéros de la paire par la règle du pivot ; référence effective et lecture sur la première Tour ; grammaire première reconstruite ; progression ; origine canonique et parcours par demi-tours ; événement d'arrêt ; comptage ; démonstration sans RH pour tout zéro (test de vérification par théorème) ; représentation du miroir ; zéro réfléchi et son parcours opposé ; inversion des contacts (théorème) ; anneau propre de la seconde Tour (théorème) ; membre miroir authentique et ses deux Tours sur le même anneau ; équivalence de chacun des deux constats avec une position dans les anneaux (théorème) ; exclusion hors ligne (théorème) ; collision entre l'exigence de progression et le constat de vérification ; universalisation. (l. 133)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `firstTower_reaches_expected`) et provoque la série de conséquences suivantes : `firstTower_reaches_occurrence` (La première Tour de tout zéro lit son occurrence (théorème).) ; `mirror_ownTower_reads` (La Tour propre du membre miroir atteint son occurrence et son minimum attendu.) ; `reaches_expected` (Pour tout zéro, la première Tour atteint (compte jusqu'à son dernier rayon) le minimum attendu p_mi…) ; `upright_presents_forward` (Pour tout membre w, la Tour de w atteint Occ(w) puis p_min(w) à son dernier rayon, et Occ(w) < p_mi…). Cas restreints, confirmés sous condition (selon l'énoncé : Sous la condition « a précède b de façon consécutive ») : `verification_passes`.

#### V133 — Point clé (auteur 2026-09-25, jamais rouvert) : les points clés de zeta23 sont les mêmes ; quatre zéros, deux membres, deux événements successifs ; l'événement avance de un à chaque passage, prouvé et compilé ; la seconde Tour est la Tour d'un autre zéro, son pivot est le sien. (l. 135)
- Verdict : Cette vérité est confirmée (théorèmes : `passage_event_increment`, `eventIndex_succ_of_passage`, `quartet_chain`, `upperMirror_multiplicity`, `mirror_multiplicity`, `zeta_functionalReflect_zero`, `secondTowerOf_properState`) : `nZeroSourceIndex p.zLaterMember = nZeroSourceIndex p.zEarlierMember + 1` sur tout passage (inconditionnel) ; quatre zéros : `zetaReflect (cZeroSupport z) = cZeroSupport (mirrorMember z)` et `zetaFunctionalReflect (…) = conj (cZeroSupport (mirrorMember z))` de même multiplicité ; pivot propre de la seconde Tour : `invertedPivotPair (mirrorMember z) ↑(expectedMinimumPrime (mirrorMember z))` (révision B6)

#### V134 — Les maîtres se contredisaient (pivot de la première donné à la seconde) ; cette contradiction est levée dans le sens de l'événement propre. (l. 135)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V135 — Établi par théorème : le miroir hors ligne est un membre authentique et distinct ; deux Tours sur le même anneau ; sa première Tour lit son occurrence ; sa seconde Tour a son dernier rayon sous son pivot et son entrée au moins son pivot ; lecture ⟺ « occurrence du miroir dans un anneau strictement inférieur à celui de son minimum attendu » ; vérification ⟺ « minimum attendu du zéro original dans l'anneau du minimum attendu du miroir » ; hors ligne les deux constats s'excluent ; sous consécutivité stricte chacun est la négation de l'autre. (l. 137)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `invertedPivotPair_lastRay_lt_pivot`, `invertedPivotPair_not_reaches`, `invertedPivotPair_not_reaches_of_le`, `secondTower_cell_contains_own_expected`, `secondTower_entry_reaches_own_expected`, `secondTower_not_reaches_own_expected`, `secondTower_counted_lt_own_expected`, `secondTower_reads_occurrence_iff_coordinate_lt`, `mirrorMember_firstTower_reaches_occurrence`, `mirror_two_towers_same_ring`, `remaining_open_question_is_readout_only`, `reflected_presents_reversed`) et provoque la série de conséquences suivantes : `secondTowerOwnContacts_meets_arithmeticChain` (Sous ces conditions, l'entrée de la seconde Tour de `z` dépasse strictement l'occurrence du miroir,…) ; `secondTower_entry_reaches_mirror_occurrence` (À l'entrée, la seconde Tour atteint l'occurrence du membre miroir (Occ(z*) < p_min(z*) ≤ entrée), s…) ; `secondTower_reads_iff_progression_pos` (La seconde Tour lit l'occurrence du miroir si et seulement si progression(z*) > 0 ; V est progressi…) ; `secondTower_reads_of_gap_ge_pi` (Si π ≤ T·log(p_min(z*)/Occ(z*)), la seconde Tour lit l'occurrence du miroir (condition suffisante p…). Cas restreints, confirmés sous condition (paire (z, miroir) strictement consécutive; zéro de côté bas (β<1/2)) : `secondTower_verification_iff_not_reads_of_consecutive`, `mirrorMember_distinct_member`. Touchée aussi (sans l'établir) par : `expectedMinimum_le_stateReadout_iff`, `stateReadout_lt_expectedMinimum_iff`.

#### V136 — Aucune implémentation de la seconde Tour ne porte les deux constats sur son contact terminal ; toute preuve des deux est une preuve de RH, puisque la collision est théorème. (l. 137)
- Verdict : Cette vérité est confirmée sous condition (théorèmes : `secondTower_verification_iff_not_reads_of_consecutive`, `secondTower_reads_occurrence_iff_coordinate_lt`, `riemannHypothesis_iff_noLowerSide`) : sous consécutivité stricte, les deux constats sur le contact terminal (dernier rayon) sont des négations exactes : les porter tous deux est `False` (collision = théorème) ; « toute preuve des deux est une preuve de RH » exigerait la consécutivité stricte de chaque zéro de côté bas et n'est pas transcrit (`exists_fiberSuccessor` donne un successeur consécutif à même hauteur, pas nécessairement le miroir) (révision B6)

#### V137 — Ce qui demeure de l'énoncé du 2026-09-24 : « atteindre » = compté jusqu'au dernier rayon, jamais rencontré pendant le trajet ; l'égalité abstraite des deux grammaires ne contient pas seule une inégalité sur le dernier rayon ; le renversement vient de l'équation fonctionnelle et de la conjugaison. (l. 137)
- Verdict : Cette vérité est confirmée (théorèmes : `reaches_iff_le_countedPrime`, `not_reaches_iff`, `countedPrime_eq_vonMangoldt`, `functionalReflect_support_eq_conj_mirror`, `reflected_presents_via_functional_reflect`, `offPassage_full_context`) : « atteindre » = compté au dernier rayon : `¬reaches S p ↔ S.lastRayContact < ↑p`, `countedPrime S = fnPrimeAtRank (… ⌊S.lastRayContact⌋₊ - 1)` ; le renversement vient de la conjugaison/équation fonctionnelle : `zetaFunctionalReflect (cZeroSupport z) = conj (cZeroSupport (mirrorMember z))`, `(secondTowerOf z).entryContact = reflectedIncidence (mirrorMember z) (-(pivotCoordinate …))` ; l'égalité des grammaires ne contient pas d'inégalité au dernier rayon : `offPassage_full_context` (paquet consistant) (révision B6)

#### V138 — La forme « le dernier rayon inversé est sous le minimum attendu sur la totalité des passages » (299/299) est retirée : automatique, ne testait rien ; le passage de 220/299 à 299/299 était un changement de grandeur testée. (l. 137 (aussi l. 225))
- Verdict : Cette vérité est confirmée (théorèmes : `secondTower_not_reaches_own_expected`, `secondTower_counted_lt_own_expected`, `invertedPivotPair_lastRay_lt_pivot`) : `¬(secondTowerOf z).properState.reaches (expectedMinimumPrime (mirrorMember z))` et `countedPrime … < expectedMinimumPrime (mirrorMember z)` pour tout zéro : la forme « 299/299 » est automatique par théorème ; les chiffres 220/299 et 299/299 sont numériques (hors code) (révision B6)

#### V139 — Expérience E086 (300 hauteurs publiées, β = 0,4/0,6/0,8 ordonnées par l'auteur, jamais des zéros, jamais rejouée) : les deux mouvements descendants n'ont aucun événement d'arrêt depuis leur origine ; dans les six situations de la seconde Tour, les deux constats ne tiennent jamais ensemble ; avec le pivot propre et le croisement du bas, la vérification tient exactement quand les deux minimums attendus sont dans le même anneau (un peu moins d'un tiers), la lecture exactement dans le cas contraire. (l. 139)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `reflected_no_stop_event`) et provoque la série de conséquences suivantes : `reflectedFromOrigin_never_reaches_expectedMinimum` (Le mouvement réfléchi du membre miroir, suivi depuis son origine (j ≥ 1), n'atteint jamais le minim…) ; `reflected_reads_no_prime` (Aucun anneau du mouvement réfléchi d'un zéro, parcouru depuis son origine, n'atteint un premier.). Réfutations compilées liées : `reflectedFromOrigin_never_reaches_expectedMinimum`.

#### V140 — Réfuté comme dérivation : rattacher la lecture à une fidélité de la reconstruction première sous la réflexion (commutation d'un opérateur de transport de fibre avec la réflexion) ; la commutation équivaut à l'annulation du défaut radial, β = 1/2 ; l'exiger de tout zéro est énoncer RH ; aucun objet de la chaîne ne porte cette commutation ; prémisse nouvelle interdite par la section dix. (l. 141)
- Verdict : Cette vérité est caractérisée seulement (équivalente à RH ou impliquant RH) (théorèmes : `mirrorTransport_iff_riemannHypothesis`, `reflectedEquivariance_iff_riemannHypothesis`, `radialOffset_eq_zero_iff_reflect_fixed`, `zetaReflect_eq_self_iff`, `reflectedReading_iff_noLowerSide`) : exiger le transport/la commutation avec la réflexion de tout zéro de côté bas est `↔ RiemannHypothesis` (`PMirrorTransport`, `PReflectedEquivariance`) ; commutation ⟺ défaut radial nul : `radialOffset z = 0 ↔ zetaReflect (cZeroSupport z) = cZeroSupport z`, `zetaReflect ρ = ρ ↔ ρ.re = 1/2`. NB : l'opérateur « fidélité de fibre » du maître lui-même (`FiberedMZEqM`) est dans `rh_gap_criterion`, hors RHV6Fresh (révision B6)

#### V141 — Aucun terme inconditionnel de type RH ne compile ; ce qui reste se réduit aux deux constats lus sur la seconde Tour, qui s'excluent hors ligne. (l. 143)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V142 — Rigidification confirmée (auteur 2026-09-27) : trois blocs sont désormais théorèmes compilés, noyau qu'aucune objection ne peut rouvrir sans invalider une preuve Lean. (l. 145)
- Verdict : Cette vérité est confirmée (théorèmes : `pivotCoordinate_unique`, `pivotCoordinate_isLeast`, `firstTower_contactPair_unique`, `firstTower_cell_contains_expected`, `consecutivePairArithmeticChain`, `countedRank_eq_vonMangoldt`, `countedPrime_eq_vonMangoldt`, `producedPrime_eq_vonMangoldt`, `InvertedContactPair.countedRank_eq_vonMangoldt`) : les trois blocs cités par le maître existent tous avec ces noms : unicité `k = pivotCoordinate z q` / `IsLeast`, chaîne arithmétique (sous consécutivité stricte), et `countedRank S = nPrimeCountingFromJ rChebyshevJNat ⌊S.lastRayContact⌋₊` dans les deux orientations (révision B6)

#### V143 — Bloc 1 : pour tout zéro, quel que soit β, la cellule contenant son minimum attendu est unique, jamais une sélection libre ; c'est le plus petit anneau qui l'atteint. (l. 147)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `firstTower_readings`, `firstTower_cell_contains_expected`, `firstTower_contactPair_unique`, `secondTower_coordinate_eq_unique_mirrorContactPair`, `pivotCoordinate_unique`, `entry_lt_pivot`, `pivot_le_lastRay`, `pivotCoordinate_eq_of_same_cell`, `pivotCoordinate_le_of_le_contactPlus`, `pivot_le_contactPlus_pivotCoordinate`, `pivotCoordinate_isLeast`, `properTowerOfMirror_and_reflectedMotion_coexist`, `geometry_selects_raccord_prime`, `prime_raccord_has_unique_tower_cell`, `control_two_onLine_towers_unique`, `off_pair_towers_unique_like_control`, `tower_reads_any_prime`, `passage_double_constraint`, `regime_captive_of_prime`, `succession_invariants`, `stop_event`, `cell_contains_expected`, `expected_mem_cell`, `reaches_expected`) et provoque la série de conséquences suivantes : `canonicalOrigin_lt_iff_zero_le_pivotCoordinate` (La référence est devant l'origine canonique exactement quand la coordonnée d'arrêt est ≥ 0 (le parc…) ; `invertedPivotPair_cell_contains` (Le pivot est dans la cellule inversée : dernier rayon (bas) strictement sous lui, entrée (haut) au…) ; `lineTower_cell_contains_expected` (Sur la droite, C⁻ < p_min(z) ≤ C⁺ : le minimum attendu est dans la cellule.) ; `secondTower_reads_occurrence_iff_coordinate_lt` (C_lecture : la seconde Tour lit l'occurrence du miroir ssi Occ(z*) tombe dans un anneau strictement…) ; `grammar_determines_stop_ray` (Sous la grammaire par hauteurs, sur tout passage, le membre postérieur est sur la ligne, sa hauteur…) ; `invertedPivotPair_lastRay_lt_pivot` (Le dernier rayon inversé est strictement sous le pivot.) ; et 3 autre(s) : `pivotCell_amplitude_brackets`, `pivotPair_reaches`, `readings`. Cas restreints, confirmés sous condition (zéro sur la droite critique (β=1/2); prémisse `PGrammarByHeight`, ⟺ RH par `grammarByHeight_iff_riemannHypothesis` ; hauteurs positives) : `lineTower_cell_contains_expected`, `grammar_determines_stop_ray`.

#### V144 — Bloc 2 : sous consécutivité stricte, l'occurrence du miroir égale exactement le minimum attendu du zéro original et les deux minima attendus s'ordonnent strictement. (l. 148)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `progression_occurrence`) et provoque la série de conséquences suivantes : `countedPrime_ne_expected_iff_cell` (Forme cellule du constat de vérification au successeur z' de z : premier compté ≠ p_min(z) ⟺ C⁺(S')…) ; `expectedMinimum_eq_mirror_occurrence_of_consecutive` (Sous consécutivité stricte, l'occurrence du miroir égale exactement le minimum attendu de z.) ; `mirror_sourceIndex_of_consecutive` (Sous consécutivité stricte de la paire (z, miroir), l'index zéro-source du miroir est celui de z pl…) ; `reached_progression` (Sous la condition « a et b sont deux membres consécutifs » : l'occurrence de b est le minimum atten…) ; `reaches_expected_of_reaches_occurrence` (Sur un passage consécutif z→z', atteindre l'occurrence de z' c'est atteindre le minimum attendu de…) ; `reads_expected_imp_ne_previous_expected` (Si l'état de z' lit son propre minimum attendu, alors il ne lit pas p_min(z) sur un passage consécu…). Cas restreints, confirmés sous condition (zéro de côté bas (β<1/2); paire (z, miroir) strictement consécutive; zéro de côté bas, β < 1/2 ; consécutivité stricte du zéro et de son miroir; zéro de côté bas ; consécutivité stricte du zéro et de son miroir) : `expectedMinimum_le_mirror_occurrence`, `expectedMinimum_eq_mirror_occurrence_of_consecutive`, `mirror_sourceIndex_of_consecutive`, `expectedMinimum_lt_mirror_expectedMinimum`, `consecutivePairArithmeticChain`, `arithmeticChain_and_reflectedFromOrigin_coexist`, `secondTowerOwnContacts_meets_arithmeticChain`, `member_index_succ_of_consecutive`, `off_mirror_same_frequency_of_consecutive`, `mirror_pivot_decomposition_of_consecutive`, `off_consecutive_translation_signature`.

#### V145 — Bloc 3 : le rang et le premier constatés à tout contact d'une Tour sont, par théorème, exactement la fonction de comptage de Tchebychev/Von Mangoldt évaluée à ce contact, à toute coordonnée, dans les deux orientations. (l. 149)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `InvertedContactPair.countedRank_eq_vonMangoldt`, `InvertedContactPair.reaches_primeAtRank_iff`, `InvertedContactPair.reaches_occurrence_iff`, `countedPrimeAt_eq_vonMangoldt`, `countedPrimeAt_eq_primeAtRank`, `contactPlusAt_lt_primeAtRank_counted`, `vonMangoldt_channel_reflectionFixed`, `countedPrimeAt_of_contactPlus_eq`, `countedPrimeAt_mono_oriented`, `reaches_primeAtRank_iff`, `reaches_occurrence_iff`, `reaches_expected_iff`, `countedPrime_eq_occurrence_iff`, `countedPrime_eq_expected_iff`, `countedPrime_eq_occurrence_iff_rank_succ`, `countedPrime_eq_expected_iff_rank_succ`, `countedRank_eq_succ_iff`, `countedPrime_eq_occurrence_iff_cell`, `countedPrime_ne_expected_iff_cell`, `countedRank_eq_vonMangoldt`, `countedPrime_eq_vonMangoldt`, `countedPrime_prime`, `countedPrime_eq_countedPrimeAt_lastRay`, `countedRank_eq_countedRankAt_lastRay`, `countedPrime_of_one_stage`, `countedPrime_analyticPairAt`, `producedPrime_eq_vonMangoldt`, `producedPrime_prime`, `primeCountAtStateUpper_eq_vonMangoldt`, `lastPrimeAtStateUpper_prime`) et provoque la série de conséquences suivantes : `countedPrime_le_lastRay` (Le premier compté est au plus le dernier rayon (comptage inclusif).) ; `InvertedContactPair.countedPrime_lt_of_not_reaches_succ` (Si le premier de rang n+1 n'est pas atteint, le premier constaté lui est strictement inférieur.) ; `InvertedContactPair.countedRank_pos_of_reaches_occurrence` (Le rang compté est positif dès que l'occurrence est atteinte.) ; `InvertedContactPair.reaches_iff_le_countedPrime` (Sur une paire inversée à compte positif, un premier p est atteint ssi p ≤ premier constaté.) ; `countedPrimeAt_lt_expected_of_contact` (Le premier constaté à toute coordonnée est sous p_min(a) dès que le contact supérieur l'est.) ; `countedPrime_eq_occurrence_iff_of_lt_two` (Pour un dernier rayon < 2, le premier compté est l'occurrence ⟺ l'index zéro-source est nul.) ; et 3 autre(s) : `countedPrime_lt_expected_of_lastRay`, `pivot_countedRank_pos`, `reaches_iff_le_countedPrime`.

#### V146 — Ces trois blocs sont indestructibles (théorèmes compilés sans hypothèse). (l. 151)
- Verdict : Cette vérité est confirmée sous condition (théorèmes : `pivotCoordinate_unique`, `firstTower_contactPair_unique`, `countedPrime_eq_vonMangoldt`, `consecutivePairArithmeticChain`) : blocs 1 et 3 inconditionnels ; bloc 2 (`consecutivePairArithmeticChain`) porte `rZeroRadialPosition ↑z < 1/2 → PZeroMembersConsecutive ↑z ↑(mirrorMember z) → …` : « sans hypothèse » s'entend « sans prémisse ajoutée », le domaine du bloc 2 est cette paire consécutive ; théorèmes compilés, 0 sorry, axiomes standard (Audit.lean) (révision B6)

#### V147 — La rigidité ne dit rien sur C_lecture ; E085 : 212/300 lecture, 88/300 V (étiquettes réalignées le 2026-09-27), jamais 300/300 ; prétendre que la rigidification clôt C_lecture serait une extension non fondée. (l. 151)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `secondTower_reads_iff_progression_pos`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve).

#### V148 — Audit (2026-09-27) : aucune affirmation contraire aux cinq faits dans le maître ; il n'affirme pas qu'une cellule contient un seul premier ; il ne cite aucun « 204/298 » ; il ne présente pas l'atteinte inversée du propre pivot comme contradiction attendue. (l. 153)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V149 — Fait 1 : injectivité du pointeur minimum attendu : deux zéros distincts de la branche supérieure pointent sur deux premiers de référence distincts ; conséquence de l'injectivité de l'index zéro-source et du rang premier. (l. 155)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `expectedMinimumPrime_injective`, `forcing_shared_expectedMinimum_is_collage`) et provoque la série de conséquences suivantes : `mirror_expectedMinimum_ne` (Pour β < 1/2, p_min(z*) ≠ p_min(z).). Cas restreints, confirmés sous condition (selon l'énoncé : Pour β < 1/2) : `mirror_expectedMinimum_ne`.

#### V150 — Fait 2 : sur tout passage consécutif, l'index avance d'exactement un et le minimum attendu avance strictement, sans hypothèse sur β ; généralise §7 (paire miroir sous `hβ`). (l. 156)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `occurrence_strict_of_passage`, `occurrence_successor_of_passage`, `expectedMinimumPrime_eq_laterOccurrence`, `eventIndex_succ_of_passage`, `expectedMinimumPrime_succ_of_passage`, `progression_strict`, `passage_event_increment`, `later_sourceIndex_eq`, `passage_raccords`) et provoque la série de conséquences suivantes : `geometry_selects_raccord_prime` (Sur tout passage (hauteurs positives : condition de domaine), l'occurrence du membre postérieur est…) ; `grammar_determines_stop_ray` (Sous la grammaire par hauteurs, sur tout passage, le membre postérieur est sur la ligne, sa hauteur…) ; `grammar_hypotheses_of_passage` (Les trois hypothèses grammaticales (place +1, raccord `Occ(l) = p_min(e)`, occurrence strictement c…) ; `off_event_increment_without_height` (Un zéro hors ligne produit un passage réel de même hauteur, dont la place avance de un, dont l'occu…) ; `onLine_clock_sync` (Sur un passage dont les deux extrémités sont sur la ligne critique, l'index de membre et l'index de…) ; `onLine_passage_shares_grammar_context` (Un passage ON partage toute la grammaire (place +1, raccord, occurrence croissante), sa hauteur pro…) ; et 6 autre(s) : `passage_double_constraint`, `passage_span_eq_log_occurrences`, `progression_occurrence`, `rank_grammar_unconditional`, `regime_captive_of_prime`, `succession_invariants`.

#### V151 — Fait 3 : « une cellule peut contenir plusieurs premiers » est un constat de la première expérience du dépôt (2026-09-23), jamais théorème requis ni question ouverte. (l. 157)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `pivotCoordinate_eq_of_same_cell`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve).

#### V152 — Fait 4 : une comparaison à une construction étrangère a été rejetée, remplacée par une comparaison à la reconstruction globale (troncature à 300 zéros), correspondance partielle attendue, sans contradiction de théorème. (l. 158)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V153 — Fait 5 : la seconde Tour, lue au sens de sa propre orientation inversée, n'atteint jamais son propre pivot (0/300, β synthétique) ; la Tour propre du membre miroir sur les mêmes rayons atteint son pivot 300/300 ; la différence tient au critère de lecture (quel rayon est « dernier »), pas à une opposition arithmétique ; la progression (minimum attendu strictement croissant) reste intacte 300/300 sans lien démontré. (l. 159)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `invertedPivotPair_not_reaches`, `secondTower_not_reaches_own_expected`, `secondTower_counted_lt_own_expected`) et provoque la série de conséquences suivantes : `invertedPivotPair_not_reaches_of_le` (Aucun premier au moins égal au pivot n'est atteint au dernier rayon inversé.). Touchée aussi (sans l'établir) par : `properTowerOfMirror_and_reflectedMotion_coexist`.

#### V154 — Ces cinq points ne rouvrent, ne referment ni ne modifient aucune étape du maître. (l. 161)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : énoncé sur le statut du document du maître (ne rouvre/ne modifie aucune étape) ; aucun théorème ne le porte (révision B6)

#### V155 — Cascade 2026-09-28 : le paragraphe « poussée verticale/horizontale » confirme sans les affaiblir tous les objets établis (trois objets, Tour et deux contacts, règle du pivot, M^Z = M, progression, miroir et quatre zéros, noyau, rigidité mod 6). (l. 163)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `passage_double_constraint`, `double_constraint_required_displacement`, `succession_invariants`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve). Touchée aussi (sans l'établir) par : `interTowerExcess_eq`, `interTowerExcess_pos_iff`, `interTowerExcess_eq_zero_iff`, `interTowerExcess_nonneg`, `off_excess_zero`, `interTowerExcess_pos_iff_riemannHypothesis`, `offPassages_interTowerExcess_pos_iff_riemannHypothesis`, `noNullPassage_iff_interTowerExcess_pos`.

#### V156 — La démonstration part toujours d'un zéro non trivial effectivement produit par zêta ; il n'y a pas de faux zéros ; la chaîne zêta → zéro → Tour propre → deux contacts → histoire première fixée ne peut être remplacée par un point synthétique, sans Tour énergétique, contacts ni lien aux premiers. (l. 165)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) (théorèmes : `zeroPoint_isNontrivial`, `zetaZeroConfig_carrier`, `isNontrivialZero_iff`, `AnalyticContactPair.recovers_beta`) : principe de méthode et restriction de domaine par définition (`towerMotionOf`, `firstTowerOf` prennent un `TrueZero`) ; la chaîne elle-même est compilée (V157) : `IsNontrivialZetaZero (zeroPoint z)`, `zetaZeroConfig.carrier = {ρ | PIsNonTrivialZetaZero ρ}`, `recovers_beta` (révision B6)

#### V157 — Cette chaîne est garantie par les théorèmes du maître : identité Tour ↔ terme du zéro dans la formule explicite compilée (§9, §11) et lien contacts ↔ comptage Tchebychev/Von Mangoldt. (l. 165)
- Verdict : Cette vérité est confirmée (théorèmes : `zeroTerm_is_derivative_of_explicit_term`, `explicit_term_of_member`, `zeroTerm_norm`, `zeroTerm_real_iff_ray`, `pi_mul_towerPosition`, `countedPrime_eq_vonMangoldt`, `liaison_analytic`) : identité Tour ↔ terme du zéro : `zeroTerm_real_iff_ray : (zeroTerm z q).im = 0 ↔ ∃ k, q = contactMinusAt z k`, `π·towerPosition z q = T·log q - phase`, `nontrivialZeroResidueTerm x ⟨zeroPoint z,_⟩ = -mult * Perron.f x (zeroPoint z)` ; lien contacts ↔ comptage : `countedPrime_eq_vonMangoldt`, `psiRecoveredFromZeros x = Chebyshev.psi x` (révision B6)

#### V158 — Les deux coordonnées jouent des rôles différents : la hauteur gouverne le rythme et l'échelle de la progression ; la position radiale déplace phase, contacts et amplitude ; la Tour conserve les deux, n'est jamais réductible à une construction ne dépendant que de la hauteur ; deux zéros situés différemment ne deviennent pas le même état de Tour du seul fait d'un même rang ou événement. (l. 167)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `phase_increment_eq_of_sameHeight`, `sameHeight_grid_rigid_translation`, `sameHeight_pitch_invariant`, `sameRadial_height_changes_pitch`, `mirror_phase_increment_eq`, `energyRatio_const_iff`, `zeroPoint_norm_lt_of_height_lt`) et provoque la série de conséquences suivantes : `amplitude_lt_of_height_lt` (À même β, la Tour la plus haute porte strictement moins d'énergie en tout q > 0.) ; `energyRatio_lt_one_of_vertical` (Si β_e = β_l et T_e < T_l, le rapport énergétique est < 1 en tout q > 0.) ; `off_consecutive_translation_signature` (Pour β < 1/2 et consécutivité stricte : n(z*) = n(z)+1, même hauteur, même événement de hauteur, mê…) ; `off_mirror_same_frequency` (Pour un zéro hors ligne, le miroir a même hauteur, même événement de hauteur, même portée première…) ; `onLine_passage_pure_vertical` (Sur un passage dont les deux extrémités sont sur la ligne : T_e < T_l, énergie horizontale nulle en…) ; `passage_grid_translation_of_sameHeight` (Sur un passage de même hauteur, la grille du later est celle de l'earlier translatée par exp(Δφ/T).) ; et 1 autre(s) : `succession_invariants`. Touchée aussi (sans l'établir) par : `off_consecutive_continuous_progression_eq_span`, `sameHeight_pivotCoordinate_dichotomy`, `horizontal_cell_dichotomy_at_raccords`.

#### V159 — En projetant la Tour sur la grammaire première (rangs, occurrences, écarts, transitions, ordre) une partie de l'information disparaît ; la grammaire décrit correctement l'histoire première (rigidité mod 6, deux états, trois classes d'écart, alternance forcée, injectivité et progression stricte, M^Z = M) ; elle est fonction du rang et de la hauteur seuls ; deux Tours différentes peuvent devenir indiscernables sans être identiques. (l. 169)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `mirror_span_eq`, `span_eq_on_sameHeight_fiber`, `memberTransition_eq_canonical`) et provoque la série de conséquences suivantes : `off_consecutive_continuous_progression_eq_span` (Sous consécutivité stricte, la progression continue du second événement du miroir vaut exactement `…) ; `off_consecutive_translation_signature` (Pour β < 1/2 et consécutivité stricte : n(z*) = n(z)+1, même hauteur, même événement de hauteur, mê…) ; `off_mirror_same_frequency` (Pour un zéro hors ligne, le miroir a même hauteur, même événement de hauteur, même portée première…) ; `onLine_mirror_trivial` (Sur la ligne, le miroir est le zéro lui-même : toutes les différences (hauteur, événement, portée,…). Cas restreints, confirmés sous condition (selon l'énoncé : Pour un zéro hors ligne; selon l'énoncé : Sous la condition « z de côté bas ») : `off_mirror_same_frequency`, `reflected_transition_content`. Touchée aussi (sans l'établir) par : `primeTransition_forward`.

#### V160 — Après injection de toute la grammaire, de la hauteur, des phases, des écarts, des contacts et de leur rigidité, il ne reste que deux égalités d'amplitude à établir ou réfuter ; la grammaire seule ne les tranche pas. (l. 169 (aussi l. 181, l. 227))
- Verdict : Cette vérité est caractérisée seulement (équivalente à RH ou impliquant RH) (théorèmes : `energy_balance_two_primes_false`, `energyBalance_iff_riemannHypothesis`, `amplitude_ratio_sameHeight`, `offPassage_full_context`, `zeroTerm_norm`) : `PEnergyBalanceAtRaccords ↔ RiemannHypothesis` : les deux égalités `‖zeroTerm e (occurrence l)‖ = ‖zeroTerm l (occurrence l)‖ ∧ ‖zeroTerm e (expectedMinimumPrime l)‖ = ‖zeroTerm l (…)‖` sont le résidu et sont équivalentes à RH ; `energy_balance_two_primes_false` (deux égalités à `q₁ < q₂` avec `β_e < β_l` : `False`) ; `offPassage_full_context` (le reste de la grammaire est consistant). Le constat « aucune tactique ne tranche » (sondes E116) est hors code (révision B6)

#### V161 — Sur la ligne critique, l'image d'un zéro par la symétrie retombe sur lui-même : un seul point à cette hauteur, une seule Tour ; la composante horizontale (séparation zéro/miroir) n'a pas de support géométrique. (l. 171)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `mirror_contact_eq_iff_onLine`, `mirror_radial_shift_eq_zero_iff`, `onLine_of_mirror_phase_shift_eq_zero`, `mirror_degeneracy_tfae`, `radialOffset_eq_zero_iff_fixed`, `radialOffset_eq_zero_iff_reflect_fixed`, `zetaReflect_eq_self_iff`) et provoque la série de conséquences suivantes : `insertionDepth_eq_zero_iff` (D = 0 si et seulement si β = 1/2.) ; `mirror_all_contacts_shift_of_offLine` (Hors ligne, le facteur de translation est ≠ 1 et aucun rayon k du miroir n'égale le rayon k de z.) ; `mirror_contacts_never_coincide` (Hors ligne (β < 1/2), le contact `C_k` du miroir ne coïncide jamais avec le contact `C_k` de `z` :…) ; `mirror_degeneracy_of_onLine` (Sur la ligne, Δβ = 0, Δφ = 0, tous les contacts et tous les termes coïncident : le mécanisme miroir…) ; `onLine_of_mirror_contact_eq` (Si un seul rayon du miroir coïncide avec le rayon de même indice de z, alors β = 1/2.) ; `raySuperposed_iff` (Le rayon k est superposé si et seulement si D = 0.). Cas restreints, confirmés sous condition (zéro sur la droite critique (β=1/2); selon l'énoncé : Sur la ligne (β = 1/2); selon l'énoncé : Sur la ligne) : `mirrorMember_eq_self_of_onLine`, `mirror_phase_shift_eq_zero_of_onLine`, `mirror_contacts_eq_of_onLine`, `mirror_zeroTerm_eq_of_onLine`, `mirror_degeneracy_of_onLine`, `horizontal_energy_action_zero_of_onLine`, `onLine_mirror_trivial`. Touchée aussi (sans l'établir) par : `radialOffset_eq_zero_iff_onLine`, `onLine_zero_iff_xiReal`.

#### V162 — Hors ligne, la symétrie produit réellement un second zéro à la même hauteur (jamais un point recopié) ; les deux ont chacun leur Tour, même hauteur, positions radiales différentes, contacts et amplitudes différents. (l. 171)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `onLine_of_mirror_contact_eq`) et provoque la série de conséquences suivantes : `mirror_all_contacts_shift_of_offLine` (Hors ligne, le facteur de translation est ≠ 1 et aucun rayon k du miroir n'égale le rayon k de z.) ; `mirror_degeneracy_tfae` (β = 1/2 ⟺ Δβ = 0 ⟺ Δφ = 0 ⟺ (∃k, ΔC_k = 0) ⟺ (∀k, ΔC_k = 0).). Cas restreints, confirmés sous condition (pour un zéro hors ligne; selon l'énoncé : Pour un zéro hors ligne) : `offPassage_full_context`, `mirror_all_contacts_shift_of_offLine`, `off_mirror_same_frequency`.

#### V163 — Théorème compilé : hors ligne, aucun contact du miroir ne coïncide avec un contact du zéro original ; le raccord entre leurs occurrences est une égalité d'entiers, jamais de positions réelles. (l. 171)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `grids_never_coincide`, `contactMinus_eq_iff_radial_eq`, `mirror_contact_eq_iff_onLine`) et provoque la série de conséquences suivantes : `mirror_contacts_never_coincide` (Hors ligne (β < 1/2), le contact `C_k` du miroir ne coïncide jamais avec le contact `C_k` de `z` :…) ; `mirror_grid_never_coincides` (Hors ligne, aucun étage de la Tour du miroir ne coïncide avec aucun étage de la Tour du zéro, à tou…) ; `onLine_of_mirror_contact_eq` (Si un seul rayon du miroir coïncide avec le rayon de même indice de z, alors β = 1/2.) ; `onLine_of_mirror_phase_shift_eq_zero` (Si Δφ = 0 alors β = 1/2.) ; `raySuperposed_iff` (Le rayon k est superposé si et seulement si D = 0.). Cas restreints, confirmés sous condition (zéro de côté bas) : `mirror_grid_never_coincides`, `mirror_all_contacts_shift_of_offLine`. Réfutations compilées liées : `mirror_contacts_never_coincide`. Touchée aussi (sans l'établir) par : `horizontal_cell_dichotomy_at_raccords`.

#### V164 — Cette configuration existe légitimement comme objet analytique potentiel de zêta ; le paragraphe ne prétend pas qu'elle serait inconcevable ailleurs. (l. 171)
- Verdict : Cette vérité est confirmée sous condition (théorèmes : `zeta_reflect_zero`, `zeta_functionalReflect_zero`, `mirrorMember_ne`, `offPassage_full_context`, `mirror_contacts_never_coincide`) : sous β<1/2 (zéro hors ligne supposé) : le miroir est un vrai zéro distinct (`zeta_reflect_zero`, `mirrorMember z ≠ z`), la configuration (contacts distincts `contactMinusAt (mirrorMember z) k ≠ contactMinusAt z k`, paquet grammatical consistant `offPassage_full_context`) est habitée en tant que terme ; « le paragraphe ne prétend pas… » est méta (révision B6)

#### V165 — Deux modes de réalisation : poussée verticale (succession = augmentation de hauteur) et poussée horizontale (à hauteur inchangée, deux positions radiales distinctes) ; « poussée » ne désigne aucune force physique ni loi de conservation. (l. 173)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `nullPassage_horizontal`, `horizontal_nullPassage`, `heightProgression_of_horizontalExclusion`, `double_constraint_required_displacement`, `passage_trichotomy_ABC`, `passage_deltaT_nonneg`, `succession_invariants`, `passage_energy_sign_dichotomy`) et provoque la série de conséquences suivantes : `horizontalExclusion_iff_riemannHypothesis` (L'exclusion horizontale (aucun passage ne réalise HMR) est équivalente à RH.) ; `offPassage_full_context` (Un zéro hors ligne produit un passage qui cumule : même hauteur, place +1, raccord, occurrence croi…) ; `riemannHypothesis_of_energyBalance` (La prémisse d'équilibre énergétique aux deux raccords entraîne RH : un zéro hors ligne fournit un p…) ; `riemannHypothesis_of_localReading` (Sous `PNoLowOffZero`, la lecture orientée au seul raccord `Occ(l)` entraîne RH.). Touchée aussi (sans l'établir) par : `localReading_fails_modeC`.

#### V166 — La ligne critique porte une continuité dynamique : le zéro suivant arrive dans une progression déjà engagée ; la progression est une transmission (zéro → Tour → énergie → événement premier suivant → raccord de la Tour suivante) ; la continuité verticale est une succession de Tours à énergies compatibles avec la progression première, jamais une simple suite d'ordonnées croissantes. (l. 175)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `amplitude_lt_of_height_lt`) et provoque la série de conséquences suivantes : `localReading_modeA` (En mode A (au sens de ce fichier : hauteur croissante, même position radiale), la « lecture orienté…) ; `onLine_amplitude_lt_of_height_lt` (Sur la ligne, deux membres de hauteurs distinctes : la Tour la plus haute porte strictement moins d…) ; `verticalEnergyPush_of_riemannHypothesis` (Sous RH, PVerticalEnergyPush est vraie.).

#### V167 — Un zéro hors ligne appartient à une autre configuration : dissymétrie radiale (contacts, amplitudes différents — chaque terme apparié à sa norme de support, jamais forme croisée — énergie dépendant de la position radiale) ; séparation horizontale et deux états énergétiques de même hauteur ; elle ne fournit pas spontanément la transformation verticale exigée. (l. 177)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `mirror_amplitude_ratio`, `amplitude_ratio_sameHeight`, `energyRatio_unbounded_of_deltaBeta_pos`, `amplitude_inverts_of_radial_lt`) et provoque la série de conséquences suivantes : `energy_balance_two_primes_false` (Si `β_e < β_l` et `q₁ < q₂`, les deux égalités de normes `‖terme(e,q₁)‖ = ‖terme(l,q₁)‖` et `‖terme…) ; `passage_energy_sign_dichotomy` (Sur tout passage, ou bien la hauteur progresse, ou bien (même hauteur) l'énergie du later domine ce…) ; `riemannHypothesis_of_verticalEnergyPush` (PVerticalEnergyPush (l'énergie du later n'excède jamais celle de l'earlier en q ≥ 1) entraîne RH.). Cas restreints, confirmés sous condition (selon l'énoncé : Pour β < 1/2 et T ≥ 2) : `sameHeight_amplitude_inverts_at_primes`, `offMirror_all_elements_hold_and_vertical_force_fails`. Touchée aussi (sans l'établir) par : `log_amplitude_ratio_eq`, `zeroTerm_norm`.

#### V168 — La question devient une question d'insertion : la Tour du candidat porte-t-elle l'état énergétique compatible avec la continuation transmise ? (l. 177)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V169 — L'objet de comparaison décisif est la compatibilité entre l'énergie transmise par la Tour précédente au raccord premier partagé et l'énergie de la Tour du candidat, non une égalité d'énergie entre les deux Tours du couple miroir. (l. 179)
- Verdict : Cette vérité est caractérisée seulement (équivalente à RH ou impliquant RH) (théorèmes : `energyBalance_iff_riemannHypothesis`, `localReading_iff_riemannHypothesis`, `passage_raccords`, `geometry_selects_raccord_prime`, `mirror_amplitude_ratio`) : la compatibilité aux raccords partagés est `PEnergyBalanceAtRaccords ↔ RiemannHypothesis` (et `PLocalReadingOrientation ↔ RH` sous `PNoLowOffZero`), avec `occurrence (later) = expectedMinimumPrime (earlier)` au raccord ; l'égalité interne au couple miroir n'est jamais imposée (`mirror_amplitude_ratio`, `amplitude_exponents_eq_iff_onLine`) ; le caractère « décisif » de l'objet est un choix de méthode (révision B6)

#### V170 — Fait établi et compilé : deux égalités d'amplitude en deux raccords distincts, à deux premiers ordonnés, forcent l'égalité des deux positions radiales ; une seule ne suffit jamais. (l. 179 (aussi l. 227))
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `passage_raccords`) et provoque la série de conséquences suivantes : `geometry_selects_raccord_prime` (Sur tout passage (hauteurs positives : condition de domaine), l'occurrence du membre postérieur est…) ; `grammar_determines_stop_ray` (Sous la grammaire par hauteurs, sur tout passage, le membre postérieur est sur la ligne, sa hauteur…) ; `succession_invariants` (Paquet sur tout passage : trichotomie, formule de R_E, constance ⟺ Δβ = 0, raccords, cellules conte…). Cas restreints, confirmés sous condition (même hauteur, `β_e < β_l`, `T_e ≥ 2` (mode C)) : `localReading_fails_modeC`, `sameHeight_amplitude_inverts_at_raccords`. Équivalences/implications RH liées (caractérisations, jamais vérité acquise) : `energyBalance_iff_riemannHypothesis`, `riemannHypothesis_of_energyBalance`. Réfutations compilées liées : `energy_balance_two_primes_false`. Touchée aussi (sans l'établir) par : `sameHeight_horizontal_dominates`, `pivotCell_amplitude_brackets`, `horizontalRaccords_amplitude_brackets`.

#### V171 — Exiger la compatibilité aux deux raccords retire la compensation accidentelle ; c'est la condition pertinente. (l. 179)
- Verdict : Cette vérité est confirmée sous condition (théorèmes : `energy_balance_two_primes_false`, `amplitude_ratio_sameHeight`) : `β_e < β_l → 0 < q₁ → q₁ < q₂ → ‖zeroTerm e q₁‖ = ‖zeroTerm l q₁‖ → ‖zeroTerm e q₂‖ = ‖zeroTerm l q₂‖ → False` (preuve via `amplitude_ratio_sameHeight` aux deux raccords) ; la mention « une seule égalité ne suffit pas » n'a pas de théorème propre (constat du compilateur, sondes E116) (révision B6)

#### V172 — Le terme énergétique de chaque zéro est déjà un objet isolé propre à ce zéro, jamais mélangé aux autres ; le pointeur zéro → premier de référence est établi sans condition. (l. 181)
- Verdict : Cette vérité est confirmée (théorèmes : `expectedMinimumPrime_injective`, `zeroTerm_norm`, `explicit_term_of_member`, `zeroTerm_is_derivative_of_explicit_term`, `countedPrime_eq_vonMangoldt`) : `expectedMinimumPrime z1 = expectedMinimumPrime z2 → z1 = z2` (pointeur zéro → premier, sans condition) ; `‖zeroTerm z q‖ = q ^ rZeroRadialPosition ↑z / ‖zeroPoint z‖` et `HasDerivAt (fun y ↦ ↑y * Perron.f y (zeroPoint z)) (zeroTerm z x) x` : le terme énergétique est fonction de `z` seul. « Objet isolé » = terme d'un membre comme sommande (`explicit_term_of_member`), pas isolement hors de la somme (voir V124, T9) (révision B6)

#### V173 — Le compilateur ramène la condition à exactement deux égalités d'amplitude aux deux raccords, réductibles à l'exposant réel de l'amplitude du terme explicite ; aucune tactique automatique ne les tranche. (l. 181)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `zeroTerm_norm`, `horizontal_energy_action`, `energyRatio_eq`) et provoque la série de conséquences suivantes : `amplitude_inverts_of_radial_lt` (Si β_e < β_l (toute hauteur), il existe q0 ≥ 1 tel que ‖E_e(q)‖ < ‖E_l(q)‖ pour tout q > q0.) ; `amplitude_le_iff_horizontal_le_vertical` (Pour `q > 0`, l'amplitude du terme du zéro postérieur est au plus celle du zéro antérieur si et seu…) ; `amplitude_lt_of_height_lt` (À même β, la Tour la plus haute porte strictement moins d'énergie en tout q > 0.) ; `amplitude_ratio_sameHeight` (Pour deux zéros quelconques `e`, `l` et `q > 0`, `‖terme(l,q)‖·‖ρ_l‖ = q^{β_l−β_e}·(‖terme(e,q)‖·‖ρ…) ; `energyRatio_const_iff` (Le rapport énergétique est constant en q si et seulement si Δβ = 0.) ; `energyRatio_const_of_deltaBeta_zero` (Si β_e = β_l, le rapport énergétique est constant en q, égal à ‖ρ_e‖/‖ρ_l‖.) ; et 8 autre(s) : `energyRatio_unbounded_of_deltaBeta_pos`, `energy_balance_two_primes_false`, `log_amplitude_ratio_eq`, `mirror_amplitude_ratio`, `mirror_zeroTerm_norm`, `pivotCell_amplitude_brackets`, `ray_energy_growth`, `succession_invariants`. Touchée aussi (sans l'établir) par : `sameHeight_horizontal_dominates`, `horizontalRaccords_amplitude_brackets`.

#### V174 — L'énoncé de M^Z = M / rigidité mod 6 : (i) tout premier > 3 est en état A (6k−1, résidu 5) ou B (6k+1, résidu 1) ; (ii) l'écart mod 6 entre deux tels premiers ne prend que 0, 2 (A→B), 4 (B→A) ; (iii) deux changements d'état effectifs consécutifs ne portent jamais la même classe ; alternance 2,4,2,4… seule possible. (l. 187, l. 189)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `prime_goodMod6`, `gapClass6_eq_zero_iff`, `gapClass6_eq_two_iff`, `gapClass6_eq_four_iff`, `gapClass6_mem`, `gapClass6_alternates`, `primeGapClass6_alternates`, `expectedMinimumPrime_gapClass6_alternates`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve).

#### V175 — La grammaire historique (regroupement en motifs, familles, ordre, méta-pattern visant `M^Z = M`) existe dans la recherche historique du dépôt depuis l'origine ; note E094 §F « vraie seulement au sens étroit ». (l. 187)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) (théorèmes : `prime_goodMod6`, `gapClass6_alternates`, `primeGapClass6_alternates`) : énoncé historique sur l'existence de recherches antérieures dans le dépôt (état/histoire) ; seule la première couche (états mod 6, classes d'écart, alternance) est compilée (`Grammar/Mod6Rigidity`) (révision B6)

#### V176 — La hiérarchie plus large (motifs, familles, méta-pattern) demeure descriptive et historique, jamais portée dans le code compilé RHV6Fresh ; seule la première couche (états, classes d'écart, alternance) est formalisée. (l. 191)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V177 — Sous le modèle d'E094/E095 (premier suivant dans le rang de la séquence fusionnée), la couche mod 6 est préservée par construction, comme progression et injectivité de `pmin` ; aucune insertion ne peut la briser. (l. 193)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `expectedMinimumPrime_gapClass6_alternates`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve).

#### V178 — Aucun lien démontré n'existe entre cette couche et le constat de vérification/lecture (C_lecture/V), seule question ouverte et data-dépendante du maître. (l. 193)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V179 — `RH_FOUND = FALSE`. (l. 195 (aussi l. 214, l. 231))
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V180 — Vérité 1 : un zéro et son miroir tirent horizontalement en sens opposés ; résultante nulle pour tout zéro ; tension propre (2δ²) nulle seulement sur la ligne. (l. 201)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `mirror_net_horizontal_force_zero`, `mirror_horizontal_tension_eq_zero_iff`, `mirror_verticalEnergy_eq_zero_iff`) et provoque la série de conséquences suivantes : `offMirror_all_elements_hold_and_vertical_force_fails` (Pour β < 1/2 et T ≥ 2 : force horizontale nette nulle, tension > 0, entrelacement de tous les rayon…). Cas restreints, confirmés sous condition (selon l'énoncé : Pour β < 1/2 et T ≥ 2) : `offMirror_all_elements_hold_and_vertical_force_fails`.

#### V181 — Un passage ON est de la verticalité pure : hauteur strictement croissante, énergie horizontale nulle pour tout premier, énergie verticale positive, poussée strictement décroissante. (l. 201)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `energyRatio_const_of_deltaBeta_zero`, `energyRatio_lt_one_of_vertical`, `amplitude_lt_of_height_lt`, `mirror_verticalEnergy_eq_zero_iff`) et provoque la série de conséquences suivantes : `energyRatio_const_iff` (Le rapport énergétique est constant en q si et seulement si Δβ = 0.) ; `localReading_modeA` (En mode A (au sens de ce fichier : hauteur croissante, même position radiale), la « lecture orienté…) ; `onLine_amplitude_lt_of_height_lt` (Sur la ligne, deux membres de hauteurs distinctes : la Tour la plus haute porte strictement moins d…) ; `verticalEnergyPush_of_riemannHypothesis` (Sous RH, PVerticalEnergyPush est vraie.). Cas restreints, confirmés sous condition (passage dont les deux extrémités sont sur la ligne ; hauteurs positives; selon l'énoncé : Sur un passage dont les deux extrémités sont sur la ligne critique; selon l'énoncé : Sur la ligne; selon l'énoncé : Sur un passage dont les deux extrémités sont sur la ligne) : `onLine_passage_shares_grammar_context`, `onLine_clock_sync`, `onLine_amplitude_lt_of_height_lt`, `onLine_passage_pure_vertical`. Touchée aussi (sans l'établir) par : `passage_height_lt_of_onLine`, `grammar_forces_mode_A`, `localReading_modeA`.

#### V182 — Vérité 2 : la distance entre deux zéros consécutifs passe par le pointage sur le premier ; le pointeur zéro → premier est injectif : un seul premier en face d'un seul zéro. (l. 203)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `expectedMinimumPrime_injective`, `forcing_shared_expectedMinimum_is_collage`) et provoque la série de conséquences suivantes : `mirror_expectedMinimum_ne` (Pour β < 1/2, p_min(z*) ≠ p_min(z).). Cas restreints, confirmés sous condition (selon l'énoncé : Pour β < 1/2; selon l'énoncé : Pour β < 1/2 et T ≥ 2) : `mirror_expectedMinimum_ne`, `offMirror_all_elements_hold_and_vertical_force_fails`.

#### V183 — Correction : « β détruit l'entrelacement » est faux ; hors ligne, le miroir s'entrelace strictement dans chaque cellule de la Tour de z ; E123 : 2100/2100, positions relatives entre 0,98 et 0,9999 ; vrais voisins ON : 25/1794 cellules doubles, 276/299 passages parfaits. (l. 205)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `mirror_relative_position`, `mirror_contact_lt_iff`, `contact_lt_mirror_iff`) et provoque la série de conséquences suivantes : `rayStrictlyInterlaced_iff` (Le rayon k est strictement entrelacé si et seulement si D ≠ 0.). Cas restreints, confirmés sous condition (selon l'énoncé : Pour β < 1/2 et tout q; selon l'énoncé : Pour β < 1/2 et tout k; selon l'énoncé : Pour β < 1/2 et T ≥ 2) : `mirror_translation_lt`, `mirror_contacts_interlace`, `offMirror_all_elements_hold_and_vertical_force_fails`.

#### V184 — β détruit la SUPERPOSITION : le rayon du miroir ne se pose plus sur celui de z, il glisse à l'intérieur de la cellule. (l. 205)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `mirror_contact_ratio_const`, `onLine_of_mirror_contact_eq`, `sameHeight_grid_rigid_translation`, `mirror_contact_eq_depth`, `towerPosition_mirror_sub`, `passage_grid_translation_of_sameHeight`) et provoque la série de conséquences suivantes : `mirror_all_contacts_shift_of_offLine` (Hors ligne, le facteur de translation est ≠ 1 et aucun rayon k du miroir n'égale le rayon k de z.) ; `mirror_degeneracy_tfae` (β = 1/2 ⟺ Δβ = 0 ⟺ Δφ = 0 ⟺ (∃k, ΔC_k = 0) ⟺ (∀k, ΔC_k = 0).) ; `mirror_translation_lt` (Pour β < 1/2 et tout q, 0 < position(miroir) − position(z) < (1−2β)/(πT).) ; `onLine_of_mirror_phase_shift_eq_zero` (Si Δφ = 0 alors β = 1/2.) ; `pivotCoordinate_mirror_mem` (Pour β < 1/2 et toute référence q, la coordonnée de pivot du miroir est celle de z ou la suivante.). Cas restreints, confirmés sous condition (voir annexe A) : `mirror_all_contacts_shift_of_offLine`. Touchée aussi (sans l'établir) par : `mirror_grid_never_coincides`, `mirror_contacts_never_coincide`.

#### V185 — La bonne loi d'exclusion est la capture (rayon miroir posé sur le rayon) ; un seul nombre par zéro la mesure, la profondeur d'insertion D(z) ; dichotomie exclusive rayon par rayon : superposition (D = 0) XOR entrelacement strict (D ≠ 0), indépendante du rayon. (l. 207)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `onLine_of_mirror_phase_shift_eq_zero`, `mirror_degeneracy_tfae`, `insertionDepth_eq`, `mirror_contact_eq_depth`, `mirror_relative_position`, `insertionDepth_pos_iff`, `insertionDepth_eq_zero_iff`, `rayStrictlyInterlaced_iff`, `raySuperposed_iff`, `superposed_xor_strictlyInterlaced`, `strictlyInterlaced_uniform`, `mirror_phase_gap_eq_arctan`) et provoque la série de conséquences suivantes : `capture_of_onLine` (Pour un zéro de la ligne, tous les rayons sont superposés et aucun n'est strictement entrelacé.) ; `premise_ladder_tfae` (Les six formes (pas de passage nul, exclusion horizontale, superposition, absence d'entrelacement s…) ; `zeroInsertionDepth_iff_riemannHypothesis` (D(z) = 0 pour tout zéro si et seulement si RH (via riemannHypothesis_iff_noLowerSide).) ; `contact_lt_mirror_iff` (C_j(z) < C_k(z*) ⟺ j − k < −D (hypothèse de notation c = j − k).) ; `insertionDepth_le` (Pour β ≤ 1/2 : 0 ≤ D ≤ (1 − 2β)/(π·T).) ; `mirror_all_contacts_shift_of_offLine` (Hors ligne, le facteur de translation est ≠ 1 et aucun rayon k du miroir n'égale le rayon k de z.) ; et 2 autre(s) : `mirror_contact_lt_iff`, `mirror_phase_gap_lt`.

#### V186 — Hors ligne, la capture est presque réalisée (défaut en 1/T) sans jamais l'être. (l. 207)
- Verdict : Cette vérité est confirmée sous condition (selon l'énoncé : Pour β ≤ 1/2; selon l'énoncé : Pour β < 1/2; selon l'énoncé : Pour β < 1/2 et tout q; selon l'énoncé : Pour β < 1/2 et consécutivité stricte) (théorèmes : `insertionDepth_le`, `mirror_phase_gap_lt`, `mirror_translation_lt`, `mirror_translation_lt_inv_pi_height`, `off_consecutive_translation_signature`) et provoque la série de conséquences suivantes : `mirror_translation_over_next_progression_lt` (Sous ces conditions, pour tout `q > 0`, la translation miroir (terme hors maître) `π·(θ(z*,q) − θ(z…).

#### V187 — La capture entraîne la verticalité pure sur tout passage ; la géométrie la décharge sur tout zéro de la ligne ; le résidu est exactement l'ensemble des zéros hors ligne. (l. 207)
- Verdict : Cette vérité est confirmée sous condition (selon l'énoncé : Sous la prémisse PNoStrictInterlacing (équivalente à RH par premise_ladder_tfae); selon l'énoncé : Pour un zéro de la ligne) (théorèmes : `capture_forces_pure_verticality`, `capture_of_onLine`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve).

#### V188 — Échelle `premise_ladder_tfae` : pas de passage nul ⟺ exclusion horizontale ⟺ superposition ⟺ absence d'entrelacement strict ⟺ D ≡ 0 ⟺ RH. (l. 207)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `insertionDepth_eq_zero_iff`, `rayStrictlyInterlaced_iff`, `raySuperposed_iff`) et provoque la série de conséquences suivantes : `capture_of_onLine` (Pour un zéro de la ligne, tous les rayons sont superposés et aucun n'est strictement entrelacé.) ; `premise_ladder_tfae` (Les six formes (pas de passage nul, exclusion horizontale, superposition, absence d'entrelacement s…) ; `superposed_xor_strictlyInterlaced` (Pour tout zéro et tout rayon, exactement un des deux : superposition ou entrelacement strict.) ; `strictlyInterlaced_uniform` (L'entrelacement strict vaut à un rayon si et seulement s'il vaut à tout autre rayon.) ; `zeroInsertionDepth_iff_riemannHypothesis` (D(z) = 0 pour tout zéro si et seulement si RH (via riemannHypothesis_iff_noLowerSide).). Équivalences/implications RH liées (caractérisations, jamais vérité acquise) : `horizontalExclusion_iff_riemannHypothesis`, `energyBalance_iff_riemannHypothesis`, `noNullPassage_iff_riemannHypothesis`, `noNullPassage_iff_heightProgression`, `noNullPassage_iff_interTowerExcess_pos`, `zeroInsertionDepth_iff_riemannHypothesis`, `premise_ladder_tfae`, `riemannHypothesis_of_noNullPassage`. Touchée aussi (sans l'établir) par : `heightProgression_of_horizontalExclusion`.

#### V189 — Verdict honnête : la prémisse est remplacée par sa forme la plus atomique (un réel par zéro, D(z) = 0), mais reste équivalente à RH ; la géométrie des Tours n'en décharge aucune partie pour un zéro hors ligne ; ce n'est pas une preuve de RH. (l. 209)
- Verdict : Cette vérité est confirmée sous condition (selon l'énoncé : Sous la prémisse PNoStrictInterlacing (équivalente à RH par premise_ladder_tfae)) (théorèmes : `capture_forces_pure_verticality`) et provoque la série de conséquences suivantes : aucune conséquence directe dans le graphe des preuves du projet (aucun autre théorème n'utilise ces théorèmes dans sa preuve). Équivalences/implications RH liées (caractérisations, jamais vérité acquise) : `zeroInsertionDepth_iff_riemannHypothesis`, `premise_ladder_tfae`, `verticalEnergyPush_iff_riemannHypothesis`. Touchée aussi (sans l'établir) par : `horizontalExclusion_iff_riemannHypothesis`, `noNullPassage_iff_riemannHypothesis`, `riemannHypothesis_of_noNullPassage`.

#### V190 — Bloc d'état : `VERTICAL_FORCE=COMPILED`, `RAY_CAPTURE=COMPILED`, `RH_FOUND=FALSE`. (l. 212–214)
- Verdict : Cette vérité est confirmée et incontestable (théorèmes : `mirror_net_horizontal_force_zero`, `superposed_xor_strictlyInterlaced`) (théorèmes cités par le maître dans la vérité elle-même) et provoque la série de conséquences suivantes : `offMirror_all_elements_hold_and_vertical_force_fails` (Pour β < 1/2 et T ≥ 2 : force horizontale nette nulle, tension > 0, entrelacement de tous les rayon…). Cas restreints, confirmés sous condition (selon l'énoncé : Sur un passage dont les deux extrémités sont sur la ligne; selon l'énoncé : Pour β < 1/2 et tout k; selon l'énoncé : Pour un zéro de la ligne) : `onLine_passage_pure_vertical`, `mirror_contacts_interlace`, `capture_of_onLine`. Équivalences/implications RH liées (caractérisations, jamais vérité acquise) : `premise_ladder_tfae`.

#### V191 — Toute modification future doit déclarer : objets scientifiques, étapes de démonstration, représentation de l'état propre, interdictions absolues, statut Lean ; une mise à jour de statut Lean n'écrase jamais le corps scientifique. (l. 219–221)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V192 — Bloc RÉFUTÉ : multiplicité des contacts ; type infini d'états ; obligation d'incidence d'entrée ; lecture par égalité du dernier premier ; loi universelle « toute Tour atteint son minimum » ; toute décorrélation des deux grammaires ; test de vérification sur le rayon du haut (220/299) ; β ↦ 1−β seul comme source du renversement ; « atteindre » = « rencontré pendant le trajet » ; lecture de la seconde Tour déplacée sur l'entrée ; réfutation d'un maître par expériences/code ; pivot commun ; constat de vérification obtenu par construction (299/299). (l. 225)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V193 — Bloc BORNÉ (état à ce jour) : quatre zéros, deux membres, deux événements compilés ; deux Tours produites (seconde sur son pivot, contacts inversés) ; référence effective et lecture de la première par théorème ; anneau propre de la seconde par théorème ; les deux constats lus, chacun équivalent à une position d'anneau, exclusifs hors ligne par théorème ; collision et universalisation transcrites ; contrainte du miroir compilée ; Tour = terme du zéro, inversion = conjugaison ; rigidité des contacts hors ligne et rigidité énergétique à deux raccords compilées. (l. 227)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

#### V194 — SÉLECTIONS : à ce jour aucune. RH_FOUND : FALSE. (l. 229, l. 231)
- Verdict : hors code (énoncé d'autorité/méthode/constat numérique/état) : aucun théorème compilé ne le porte et il n'a pas vocation à en avoir un.

## 4. Points ouverts O1…O24

#### O1 — La transcription de la question close (les deux Tours d'un membre lisent de même ; la seconde Tour du miroir lit l'histoire jusqu'à son occurrence) n'est pas encore théorème du code.
- Théorèmes rattachés (champ Vérités) : `riemannHypothesis_of_hReaches_is_vacuous` [IMPLIQUE RH SOUS PRÉMISSE].
- Note B1 : **O1** : `mirrorMember_firstTower_reaches_occurrence` (la première Tour du membre miroir lit son occurrence) et `mirror_two_towers_same_ring` sont compilés ; la transcription que le maître appelle « les deux Tours d'un membre lisent de même » n'y figure que sous la forme de l'équivalence d'anneau pour la seconde Tour.
- Note B3 : **O1** — `riemannHypothesis_of_hReaches_is_vacuous` : `hReaches` (le mouvement réfléchi atteint p_min(z*)) est la prémisse non transcrite ; elle est réfutée par un théorème hors lot (`reflectedFromOrigin_never_reaches_expectedMinimum`, module Tower/ReflectedMotion) ; le maître n'est pas modifié.
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

#### O2 — Le constat de lecture (« ce que la progression impose ») est « transcrit mais non encore théorème du code », de même que le constat de vérification.
- Théorèmes rattachés (champ Vérités) : aucun.
- Note B1 : **O2 / O4 (constat de vérification)** : `secondTower_verification_iff_not_reads_of_consecutive` (sous consécutivité stricte, vérification ⟺ non-lecture), `countedPrime_ne_expected_iff_cell`, `authorForm_iff_counted_lt`, `mirror_counted_lt_expected_iff` donnent les formes équivalentes du constat ; le lot ne contient pas de théorème qui l'établisse ou le réfute pour un zéro hors ligne donné.
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

#### O3 — Le constat de lecture n'est pas un théorème de la géométrie de la seconde Tour (équivalent seulement à une position d'anneau).
- Théorèmes rattachés (champ Vérités) : `secondTower_reads_occurrence_iff_coordinate_lt` [CONFIRMÉE].
- Note B1 : **O11 / O3 (C_lecture)** : `secondTower_reads_occurrence_iff_coordinate_lt` et `countedPrime_eq_occurrence_iff_cell` établissent uniquement l'équivalence « lecture ⟺ Occ(z*) dans un anneau strictement inférieur à celui de p_min(z*) » ; aucun théorème du lot n'établit la lecture sans condition sur le membre miroir hors ligne (le maître la déclare constat lu).
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

#### O4 — Le constat de vérification est « un constat lu, jamais une hypothèse, jamais un théorème » (au sens inconditionnel), tenant exactement quand les deux minimums attendus sont dans le même anneau du miroir.
- Théorèmes rattachés (champ Vérités) : aucun.
- Note B1 : **O2 / O4 (constat de vérification)** : `secondTower_verification_iff_not_reads_of_consecutive` (sous consécutivité stricte, vérification ⟺ non-lecture), `countedPrime_ne_expected_iff_cell`, `authorForm_iff_counted_lt`, `mirror_counted_lt_expected_iff` donnent les formes équivalentes du constat ; le lot ne contient pas de théorème qui l'établisse ou le réfute pour un zéro hors ligne donné.
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

#### O5 — Les deux lois de l'inversion (liaison et vérification) exigées de tout zéro de côté bas : leur conjonction est RH ; elles restent à établir.
- Théorèmes rattachés (champ Vérités) : aucun.
- Statut : reste ouvert ; aucun lot ne le touche.

#### O6 — Isoler dans la somme sur les zéros le terme de la paire hors ligne : « ce théorème d'isolement, lui, n'existe ni dans la base ni dans Mathlib ».
- Théorèmes rattachés (champ Vérités) : aucun.
- Note B4 : **O6, O9** (isolement du terme de la paire hors ligne ; la formule explicite ne contraint que la somme) : `explicitIndex_*` et `explicitFormula_counts_members` décrivent la paire comme deux index distincts de la somme ; ils n'isolent pas le terme (le module CriticalityCharacterization le dit : « Ce qui reste est inchangé »).
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

#### O7 — Aucun terme inconditionnel de type RH ne compile ; « ce qui reste se réduit aux deux constats lus sur la seconde Tour, qui s'excluent hors ligne ».
- Théorèmes rattachés (champ Vérités) : `allOnLine_of_regimeCapture` [CONFIRMÉE SOUS CONDITION].
- Note B3 : **O7, O23** — `riemannHypothesis_of_noOff`, `riemannHypothesis_of_noLowerSide`, `riemannHypothesis_of_regimeCapture`, `riemannHypothesis_of_PHeightProgression`, `riemannHypothesis_of_verticalEnergyPush` : chacune ferme RH sous une prémisse ; aucune n'est un terme inconditionnel (O7). L'« universalisation » compilée est `riemannHypothesis_of_noOff` (O23).
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

#### O8 — Sous la loi de liaison, la loi de vérification est fausse en tout zéro de côté bas : la fermeture ne peut venir que d'un énoncé qui contredit la liaison hors ligne.
- Théorèmes rattachés (champ Vérités) : aucun.
- Statut : reste ouvert ; aucun lot ne le touche.

#### O9 — La formule explicite compilée ne contraint que la somme, jamais un terme isolé (frontière de l'isolement).
- Théorèmes rattachés (champ Vérités) : aucun.
- Note B1 : **T9 / O9** : aucun théorème du lot ne porte sur la formule explicite ; non touché.
- Note B4 : **O6, O9** (isolement du terme de la paire hors ligne ; la formule explicite ne contraint que la somme) : `explicitIndex_*` et `explicitFormula_counts_members` décrivent la paire comme deux index distincts de la somme ; ils n'isolent pas le terme (le module CriticalityCharacterization le dit : « Ce qui reste est inchangé »).
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

#### O10 — La cible « caractérisation de la droite critique » (accord des deux grammaires partout) reste ⟺ RH ; « Aucun terme n'en sort ».
- Théorèmes rattachés (champ Vérités) : `pastOnLine_all_iff_riemannHypothesis` [ÉQUIVALENTE À RH].
- Note B4 : **O10** (caractérisation de la droite critique ⟺ RH, « aucun terme n'en sort ») : `pastOnLine_all_iff_riemannHypothesis`, `grammarsAgree_all_iff_pastOnLine_all` sont cette caractérisation compilée ; `fixedLocusSelection_iff_riemannHypothesis` et `xiRealZeros_iff_riemannHypothesis` en sont d'autres formes équivalentes.
- Touché par : `fixedLocusSelection_iff_riemannHypothesis`, `xiRealZeros_iff_riemannHypothesis`.
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

#### O11 — C_lecture (`secondTower_reads_occurrence_iff_coordinate_lt`) reste « une lecture data-dépendante », non clôturée par la rigidification (212/300 lecture, 88/300 V).
- Théorèmes rattachés (champ Vérités) : `secondTower_reads_occurrence_iff_coordinate_lt` [CONFIRMÉE], `remaining_open_question_is_readout_only` [CONFIRMÉE], `secondTower_reads_of_gap_ge_pi` [CONFIRMÉE SOUS CONDITION], `pivotCoordinate_mirror_mem` [CONFIRMÉE SOUS CONDITION], `secondTower_reads_iff_progression_pos` [CONFIRMÉE], `reflected_presents_reversed` [CONFIRMÉE].
- Note B1 : **O11 / O3 (C_lecture)** : `secondTower_reads_occurrence_iff_coordinate_lt` et `countedPrime_eq_occurrence_iff_cell` établissent uniquement l'équivalence « lecture ⟺ Occ(z*) dans un anneau strictement inférieur à celui de p_min(z*) » ; aucun théorème du lot n'établit la lecture sans condition sur le membre miroir hors ligne (le maître la déclare constat lu).
- Note B2 : **O11** : `secondTowerOwnContacts_meets_arithmeticChain`
- Note B2 : O11 / V85 : `secondTowerOwnContacts_meets_arithmeticChain` établit `Occ(z*) <` entrée et dernier rayon `< p_min(z*)` ; son type ne compare pas `Occ(z*)` au dernier rayon (la lecture C_lecture y reste hors énoncé).
- Note B3 : **O11** — `remaining_open_question_is_readout_only`, `secondTower_reads_iff_progression_pos`, `secondTower_reads_of_gap_ge_pi`, `pivotCoordinate_mirror_mem` : C_lecture y est caractérisée (équivalence avec une position d'anneau, avec progression(z*) > 0, condition suffisante par un pas π/T) ; aucun théorème du lot ne la force ni ne l'exclut.
- Note B4 : **O11** (C_lecture, lecture data-dépendante) : `reflected_presents_reversed` établit entrée et dernier rayon de la seconde Tour par rapport à p_min(z*) et rappelle que l'atteinte de Occ(z*) au dernier rayon reste une lecture.
- Touché par : `secondTowerOwnContacts_meets_arithmeticChain`.
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

#### O12 — Aucun lien démontré entre la couche mod 6/M^Z = M et le constat de vérification/lecture.
- Théorèmes rattachés (champ Vérités) : aucun.
- Note B1 : **O12 / O13** : `Grammar/Mod6Rigidity` porte la première couche (états A/B, classes 0/2/4, alternance) ; le lot ne contient aucun théorème sur motifs, familles ou méta-pattern, ni aucun lien avec C_lecture/V.
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

#### O13 — La hiérarchie plus large (motifs, familles, méta-pattern) n'est pas portée dans le code compilé RHV6Fresh.
- Théorèmes rattachés (champ Vérités) : `memberTransition_eq_canonical` [CONFIRMÉE].
- Note B1 : **O12 / O13** : `Grammar/Mod6Rigidity` porte la première couche (états A/B, classes 0/2/4, alternance) ; le lot ne contient aucun théorème sur motifs, familles ou méta-pattern, ni aucun lien avec C_lecture/V.
- Note B4 : **O13** (hiérarchie transition/motif/famille non portée) : `memberTransition_eq_canonical`, `primeTransition_forward` sont la couche « transitions » compilée ; motifs, familles, méta-pattern restent hors code.
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

#### O14 — Savoir si le modèle « premier suivant par rang de la séquence fusionnée » est la bonne représentation d'une insertion hors ligne authentique reste une décision de modélisation non tranchée par un théorème.
- Théorèmes rattachés (champ Vérités) : aucun.
- Statut : reste ouvert ; aucun lot ne le touche.

#### O15 — Lien (β, T) → événements : non évaluable sur aucun zéro hors ligne (aucun ne se calcule).
- Théorèmes rattachés (champ Vérités) : aucun.
- Statut : reste ouvert ; aucun lot ne le touche.

#### O16 — Aucun lien démontré entre la progression (minimum attendu croissant, 300/300) et le constat d'atteinte inversée du propre pivot (0/300).
- Théorèmes rattachés (champ Vérités) : aucun.
- Note B1 : **O16** : `expectedMinimumPrime_succ_of_passage` (minimum attendu strictement croissant, tout β) et `invertedPivotPair_not_reaches` / `secondTower_not_reaches_own_expected` (le pivot propre n'est jamais compté au dernier rayon inversé) sont établis séparément ; le lot ne contient pas de théorème qui les relie.
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

#### O17 — Condition de compatibilité énergétique aux deux raccords, ramenée à exactement deux égalités d'amplitude de `q^β/‖ρ‖` (exposant réel de l'amplitude du terme explicite), non tranchées : aucune tactique automatique.
- Théorèmes rattachés (champ Vérités) : aucun.
- Note B2 : **O17** : `amplitude_le_iff_horizontal_le_vertical`, `verticalDominates_of_verticalEnergyPush`, `zeroTerm_norm`, `pivotCell_amplitude_brackets`, `horizontalRaccords_amplitude_brackets`, `sameCell_four_contacts_bracket`, `energy_balance_two_primes_false`, `riemannHypothesis_of_energyBalance`, `energyBalance_iff_riemannHypothesis`, `riemannHypothesis_of_localReading`
- Note B2 : O17 / O18 / O24 : `energy_balance_two_primes_false`, `riemannHypothesis_of_energyBalance`, `energyBalance_iff_riemannHypothesis` compilent la rigidité à deux raccords et montrent que la prémisse d'équilibre énergétique est équivalente à RH ; les encadrements `pivotCell_amplitude_brackets`, `horizontalRaccords_amplitude_brackets`, `sameCell_four_contacts_bracket` ne forcent aucune égalité ; la taille relative des deux premiers aux raccords (O18) n'est traitée par aucun énoncé du lot.
- Note B4 : **O17, O24** (deux égalités d'amplitude) : `cpow_reflect_product` (produit x^β·x^(1−β) = x) et `explicitFormula_counts_members` (x^β ≤ x^(1−β)) touchent l'amplitude sans trancher.
- Touché par : `amplitude_le_iff_horizontal_le_vertical`, `verticalDominates_of_verticalEnergyPush`, `zeroTerm_norm`, `pivotCell_amplitude_brackets`, `horizontalRaccords_amplitude_brackets`, `sameCell_four_contacts_bracket`, `energy_balance_two_primes_false`, `riemannHypothesis_of_energyBalance`, `energyBalance_iff_riemannHypothesis`, `riemannHypothesis_of_localReading`.
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

#### O18 — Ce qui manque : « une relation de taille, jamais démontrée dans la base ni dans Mathlib, entre la position d'un zéro et la grandeur numérique précise des nombres premiers que la chaîne lui assigne à ses deux raccords ».
- Théorèmes rattachés (champ Vérités) : aucun.
- Note B2 : **O18** : `energy_balance_two_primes_false`
- Note B2 : O17 / O18 / O24 : `energy_balance_two_primes_false`, `riemannHypothesis_of_energyBalance`, `energyBalance_iff_riemannHypothesis` compilent la rigidité à deux raccords et montrent que la prémisse d'équilibre énergétique est équivalente à RH ; les encadrements `pivotCell_amplitude_brackets`, `horizontalRaccords_amplitude_brackets`, `sameCell_four_contacts_bracket` ne forcent aucune égalité ; la taille relative des deux premiers aux raccords (O18) n'est traitée par aucun énoncé du lot.
- Touché par : `energy_balance_two_primes_false`.
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

#### O19 — Le paragraphe de l'hypothèse (poussée verticale engagée ⇒ pas de place pour un zéro hors ligne d'énergie incompatible) est une hypothèse portée par la démonstration, non un théorème.
- Théorèmes rattachés (champ Vérités) : aucun.
- Statut : reste ouvert ; aucun lot ne le touche.

#### O20 — Cette conclusion est locale à la branche verticale ; pour fermer RH il faut établir séparément que la continuité verticale énumère exhaustivement tous les zéros non triviaux du domaine (« ce pont ») ; « reste à établir séparément ».
- Théorèmes rattachés (champ Vérités) : aucun.
- Statut : reste ouvert ; aucun lot ne le touche.

#### O21 — Prémisse `D(z) = 0` (un réel par zéro) équivalente à RH ; la géométrie des Tours n'en décharge aucune partie hors ligne.
- Théorèmes rattachés (champ Vérités) : `zeroInsertionDepth_iff_riemannHypothesis` [ÉQUIVALENTE À RH], `premise_ladder_tfae` [ÉQUIVALENTE À RH].
- Note B3 : **O21** — `zeroInsertionDepth_iff_riemannHypothesis`, `premise_ladder_tfae` : la prémisse D ≡ 0 est équivalente à RH ; `capture_of_onLine` la décharge sur la ligne seulement.
- Note B4 : **O21** (D(z) = 0 équivalent à RH) : voisin des équivalences compilées de cette liste, non lié par le graphe.
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

#### O22 — Statut Lean : RH jamais certifiée Lean-vraie par ce document ; `RH_FOUND = FALSE`.
- Théorèmes rattachés (champ Vérités) : aucun.
- Statut : reste ouvert ; aucun lot ne le touche.

#### O23 — Ouvert par nature : la contradiction « relationnelle » (l. 111) et l'« universalisation » (l. 115) sont dites « transcrites » (l. 227), non établies comme théorèmes inconditionnels : « collision et universalisation transcrites ».
- Théorèmes rattachés (champ Vérités) : `riemannHypothesis_of_noOff` [IMPLIQUE RH SOUS PRÉMISSE], `riemannHypothesis_of_noLowerSide` [IMPLIQUE RH SOUS PRÉMISSE].
- Note B2 : **O23** : `arithmeticChain_and_reflectedFromOrigin_coexist`, `terminalCollision_conditional_on_reflectedObligation`
- Note B2 : O23 / T6 / T5 : `terminalCollision_conditional_on_reflectedObligation`, `arithmeticChain_and_reflectedFromOrigin_coexist`, `properTowerOfMirror_and_reflectedMotion_coexist` : la non-atteinte réfléchie et la chaîne arithmétique (ou la Tour propre du miroir) tiennent ensemble ; le schéma « atteint ∧ n'atteint pas ⟹ ⊥ » n'a de prémisse que réfutée.
- Note B3 : **O7, O23** — `riemannHypothesis_of_noOff`, `riemannHypothesis_of_noLowerSide`, `riemannHypothesis_of_regimeCapture`, `riemannHypothesis_of_PHeightProgression`, `riemannHypothesis_of_verticalEnergyPush` : chacune ferme RH sous une prémisse ; aucune n'est un terme inconditionnel (O7). L'« universalisation » compilée est `riemannHypothesis_of_noOff` (O23).
- Touché par : `arithmeticChain_and_reflectedFromOrigin_coexist`, `terminalCollision_conditional_on_reflectedObligation`.
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

#### O24 — Le compilateur : après injection de tout, résidu = deux égalités d'amplitude, non tranchées.
- Théorèmes rattachés (champ Vérités) : aucun.
- Note B2 : **O24** : `riemannHypothesis_of_energyBalance`
- Note B2 : O17 / O18 / O24 : `energy_balance_two_primes_false`, `riemannHypothesis_of_energyBalance`, `energyBalance_iff_riemannHypothesis` compilent la rigidité à deux raccords et montrent que la prémisse d'équilibre énergétique est équivalente à RH ; les encadrements `pivotCell_amplitude_brackets`, `horizontalRaccords_amplitude_brackets`, `sameCell_four_contacts_bracket` ne forcent aucune égalité ; la taille relative des deux premiers aux raccords (O18) n'est traitée par aucun énoncé du lot.
- Note B4 : **O17, O24** (deux égalités d'amplitude) : `cpow_reflect_product` (produit x^β·x^(1−β) = x) et `explicitFormula_counts_members` (x^β ≤ x^(1−β)) touchent l'amplitude sans trancher.
- Touché par : `riemannHypothesis_of_energyBalance`.
- Statut : reste ouvert (aucun fragment ne signale de théorème qui le ferme sans condition).

## 5. Ajouts : vérités compilées absentes du maître

Propositions d'ajout fusionnées et dédoublonnées (B1–B3), chacune en une phrase au style du maître avec ses théorèmes. Lot d'origine entre crochets ; B4 n'y contribue pas (ses ajouts sont dans la section 8).

1. [B1] Deux Tours propres quelconques ont un décalage de phase strictement inférieur à π/2 ; à même hauteur, leurs grilles de coordonnées de pivot pour toute référence positive sont alignées à un anneau près (écart au plus un). Établie par : `towerPosition_shift_abs_lt_half`, `pivotCoordinate_sameHeight_shift_le_one`.

2. [B1] Pour un zéro de côté bas, tout successeur consécutif est strictement plus à droite que lui et n'excède pas son miroir (β(z) < β(z') ≤ 1−β(z)) ; le même énoncé vaut pour un successeur consécutif de même hauteur. Établie par : `radial_gt_of_consecutive_lowerSide`, `radial_le_mirror_of_consecutive_lowerSide`, `fiberSuccessor_radial_gt`, `fiberSuccessor_radial_le_mirror`.

3. [B1] Tout zéro hors ligne a un côté β < 1/2 : lui-même ou son miroir. Établie par : `off_lowerSide`.

4. [B1] Le minimum attendu de tout zéro est au moins 3. Établie par : `three_le_expectedMinimumPrime`.

5. [B2] Pour tout zéro et tout rang n, la progression continue d'un événement, π·(position de Tour en p_{n+1} − position de Tour en p_n), est strictement positive, majorée par T·log 2 et minorée par T·log(1 + 1/p_n) (T·log(1 + 2/p_n) au-delà du premier 2) ; deux zéros de même hauteur ont la même progression continue à tout rang. — établi par : `phase_increment_pos`, `phase_increment_le_height_mul_log_two`, `phase_increment_ge_height_mul_log_one_add_inv`, `phase_increment_ge_height_mul_log_one_add_two_div`, `phase_increment_eq_of_sameHeight`, `primeSuccessor_le_two_mul`, `primeGap_ge_one`, `primeGap_ge_two_of_two_lt`.

6. [B2] Sous consécutivité stricte, la progression continue du second événement du miroir est strictement positive, vaut exactement T·log(p_{n+2}/p_{n+1}) (fonction de (T, n) seuls) et est bornée par T·log 2 ; la translation miroir rapportée à cette progression est strictement majorée par (1 − 2β)/(T²·log(p_{n+2}/p_{n+1})). — établi par : `mirror_continuous_progression_pos`, `off_consecutive_continuous_progression_eq_span`, `consecutive_continuous_signature`, `mirror_translation_over_next_progression_lt`.

7. [B2] Un minorant local c de la progression continue donne la borne locale T ≥ c / log(p_{n+1}/p_n) ; une seule hauteur T suffit à satisfaire un même minorant c aux deux arêtes consécutives n et n+1 dès que T dépasse un seuil ; aucune constante globale n'est posée. — établi par : `height_lower_bound_of_phase_quantum`, `quantum_pair_satisfiable_at_same_height`.

8. [B2] L'énergie du terme explicite se décompose exactement : log‖terme(l,q)‖ − log‖terme(e,q)‖ = H − V avec H = (β_l − β_e)·log q (énergie horizontale) et V = log‖ρ_l‖ − log‖ρ_e‖ (énergie verticale) ; l'amplitude du postérieur est au plus celle de l'antérieur si et seulement si H ≤ V ; dès que β_e < β_l et que q dépasse exp(V/(β_l − β_e)), la Tour postérieure domine strictement. — établi par : `log_amplitude_ratio_eq`, `amplitude_le_iff_horizontal_le_vertical`, `sameHeight_horizontal_dominates`, `verticalDominates_of_verticalEnergyPush`.

9. [B2] L'amplitude du terme au premier q est strictement supérieure à celle du contact d'entrée de sa cellule et au plus égale à celle du dernier rayon ; la même chose vaut aux deux raccords Occ(l) et p_min(l) pour tout couple de zéros ; si deux zéros lisent la même coordonnée de pivot, chacun est encadré par ses deux contacts indexés par le même entier ; à même hauteur deux zéros lisent des coordonnées de pivot qui diffèrent d'au plus un cran. — établi par : `pivotCell_amplitude_brackets`, `horizontalRaccords_amplitude_brackets`, `sameCell_four_contacts_bracket`, `sameHeight_pivotCoordinate_dichotomy`, `horizontal_cell_dichotomy_at_raccords`.

10. [B2] Sur tout passage, l'excès inter-Tours J(p) vaut (T_l − T_e)·log(p_{n+2}/p_{n+1}) ; J(p) > 0 si et seulement si T_e < T_l, J(p) = 0 si et seulement si T_e = T_l, J(p) ≥ 0 toujours ; la hauteur du membre antérieur est toujours au plus celle du postérieur. — établi par : `interTowerExcess_eq`, `interTowerExcess_pos_iff`, `interTowerExcess_eq_zero_iff`, `interTowerExcess_nonneg`, `passage_height_le`.

11. [B2] La grammaire par rang (place +1, raccord, occurrence croissante) est vraie sur tout passage, ON comme OFF ; un zéro hors ligne fournit un passage qui la satisfait avec un excès inter-Tours nul : elle ne sépare pas ON de OFF. — établi par : `rank_grammar_unconditional`, `grammar_hypotheses_of_passage`, `rank_grammar_forces_no_displacement`, `off_excess_zero`, `onLine_passage_shares_grammar_context`.

12. [B2] L'excès inter-Tours strictement positif sur tout passage (même avec les trois hypothèses grammaticales, même restreint aux passages à extrémité hors ligne), la grammaire par hauteurs et l'équilibre énergétique aux deux raccords sont chacun équivalents à RH. — établi par : `interTowerExcess_pos_iff_riemannHypothesis`, `offPassages_interTowerExcess_pos_iff_riemannHypothesis`, `interTowerExcess_pos_of_grammar_iff_riemannHypothesis`, `displacement_forced_iff_grammarByHeight`, `grammarByHeight_iff_riemannHypothesis`, `energyBalance_iff_riemannHypothesis`, `riemannHypothesis_of_energyBalance`.

13. [B2] La lecture énergétique orientée au raccord Occ(l) (amplitude du postérieur ≤ amplitude de l'antérieur) tient en mode A, est fausse au raccord en mode C dès T ≥ 2, est impliquée par RH, et, modulo « tout zéro hors ligne a T ≥ 2 » (fait classique hors base), est équivalente à RH. — établi par : `localReading_modeA`, `localReading_fails_modeC`, `localReading_of_riemannHypothesis`, `riemannHypothesis_of_localReading`, `localReading_iff_riemannHypothesis`.

14. [B2] Pour un état de Tour d'un zéro b et le minimum attendu d'un zéro quelconque a, le dernier premier lu à l'état atteint (resp. reste strictement sous) le minimum attendu de a si et seulement si le contact supérieur de l'état l'atteint (resp. reste strictement sous). — établi par : `expectedMinimum_le_stateReadout_iff`, `stateReadout_lt_expectedMinimum_iff`.

15. [B2] Le point complexe ρ d'un zéro a pour partie réelle β et pour partie imaginaire T, est non nul, ρ + 1 est non nul, ρ ≠ −1, tout membre est un zéro non trivial au sens de la formule explicite de la base ; pour q > 0, q^ρ a pour parties réelle et imaginaire q^β·cos(T·log q) et q^β·sin(T·log q), et le terme explicite a pour partie imaginaire q^β(β·sin θ − T·cos θ)/‖ρ‖², θ = T·log q. (Lemmes de support.) — établi par : `zeroPoint_re`, `zeroPoint_im`, `zeroPoint_ne_zero`, `zeroPoint_add_one_ne_zero`, `zeroPoint_ne_neg_one`, `zeroPoint_isNontrivial`, `cpow_zeroPoint_re`, `cpow_zeroPoint_im`, `zeroTerm_im`.

16. [B2] Deux entiers ne peuvent être ordonnés à la fois `a ≤ b` et `b < a` (lemme d'ordre conservé). — établi par : `expected_le_counted_lt_expected_false`.

17. [B3] Le miroir d'un zéro lit la même portée première et progresse en phase exactement comme lui sur tout intervalle : la fréquence est identique, seul l'offset de phase constant distingue la paire. — établi par : `mirror_span_eq`, `mirror_phase_increment_eq`, `mirror_phase_offset_const`, `phase_increment_eq_pi_span`. [fusionné avec B3 : La portée de Tour d'une place est l'accroissement de phase π·ΔΘ du terme explicite du zéro entre les deux premiers de la place, et sur un passage elle vaut T_E/π·log(Occ(L)/Occ(E)). — établi par : `phase_increment_eq_pi_span`, `passage_span_eq_log_occurrences`, `passage_span_pos`.]

18. [B3] Les rayons d'un zéro ont la forme exacte exp((arctan(T/β)+kπ)/T), et le rayon k du miroir est celui de z multiplié par le facteur unique exp(−πD/T), avec D = (arctan(T/β) − arctan(T/(1−β)))/π, |D| < 1/2, de signe de 1/2 − β. — établi par : `contactMinusAt_eq_exp`, `insertionDepth_eq`, `mirror_contact_eq_depth`, `mirror_contact_ratio_const`, `abs_insertionDepth_lt_half`, `insertionDepth_pos_iff`, `phase_lt_iff`.

19. [B3] À même hauteur, la grille d'un zéro w est la grille de z translatée par un facteur unique, et le pas logarithmique ne voit pas β ; à même position radiale, un changement de hauteur change le pas. — établi par : `sameHeight_grid_rigid_translation`, `passage_grid_translation_of_sameHeight`, `sameHeight_pitch_invariant`, `sameRadial_height_changes_pitch`.

20. [B3] Sur un rayon, le terme explicite est réel de signe (−1)^k et d'amplitude C_k^β/‖ρ‖, et d'un rayon au suivant l'amplitude est multipliée par exp(πβ/T). — établi par : `ray_energy`, `ray_energy_alternates`, `ray_energy_growth`, `zeroTerm_re_eq_cos_towerPosition`.

21. [B3] Le rapport énergétique de deux zéros vaut q^{Δβ}·‖ρ_e‖/‖ρ_l‖ ; il est constant en q ssi Δβ = 0, et non borné dès que β_e < β_l ; à même β, la hauteur la plus grande porte strictement moins d'énergie en tout q > 0. — établi par : `energyRatio_eq`, `energyRatio_const_iff`, `energyRatio_unbounded_of_deltaBeta_pos`, `amplitude_lt_of_height_lt`, `amplitude_inverts_of_radial_lt`.

22. [B3] Sur tout passage, ou bien la hauteur progresse, ou bien (même hauteur) l'énergie du later domine celle de l'earlier au-delà d'un seuil ; à même hauteur T ≥ 2, elle la domine dès q ≥ 2, donc aux deux raccords. — établi par : `passage_energy_sign_dichotomy`, `sameHeight_amplitude_inverts_at_primes`, `sameHeight_amplitude_inverts_at_raccords`.

23. [B3] La poussée verticale énergétique (l'énergie du later n'excède jamais celle de l'earlier) est équivalente à RH. — établi par : `verticalEnergyPush_iff_riemannHypothesis`, `riemannHypothesis_of_verticalEnergyPush`, `verticalEnergyPush_of_riemannHypothesis`.

24. [B3] Sur tout passage, l'excès inter-Tours J vaut (T_l − T_e)·log(p_{n+2}/p_{n+1}), est positif ou nul, et nul exactement à même hauteur ; la double contrainte grammaire-géométrie-excès est satisfaite par tout passage, ON ou OFF. — établi par : `double_constraint_required_displacement`, `passage_double_constraint`, `succession_invariants`.

25. [B3] Sur tout passage, p_min(l) = p_{n_e+2} en plus de Occ(l) = p_min(e) = p_{n_e+1} ; le successeur pointe sur le minimum attendu du précédent et sa cellule contient son propre minimum attendu. — établi par : `passage_raccords`, `regime_captive_of_prime`.

26. [B3] Le glissement OFF sur le carré des deux horloges : la place avance de un, la hauteur d'événement ne bouge pas, la portée est identique ; l'horloge des hauteurs est toujours en retard ou à l'heure sur celle des membres, et leur accord est équivalent à RH. — établi par : `off_clock_slip`, `clock_h_le_n`, `clock_ph_le_pn`, `clock_agree_iff_riemannHypothesis`, `onLine_clock_sync`.

27. [B3] La capture de régime (β_e = 1/2 ⟹ β_l = 1/2 sur tout passage) équivaut à RH modulo le plus bas zéro sur la ligne ; hors ligne, un zéro entre comme successeur d'un zéro de la ligne. — établi par : `regimeCapture_iff_riemannHypothesis`, `riemannHypothesis_of_regimeCapture`, `off_enters_regime`, `exists_consecutive_predecessor`.

28. [B3] Sous β < 1/2, la translation de phase du miroir vaut arctan(T(1−2β)/(β(1−β)+T²)), strictement dans ]0,(1−2β)/T[ ; la coordonnée de pivot du miroir est celle de z ou la suivante, et, sous consécutivité stricte, se décompose en la progression première plus δk ∈ {0,1}. — établi par : `mirror_phase_gap_eq_arctan`, `mirror_phase_gap_lt`, `pivotCoordinate_mirror_mem`, `mirror_pivot_decomposition_of_consecutive`, `mirror_pivot_mono_of_consecutive`.

29. [B3] La lecture de la seconde Tour équivaut à progression(z*) > 0, et un pas entier π/T entre Occ(z*) et p_min(z*) suffit à la lecture. — établi par : `secondTower_reads_iff_progression_pos`, `secondTower_reads_of_gap_ge_pi`, `coordinate_lt_of_gap_ge_pi`, `sameRing_imp_gap_lt_pi`.

30. [B3] Deux zéros de même norme de support et de même phase de Tour sont le même zéro. — établi par : `zeroPoint_eq_of_phase_norm_eq`, `phase_norm_ne_of_ne`.

31. [B3] Pour β < 1/2, V(z, z*) > 0 et V(z, z*) = 0 ssi β = 1/2 : l'énergie verticale de la paire miroir ne s'annule que sur la ligne. — établi par : `mirror_verticalEnergy_pos`, `mirror_verticalEnergy_eq_zero_iff`.

Théorèmes marqués AJOUT non repris dans un item ci-dessus (lemmes de support ou trop locaux) : `nat_le_exp_div_iff`, `reaches_and_not_reaches_false`, `tendsto_conj_nhds`, `analyticAt_conj_conj`, `analyticOrderAt_conj_conj`, `two_pi_ne_zero'`, `Efac_ne_zero`, `analyticAt_Efac`, `riemannZeta_analyticOnNhd_compl_one`, `isConnected_compl_one`, `nullPassage_offLine`, `heightEventIndex_le_sourceIndex`, `mirror_translation_factor_eq_one_iff`, `mirror_contact_lt_iff`, `contact_lt_mirror_iff`, `arctan_sub_le`, `cos_phase_eq`, `zeroTerm_re`, `mirror_phase_lt`, `towerPosition_mirror_sub`, `regimeCapture_of_riemannHypothesis`, `allOnLine_of_regimeCapture`, `pivotCoordinate_mono`, `progression_nonneg`, `passage_heightEventIndex_dichotomy`, `clock_Sn_pos`, `zeroPoint_norm_pos`, `zeroPoint_norm_eq_of_eq`, `one_lt_log_four`, `one_add_lt_four_rpow`, `offMirror_all_elements_hold_and_vertical_force_fails`, `memberHeightTransport_iff_index`, `transport_at_z_gives_nothing`, `primeTransition_forward`, `reversedTransition_backward`, `heightEventTransition_fst`, `reflectedEquivariance_all_iff_noZero`, `reflectedHeightEquivariance_all_iff_noZero`, `explicitIndex_val`, `heightsBelow_subset_image`, `mirror_radialOffset`, `mirror_radialOffset_sq`, `radialOffset_eq_zero_iff_onLine`, `completedZeta_eq_mul`, `Gammaℝ_conj`, `completedZeta_conj`, `completedZeta_zetaReflect`, `centeredPoint_re`, `centeredPoint_im`, `zetaReflect_centeredPoint`, `support_eq_centeredPoint`, `completedZeta_centered_neg`, `xiReal_even`, `xiImag_odd`, `xiImag_zero_onLine`, `completedZeta_eq_zero_iff`, `centeredPoint_nontrivialZero_iff`, `onLine_zero_iff_xiReal`, `pair_same_conditions`, `radialOffset_abs_lt`, `off_member_two_equations`, `centeredPoint_not_trivial`, `centeredPoint_ne_one`, `fixedLocusSelection_iff_riemannHypothesis`, `centeredPoint_eq_add`, `hasDerivAt_completedZeta_centered`, `hasDerivAt_xiReal`, `hasDerivAt_xiImag`, `deriv_completedZeta_re_onLine`, `deriv_completedZeta_onLine`, `deriv_eq_zero_iff_oddFactor`, `oddFactor_eq_deriv_xiImag`, `hasDerivAt_xiReal_height`, `radial_height_derivative_same_norm`, `deriv_nonneg_of_pos_right`, `deriv_nonpos_of_pos_left`, `constant_sign_of_no_zero`, `deriv_sign_alternates_at_consecutive_zeros`, `oddFactor_sign_alternates`, `scanConstraint_of_riemannHypothesis`, `scanConstraint_gives_only_height_avoidance`, `trivial_zero_not_completedZeta_zero`, `completedZeta_centered_eq_zero_iff`, `xiRealZeros_iff_riemannHypothesis`, `weilPairTerm_onLine`, `weilPairTerm_nonneg_onLine`, `weilPairTerm_test_eq`, `weilPairTerm_off_neg`, `weilPairPositivity_iff_onLine`, `allNontrivial_onLine_iff_riemannHypothesis`, `weilPairPositivity_zeta_iff_riemannHypothesis`, `offPairConfig_not_weilPositive`, `weilPairPositivity_not_from_config`, `zeroSideWindow_nonneg_of_onLine`, `zeroSideWindow_zeta_nonneg_of_riemannHypothesis`, `conj_zetaReflect`, `zetaReflect_eq_conj`, `cpow_zetaReflect`, `cpow_reflect_product`, `weilPairTerm_perron_eq`, `perronPairDenominator_re_pos`, `perronPairDenominator_ne_zero`, `weilPairTerm_perron_pos`, `perronFamily_positive_zeta`, `perronFamily_positive_offPair`, `perronFamily_positivity_not_riemannHypothesis`.

## 6. Tensions internes du maître T1…T20 éclairées par le code

Aucune tension n'est résolue par avis : on donne ce que disent les fragments sur les théorèmes compilés.

#### T1 — tension interne (fichiers retirés cités comme compilés)
- Énoncé de la tension (maître) : le maître cite `Terminal/PairHeightGap.lean` (l. 107) et `Terminal/InversionClosure.lean` (l. 107) comme « Compilé » ; CLAUDE.md §4 (destruction de « V » et `Xor`, 2026-09-26) indique ces fichiers retirés (`ls RHV6Fresh/Terminal` : absents ; présents : `ReflectedObligation`, `ExplicitFormulaLink`, `CriticalityCharacterization`, `EventHeightProgression`). L. 107 cite aussi comme « compilée » la collision (l. 107, l. 133, l. 137, l. 227) alors que CLAUDE.md dit « il n'existe plus aucune route de collision dans le code ».
- Ce que dit le code (B3) : **T1 / T15** — `mirror_heightEventIndex_eq` (docstring) renvoie à `Terminal/MirrorEventCollision.lean`, fichier de piste parquée (CLAUDE.md, purge 2026-09-27), toujours présent dans le code.
- Ce que dit le code (B4) : **T1** (fichiers retirés cités comme compilés) : le docstring de RHV6Demonstration cite `Terminal/PairContradiction.lean` et `RHV6Closure.lean`, absents du dépôt (`ls` : aucun des deux fichiers), retirés par CLAUDE.md §4 (destruction de « V » et `Xor`).

#### T2 — tension interne (théorème vs transcrit)
- Énoncé de la tension (maître) : l. 129, l. 133 et l. 107 classent la collision, l'exclusion et l'« universalisation » parmi les théorèmes ; l. 137 place les deux constats en « Frontière, transcrite mais non encore théorème du code » ; l. 227 dit « collision et universalisation transcrites ». (Aussi l. 111–115 conclut RH par cette collision.)
- Ce que dit le code : aucun fragment ne rattache de théorème à cette tension (elle porte sur le texte du maître).

#### T3 — tension interne
- Énoncé de la tension (maître) : l. 129 « Tout ce qui précède les deux lois de l'inversion est théorème : … la naissance des deux constats, leur exclusion, l'universalisation » vs l. 93 et l. 105 « Sa transcription n'est pas encore théorème du code » (question close, loi de liaison) ; les deux lois de l'inversion sont pourtant dites reste (l. 129).
- Ce que dit le code : aucun fragment ne rattache de théorème à cette tension (elle porte sur le texte du maître).

#### T4 — tension interne (conclusion RH vs statut)
- Énoncé de la tension (maître) : l. 111–115 « Donc aucun zéro distinct ne peut exister hors de la droite critique… C'est l'hypothèse de Riemann » vs l. 127 « aucun tel terme ne compile », l. 143, l. 195 `RH_FOUND = FALSE`, l. 129 (les deux lois hors ligne s'excluent, fermeture non venant), l. 209 « Ceci n'est pas une preuve de RH ».
- Ce que dit le code : aucun fragment ne rattache de théorème à cette tension (elle porte sur le texte du maître).

#### T5 — tension interne (la seconde Tour atteint / n'atteint pas son pivot)
- Énoncé de la tension (maître) : l. 117 « la seconde Tour atteint son pivot et lit son occurrence à son entrée, par théorème » ; l. 91, l. 139 (« aucun événement d'arrêt depuis leur origine ») ; l. 159 « la seconde Tour, lue au sens de sa propre orientation inversée, n'atteint jamais son propre pivot (0/300) » ; l. 111 « la seconde ne l'atteint pas » ; l. 105 « elle a atteint ce minimum ». Plusieurs sens de « atteindre » / de « seconde Tour » coexistent ; l. 137 fixe « atteindre = compté jusqu'au dernier rayon ».
- Ce que dit le code (B1) : **T5 / T6 (seconde Tour : atteint / n'atteint pas ; deux descriptions)** : `secondTower_entry_reaches_own_expected` (l'entrée atteint p_min(z*)) coexiste avec `secondTower_not_reaches_own_expected` (le dernier rayon ne l'atteint pas) et avec `reflected_no_stop_event` / `reflectedFromOrigin_never_reaches_expectedMinimum` (le mouvement réfléchi depuis son origine n'atteint aucun premier) ; `invertedPairAt_eq_reflected` place la paire inversée sur l'anneau réfléchi à la coordonnée −(k+1), tandis que `invertedPairAt_coordinate_le_zero` montre que ces coordonnées sont hors du domaine j ≥ 1 du mouvement réfléchi depuis son origine.
- Ce que dit le code (B2) : **T5** : `properTowerOfMirror_and_reflectedMotion_coexist`
- Ce que dit le code (B2) : O23 / T6 / T5 : `terminalCollision_conditional_on_reflectedObligation`, `arithmeticChain_and_reflectedFromOrigin_coexist`, `properTowerOfMirror_and_reflectedMotion_coexist` : la non-atteinte réfléchie et la chaîne arithmétique (ou la Tour propre du miroir) tiennent ensemble ; le schéma « atteint ∧ n'atteint pas ⟹ ⊥ » n'a de prémisse que réfutée.
- Ce que dit le code (B3) : **T5 / T6** — `secondTower_inversion_is_unconditional` : les contacts de la seconde Tour sont exprimés par `reflectedIncidence` du miroir à coordonnées −(k+1) et −(k+1)+1 (k = coordonnée pivot du miroir) ; la même Tour est décrite ailleurs comme n'ayant aucun arrêt depuis son origine (`reflected_reads_no_prime`, `reflected_mirror_reads_nothing`). Le lot n'arbitre pas.
- Ce que dit le code (B4) : **T5, T6** (seconde Tour : atteint/n'atteint pas ; deux descriptions) : `reflection_creates_no_prime_event` (mouvement depuis son origine, aucun premier) et `reflected_presents_reversed` / `reflected_presents_via_functional_reflect` (seconde Tour sur le membre miroir, entrée au moins p_min(z*)) sont deux théorèmes compilés côte à côte dans le même module ; ils ne se contredisent pas.

#### T6 — tension interne (deux descriptions de la seconde Tour)
- Énoncé de la tension (maître) : l. 51/l. 89 décrivent un parcours qui « part de l'origine canonique… s'arrête au pivot » avec inversion des contacts (théorème) ; l. 91/l. 139/l. 159 disent que le mouvement réfléchi n'a aucun événement d'arrêt depuis sa propre origine et que l'événement d'arrêt est celui du membre miroir sur son pivot. (CLAUDE.md §4 : `secondTowerOf` n'est pas obtenu en suivant ce mouvement ; non résolu dans le maître.)
- Ce que dit le code (B1) : **T5 / T6 (seconde Tour : atteint / n'atteint pas ; deux descriptions)** : `secondTower_entry_reaches_own_expected` (l'entrée atteint p_min(z*)) coexiste avec `secondTower_not_reaches_own_expected` (le dernier rayon ne l'atteint pas) et avec `reflected_no_stop_event` / `reflectedFromOrigin_never_reaches_expectedMinimum` (le mouvement réfléchi depuis son origine n'atteint aucun premier) ; `invertedPairAt_eq_reflected` place la paire inversée sur l'anneau réfléchi à la coordonnée −(k+1), tandis que `invertedPairAt_coordinate_le_zero` montre que ces coordonnées sont hors du domaine j ≥ 1 du mouvement réfléchi depuis son origine.
- Ce que dit le code (B2) : **T6** : `arithmeticChain_and_reflectedFromOrigin_coexist`, `terminalCollision_conditional_on_reflectedObligation`, `properTowerOfMirror_and_reflectedMotion_coexist`
- Ce que dit le code (B2) : O23 / T6 / T5 : `terminalCollision_conditional_on_reflectedObligation`, `arithmeticChain_and_reflectedFromOrigin_coexist`, `properTowerOfMirror_and_reflectedMotion_coexist` : la non-atteinte réfléchie et la chaîne arithmétique (ou la Tour propre du miroir) tiennent ensemble ; le schéma « atteint ∧ n'atteint pas ⟹ ⊥ » n'a de prémisse que réfutée.
- Ce que dit le code (B3) : **T5 / T6** — `secondTower_inversion_is_unconditional` : les contacts de la seconde Tour sont exprimés par `reflectedIncidence` du miroir à coordonnées −(k+1) et −(k+1)+1 (k = coordonnée pivot du miroir) ; la même Tour est décrite ailleurs comme n'ayant aucun arrêt depuis son origine (`reflected_reads_no_prime`, `reflected_mirror_reads_nothing`). Le lot n'arbitre pas.
- Ce que dit le code (B4) : **T5, T6** (seconde Tour : atteint/n'atteint pas ; deux descriptions) : `reflection_creates_no_prime_event` (mouvement depuis son origine, aucun premier) et `reflected_presents_reversed` / `reflected_presents_via_functional_reflect` (seconde Tour sur le membre miroir, entrée au moins p_min(z*)) sont deux théorèmes compilés côte à côte dans le même module ; ils ne se contredisent pas.

#### T7 — tension interne (rôle du constat de vérification)
- Énoncé de la tension (maître) : l. 95, l. 107 « constat lu, jamais une hypothèse, jamais un théorème » ; l. 107 (même paragraphe) « la vérification est un théorème » sur la droite ; l. 135/137 « chacun équivalent à une position d'anneau, par théorème » ; l. 137 « sous consécutivité stricte chacun est la négation de l'autre ».
- Ce que dit le code (B1) : **T7 / T20 (rôle et étiquette du constat de vérification)** : `secondTower_verification_iff_not_reads_of_consecutive` rend le constat de vérification équivalent, sous consécutivité stricte, à la négation de la lecture ; l'étiquette « V » figure dans les docstrings de `pivotCell_mirror_reaches_expected`, `lock_imp_pivot_lt_expected`, `lock_imp_counted_lt_occurrence` et `not_reaches_of_lastRay_lt`.

#### T8 — tension interne (lecture forcée ?)
- Énoncé de la tension (maître) : l. 93/l. 105 « question close … n'est pas rouvert » (la seconde Tour lit) ; l. 151 (E085) « la lecture… jamais 300/300 » ; l. 129 « sous cette loi, la loi de vérification est fausse en tout zéro de côté bas » ; l. 139 « dans les six situations… les deux constats ne tiennent jamais ensemble ». Le maître affirme à la fois la lecture close et la data-dépendance de C_lecture (l. 151, l. 193).
- Ce que dit le code (B4) : **T8** (lecture forcée ?) : `reflected_presents_reversed` ne force pas la lecture de Occ(z*) au dernier rayon.

#### T9 — tension interne (somme vs terme isolé)
- Énoncé de la tension (maître) : l. 129 « La formule explicite compilée ne contraint que la somme… jamais un terme isolé » et « le théorème d'isolement… n'existe ni dans la base ni dans Mathlib » vs l. 181 « le terme énergétique de chaque zéro est déjà, par construction, un objet isolé propre à ce zéro seul » et « Ce résidu ne porte pas sur une somme » ; l. 107 « le terme de la Tour est la dérivée du terme du zéro dans cette reconstruction ».
- Ce que dit le code (B1) : **T9 / O9** : aucun théorème du lot ne porte sur la formule explicite ; non touché.
- Ce que dit le code (B2) : **T9** : `explicit_term_of_member`, `explicit_term_derivative`
- Ce que dit le code (B2) : T9 : `explicit_term_of_member`, `explicit_term_derivative` traitent le terme d'un seul zéro comme objet isolé ; aucun énoncé du lot n'isole un terme dans la somme sur les zéros.
- Ce que dit le code (B3) : **T9** — `energyRatio_eq`, `horizontal_energy_action`, `sameHeight_amplitude_inverts_at_primes` : les termes `zeroTerm z q` sont traités comme objets propres à un zéro, sans passer par la somme sur les zéros (cohérent avec le maître l. 181, en tension avec l. 129).

#### T10 — tension interne (renvoi « ci-dessus » orienté vers le bas)
- Énoncé de la tension (maître) : l. 163 cite « la rigidité modulo six de la grammaire première historique… (ci-dessus) » alors que ce paragraphe (l. 187–193) vient plus loin ; de même l. 165, l. 167 « rigidification confirmée, ci-dessus » (précédent, correct) mais l. 163 « ci-dessus » pour mod 6 (suivant).
- Ce que dit le code : aucun fragment ne rattache de théorème à cette tension (elle porte sur le texte du maître).

#### T11 — tension interne (numérotation/sections)
- Énoncé de la tension (maître) : le titre `## 11 quinquies` (l. 197) n'a pas de `11 bis/ter/quater` dans le fichier ; les sous-blocs du §11 (l. 129–195) sont des paragraphes en gras non numérotés, alors que l. 93/l. 105 renvoient à « section onze » et l. 141 à « section dix » pour l'interdiction de la prémisse fidélité (§10 l. 121 ne nomme pas cette prémisse). Le §12 est ensuite intitulé « 12 ».
- Ce que dit le code : aucun fragment ne rattache de théorème à cette tension (elle porte sur le texte du maître).

#### T12 — tension interne (« pivot de la première Tour » : deux lectures)
- Énoncé de la tension (maître) : l. 91 « Le pivot de la première Tour est le minimum attendu du zéro original » (première Tour du zéro) puis l. 91 « Les deux Tours du miroir, sa première Tour et la seconde Tour… arrêtent… dans le même anneau, celui du minimum attendu du miroir » (première Tour du miroir) ; l. 89 « sa première Tour » désigne selon le contexte celle du zéro ou celle du miroir. Non résolu dans le maître.
- Ce que dit le code : aucun fragment ne rattache de théorème à cette tension (elle porte sur le texte du maître).

#### T13 — tension interne (ordre et « argument scientifique »)
- Énoncé de la tension (maître) : l. 13 « ne… jamais un argument scientifique de la preuve » vs l. 89, l. 107 « la nullité de la progression de la partie imaginaire n'y entre que par l'ordre, qui fait du miroir un membre postérieur » (l. 107) et l. 131 (second disjoint dans l'ordre, via `mirror` postérieur).
- Ce que dit le code (B1) : **T13 / V68 (ordre, miroir strictement consécutif)** : `fiberSuccessor_eq_mirror_or_precedes` (dichotomie : le successeur consécutif est le miroir ou précède strictement le miroir) et `fiberSuccessor_eq_mirror_of_noInterposition` ne fixent « successeur = miroir » que sous absence d'interposition ; `mirror_sourceIndex_of_consecutive` et `expectedMinimum_eq_mirror_occurrence_of_consecutive` supposent la consécutivité stricte de la paire (z, miroir).

#### T14 — tension interne (expériences synthétiques)
- Énoncé de la tension (maître) : l. 15 « aucune expérience synthétique ne vaut », l. 17 « exclusivement les zéros publiés par Odlyzko » vs l. 139 (E086 : « partie réelle 0,4, 0,6 et 0,8 ordonnées par l'auteur, jamais des zéros »), l. 151 (E085 sur β synthétique), l. 159 (« β synthétique »), l. 193 (« synthétiquement hors d'elle »).
- Ce que dit le code : aucun fragment ne rattache de théorème à cette tension (elle porte sur le texte du maître).

#### T15 — tension interne (fichiers parqués cités comme actifs)
- Énoncé de la tension (maître) : l. 131 cite `Terminal/CriticalityCharacterization.lean` comme « Compilé » ; CLAUDE.md §4 (Purge du 2026-09-27) le range parmi les pistes parquées (le fichier existe toujours dans `Terminal/`).
- Ce que dit le code (B3) : **T1 / T15** — `mirror_heightEventIndex_eq` (docstring) renvoie à `Terminal/MirrorEventCollision.lean`, fichier de piste parquée (CLAUDE.md, purge 2026-09-27), toujours présent dans le code.
- Ce que dit le code (B4) : **T15** (fichiers parqués cités comme actifs) : CriticalityCharacterization, cité comme « Compilé » par le maître (l. 131), est parqué par CLAUDE.md ; ce lot en montre les 17 théorèmes compilés, sans dépendance active.

#### T16 — tension interne (chiffres)
- Énoncé de la tension (maître) : l. 53 « les trois cents premiers zéros… les quinze contacts historiques » et l. 103 « Sur les quinze zéros publiés » ; l. 137 cite « 220/299 » et « 299/299 » (retirés) et l. 159 cite « 0/300, 300/300 » ; l. 139/l. 151 « un peu moins d'un tiers » vs « 88/300 V » (cohérent) mais l. 53 « près d'un tiers » pour cible > référence : deux « tiers » de sens différents.
- Ce que dit le code : aucun fragment ne rattache de théorème à cette tension (elle porte sur le texte du maître).

#### T17 — tension interne (« seule question ouverte »)
- Énoncé de la tension (maître) : l. 193 « C_lecture/V… reste la seule question ouverte et data-dépendante de ce maître » vs l. 129 (le reste = isoler le terme de la paire hors ligne), l. 181 (deux égalités d'amplitude, relation de taille manquante), l. 185 (pont d'exhaustivité), l. 209 (D ≡ 0 ⟺ RH).
- Ce que dit le code : aucun fragment ne rattache de théorème à cette tension (elle porte sur le texte du maître).

#### T18 — tension interne (hypothèse « que porte la démonstration »)
- Énoncé de la tension (maître) : l. 183 formule l'hypothèse (poussée verticale ⇒ pas de place pour un OFF) alors que l. 129 dit « Aucune hypothèse ne remplace cet énoncé » et §10 (l. 121) interdit toute hypothèse non déchargée dans un terme final ; l. 185 précise qu'elle est locale.
- Ce que dit le code : aucun fragment ne rattache de théorème à cette tension (elle porte sur le texte du maître).

#### T19 — tension interne (statut normatif)
- Énoncé de la tension (maître) : l. 125 « normatif pour le sens scientifique entier » vs l. 5 « peuvent contenir des erreurs et sont corrigés dès qu'un théorème compilé les contredit ».
- Ce que dit le code : aucun fragment ne rattache de théorème à cette tension (elle porte sur le texte du maître).

#### T20 — tension interne (vérification lue vs V)
- Énoncé de la tension (maître) : l. 107 le constat de vérification est décrit comme « le dernier rayon sous le minimum attendu du zéro original » ; l. 151 précise que E085 nomme « V » l'événement `C⁺ < p_min`, « qui est la lecture compilée `reads` » ; le maître garde donc deux emplois du sigle « V ».
- Ce que dit le code (B1) : **T7 / T20 (rôle et étiquette du constat de vérification)** : `secondTower_verification_iff_not_reads_of_consecutive` rend le constat de vérification équivalent, sous consécutivité stricte, à la négation de la lecture ; l'étiquette « V » figure dans les docstrings de `pivotCell_mirror_reaches_expected`, `lock_imp_pivot_lt_expected`, `lock_imp_counted_lt_occurrence` et `not_reaches_of_lastRay_lt`.
- Ce que dit le code (B3) : **T20** — `secondTower_reads_iff_progression_pos` : la docstring dit « C_lecture EST progression ≥ 1 ; sa négation V EST progression = 0 » ; le sigle V y désigne la négation de la lecture (`reads`), cohérent avec le glossaire du maître (V = négation de C_lecture) mais deux emplois du sigle coexistent.

## 7. Incidents

**Incidents transversaux (données de l'extraction et fragments).**

- Dépendance parquée : `mirror_sameHeightIndex` (`Terminal/MirrorEventCollision`, piste parquée) → `mirror_heightEventIndex_eq` (`Terminal/MirrorFrequency`, module actif), et par elle `off_consecutive_translation_signature`, `off_mirror_same_frequency`, `off_mirror_same_frequency_of_consecutive`, `onLine_mirror_trivial` ; seul lien de ce type (B4). CLAUDE.md dit qu'aucune piste parquée n'est sur la voie active ; le fait établi est plus étroit (une dépendance de preuve).
- Docstrings périmés citant des fichiers retirés : la docstring de `RHV6Demonstration.lean` renvoie à `Terminal/PairContradiction.lean` et `RHV6Closure.lean`, retirés le 2026-09-26 (B4) ; le maître cite `PairHeightGap.lean` et `InversionClosure.lean` (V94, T1).
- 51 oleans orphelins (source absente) dans `.lake/build`, exclus de l'extraction (`RHV6Fresh_modules.tsv`) ; 10 théorèmes privés ; 720 théorèmes par grep contre 742 extraits.
- Aucun `sorryAx`, aucun axiome hors standard, aucun terme de type exactement `RiemannHypothesis` sans hypothèse (résultat des quatre lots).

**Incidents par lot (verbatim des fragments : docstring ≠ type, noms promettant plus que le type, autres).**

- [B1] `sorryAx` : 0 théorème(s) du lot.
- [B1] Axiome hors standard : 0 théorème(s) du lot (tous les axiomes sont dans {propext, Classical.choice, Quot.sound} d'après le jsonl).
- [B1] Terme `RiemannHypothesis` fermé ou mentionné dans un type : 0 (aucun théorème du lot ne mentionne RH ; aucun statut ÉQUIVALENTE À RH ou IMPLIQUE RH).
- [B1] docstring ≠ type : `expectedMinimumPrime_gapClass6_alternates` (Grammar/Mod6Rigidity l.120) — la docstring l'annonce comme application au pointeur `pmin` sur trois zéros consécutifs ; son type quantifie sur trois nombres premiers quelconques > 3 sans mentionner `expectedMinimumPrime` ni zéro (preuve = `primeGapClass6_alternates`, type identique).
- [B1] Nom/docstring qui promet plus que le type : `reaches_and_not_reaches_false` (Direct/Reached l.130), docstring « forme littérale de la fermeture » ; le type est la contradiction logique triviale `reaches → ¬reaches → False`, sans contenu arithmétique (hypothèses contradictoires).
- [B1] Divergence de nom sans effet sur le type : la docstring de `secondTower_entry_reaches_mirror_occurrence` écrit `p_min(z*) ≤ C⁻` pour l'entrée de la seconde Tour, dont le contact est le rayon du haut (`entryContact`, orientation inversée) ; le type ne porte que `occurrence ≤ entryContact`.
- [B1] Théorèmes citant « V » dans leur docstring (étiquette hors lecture compilée, cf. T20) : `pivotCell_mirror_reaches_expected`, `lock_imp_pivot_lt_expected`, `lock_imp_counted_lt_occurrence`, `not_reaches_of_lastRay_lt` ; les types ne portent que des inégalités ou `reaches`.
- [B1] Incident de méthode (hors théorèmes) : le scratchpad de session est partagé avec d'autres agents ; le fichier `dump.py` du scratchpad a été écrasé en concurrence ; les fichiers de travail de ce lot sont dans `scratchpad/b1/`. Aucun fichier du dépôt existant n'a été modifié.
- [B2] `sorryAx` : 0 théorème(s) ; axiome hors standard : 0 ; terme de type exactement `RiemannHypothesis` sans hypothèse (TERME RH FERMÉ) : 0.
- [B2] docstring ≠ type : `sameHeight_horizontal_dominates` (le docstring dit « à même hauteur », le type n'a aucune hypothèse de hauteur).
- [B2] Nom promet plus que le type : `amplitude_ratio_sameHeight` (aucune hypothèse de hauteur dans le type) ; `terminalCollision_conditional_on_reflectedObligation` (« collision » : le type n'énonce que la non-atteinte réfléchie, `¬ ∃ j, …`).
- [B2] Observation graphe/docstring : `mirror_translation_over_next_progression_lt` cite `phase_increment_eq_pi_span` dans son docstring, absent de `deps_project` (le type porte la portée `TowerPrimeGapSpan` directement).
- [B2] 18 théorèmes du lot mentionnent `RiemannHypothesis` dans leur type ; statuts : 15 `ÉQUIVALENTE À RH`, 3 `IMPLIQUE RH SOUS PRÉMISSE`, et 3 `CONFIRMÉE` où RH est l'antécédent (`passage_height_lt_of_riemannHypothesis`, `sourceIndex_eq_heightEventIndex_of_riemannHypothesis`, `localReading_of_riemannHypothesis`). Aucun ne prouve RH sans prémisse.
- [B2] Théorèmes dont la prémisse nommée est elle-même équivalente à RH par un autre théorème compilé (hors ou dans le lot) : `verticalDominates_of_verticalEnergyPush` (`verticalEnergyPush_iff_riemannHypothesis`, hors lot) ; `grammar_forces_displacement`, `grammar_forces_mode_A`, `grammar_determines_stop_ray` (`PGrammarByHeight`, `grammarByHeight_iff_riemannHypothesis`) ; `heightProgression_of_horizontalExclusion` (HME, `horizontalExclusion_iff_riemannHypothesis`). Statut retenu selon le correctif de contrôle n°1 : implication entre deux notions = CONFIRMÉE ; prémisse nommée servant de condition = CONFIRMÉE SOUS CONDITION.
- [B3] `sorryAx` : aucun (147 théorèmes, `uses_sorry` faux partout). Axiomes : `propext`, `Classical.choice`, `Quot.sound` uniquement, partout. Aucun axiome hors standard.
- [B3] Terme RH fermé (type exactement `RiemannHypothesis`, sans hypothèse) : aucun dans le lot.
- [B3] docstring ≠ type : `horizontal_energy_action` (docstring « pour deux zéros de même hauteur », le type quantifie sur deux zéros quelconques).
- [B3] Nom promettant plus que le type : `remaining_open_question_is_readout_only` (le type est l'équivalence de lecture ; « seule question ouverte » n'est pas un énoncé du type) ; `forcing_shared_expectedMinimum_is_collage` (le type est l'égalité d'index à p_min égal ; « collage » et E088 relèvent de la docstring) ; `riemannHypothesis_of_hReaches_is_vacuous` (le type est une implication sous prémisse ; « vide » repose sur un théorème hors lot) ; `control_two_onLine_towers_unique` (l'hypothèse β = 1/2 du type n'est pas utilisée par la preuve, d'après ses dépendances).
- [B3] `reflectedReading_iff_noLowerSide` : `mentions_RH` faux dans le type (côté droit `∀ z, ¬ β < 1/2`) ; classée ÉQUIVALENTE À RH par `riemannHypothesis_iff_noLowerSide`.
- [B3] Termes hors maître introduits : portée de Tour, capture de régime, `PLowestZeroOnLine`, progression, poussée verticale énergétique (CLAUDE.md, code).
- [B4] **sorryAx** : 0 sur les 134 théorèmes (`uses_sorry` faux partout).
- [B4] **Axiome hors standard** : aucun. Axiomes recensés : {propext, Classical.choice, Quot.sound} pour 133 théorèmes ; `forward_and_backward_false` a une liste d'axiomes vide (preuve sans axiome).
- [B4] **Terme RH fermé** (type exactement `RiemannHypothesis`) : aucun.
- [B4] **Docstring ≠ type** : aucune divergence relevée à la lecture des types (les docstrings de `explicitIndex_mirror_ne`, `mirror_sameHeightEvent`, etc. sont vides ou brèves : 24 théorèmes du lot n'ont aucun docstring).
- [B4] **Nom qui promet plus que le type** : `perronFamily_positivity_not_riemannHypothesis` (le nom évoque RH ; le type est « ∃ C, (termes de paire Perron positifs pour tout q > 0 sur C) ∧ ¬PWeilPairPositivity C » et ne contient pas RiemannHypothesis ; le docstring, lui, dit « n'implique pas RH » : ce passage est interprétatif, il n'est pas dans le type). `weilPairPositivity_not_from_config` : le nom dit « pas issue de la configuration », le type est la négation de « ∀ C, PWeilPairPositivity C » (correspond). `reflected_equivariance_false_onLine` : nom et type concordent (aucun côté bas n'est mentionné).
- [B4] **Docstring périmé** : le docstring de `RHV6Demonstration.lean` renvoie le raccord à RH vers `Terminal/PairContradiction.lean`, `Terminal/Universalization.lean` et `RHV6Closure.lean` ; `PairContradiction.lean` et `RHV6Closure.lean` n'existent plus (retirés le 2026-09-26). `Universalization.lean` existe. Le corps de la bibliothèque (11 théorèmes) n'est pas affecté.
- [B4] **Aucune dépendance active sur une piste parquée, sauf une** : `mirror_sameHeightIndex` → `mirror_heightEventIndex_eq` (MirrorFrequency, module actif). À signaler à l'auteur car CLAUDE.md dit des six pistes qu'aucune « n'est sur la voie active » ; le fait établi ici est plus étroit : une dépendance de preuve existe pour un théorème.
- [B4] **Audit.lean** : 0 théorème, 158 `#print axioms`, dont 23 sur des théorèmes parqués ; le manifeste liste les onze théorèmes de RHV6Demonstration dans sa prose seulement.

## 8. Ajout : pistes parquées

Ce paragraphe est en fin de corps, hors voie active. Cadre (CLAUDE.md §4, purge du 2026-09-27) : six pistes retirées du fichier CLAUDE.md mais toujours compilées dans le code et importées par `RHV6Fresh.lean`. Les théorèmes de ces pistes sont audités à l'annexe A (lot B4, partie B). Chaque piste ci-dessous est PARQUÉE.

Cadre (CLAUDE.md §4, bullet « Purge des pistes parquées », auteur, 2026-09-27) : six pistes — collision d'événements (`Terminal/MirrorEventCollision.lean`), équivariance orientée (`Terminal/ReflectedTransition.lean`), réorientation/caractérisation de criticité (`Terminal/CriticalityCharacterization.lean`), parité de ξ et lieu fixe (`Terminal/FixedLocusParity.lean`), critères de stabilité globale (`Terminal/StabilityCriteria.lean`), fonctionnel positif côté premier (`Terminal/PrimePositivity.lean`) — « sont retirées de ce fichier. Elles restent dans le code (aucun fichier supprimé, aucune régression de build) et dans `git log`, qui en tient lieu d'historique (§2) ; aucune d'elles n'a produit de contradiction, aucune n'est sur la voie active actuelle (chaîne arithmétique / C_lecture / injectivité et progression de `pmin`) ». Motif donné par CLAUDE.md : « Les conserver ici entretenait la confusion entre « exploré et parqué sans résultat » et « actif » ». Ce motif porte sur le fichier CLAUDE.md ; le code Lean des six modules reste compilé et est importé par `RHV6Fresh.lean` (lignes 46–51).

**Dépendance des théorèmes actifs envers les pistes parquées (graphe `deps_project` sur les 742 théorèmes)** : `mirror_sameHeightIndex` est utilisé par `mirror_heightEventIndex_eq` (RHV6Fresh.Terminal.MirrorFrequency). Il s'agit du seul lien de ce type. `mirror_heightEventIndex_eq` a lui-même pour dépendants transitifs : off_consecutive_translation_signature, off_mirror_same_frequency, off_mirror_same_frequency_of_consecutive, onLine_mirror_trivial. Au niveau des fichiers : `Terminal/MirrorFrequency.lean` importe `Terminal/MirrorEventCollision.lean` (ligne 4) ; `Terminal/TranslationVsProgression.lean` importe `MirrorFrequency` ; `RHV6Fresh.lean` importe les six modules et `Audit.lean` en importe quatre. Recherche textuelle des 123 noms de théorèmes des six modules dans tous les `.lean` de `RHV6Fresh/` (hors leur module propre) : seuls `Audit.lean` (23 `#print axioms`), `MirrorFrequency.lean` (`mirror_sameHeightIndex`) et les autres pistes parquées les nomment ; aucun autre fichier actif.

### PARQUÉE — Piste 1 : collision d'événements (`Terminal/MirrorEventCollision.lean`)

Comptes calculés sur l'annexe A : 14 théorèmes ; CONFIRMÉE : 5 ; CONFIRMÉE SOUS CONDITION : 4 ; ÉQUIVALENTE À RH : 2 ; RÉFUTATION COMPILÉE : 3.

**Ce que la piste établit, dans les mots du maître (docstring du module, auteur 2026-09-25)** : la contradiction candidate est « la réflexion ne crée pas un nouvel événement » contre « l'ordre des membres fait avancer l'événement », avec z = (β, T), z* = (1 − β, T), β < 1/2, aucune hypothèse nouvelle. Verdict du compilateur : Cible A (progression stricte des membres) = théorème ; Cible B (le miroir ne consomme aucun événement de hauteur mais consomme un index de membre) = théorèmes, deux grammaires distinctes ; Cible C (`Occ(z*) = Occ(z)`) réfutée par théorème pour tout z de côté bas, l'exiger de tout zéro de côté bas est RH ; le transport « occurrence par hauteur → occurrence par membre » au miroir est réfuté hors ligne ; le maître dit : « Aucun terme `RiemannHypothesis` ne sort de cette route ».

**Statut** : 14 théorèmes ; CONFIRMÉE SOUS CONDITION : 4, CONFIRMÉE : 5, RÉFUTATION COMPILÉE : 3, ÉQUIVALENTE À RH : 2. Aucune contradiction ; deux équivalences à RH sur des prémisses exigées de tout zéro de côté bas (Cible C, transport au miroir) et trois réfutations compilées (Cible C, transport aux deux membres, transport au miroir). Le maître (V131) reprend, hors de ce module, l'énoncé « la grammaire par hauteurs tolère un zéro hors ligne (même premier au membre et à son miroir) », établi ici par `mirror_sameHeightPrime`.

**Pourquoi parquée (CLAUDE.md §4)** : Le module figure dans la liste des six pistes purgées. Ce que CLAUDE.md dit de la route : elle est parquée « sans résultat » (aucune contradiction) ; `mirror_sameHeightIndex` a pourtant un usage actif ci-dessous.

**Un théorème actif en dépend-il ?** Oui, un seul lien : `mirror_sameHeightIndex` est utilisé par `mirror_heightEventIndex_eq` du module actif `Terminal/MirrorFrequency.lean` (importé par `RHV6Fresh.lean` et par `TranslationVsProgression.lean`), dont la preuve l'appelle (`MirrorFrequency.lean` l. 108, `mirror_sameHeightIndex z`). Aucun autre théorème du module n'est utilisé hors du module (dans `deps_project`).

**Théorèmes hors lot sur lesquels la piste s'appuie le plus** : sourceIndex_lt_mirror (3), mirrorMember_ordinate (3), riemannHypothesis_of_noLowerSide (2), occurrence_eq_canonicalAnchor (1), occurrence_eq_primeAtRank (1), heightEventIndex_le_sourceIndex (1).

### PARQUÉE — Piste 2 : équivariance orientée (`Terminal/ReflectedTransition.lean`)

Comptes calculés sur l'annexe A : 23 théorèmes ; CONFIRMÉE : 15 ; CONFIRMÉE SOUS CONDITION : 1 ; ÉQUIVALENTE À RH : 1 ; RÉFUTATION COMPILÉE : 6.

**Ce que la piste établit, dans les mots du maître (docstring du module, auteur 2026-09-25)** : partir du quartet zeta23 (ρ ↦ 1 − ρ̄ puis 1 − ρ̄ ↦ 1 − ρ), utiliser `trajet(1 − ρ) = reverse(trajet(1 − ρ̄))`, projeter l'événement sur la grammaire première ; si l'événement droit donne (p_n, p_{n+1}), sa réflexion pure donne (p_{n+1}, p_n), or M^Z = M dit que les transitions sont toujours orientées p_k → p_{k+1}, d'où p_n < p_{n+1} < p_n. Compilé : la réflexion ne crée aucun événement premier ; quartet et renversement ; la transition d'un membre est canonique ; l'orientation droite présente la transition dans l'ordre, la réflexion à rebours ; l'arithmétique refuse le retour. Le `False` sort de la prémisse « la transition présentée par la réflexion est une transition de la grammaire », réfutée pour tout membre, sur la droite comme hors ligne ; l'exiger de tout zéro de côté bas est RH, de tout zéro est « il n'existe aucun zéro supérieur ». Raison compilée : le zéro réfléchi a une hauteur strictement négative, aucune grammaire de la base n'est définie sur lui. Le maître du module : « Aucun terme `RiemannHypothesis` ne sort de cette route ».

**Statut** : 23 théorèmes ; CONFIRMÉE : 15, RÉFUTATION COMPILÉE : 6, ÉQUIVALENTE À RH : 1, CONFIRMÉE SOUS CONDITION : 1. Aucune contradiction inconditionnelle : le `False` ne distingue pas β < 1/2 de β = 1/2 (`reflected_equivariance_false_onLine`) ; une équivalence à RH (`reflectedEquivariance_iff_riemannHypothesis`). Les théorèmes géométriques du module (`quartet_chain`, `trajectory_reversal`, `reflection_creates_no_prime_event`, `reflection_reverses_existing_ring`, `reflectedZero_not_member`, `upright_presents_forward`, `reflected_presents_reversed`, `reflected_presents_via_functional_reflect`) rejoignent des vérités du maître (V63, V72/V96, V80, V88, V135).

**Pourquoi parquée (CLAUDE.md §4)** : Module de la liste des six pistes purgées ; le maître (V72, V96) cite comme « compilé » le mouvement réfléchi sans événement d'arrêt, avec le fichier `Terminal/ReflectedObligation.lean` (non parqué) et non ce module. CLAUDE.md ajoute, dans le bullet « Mise en garde de l'auteur » (2026-09-26), que la seconde Tour n'est pas obtenue en suivant le mouvement réfléchi depuis son origine (deux objets distincts) ; les théorèmes de ce module manipulent les deux (`reflection_creates_no_prime_event` : mouvement depuis l'origine ; `reflected_presents_reversed`, `reflected_presents_via_functional_reflect` : `secondTowerOf`).

**Un théorème actif en dépend-il ?** Non : aucun des 23 théorèmes du module n'est utilisé par un théorème hors du module (`deps_project`). Le module dépend, lui, de théorèmes actifs (`secondTower_*`, `reflectedIncidence_eq`, `reflected_reads_no_prime`, `occurrence_lt_expectedMinimumPrime`, etc.), voir la liste ci-dessus.

**Théorèmes hors lot sur lesquels la piste s'appuie le plus** : reflectedZero_support (2), occurrence_eq_primeAtRank (1), riemannHypothesis_of_noLowerSide (1), reflectedZero_im (1), secondTower_entry_reaches_mirror_occurrence (1), secondTower_entry_reaches_own_expected (1), secondTower_cell_contains_own_expected (1), secondTower_lastRay_eq_reflected (1), secondTower_entry_eq_reflected (1), reflected_reads_no_prime (1).

### PARQUÉE — Piste 3 : réorientation, criticité comme caractéristique (`Terminal/CriticalityCharacterization.lean`)

Comptes calculés sur l'annexe A : 17 théorèmes ; CONFIRMÉE : 7 ; CONFIRMÉE SOUS CONDITION : 8 ; ÉQUIVALENTE À RH : 2.

**Ce que la piste établit, dans les mots du maître (docstring du module, auteur 2026-09-25)** : « Toutes les routes « OFF ⟹ False » ont fini sur une prémisse réfutée hors ligne ou équivalente à RH. La cible change de forme : … quelle caractéristique compilée distingue la droite critique ». (1) La formule explicite compilée compte les membres, non les événements : un index par point, une paire hors ligne est deux index à même fréquence, même événement de hauteur, deux amplitudes x^β et x^(1−β) ; sur la droite un seul index. (2) `n(z) = h(z)` si et seulement si tout membre qui précède z est sur la droite : caractéristique globale, position radiale de z sans effet ; z de côté bas au passé sur la droite a n = h et son miroir h < n ; un seul membre hors ligne dans le passé la détruit ; exigée de tout membre, elle est RH. (3) La chaîne « progression ⟹ un événement par étape ⟹ z* = z ⟹ β = 1/2 » a pour maillon central « un membre par hauteur », c'est-à-dire n = h partout, c'est-à-dire RH ; ce qui reste est d'isoler le terme de la paire hors ligne dans la somme (absent de la base et de Mathlib). Le module : « Aucun terme `RiemannHypothesis` ne sort de ce module ».

**Statut** : 17 théorèmes ; CONFIRMÉE : 7, CONFIRMÉE SOUS CONDITION : 8, ÉQUIVALENTE À RH : 2. Aucune contradiction ; une équivalence à RH (`pastOnLine_all_iff_riemannHypothesis`, et son pendant `grammarsAgree_all_iff_pastOnLine_all`). Ce module porte les énoncés que le maître cite comme « Compilé » aux lignes 131 (V127, V128, V129) ; c'est la tension T15 de `VERITES_MAITRE.md` (fichier parqué par CLAUDE.md mais cité comme compilé par le maître) — signalée, non résolue ici.

**Pourquoi parquée (CLAUDE.md §4)** : Module de la liste des six pistes purgées de CLAUDE.md ; mais le maître sémantique (l. 131) cite ses résultats. Le code compilé prime (CLAUDE.md §2) : les théorèmes sont vrais, le rangement « parqué » ne concerne que le statut de piste dans CLAUDE.md.

**Un théorème actif en dépend-il ?** Non : aucun théorème hors du module n'utilise l'un des 17 (`deps_project`). Le module dépend de `mirror_sameHeightEvent` et `mirror_amplitude_exponent_dominates`, `mirror_sameHeightIndex` (MirrorEventCollision), de `grammarsAgree_iff_riemannHypothesis` et d'autres théorèmes actifs.

**Théorèmes hors lot sur lesquels la piste s'appuie le plus** : mirrorMember_ordinate (3), heightEventIndex_le_sourceIndex (2), mirror_amplitude_exponent_dominates (1), mirrorMember_eq_self_of_onLine (1), mirrorMember_radial (1), sourceIndex_lt_mirror (1), grammarsAgree_iff_riemannHypothesis (1).

### PARQUÉE — Piste 4 : parité de ξ et lieu fixe (`Terminal/FixedLocusParity.lean`)

Comptes calculés sur l'annexe A : 44 théorèmes ; CONFIRMÉE : 40 ; CONFIRMÉE SOUS CONDITION : 3 ; ÉQUIVALENTE À RH : 1.

**Ce que la piste établit, dans les mots du maître (docstring du module, auteur 2026-09-25)** : la droite critique est le lieu fixe x = 0 de l'involution x ↦ −x (x = β − 1/2) ; la fonction complétée est réelle sur ce lieu ; sur la droite un zéro est UNE équation réelle (A(0, t) = 0), hors ligne DEUX (A = 0 et G = 0) ; le « théorème candidat » est A = 0 ⟹ G ≠ 0 pour 0 < |x| < 1/2, t > 0. Compilé sur la fonction complétée de Mathlib sans hypothèse : lieu fixe (trois descriptions), parité (A paire, B impaire, Λ(reflect s) = conj Λ(s)), le théorème candidat est RH mot pour mot, G(0, t) est la dérivée (G(0, γ) ≠ 0 est « le zéro est simple ») et la « transversalité radiale » n'est pas distincte de la simplicité, l'alternance + − + − est automatique (analyse réelle élémentaire), le scan ne contraint que l'évitement des hauteurs, les zéros triviaux ne sont pas des zéros de Λ. Le module : « Aucun terme `RiemannHypothesis` ne sort de cette route : le théorème candidat en est la reformulation exacte ».

**Statut** : 44 théorèmes ; CONFIRMÉE : 40, CONFIRMÉE SOUS CONDITION : 3, ÉQUIVALENTE À RH : 1. Aucune contradiction ; une équivalence à RH (`fixedLocusSelection_iff_riemannHypothesis`) ; le reste sont des faits de parité et de dérivation sur Λ, dont la plupart n'ont pas de phrase correspondante dans le maître (AJOUT), sauf le lieu fixe (V77, V161, V62).

**Pourquoi parquée (CLAUDE.md §4)** : Module de la liste des six pistes purgées, « aucune contradiction, aucune sur la voie active ». Le maître ne cite pas ce module.

**Un théorème actif en dépend-il ?** Non : aucun théorème actif n'utilise l'un des 44 théorèmes ; StabilityCriteria en utilise plusieurs (`centeredPoint_nontrivialZero_iff`, `off_member_two_equations`, etc. : voir le tableau des dépendances croisées ci-dessous, calculé).

**Théorèmes hors lot sur lesquels la piste s'appuie le plus** : mirrorMember_radial (2), zetaReflect_re (2), zetaReflect_im (2), riemannHypothesis_of_noOff (1), mirrorMember_eq_self_of_onLine (1).

### PARQUÉE — Piste 5 : critères de stabilité globale (Weil, Laguerre–Pólya, de Branges) (`Terminal/StabilityCriteria.lean`)

Comptes calculés sur l'annexe A : 14 théorèmes ; CONFIRMÉE : 3 ; CONFIRMÉE SOUS CONDITION : 6 ; ÉQUIVALENTE À RH : 3 ; RÉFUTATION COMPILÉE : 2.

**Ce que la piste établit, dans les mots du maître (docstring du module, auteur 2026-09-25)** : trois pistes soumises (positivité de Weil, de Branges / Hermite–Biehler, Laguerre–Pólya) ; verdict remis avant le module : trois équivalents exacts de RH, la flèche « premiers ⟹ positivité » étant l'inconnue. Compilé : Laguerre–Pólya pour Ξ est RH mot pour mot ; le terme de paire de Weil vaut ‖φ(ρ)‖² sur la droite, et hors ligne un test rend négatifs les deux termes de la paire ; la positivité de paire d'une configuration est exactement « tous ses points sont sur la droite », donc RH pour `zetaZeroConfig` (sens facile de Weil) ; une configuration hors ligne satisfait tous les axiomes de `ZeroConfig` et viole la positivité, donc aucune positivité n'est un théorème des axiomes de `ZeroConfig` ; la forme côté zéros d'une configuration sur la droite est positive sur toute fenêtre finie. Le module : « Aucun sorry, aucun admit, aucun axiome nouveau, aucune hypothèse ».

**Statut** : 14 théorèmes ; CONFIRMÉE : 3, ÉQUIVALENTE À RH : 3, CONFIRMÉE SOUS CONDITION : 6, RÉFUTATION COMPILÉE : 2. Aucune contradiction ; trois équivalences à RH (`xiRealZeros_iff_riemannHypothesis`, `allNontrivial_onLine_iff_riemannHypothesis`, `weilPairPositivity_zeta_iff_riemannHypothesis`) ; deux réfutations compilées (`offPairConfig_not_weilPositive`, `weilPairPositivity_not_from_config`) ; deux théorèmes sous prémisse RiemannHypothesis (`zeroSideWindow_zeta_nonneg_of_riemannHypothesis`, et `scanConstraint_of_riemannHypothesis` dans FixedLocusParity).

**Pourquoi parquée (CLAUDE.md §4)** : Module de la liste des six pistes purgées. Le maître ne le cite pas.

**Un théorème actif en dépend-il ?** Non : aucun théorème actif n'utilise l'un des 14 ; `offPairConfig_not_weilPositive` est utilisé par `perronFamily_positivity_not_riemannHypothesis` de PrimePositivity (dépendance entre pistes parquées, voir tableau croisé).

**Théorèmes hors lot sur lesquels la piste s'appuie le plus** : zetaReflect_re (3), zetaReflect_im (3), riemannHypothesis_of_noOff (2), zetaZeroConfig_carrier (1), ZeroConfig.finite_window (1).

### PARQUÉE — Piste 6 : fonctionnel positif côté premier (`Terminal/PrimePositivity.lean`)

Comptes calculés sur l'annexe A : 11 théorèmes ; CONFIRMÉE : 11.

**Ce que la piste établit, dans les mots du maître (docstring du module, auteur 2026-09-25)** : les découvertes du projet ne servent plus à transporter un zéro vers un premier mais à fabriquer une positivité ou une stabilité globale ; première étape obligée : quelle positivité la formule explicite compilée rend-elle visible, et voit-elle β ? Compilé : le mécanisme `x^ρ · conj(x^{1 − ρ̄}) = x` pour tout ρ (le produit des amplitudes d'une paire est toujours x) ; le terme de paire de la famille compilée (`Perron.f x`) est positif pour tout point de la bande, donc sur la configuration de ζ sans RH ET sur la paire hors ligne. Verdict du module : la positivité que la formule explicite compilée rend visible terme par terme est un théorème et elle est aveugle à β ; un fonctionnel qui voit β exige la formule explicite du noyau convolé `f ∗ f̃`, « ni dans la base ni dans Mathlib ». Le module : « Aucun sorry, aucun admit, aucun axiome nouveau, aucune hypothèse ».

**Statut** : 11 théorèmes ; CONFIRMÉE : 11. Aucune contradiction ; aucune équivalence à RH ; un contre-modèle (`perronFamily_positivity_not_riemannHypothesis`) : le nom promet une relation avec RiemannHypothesis alors que le type ne mentionne pas RiemannHypothesis (voir Incidents).

**Pourquoi parquée (CLAUDE.md §4)** : Module de la liste des six pistes purgées. Le maître ne le cite pas ; sa conclusion (aveuglement à β de la positivité visible terme par terme) rejoint V160 et V167 par le résultat, sans théorème commun.

**Un théorème actif en dépend-il ?** Non : aucun théorème hors du module n'utilise l'un des 11.

**Théorèmes hors lot sur lesquels la piste s'appuie le plus** : .

Dépendance active unique : `mirror_sameHeightIndex` → `mirror_heightEventIndex_eq` (voir section 7).

## Annexe A — entrées complètes

Une entrée par théorème, verbatim des fragments validés B1–B4 (les titres de sous-sections sont abaissés d'un niveau pour tenir dans l'annexe).

### Lot B1 — B1 (Foundation/Tower/Voyage/Direct/Grammar/CleanTerminal)

##### Module `RHV6Fresh.CleanTerminal` (3 théorèmes)

#### `occurrence_eq_canonicalAnchor` — `CleanTerminal` l.21 — CONFIRMÉE
- **Énoncé** : L'occurrence d'un zéro est son ancre canonique de la base.
- **Vérités** : V27, V79
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `occurrence`. Base rhv3 : `RHV3Lean.nMemberCanonicalAnchor`, `RHV3Lean.thm_memberMZOccurrence_eq_canonicalAnchor_unconditional`.
- **Entraîne** (9) : `clock_pn_eq`, `memberHeightTransport_iff_index`, `occurrence_eq_primeAtRank`, `occurrence_lt_expectedMinimumPrime`, `occurrence_strict_of_passage`, `occurrence_successor_of_passage`, `occurrences_agree_iff_riemannHypothesis`, `off_mirror_two_grammars`, `passage_span_eq_log_occurrences`.

#### `occurrence_strict_of_passage` — `CleanTerminal` l.25 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : hauteurs des deux membres > 0)
- **Énoncé** : Sur tout passage (membres supérieurs), l'occurrence du membre antérieur est strictement inférieure à celle du postérieur.
- **Vérités** : V56, V150
- **Repose sur** : théorèmes : `occurrence_eq_canonicalAnchor`; définitions/structures : `occurrence`. Base rhv3 : `RHV3Lean.TZeroPassage`, `RHV3Lean.rZeroHeight`, `RHV3Lean.TZeroPassage.zEarlierMember`, `RHV3Lean.TZeroPassage.zLaterMember`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.nMemberCanonicalAnchor`, `RHV3Lean.thm_memberCanonicalAnchors_strict_of_passage`.
- **Entraîne** (2) : `passage_event_increment`, `progression_strict`.

#### `occurrence_successor_of_passage` — `CleanTerminal` l.41 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : hauteurs des deux membres > 0)
- **Énoncé** : Sur tout passage, l'occurrence du membre postérieur est le premier successeur de l'index zéro-source du membre antérieur.
- **Vérités** : V56, V54, V150
- **Repose sur** : théorèmes : `occurrence_eq_canonicalAnchor`; définitions/structures : `occurrence`. Base rhv3 : `RHV3Lean.TZeroPassage`, `RHV3Lean.rZeroHeight`, `RHV3Lean.TZeroPassage.zEarlierMember`, `RHV3Lean.TZeroPassage.zLaterMember`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.fnPrimeSuccessor`, `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.nMemberCanonicalAnchor`, `RHV3Lean.thm_memberCanonicalAnchor_succ_of_passage`.
- **Entraîne** (2) : `expectedMinimumPrime_eq_laterOccurrence`, `passage_span_eq_log_occurrences`.


##### Module `RHV6Fresh.Direct.InvertedCount` (19 théorèmes)

#### `InvertedContactPair.not_reaches_iff` — `Direct.InvertedCount` l.35 — CONFIRMÉE
- **Énoncé** : Sur une paire inversée, un premier p n'est pas atteint ssi le dernier rayon est strictement sous p.
- **Vérités** : V52, V84
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.reaches`, `InvertedContactPair.lastRayContact`. Base rhv3 : aucun.
- **Entraîne** (2) : `InvertedContactPair.not_reaches_of_lastRay_lt`, `secondTower_verification_iff_not_reads_of_consecutive`.

#### `InvertedContactPair.reaches_of_le` — `Direct.InvertedCount` l.39 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : p ≤ q ; q atteint)
- **Énoncé** : Si q est atteint sur une paire inversée, tout p ≤ q l'est aussi.
- **Vérités** : V52
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.reaches`, `InvertedContactPair.lastRayContact`. Base rhv3 : aucun.
- **Entraîne** (1) : `invertedPivotPair_not_reaches_of_le`.

#### `InvertedContactPair.not_reaches_of_lastRay_lt` — `Direct.InvertedCount` l.42 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : dernier rayon < p)
- **Énoncé** : Si le dernier rayon inversé est sous p, p n'est pas atteint.
- **Vérités** : V52, V84
- **Repose sur** : théorèmes : `InvertedContactPair.not_reaches_iff`; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.lastRayContact`, `InvertedContactPair.reaches`. Base rhv3 : aucun.
- **Entraîne** (1) : `invertedPivotPair_not_reaches`.

#### `InvertedContactPair.countedPrime_prime` — `Direct.InvertedCount` l.51 — CONFIRMÉE
- **Énoncé** : Le premier compté sur une paire inversée est un nombre premier.
- **Vérités** : V52
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.countedPrime`, `InvertedContactPair.countedRank`. Base rhv3 : `RHV3Lean.thm_primeAtRank_isPrime`.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedContactPair.countedRank_eq_vonMangoldt` — `Direct.InvertedCount` l.53 — CONFIRMÉE
- **Énoncé** : Le rang compté au dernier rayon d'une paire inversée est le comptage Chebyshev/Von Mangoldt évalué à ce dernier rayon.
- **Vérités** : V145, V52
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.countedRank`, `InvertedContactPair.lastRayContact`. Base rhv3 : `RHV3Lean.nPrimeCountingFromJ`, `RHV3Lean.rChebyshevJNat`, `RHV3Lean.nEdgePrimeRank`, `RHV3Lean.thm_edgePrimeRank_eq_primeCountingFromJ`.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedContactPair.reaches_primeAtRank_iff` — `Direct.InvertedCount` l.58 — CONFIRMÉE
- **Énoncé** : Dualité rang/contact au dernier rayon inversé : le premier de rang r est atteint ssi r < rang compté.
- **Vérités** : V145, V52
- **Repose sur** : théorèmes : `InvertedContactPair.lastRayContact_pos`; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.reaches`, `InvertedContactPair.countedRank`, `InvertedContactPair.lastRayContact`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.nEdgePrimeRank`, `RHV3Lean.thm_edgeRank_le_iff_lt_primeAtRank`.
- **Entraîne** (3) : `InvertedContactPair.countedPrime_lt_of_not_reaches_succ`, `InvertedContactPair.reaches_iff_le_countedPrime`, `InvertedContactPair.reaches_occurrence_iff`.

#### `InvertedContactPair.reaches_iff_le_countedPrime` — `Direct.InvertedCount` l.70 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : p premier ; rang compté > 0)
- **Énoncé** : Sur une paire inversée à compte positif, un premier p est atteint ssi p ≤ premier constaté.
- **Vérités** : V52, V38
- **Repose sur** : théorèmes : `InvertedContactPair.reaches_primeAtRank_iff`; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.countedRank`, `InvertedContactPair.reaches`, `InvertedContactPair.countedPrime`, `InvertedContactPair.reaches_iff_le_countedPrime._proof_1_1`, `InvertedContactPair.reaches_iff_le_countedPrime._proof_1_2`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.thm_primeAtRank_surjective_onPrimes`, `RHV3Lean.thm_primeAtRank_strictMono`.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedContactPair.countedPrime_lt_of_not_reaches_succ` — `Direct.InvertedCount` l.89 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : premier de rang n+1 non atteint)
- **Énoncé** : Si le premier de rang n+1 n'est pas atteint, le premier constaté lui est strictement inférieur.
- **Vérités** : V52
- **Repose sur** : théorèmes : `InvertedContactPair.reaches_primeAtRank_iff`; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.reaches`, `InvertedContactPair.countedPrime`, `InvertedContactPair.countedRank`, `InvertedContactPair.countedPrime_lt_of_not_reaches_succ._proof_1_1`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.thm_primeAtRank_strictMono`.
- **Entraîne** (1) : `secondTower_counted_lt_own_expected`.

#### `InvertedContactPair.reaches_occurrence_iff` — `Direct.InvertedCount` l.97 — CONFIRMÉE
- **Énoncé** : L'occurrence du zéro est atteinte sur une paire inversée exactement quand le rang compté dépasse l'index zéro-source.
- **Vérités** : V145, V49, V27
- **Repose sur** : théorèmes : `occurrence_eq_primeAtRank`, `InvertedContactPair.reaches_primeAtRank_iff`; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.reaches`, `occurrence`, `InvertedContactPair.countedRank`. Base rhv3 : `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.fnPrimeAtRank`.
- **Entraîne** (1) : `InvertedContactPair.countedRank_pos_of_reaches_occurrence`.

#### `InvertedContactPair.countedRank_pos_of_reaches_occurrence` — `Direct.InvertedCount` l.103 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : occurrence atteinte)
- **Énoncé** : Le rang compté est positif dès que l'occurrence est atteinte.
- **Vérités** : V52
- **Repose sur** : théorèmes : `InvertedContactPair.reaches_occurrence_iff`; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.reaches`, `occurrence`, `InvertedContactPair.countedRank`, `InvertedContactPair.countedRank_pos_of_reaches_occurrence._proof_1_1`. Base rhv3 : `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `invertedPivotPair_entryContact` — `Direct.InvertedCount` l.118 — CONFIRMÉE
- **Énoncé** : L'entrée de la paire inversée du pivot est le dernier rayon de la paire du pivot (rôles échangés).
- **Vérités** : V34, V29
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair.entryContact`, `invertedPivotPair`, `AnalyticContactPair.lastRayContact`, `pivotPair`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `invertedPivotPair_lastRayContact` — `Direct.InvertedCount` l.121 — CONFIRMÉE
- **Énoncé** : Le dernier rayon de la paire inversée du pivot est l'entrée de la paire du pivot.
- **Vérités** : V34, V29
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair.lastRayContact`, `invertedPivotPair`, `AnalyticContactPair.entryContact`, `pivotPair`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `invertedPivotPair_upright` — `Direct.InvertedCount` l.124 — CONFIRMÉE
- **Énoncé** : Redressée, la paire inversée du pivot est la paire du pivot.
- **Vérités** : V34, V71
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `InvertedContactPair.upright`, `invertedPivotPair`, `pivotPair`. Base rhv3 : aucun.
- **Entraîne** (2) : `invertedPivotPair_entryCoordinate`, `invertedPivotPair_stageCount`.

#### `invertedPivotPair_cell_contains` — `Direct.InvertedCount` l.127 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : q>0)
- **Énoncé** : Le pivot est dans la cellule inversée : dernier rayon (bas) strictement sous lui, entrée (haut) au moins lui.
- **Vérités** : V82, V34
- **Repose sur** : théorèmes : `entry_lt_pivot`, `pivot_le_lastRay`; définitions/structures : `TrueZero`, `InvertedContactPair.lastRayContact`, `invertedPivotPair`, `InvertedContactPair.entryContact`. Base rhv3 : aucun.
- **Entraîne** (1) : `secondTower_cell_contains_own_expected`.

#### `invertedPivotPair_lastRay_lt_pivot` — `Direct.InvertedCount` l.133 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : q>0)
- **Énoncé** : Le dernier rayon inversé est strictement sous le pivot.
- **Vérités** : V82, V135
- **Repose sur** : théorèmes : `entry_lt_pivot`; définitions/structures : `TrueZero`, `InvertedContactPair.lastRayContact`, `invertedPivotPair`. Base rhv3 : aucun.
- **Entraîne** (1) : `invertedPivotPair_not_reaches`.

#### `invertedPivotPair_not_reaches` — `Direct.InvertedCount` l.137 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : p>0)
- **Énoncé** : Dans la seconde orientation, le pivot n'est jamais compté au dernier rayon (rayon du bas de son anneau).
- **Vérités** : V82, V135, V153
- **Repose sur** : théorèmes : `InvertedContactPair.not_reaches_of_lastRay_lt`, `invertedPivotPair_lastRay_lt_pivot`; définitions/structures : `TrueZero`, `InvertedContactPair.reaches`, `invertedPivotPair`. Base rhv3 : aucun.
- **Entraîne** (2) : `invertedPivotPair_not_reaches_of_le`, `secondTower_not_reaches_own_expected`.

#### `invertedPivotPair_not_reaches_of_le` — `Direct.InvertedCount` l.144 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : q>0 ; q ≤ p)
- **Énoncé** : Aucun premier au moins égal au pivot n'est atteint au dernier rayon inversé.
- **Vérités** : V82, V135
- **Repose sur** : théorèmes : `invertedPivotPair_not_reaches`, `InvertedContactPair.reaches_of_le`; définitions/structures : `TrueZero`, `InvertedContactPair.reaches`, `invertedPivotPair`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `invertedPivotPair_entryCoordinate` — `Direct.InvertedCount` l.149 — CONFIRMÉE
- **Énoncé** : La coordonnée d'entrée de la paire inversée du pivot est celle du rayon du haut, k+1.
- **Vérités** : V80, V43
- **Repose sur** : théorèmes : `invertedPivotPair_upright`, `pivotPair_entryCoordinate`, `pivotPair_stageCount`; définitions/structures : `TrueZero`, `InvertedContactPair.entryCoordinate`, `invertedPivotPair`, `pivotCoordinate`, `AnalyticContactPair.entryCoordinate`, `InvertedContactPair.upright`, `AnalyticContactPair.stageCount`, `pivotPair`, `AnalyticContactPair`. Base rhv3 : aucun.
- **Entraîne** (1) : `secondTower_readings`.

#### `invertedPivotPair_stageCount` — `Direct.InvertedCount` l.156 — CONFIRMÉE
- **Énoncé** : Le nombre d'étages de la paire inversée du pivot vaut un.
- **Vérités** : V43, V32
- **Repose sur** : théorèmes : `invertedPivotPair_upright`, `pivotPair_stageCount`; définitions/structures : `TrueZero`, `InvertedContactPair.stageCount`, `invertedPivotPair`, `AnalyticContactPair.stageCount`, `InvertedContactPair.upright`, `pivotPair`, `AnalyticContactPair`. Base rhv3 : aucun.
- **Entraîne** (1) : `secondTower_readings`.


##### Module `RHV6Fresh.Direct.MirrorCount` (21 théorèmes)

#### `mirrorMember_ordinate` — `Direct.MirrorCount` l.50 — CONFIRMÉE
- **Énoncé** : Le membre miroir a la même hauteur T que le zéro.
- **Vérités** : V65
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `mirrorMember`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.thm_mirror_sameHeight`.
- **Entraîne** (32) : `consecutive_continuous_signature`, `exists_fiberSuccessor`, `explicitIndex_mirror_im`, `fiberSuccessor_ordinate_eq`, `fiberSuccessor_radial_le_mirror`, `grammarsAgree_at_iff_onLine_below`, `mirrorMember_contactMinusAt`, `mirrorMember_contactPlusAt`, `mirrorMember_eq_self_of_onLine`, `mirrorMember_phase`, `mirror_contact_eq_iff_onLine`, `mirror_contact_ratio_const` et 20 autres.

#### `mirrorMember_radial` — `Direct.MirrorCount` l.54 — CONFIRMÉE
- **Énoncé** : Le membre miroir a pour position radiale 1−β.
- **Vérités** : V65
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `mirrorMember`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.thm_mirror_radialPosition`.
- **Entraîne** (23) : `fiberSuccessor_radial_le_mirror`, `grammarsAgree_at_iff_onLine_below`, `mirrorMember_eq_self_of_onLine`, `mirrorMember_mirrorMember_radial`, `mirrorMember_ne`, `mirrorMember_phase`, `mirror_contact_eq_iff_onLine`, `mirror_grid_never_coincides`, `mirror_horizontal_tension_eq_zero_iff`, `mirror_net_horizontal_force_zero`, `mirror_phase_gap_eq_arctan`, `mirror_phase_lt` et 11 autres.

#### `mirrorMember_eq_self_of_onLine` — `Direct.MirrorCount` l.58 — CONFIRMÉE SOUS CONDITION (zéro sur la droite critique (β=1/2))
- **Énoncé** : Sur la droite critique, le membre miroir est le zéro lui-même.
- **Vérités** : V77, V161
- **Repose sur** : théorèmes : `mirrorMember_radial`, `mirrorMember_ordinate`; définitions/structures : `TrueZero`, `mirrorMember`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroHeight`.
- **Entraîne** (7) : `explicitIndex_mirror_eq_of_onLine`, `insertionDepth_eq_zero_iff`, `mirror_contacts_eq_of_onLine`, `mirror_phase_shift_eq_zero_of_onLine`, `mirror_zeroTerm_eq_of_onLine`, `onLine_mirror_trivial`, `radialOffset_eq_zero_iff_fixed`.

#### `mirrorMember_phase` — `Direct.MirrorCount` l.72 — CONFIRMÉE
- **Énoncé** : La phase de la Tour propre du membre miroir est φ* = arctan(T/(1−β)).
- **Vérités** : V67, V80
- **Repose sur** : théorèmes : `towerMotion_phase`, `mirrorMember_ordinate`, `mirrorMember_radial`; définitions/structures : `TrueZero`, `TowerMotion.phase`, `mirrorMember`, `towerMotionOf`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`.
- **Entraîne** (4) : `insertionDepth_eq`, `mirrorMember_contactMinusAt`, `mirrorMember_contactPlusAt`, `mirror_phase_gap_eq_arctan`.

#### `mirrorMember_contactMinusAt` — `Direct.MirrorCount` l.78 — CONFIRMÉE
- **Énoncé** : Le contact inférieur de coordonnée k de la Tour du miroir vaut exp((arctan(T/(1−β))+kπ)/T) : formule tangentielle exacte.
- **Vérités** : V67, V80, V45
- **Repose sur** : théorèmes : `towerMotion_incidence`, `mirrorMember_phase`, `mirrorMember_ordinate`; définitions/structures : `TrueZero`, `contactMinusAt`, `mirrorMember`, `TowerMotion.incidence`, `towerMotionOf`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`.
- **Entraîne** (3) : `contact_lt_mirror_iff`, `mirror_contact_lt_iff`, `mirror_contacts_interlace`.

#### `mirrorMember_contactPlusAt` — `Direct.MirrorCount` l.87 — CONFIRMÉE
- **Énoncé** : Le contact supérieur de coordonnée k de la Tour du miroir vaut le contact inférieur de coordonnée k+1 (formule tangentielle exacte).
- **Vérités** : V67, V80, V45
- **Repose sur** : théorèmes : `towerMotion_incidence`, `mirrorMember_phase`, `mirrorMember_ordinate`; définitions/structures : `TrueZero`, `contactPlusAt`, `mirrorMember`, `TowerMotion.incidence`, `towerMotionOf`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`.
- **Entraîne** (0) : aucun théorème du projet.

#### `mirror_radial_gt` — `Direct.MirrorCount` l.97 — CONFIRMÉE SOUS CONDITION (zéro de côté bas (β<1/2))
- **Énoncé** : Pour un zéro de côté bas, la position radiale du miroir est strictement supérieure à celle du zéro.
- **Vérités** : V65
- **Repose sur** : théorèmes : `mirrorMember_radial`; définitions/structures : `TrueZero`, `mirrorMember`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (2) : `mirror_precedes`, `offMirror_all_elements_hold_and_vertical_force_fails`.

#### `countedPrimeAt_eq_vonMangoldt` — `Direct.MirrorCount` l.113 — CONFIRMÉE
- **Énoncé** : Le premier constaté au contact supérieur de coordonnée k est le premier de rang π(⌊C⁺⌋) (comptage Chebyshev/Von Mangoldt) : le comptage lit à toute coordonnée.
- **Vérités** : V145, V52
- **Repose sur** : théorèmes : `producedPrime_eq_vonMangoldt`; définitions/structures : `TrueZero`, `countedPrimeAt`, `contactPlusAt`, `towerStateAt`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.nPrimeCountingFromJ`, `RHV3Lean.rChebyshevJNat`.
- **Entraîne** (1) : `vonMangoldt_channel_reflectionFixed`.

#### `countedPrimeAt_eq_primeAtRank` — `Direct.MirrorCount` l.118 — CONFIRMÉE
- **Énoncé** : Le premier constaté en coordonnée k est le premier de rang (rang compté − 1).
- **Vérités** : V145, V52
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `countedPrimeAt`, `countedRankAt`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`.
- **Entraîne** (1) : `countedPrimeAt_lt_expected_of_contact`.

#### `contactPlusAt_lt_primeAtRank_counted` — `Direct.MirrorCount` l.121 — CONFIRMÉE
- **Énoncé** : Le premier de rang π(C⁺) est le premier candidat au-delà du contact supérieur (dualité rang/contact).
- **Vérités** : V145, V52
- **Repose sur** : théorèmes : `contactPlusAt_positive`; définitions/structures : `TrueZero`, `contactPlusAt`, `countedRankAt`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.nEdgePrimeRank`, `RHV3Lean.thm_edgeRank_le_iff_lt_primeAtRank`.
- **Entraîne** (0) : aucun théorème du projet.

#### `mirror_precedes` — `Direct.MirrorCount` l.135 — CONFIRMÉE SOUS CONDITION (zéro de côté bas (β<1/2))
- **Énoncé** : Pour un zéro de côté bas, le miroir est strictement postérieur au zéro dans l'ordre des membres.
- **Vérités** : V68, V74
- **Repose sur** : théorèmes : `mirrorMember_ordinate`, `mirror_radial_gt`; définitions/structures : `TrueZero`, `mirrorMember`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.PZeroMemberPrecedes`, `RHV3Lean.rZeroHeight`, `RHV3Lean.thm_zeroMemberPrecedes_iff_height_radial_lex`.
- **Entraîne** (7) : `exists_fiberSuccessor`, `fiberSuccessor_eq_mirror_of_noInterposition`, `fiberSuccessor_eq_mirror_or_precedes`, `fiberSuccessor_ordinate_eq`, `fiberSuccessor_radial_le_mirror`, `mirrorMember_distinct_member`, `sourceIndex_lt_mirror`.

#### `sourceIndex_lt_mirror` — `Direct.MirrorCount` l.141 — CONFIRMÉE SOUS CONDITION (zéro de côté bas (β<1/2))
- **Énoncé** : Pour un zéro de côté bas, l'index zéro-source du miroir est strictement supérieur à celui du zéro.
- **Vérités** : V68, V74
- **Repose sur** : théorèmes : `mirror_precedes`; définitions/structures : `TrueZero`, `mirrorMember`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.thm_zeroSourceIndex_strictMono`.
- **Entraîne** (8) : `expectedMinimum_le_mirror_occurrence`, `member_index_lt_of_lowerSide`, `mirrorMember_distinct_member`, `mirror_consumes_member_index`, `mirror_heightEventIndex_lt_sourceIndex`, `mirror_occurrence_strict`, `mirror_transport_refuted`, `off_member_index_lt_mirror`.

#### `expectedMinimum_le_mirror_occurrence` — `Direct.MirrorCount` l.145 — CONFIRMÉE SOUS CONDITION (zéro de côté bas (β<1/2))
- **Énoncé** : Pour un zéro de côté bas, l'occurrence du miroir est au moins le minimum attendu de z (progression → minimum attendu).
- **Vérités** : V54, V74, V144
- **Repose sur** : théorèmes : `occurrence_eq_primeAtRank`, `sourceIndex_lt_mirror`; définitions/structures : `TrueZero`, `expectedMinimumPrime`, `occurrence`, `mirrorMember`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.fnPrimeSuccessor`, `RHV3Lean.thm_primeAtRank_strictMono`.
- **Entraîne** (4) : `expectedMinimum_lt_mirror_expectedMinimum`, `lock_imp_counted_lt_occurrence`, `mirrorMember_distinct_member`, `pivotCell_mirror_reaches_expected`.

#### `expectedMinimum_eq_mirror_occurrence_of_consecutive` — `Direct.MirrorCount` l.154 — CONFIRMÉE SOUS CONDITION (paire (z, miroir) strictement consécutive)
- **Énoncé** : Sous consécutivité stricte, l'occurrence du miroir égale exactement le minimum attendu de z.
- **Vérités** : V69, V144, V54
- **Repose sur** : théorèmes : `progression_occurrence`; définitions/structures : `TrueZero`, `mirrorMember`, `expectedMinimumPrime`, `occurrence`. Base rhv3 : `RHV3Lean.PZeroMembersConsecutive`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (4) : `consecutivePairArithmeticChain`, `mirror_pivot_decomposition_of_consecutive`, `off_mirror_same_frequency_of_consecutive`, `secondTower_verification_iff_not_reads_of_consecutive`.

#### `mirror_counted_lt_expected_iff` — `Direct.MirrorCount` l.162 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : rang compté > 0)
- **Énoncé** : Sur un état de la seconde Tour du miroir (compte positif), « premier constaté < p_min(a) » équivaut à « dernier rayon < p_min(a) ».
- **Vérités** : V84
- **Repose sur** : théorèmes : `produced_lt_expectedMinimum_iff`; définitions/structures : `TrueZero`, `countedRankAt`, `mirrorMember`, `countedPrimeAt`, `expectedMinimumPrime`, `contactPlusAt`, `towerStateAt`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `countedPrimeAt_lt_expected_of_contact` — `Direct.MirrorCount` l.170 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : contact supérieur < p_min(a))
- **Énoncé** : Le premier constaté à toute coordonnée est sous p_min(a) dès que le contact supérieur l'est.
- **Vérités** : V84, V52
- **Repose sur** : théorèmes : `produced_lt_expectedMinimum_iff`, `countedPrimeAt_eq_primeAtRank`, `three_le_expectedMinimumPrime`; définitions/structures : `TrueZero`, `contactPlusAt`, `expectedMinimumPrime`, `countedPrimeAt`, `countedRankAt`, `producedPrime`, `towerStateAt`, `countedPrimeAt_lt_expected_of_contact._proof_1_1`, `countedPrimeAt_lt_expected_of_contact._proof_1_2`. Base rhv3 : `RHV3Lean.TTrueHarmonicTowerState.contactPlus`, `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.thm_primeAtRank_zero_eq_two`.
- **Entraîne** (1) : `countedPrime_lt_expected_of_lastRay`.

#### `off_lowerSide` — `Direct.MirrorCount` l.187 — CONFIRMÉE SOUS CONDITION (zéro hors ligne)
- **Énoncé** : Un zéro hors ligne a un côté β<1/2 : lui-même ou son miroir.
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : `mirrorMember_radial`; définitions/structures : `TrueZero`, `mirrorMember`. Base rhv3 : `RHV3Lean.PIsOffCriticalLine`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.PIsOffCriticalLine._proof_1`.
- **Entraîne** (2) : `off_member_index_lt_mirror`, `riemannHypothesis_of_noLowerSide`.

#### `mirrorMember_mirrorMember_radial` — `Direct.MirrorCount` l.197 — CONFIRMÉE
- **Énoncé** : Le miroir du miroir a la position radiale du zéro (involution radiale).
- **Vérités** : V65
- **Repose sur** : théorèmes : `mirrorMember_radial`; définitions/structures : `TrueZero`, `mirrorMember`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `vonMangoldt_channel_reflectionFixed` — `Direct.MirrorCount` l.216 — CONFIRMÉE
- **Énoncé** : Le canal collectif de comptage lu à la Tour du miroir est le même que celui de la Tour de z : seul le contact change.
- **Vérités** : V145, V52
- **Repose sur** : théorèmes : `countedPrimeAt_eq_vonMangoldt`; définitions/structures : `TrueZero`, `countedPrimeAt`, `mirrorMember`, `contactPlusAt`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.nPrimeCountingFromJ`, `RHV3Lean.rChebyshevJNat`.
- **Entraîne** (0) : aucun théorème du projet.

#### `countedPrimeAt_of_contactPlus_eq` — `Direct.MirrorCount` l.226 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : contacts supérieurs égaux)
- **Énoncé** : La lecture ne dépend que du contact : deux membres dont les contacts supérieurs coïncident constatent le même premier.
- **Vérités** : V145, V52
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `contactPlusAt`, `countedPrimeAt`, `producedPrime`, `towerStateAt`, `lastPrimeAtStateUpper`, `primeCountAtStateUpper`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.nEdgePrimeRank`, `RHV3Lean.TTrueHarmonicTowerState.contactPlus`.
- **Entraîne** (0) : aucun théorème du projet.

#### `countedPrimeAt_mono_oriented` — `Direct.MirrorCount` l.236 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : k ≤ l)
- **Énoncé** : Le premier constaté est monotone en la coordonnée sur toute la Tour orientée.
- **Vérités** : V145, V52
- **Repose sur** : théorèmes : `producedPrime_mono`, `towerMotion_incidence_strictOrder`; définitions/structures : `TrueZero`, `countedPrimeAt`, `towerStateAt`, `countedPrimeAt_mono_oriented._proof_1_1`. Base rhv3 : `RHV3Lean.TTrueHarmonicTowerState.contactPlus`.
- **Entraîne** (0) : aucun théorème du projet.


##### Module `RHV6Fresh.Direct.PairTowers` (29 théorèmes)

#### `mirror_sourceIndex_of_consecutive` — `Direct.PairTowers` l.48 — CONFIRMÉE SOUS CONDITION (paire (z, miroir) strictement consécutive)
- **Énoncé** : Sous consécutivité stricte de la paire (z, miroir), l'index zéro-source du miroir est celui de z plus un (la place avance de un).
- **Vérités** : V144, V54, V68
- **Repose sur** : théorèmes : `progression_occurrence`, `occurrence_eq_primeAtRank`; définitions/structures : `TrueZero`, `mirrorMember`, `occurrence`, `expectedMinimumPrime`. Base rhv3 : `RHV3Lean.PZeroMembersConsecutive`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.thm_primeAtRank_strictMono`.
- **Entraîne** (6) : `consecutivePairArithmeticChain`, `consecutive_continuous_signature`, `member_index_succ_of_consecutive`, `off_consecutive_continuous_progression_eq_span`, `off_consecutive_translation_signature`, `off_mirror_same_frequency_of_consecutive`.

#### `firstTowerOf_properState` — `Direct.PairTowers` l.65 — CONFIRMÉE
- **Énoncé** : L'état propre de la première Tour de z est la cellule du pivot de z.
- **Vérités** : V28, V15
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `TrueTower.properState`, `firstTowerOf`, `pivotCell`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `firstTowerOf_eq_lineTowerOf` — `Direct.PairTowers` l.68 — CONFIRMÉE SOUS CONDITION (zéro sur la droite critique (β=1/2))
- **Énoncé** : Pour un zéro de la droite, la première Tour est la Tour de la droite.
- **Vérités** : V28, V77
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `TrueTower`, `firstTowerOf`, `lineTowerOf`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `firstTower_reaches_expected` — `Direct.PairTowers` l.71 — CONFIRMÉE
- **Énoncé** : La première Tour de tout zéro atteint le minimum attendu de son zéro (par la règle du pivot).
- **Vérités** : V88, V132
- **Repose sur** : théorèmes : `pivotPair_reaches`, `expectedMinimumPrime_pos`; définitions/structures : `TrueZero`, `reaches`, `TrueTower.properState`, `firstTowerOf`, `expectedMinimumPrime`. Base rhv3 : aucun.
- **Entraîne** (4) : `firstTower_reaches_occurrence`, `mirror_ownTower_reads`, `reaches_expected`, `upright_presents_forward`.

#### `firstTower_reaches_occurrence` — `Direct.PairTowers` l.76 — CONFIRMÉE
- **Énoncé** : La première Tour de tout zéro lit son occurrence (théorème).
- **Vérités** : V88, V75
- **Repose sur** : théorèmes : `reaches_of_le`, `occurrence_lt_expectedMinimumPrime`, `firstTower_reaches_expected`; définitions/structures : `TrueZero`, `reaches`, `TrueTower.properState`, `firstTowerOf`, `occurrence`, `expectedMinimumPrime`. Base rhv3 : aucun.
- **Entraîne** (6) : `mirrorMember_firstTower_reaches_occurrence`, `mirror_ownTower_reads`, `reached_progression`, `reaches_occurrence`, `upright_presents_forward`, `verification_passes`.

#### `firstTower_readings` — `Direct.PairTowers` l.82 — CONFIRMÉE
- **Énoncé** : La première Tour a pour coordonnée d'entrée celle du pivot de p_min(z) et un étage.
- **Vérités** : V43, V143
- **Repose sur** : théorèmes : `pivotPair_entryCoordinate`, `pivotPair_stageCount`; définitions/structures : `TrueZero`, `AnalyticContactPair.entryCoordinate`, `TrueTower.properState`, `firstTowerOf`, `pivotCoordinate`, `expectedMinimumPrime`, `AnalyticContactPair.stageCount`. Base rhv3 : aucun.
- **Entraîne** (4) : `firstTower_contactPair_unique`, `readings`, `secondTower_coordinate_eq_unique_mirrorContactPair`, `stop_event`.

#### `firstTower_cell_contains_expected` — `Direct.PairTowers` l.97 — CONFIRMÉE
- **Énoncé** : Pour tout zéro et tout β, la cellule de la première Tour contient le minimum attendu (C⁻ < p_min(z) ≤ C⁺).
- **Vérités** : V143, V40
- **Repose sur** : théorèmes : `entry_lt_pivot`, `expectedMinimumPrime_pos`, `pivot_le_lastRay`; définitions/structures : `TrueZero`, `AnalyticContactPair.entryContact`, `TrueTower.toAnalyticContactPair`, `firstTowerOf`, `expectedMinimumPrime`, `AnalyticContactPair.lastRayContact`. Base rhv3 : aucun.
- **Entraîne** (3) : `grammar_determines_stop_ray`, `properTowerOfMirror_and_reflectedMotion_coexist`, `regime_captive_of_prime`.

#### `firstTower_contactPair_unique` — `Direct.PairTowers` l.105 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : la cellule de k contient p_min(z))
- **Énoncé** : Toute coordonnée k dont la cellule contient p_min(z) est la coordonnée d'entrée de la première Tour : la paire de contacts est unique, pour tout β.
- **Vérités** : V143, V36, V46
- **Repose sur** : théorèmes : `firstTower_readings`, `pivotCoordinate_unique`, `expectedMinimumPrime_pos`; définitions/structures : `TrueZero`, `contactMinusAt`, `expectedMinimumPrime`, `contactPlusAt`, `AnalyticContactPair.entryCoordinate`, `TrueTower.properState`, `firstTowerOf`, `pivotCoordinate`, `AnalyticContactPair.stageCount`. Base rhv3 : aucun.
- **Entraîne** (2) : `control_two_onLine_towers_unique`, `off_pair_towers_unique_like_control`.

#### `secondTowerOf_properState` — `Direct.PairTowers` l.137 — CONFIRMÉE
- **Énoncé** : L'état propre de la seconde Tour de z est la paire inversée du pivot de p_min(z*) sur le membre miroir.
- **Vérités** : V29, V82, V76
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair`, `mirrorMember`, `InvertedTower.properState`, `secondTowerOf`, `invertedPivotPair`, `expectedMinimumPrime`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `secondTower_ring_eq_mirror_firstTower` — `Direct.PairTowers` l.141 — CONFIRMÉE
- **Énoncé** : Redressé, l'anneau de la seconde Tour est celui de la première Tour du membre miroir : un membre, un anneau, deux orientations.
- **Vérités** : V71, V76, V67
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `mirrorMember`, `InvertedContactPair.upright`, `InvertedTower.properState`, `secondTowerOf`, `TrueTower.properState`, `firstTowerOf`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `secondTower_entry_eq_incidence` — `Direct.PairTowers` l.146 — CONFIRMÉE
- **Énoncé** : L'entrée de la seconde Tour est le rayon du haut de l'anneau du pivot du miroir (C*_{k₂+1}).
- **Vérités** : V80, V82
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair.entryContact`, `mirrorMember`, `InvertedTower.toInvertedContactPair`, `secondTowerOf`, `TowerMotion.incidence`, `towerMotionOf`, `pivotCoordinate`, `expectedMinimumPrime`. Base rhv3 : aucun.
- **Entraîne** (1) : `secondTower_entry_eq_reflected`.

#### `secondTower_lastRay_eq_incidence` — `Direct.PairTowers` l.152 — CONFIRMÉE
- **Énoncé** : Le dernier rayon de la seconde Tour est le rayon du bas de l'anneau du pivot du miroir (C*_{k₂}).
- **Vérités** : V80, V82
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair.lastRayContact`, `mirrorMember`, `InvertedTower.toInvertedContactPair`, `secondTowerOf`, `TowerMotion.incidence`, `towerMotionOf`, `pivotCoordinate`, `expectedMinimumPrime`. Base rhv3 : aucun.
- **Entraîne** (1) : `secondTower_lastRay_eq_reflected`.

#### `secondTower_entry_eq_reflected` — `Direct.PairTowers` l.158 — CONFIRMÉE
- **Énoncé** : L'entrée de la seconde Tour est l'entrée du zéro réfléchi à sa coordonnée −(k₂+1) : l'inversion est un théorème.
- **Vérités** : V34, V80
- **Repose sur** : théorèmes : `secondTower_entry_eq_incidence`, `reflectedIncidence_eq`; définitions/structures : `TrueZero`, `InvertedContactPair.entryContact`, `mirrorMember`, `InvertedTower.toInvertedContactPair`, `secondTowerOf`, `reflectedIncidence`, `pivotCoordinate`, `expectedMinimumPrime`, `TowerMotion.incidence`, `towerMotionOf`. Base rhv3 : aucun.
- **Entraîne** (2) : `reflected_presents_via_functional_reflect`, `secondTower_inversion_is_unconditional`.

#### `secondTower_lastRay_eq_reflected` — `Direct.PairTowers` l.166 — CONFIRMÉE
- **Énoncé** : Le dernier rayon de la seconde Tour est le rayon suivant du zéro réfléchi à la coordonnée −(k₂+1)+1.
- **Vérités** : V34, V80
- **Repose sur** : théorèmes : `secondTower_lastRay_eq_incidence`, `reflectedIncidence_eq`; définitions/structures : `TrueZero`, `InvertedContactPair.lastRayContact`, `mirrorMember`, `InvertedTower.toInvertedContactPair`, `secondTowerOf`, `reflectedIncidence`, `pivotCoordinate`, `expectedMinimumPrime`, `TowerMotion.incidence`, `towerMotionOf`, `TowerMotion`. Base rhv3 : aucun.
- **Entraîne** (2) : `reflected_presents_via_functional_reflect`, `secondTower_inversion_is_unconditional`.

#### `secondTower_readings` — `Direct.PairTowers` l.176 — CONFIRMÉE
- **Énoncé** : La seconde Tour a pour coordonnée d'entrée k₂+1 (k₂ = coordonnée du pivot du miroir) et un étage.
- **Vérités** : V80, V43
- **Repose sur** : théorèmes : `invertedPivotPair_entryCoordinate`, `invertedPivotPair_stageCount`; définitions/structures : `TrueZero`, `InvertedContactPair.entryCoordinate`, `mirrorMember`, `InvertedTower.properState`, `secondTowerOf`, `pivotCoordinate`, `expectedMinimumPrime`, `InvertedContactPair.stageCount`. Base rhv3 : aucun.
- **Entraîne** (1) : `secondTower_coordinate_eq_unique_mirrorContactPair`.

#### `secondTower_coordinate_eq_unique_mirrorContactPair` — `Direct.PairTowers` l.182 — CONFIRMÉE
- **Énoncé** : La coordonnée de la seconde Tour moins un est la coordonnée unique de la première Tour du membre miroir : pas une re-sélection.
- **Vérités** : V143, V76, V80
- **Repose sur** : théorèmes : `secondTower_readings`, `firstTower_readings`; définitions/structures : `TrueZero`, `InvertedContactPair.entryCoordinate`, `mirrorMember`, `InvertedTower.properState`, `secondTowerOf`, `AnalyticContactPair.entryCoordinate`, `TrueTower.properState`, `firstTowerOf`, `pivotCoordinate`, `expectedMinimumPrime`, `InvertedContactPair.stageCount`, `AnalyticContactPair.stageCount`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `secondTower_cell_contains_own_expected` — `Direct.PairTowers` l.195 — CONFIRMÉE
- **Énoncé** : La seconde Tour atteint l'anneau de son pivot propre p_min(z*) : dernier rayon strictement sous lui, entrée au moins égale.
- **Vérités** : V135, V82, V76
- **Repose sur** : théorèmes : `invertedPivotPair_cell_contains`, `expectedMinimumPrime_prime`; définitions/structures : `TrueZero`, `InvertedContactPair.lastRayContact`, `mirrorMember`, `InvertedTower.toInvertedContactPair`, `secondTowerOf`, `expectedMinimumPrime`, `InvertedContactPair.entryContact`. Base rhv3 : aucun.
- **Entraîne** (3) : `reflected_presents_reversed`, `secondTowerOwnContacts_meets_arithmeticChain`, `secondTower_entry_reaches_own_expected`.

#### `secondTower_entry_reaches_own_expected` — `Direct.PairTowers` l.203 — CONFIRMÉE
- **Énoncé** : Dans la seconde orientation, le contact qui atteint le pivot propre est l'entrée (p_min(z*) ≤ entrée).
- **Vérités** : V135, V111, V82
- **Repose sur** : théorèmes : `secondTower_cell_contains_own_expected`; définitions/structures : `TrueZero`, `expectedMinimumPrime`, `mirrorMember`, `InvertedContactPair.entryContact`, `InvertedTower.properState`, `secondTowerOf`, `InvertedContactPair.lastRayContact`, `InvertedTower.toInvertedContactPair`. Base rhv3 : aucun.
- **Entraîne** (2) : `reflected_presents_reversed`, `secondTower_entry_reaches_mirror_occurrence`.

#### `secondTower_not_reaches_own_expected` — `Direct.PairTowers` l.208 — CONFIRMÉE
- **Énoncé** : La seconde Tour, lue à son dernier rayon, n'atteint jamais son pivot propre p_min(z*).
- **Vérités** : V135, V153
- **Repose sur** : théorèmes : `invertedPivotPair_not_reaches`, `expectedMinimumPrime_prime`; définitions/structures : `TrueZero`, `InvertedContactPair.reaches`, `mirrorMember`, `InvertedTower.properState`, `secondTowerOf`, `expectedMinimumPrime`. Base rhv3 : aucun.
- **Entraîne** (1) : `secondTower_counted_lt_own_expected`.

#### `secondTower_counted_lt_own_expected` — `Direct.PairTowers` l.213 — CONFIRMÉE
- **Énoncé** : Le premier compté au dernier rayon de la seconde Tour est strictement sous son pivot propre.
- **Vérités** : V135, V153
- **Repose sur** : théorèmes : `secondTower_not_reaches_own_expected`, `InvertedContactPair.countedPrime_lt_of_not_reaches_succ`; définitions/structures : `TrueZero`, `InvertedContactPair.countedPrime`, `mirrorMember`, `InvertedTower.properState`, `secondTowerOf`, `expectedMinimumPrime`, `InvertedContactPair.reaches`. Base rhv3 : `RHV3Lean.fnPrimeSuccessor`, `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `secondTower_entry_reaches_mirror_occurrence` — `Direct.PairTowers` l.220 — CONFIRMÉE
- **Énoncé** : À l'entrée, la seconde Tour atteint l'occurrence du membre miroir (Occ(z*) < p_min(z*) ≤ entrée), sans hypothèse.
- **Vérités** : V111, V114
- **Repose sur** : théorèmes : `occurrence_lt_expectedMinimumPrime`, `secondTower_entry_reaches_own_expected`; définitions/structures : `TrueZero`, `occurrence`, `mirrorMember`, `InvertedContactPair.entryContact`, `InvertedTower.properState`, `secondTowerOf`, `expectedMinimumPrime`. Base rhv3 : aucun.
- **Entraîne** (1) : `reflected_presents_reversed`.

#### `expectedMinimum_lt_mirror_expectedMinimum` — `Direct.PairTowers` l.235 — CONFIRMÉE SOUS CONDITION (zéro de côté bas (β<1/2))
- **Énoncé** : Pour un zéro de côté bas, le minimum attendu de z est strictement sous celui du miroir.
- **Vérités** : V144
- **Repose sur** : théorèmes : `expectedMinimum_le_mirror_occurrence`, `occurrence_lt_expectedMinimumPrime`; définitions/structures : `TrueZero`, `expectedMinimumPrime`, `mirrorMember`, `occurrence`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `consecutivePairArithmeticChain`.

#### `secondTower_reads_occurrence_iff_coordinate_lt` — `Direct.PairTowers` l.242 — CONFIRMÉE
- **Énoncé** : C_lecture : la seconde Tour lit l'occurrence du miroir ssi Occ(z*) tombe dans un anneau strictement sous celui de p_min(z*) (équivalence de position d'anneau, non lecture inconditionnelle).
- **Vérités** : V85, V135, O3, O11
- **Repose sur** : théorèmes : `occurrence_prime`, `pivotCoordinate_le_of_le_contactPlus`, `pivot_le_contactPlus_pivotCoordinate`, `towerMotion_incidence_mono`; définitions/structures : `TrueZero`, `InvertedContactPair.reaches`, `mirrorMember`, `InvertedTower.properState`, `secondTowerOf`, `occurrence`, `pivotCoordinate`, `expectedMinimumPrime`, `contactMinusAt`, `contactPlusAt`, `TowerMotion.incidence`, `towerMotionOf` et 2 autres. Base rhv3 : aucun.
- **Entraîne** (4) : `mirror_two_towers_same_ring`, `remaining_open_question_is_readout_only`, `secondTower_reads_iff_progression_pos`, `secondTower_reads_of_gap_ge_pi`.

#### `secondTower_verification_iff_not_reads_of_consecutive` — `Direct.PairTowers` l.280 — CONFIRMÉE SOUS CONDITION (paire (z, miroir) strictement consécutive)
- **Énoncé** : Sous consécutivité stricte, le constat de vérification (dernier rayon < p_min(z)) équivaut à la négation du constat de lecture : les deux constats s'excluent, tautologie de l'ordre.
- **Vérités** : V84, V93, V135
- **Repose sur** : théorèmes : `expectedMinimum_eq_mirror_occurrence_of_consecutive`, `InvertedContactPair.not_reaches_iff`; définitions/structures : `TrueZero`, `mirrorMember`, `InvertedContactPair.lastRayContact`, `InvertedTower.properState`, `secondTowerOf`, `expectedMinimumPrime`, `InvertedContactPair.reaches`, `occurrence`. Base rhv3 : `RHV3Lean.PZeroMembersConsecutive`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `authorForm_iff_counted_lt` — `Direct.PairTowers` l.321 — CONFIRMÉE
- **Énoncé** : Sur tout état inversé du miroir, « p_min(z) au moins le premier suivant le compté » équivaut à « le premier compté est strictement sous p_min(z) » (forme comptée du constat de vérification).
- **Vérités** : V84
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair`, `mirrorMember`, `InvertedContactPair.countedRank`, `expectedMinimumPrime`, `InvertedContactPair.countedPrime`, `authorForm_iff_counted_lt._proof_1_1`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.fnPrimeSuccessor`, `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.thm_primeAtRank_strictMono`.
- **Entraîne** (0) : aucun théorème du projet.

#### `mirrorMember_ne` — `Direct.PairTowers` l.339 — CONFIRMÉE SOUS CONDITION (zéro de côté bas (β<1/2))
- **Énoncé** : Le membre miroir d'un zéro de côté bas est distinct du zéro original.
- **Vérités** : V74
- **Repose sur** : théorèmes : `mirrorMember_radial`; définitions/structures : `TrueZero`, `mirrorMember`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (2) : `mirrorMember_distinct_member`, `mirror_expectedMinimum_ne`.

#### `mirrorMember_distinct_member` — `Direct.PairTowers` l.347 — CONFIRMÉE SOUS CONDITION (zéro de côté bas (β<1/2))
- **Énoncé** : Un zéro de côté bas a un miroir membre authentique et distinct, strictement postérieur, d'index avancé, d'occurrence ≥ p_min(z).
- **Vérités** : V74, V68, V135
- **Repose sur** : théorèmes : `mirrorMember_ne`, `mirror_precedes`, `sourceIndex_lt_mirror`, `expectedMinimum_le_mirror_occurrence`; définitions/structures : `TrueZero`, `mirrorMember`, `expectedMinimumPrime`, `occurrence`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.PZeroMemberPrecedes`, `RHV3Lean.nZeroSourceIndex`.
- **Entraîne** (0) : aucun théorème du projet.

#### `mirrorMember_firstTower_reaches_occurrence` — `Direct.PairTowers` l.357 — CONFIRMÉE
- **Énoncé** : La première Tour du membre miroir lit son occurrence (la liaison portée par cette Tour).
- **Vérités** : V75, V135
- **Repose sur** : théorèmes : `firstTower_reaches_occurrence`; définitions/structures : `TrueZero`, `reaches`, `mirrorMember`, `TrueTower.properState`, `firstTowerOf`, `occurrence`. Base rhv3 : aucun.
- **Entraîne** (1) : `mirror_two_towers_same_ring`.

#### `mirror_two_towers_same_ring` — `Direct.PairTowers` l.363 — CONFIRMÉE
- **Énoncé** : Les deux Tours du membre miroir lisent le même anneau en sens opposés : la première lit son occurrence, la seconde la lit ssi Occ(z*) est dans un anneau strictement sous celui de p_min(z*).
- **Vérités** : V71, V76, V135, V85
- **Repose sur** : théorèmes : `mirrorMember_firstTower_reaches_occurrence`, `secondTower_reads_occurrence_iff_coordinate_lt`; définitions/structures : `TrueZero`, `reaches`, `mirrorMember`, `TrueTower.properState`, `firstTowerOf`, `occurrence`, `InvertedContactPair.reaches`, `InvertedTower.properState`, `secondTowerOf`, `pivotCoordinate`, `expectedMinimumPrime`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.


##### Module `RHV6Fresh.Direct.PivotCell` (32 théorèmes)

#### `expectedMinimumPrime_pos` — `Direct.PivotCell` l.43 — CONFIRMÉE
- **Énoncé** : Le minimum attendu d'un zéro (premier suivant son occurrence) est strictement positif.
- **Vérités** : V54
- **Repose sur** : théorèmes : `expectedMinimumPrime_prime`; définitions/structures : `TrueZero`, `expectedMinimumPrime`. Base rhv3 : aucun.
- **Entraîne** (12) : `cell_contains_expected`, `firstTower_cell_contains_expected`, `firstTower_contactPair_unique`, `firstTower_reaches_expected`, `geometry_selects_raccord_prime`, `horizontalRaccords_amplitude_brackets`, `lineTower_cell_contains_expected`, `lineTower_reaches_expected`, `passage_double_constraint`, `pivotPair_mirror_reaches_of_ge`, `secondTower_reads_of_gap_ge_pi`, `stop_event`.

#### `pivotPair_entryContact` — `Direct.PivotCell` l.61 — CONFIRMÉE
- **Énoncé** : L'incidence d'entrée de la paire du pivot est le rayon de coordonnée pivotCoordinate z q (croisement d'arrêt de la règle du pivot).
- **Vérités** : V28, V32, V33
- **Repose sur** : théorèmes : `analyticPairAt_entryContact`, `towerMotion_incidence`; définitions/structures : `TrueZero`, `AnalyticContactPair.entryContact`, `pivotPair`, `TowerMotion.phase`, `towerMotionOf`, `pivotCoordinate`, `analyticPairAt`, `contactMinusAt`, `TowerMotion.incidence`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (2) : `entry_lt_pivot`, `pivotPair_entryReading`.

#### `pivotPair_lastRayContact` — `Direct.PivotCell` l.70 — CONFIRMÉE
- **Énoncé** : Le dernier rayon de la paire du pivot est le rayon suivant la coordonnée du pivot.
- **Vérités** : V28, V32, V33
- **Repose sur** : théorèmes : `analyticPairAt_lastRayContact`, `towerMotion_incidence`; définitions/structures : `TrueZero`, `AnalyticContactPair.lastRayContact`, `pivotPair`, `TowerMotion.phase`, `towerMotionOf`, `pivotCoordinate`, `analyticPairAt`, `contactPlusAt`, `TowerMotion.incidence`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `pivot_le_lastRay`.

#### `pivotCoordinate_unique` — `Direct.PivotCell` l.79 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : q>0 ; q dans la cellule de coordonnée k)
- **Énoncé** : Toute coordonnée k dont la cellule contient la référence q (C_k < q ≤ C_{k+1}) est la coordonnée du pivot : k n'est pas choisi.
- **Vérités** : V143, V36, V44
- **Repose sur** : théorèmes : `towerMotion_incidence`; définitions/structures : `TrueZero`, `contactMinusAt`, `contactPlusAt`, `pivotCoordinate`, `TowerMotion.phase`, `towerMotionOf`, `TowerMotion.incidence`, `towerPosition`, `pivotCoordinate_unique._proof_1_1`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (3) : `firstTower_contactPair_unique`, `geometry_selects_raccord_prime`, `pivotCoordinate_eq_of_same_cell`.

#### `pivotPair_entryReading` — `Direct.PivotCell` l.106 — CONFIRMÉE
- **Énoncé** : La coordonnée d'entrée lue sur la paire du pivot est la coordonnée calculée par la règle.
- **Vérités** : V43, V32
- **Repose sur** : théorèmes : `pivotPair_entryContact`, `towerMotion_phase`; définitions/structures : `TrueZero`, `AnalyticContactPair.entryReading`, `pivotPair`, `pivotCoordinate`, `AnalyticContactPair.entryContact`, `TowerMotion.phase`, `towerMotionOf`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rTowerPhase`, `RHV3Lean.rZeroRadialPosition`.
- **Entraîne** (1) : `pivotPair_entryCoordinate`.

#### `pivotPair_entryCoordinate` — `Direct.PivotCell` l.120 — CONFIRMÉE
- **Énoncé** : La coordonnée d'entrée de la paire du pivot est la coordonnée calculée.
- **Vérités** : V43, V32
- **Repose sur** : théorèmes : `AnalyticContactPair.entryCoordinate_cast`, `pivotPair_entryReading`; définitions/structures : `TrueZero`, `AnalyticContactPair.entryCoordinate`, `pivotPair`, `pivotCoordinate`, `AnalyticContactPair.entryReading`. Base rhv3 : aucun.
- **Entraîne** (3) : `firstTower_readings`, `invertedPivotPair_entryCoordinate`, `lineTower_readings`.

#### `pivotPair_stageReading` — `Direct.PivotCell` l.127 — CONFIRMÉE
- **Énoncé** : Le nombre d'étages lu sur la paire du pivot vaut un.
- **Vérités** : V32, V43
- **Repose sur** : théorèmes : `analyticPairAt_lastRayContact`, `analyticPairAt_entryContact`, `contactAt_consecutive_logWidth`; définitions/structures : `TrueZero`, `AnalyticContactPair.stageReading`, `pivotPair`, `AnalyticContactPair.logDiameter`, `AnalyticContactPair.lastRayContact`, `AnalyticContactPair.entryContact`, `analyticPairAt`, `pivotCoordinate`, `contactPlusAt`, `contactMinusAt`. Base rhv3 : `RHV3Lean.rTowerDensity`, `RHV3Lean.rTowerHeight`, `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `pivotPair_stageCount`.

#### `pivotPair_stageCount` — `Direct.PivotCell` l.139 — CONFIRMÉE
- **Énoncé** : Le nombre d'étages de la paire du pivot vaut un.
- **Vérités** : V32, V43
- **Repose sur** : théorèmes : `AnalyticContactPair.stageCount_cast`, `pivotPair_stageReading`; définitions/structures : `TrueZero`, `AnalyticContactPair.stageCount`, `pivotPair`, `AnalyticContactPair.stageReading`. Base rhv3 : aucun.
- **Entraîne** (4) : `firstTower_readings`, `invertedPivotPair_entryCoordinate`, `invertedPivotPair_stageCount`, `lineTower_readings`.

#### `entry_lt_pivot` — `Direct.PivotCell` l.147 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : q>0)
- **Énoncé** : L'incidence d'entrée de la paire du pivot est strictement sous la référence.
- **Vérités** : V143, V40
- **Repose sur** : théorèmes : `pivotPair_entryContact`; définitions/structures : `TrueZero`, `AnalyticContactPair.entryContact`, `pivotPair`, `TowerMotion.phase`, `towerMotionOf`, `pivotCoordinate`, `towerPosition`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (8) : `canonicalOrigin_lt_iff_zero_le_pivotCoordinate`, `cell_contains_expected`, `firstTower_cell_contains_expected`, `invertedPivotPair_cell_contains`, `invertedPivotPair_lastRay_lt_pivot`, `lineTower_cell_contains_expected`, `pivotCoordinate_le_of_le_contactPlus`, `prime_raccord_has_unique_tower_cell`.

#### `pivot_le_lastRay` — `Direct.PivotCell` l.165 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : q>0)
- **Énoncé** : La référence est au plus égale au dernier rayon de sa paire de pivot.
- **Vérités** : V143, V40, V37
- **Repose sur** : théorèmes : `pivotPair_lastRayContact`; définitions/structures : `TrueZero`, `AnalyticContactPair.lastRayContact`, `pivotPair`, `TowerMotion.phase`, `towerMotionOf`, `pivotCoordinate`, `towerPosition`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (7) : `cell_contains_expected`, `firstTower_cell_contains_expected`, `invertedPivotPair_cell_contains`, `lineTower_cell_contains_expected`, `pivotPair_reaches`, `pivot_le_contactPlus_pivotCoordinate`, `prime_raccord_has_unique_tower_cell`.

#### `pivotPair_reaches` — `Direct.PivotCell` l.182 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : p>0)
- **Énoncé** : La référence (un naturel p>0) est atteinte par la cellule qu'elle arrête (p ≤ dernier rayon).
- **Vérités** : V37, V88
- **Repose sur** : théorèmes : `pivot_le_lastRay`; définitions/structures : `TrueZero`, `reaches`, `pivotPair`. Base rhv3 : aucun.
- **Entraîne** (5) : `firstTower_reaches_expected`, `lineTower_reaches_expected`, `pivotPair_reaches_of_le`, `pivot_countedRank_pos`, `pivot_le_counted`.

#### `pivotPair_reaches_of_le` — `Direct.PivotCell` l.187 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : q>0 ; p ≤ q)
- **Énoncé** : Tout entier p au plus égal à la référence q est atteint par la cellule de q.
- **Vérités** : V37, V88
- **Repose sur** : théorèmes : `reaches_of_le`, `pivotPair_reaches`; définitions/structures : `TrueZero`, `reaches`, `pivotPair`. Base rhv3 : aucun.
- **Entraîne** (1) : `pivotPair_mirror_reaches_of_ge`.

#### `pivotCoordinate_eq_of_same_cell` — `Direct.PivotCell` l.192 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : q,q'>0 ; q et q' dans la même cellule de coordonnée k)
- **Énoncé** : Deux références de la même cellule donnent la même coordonnée de pivot : la règle est aveugle au premier choisi dans la cellule.
- **Vérités** : V36, V143, V151
- **Repose sur** : théorèmes : `pivotCoordinate_unique`; définitions/structures : `TrueZero`, `contactMinusAt`, `contactPlusAt`, `pivotCoordinate`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `pivotCoordinate_le_of_le_contactPlus` — `Direct.PivotCell` l.202 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : q>0 ; q ≤ C_{k+1})
- **Énoncé** : Toute coordonnée dont le croisement suivant atteint q est ≥ la coordonnée du pivot : la règle s'arrête au premier anneau qui atteint la référence.
- **Vérités** : V32, V143
- **Repose sur** : théorèmes : `analyticPairAt_entryContact`, `towerMotion_incidence_mono`, `entry_lt_pivot`; définitions/structures : `TrueZero`, `contactPlusAt`, `pivotCoordinate`, `pivotCoordinate_le_of_le_contactPlus._proof_1_1`, `AnalyticContactPair.entryContact`, `pivotPair`, `analyticPairAt`, `contactMinusAt`, `TowerMotion.incidence`, `towerMotionOf`. Base rhv3 : aucun.
- **Entraîne** (2) : `pivotCoordinate_isLeast`, `secondTower_reads_occurrence_iff_coordinate_lt`.

#### `pivot_le_contactPlus_pivotCoordinate` — `Direct.PivotCell` l.215 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : q>0)
- **Énoncé** : La référence est atteinte au croisement suivant la coordonnée du pivot.
- **Vérités** : V32, V143
- **Repose sur** : théorèmes : `pivot_le_lastRay`, `analyticPairAt_lastRayContact`; définitions/structures : `TrueZero`, `contactPlusAt`, `pivotCoordinate`, `AnalyticContactPair.lastRayContact`, `pivotPair`, `analyticPairAt`. Base rhv3 : aucun.
- **Entraîne** (3) : `canonicalOrigin_lt_iff_zero_le_pivotCoordinate`, `pivotCoordinate_isLeast`, `secondTower_reads_occurrence_iff_coordinate_lt`.

#### `pivotCoordinate_isLeast` — `Direct.PivotCell` l.222 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : q>0)
- **Énoncé** : La coordonnée du pivot est le plus petit k tel que q ≤ C_{k+1} : événement d'arrêt, plus petit anneau qui atteint la référence.
- **Vérités** : V143, V32, V44
- **Repose sur** : théorèmes : `pivot_le_contactPlus_pivotCoordinate`, `pivotCoordinate_le_of_le_contactPlus`; définitions/structures : `TrueZero`, `contactPlusAt`, `pivotCoordinate`. Base rhv3 : aucun.
- **Entraîne** (1) : `stop_event`.

#### `canonicalOrigin_lt_iff_zero_le_pivotCoordinate` — `Direct.PivotCell` l.228 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : q>0)
- **Énoncé** : La référence est devant l'origine canonique exactement quand la coordonnée d'arrêt est ≥ 0 (le parcours part de l'origine canonique).
- **Vérités** : V32, V22
- **Repose sur** : théorèmes : `pivot_le_contactPlus_pivotCoordinate`, `towerMotion_incidence_lt_iff`, `analyticPairAt_entryContact`, `towerMotion_incidence_mono`, `entry_lt_pivot`; définitions/structures : `TrueZero`, `canonicalOrigin`, `pivotCoordinate`, `contactPlusAt`, `TowerMotion.incidence`, `towerMotionOf`, `canonicalOrigin_lt_iff_zero_le_pivotCoordinate._proof_1_1`, `AnalyticContactPair.entryContact`, `pivotPair`, `analyticPairAt`, `contactMinusAt`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `pivot_countedRank_pos` — `Direct.PivotCell` l.249 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : q premier)
- **Énoncé** : Le rang compté au dernier rayon de la cellule d'une référence première est strictement positif.
- **Vérités** : V52, V37
- **Repose sur** : théorèmes : `reaches_primeAtRank_iff`, `pivotPair_reaches`; définitions/structures : `TrueZero`, `countedRank`, `pivotPair`, `reaches`, `pivot_countedRank_pos._proof_1_1`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.thm_primeAtRank_surjective_onPrimes`.
- **Entraîne** (1) : `pivot_le_counted`.

#### `pivot_le_counted` — `Direct.PivotCell` l.256 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : q premier)
- **Énoncé** : La cible constatée (dernier premier compté au dernier rayon) est au moins la référence : elle peut la dépasser, jamais descendre sous elle.
- **Vérités** : V38, V37, V52
- **Repose sur** : théorèmes : `reaches_iff_le_countedPrime`, `pivot_countedRank_pos`, `pivotPair_reaches`; définitions/structures : `TrueZero`, `countedPrime`, `pivotPair`, `reaches`. Base rhv3 : aucun.
- **Entraîne** (2) : `expected_le_counted`, `lineTower_expected_le_counted`.

#### `R1_iff_expected_le_counted` — `Direct.PivotCell` l.262 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : rang compté > 0)
- **Énoncé** : Sur toute paire de contacts à compte positif, le minimum attendu est atteint ssi il ne dépasse pas la cible constatée.
- **Vérités** : V37, V52
- **Repose sur** : théorèmes : `reaches_iff_le_countedPrime`, `expectedMinimumPrime_prime`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `countedRank`, `reaches`, `expectedMinimumPrime`, `countedPrime`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `lineTowerOf_properState` — `Direct.PivotCell` l.281 — CONFIRMÉE SOUS CONDITION (zéro sur la droite critique (β=1/2))
- **Énoncé** : Pour un zéro de la droite, l'état propre de la Tour de la droite est la cellule du pivot.
- **Vérités** : V28, V77
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `TrueTower.properState`, `lineTowerOf`, `pivotCell`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `lineTower_reaches_expected` — `Direct.PivotCell` l.284 — CONFIRMÉE SOUS CONDITION (zéro sur la droite critique (β=1/2))
- **Énoncé** : Sur la droite, la Tour atteint le minimum attendu de son zéro (par construction de la règle).
- **Vérités** : V88, V28
- **Repose sur** : théorèmes : `pivotPair_reaches`, `expectedMinimumPrime_pos`; définitions/structures : `TrueZero`, `reaches`, `TrueTower.properState`, `lineTowerOf`, `expectedMinimumPrime`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `lineTower_reaches_occurrence`.

#### `lineTower_reaches_occurrence` — `Direct.PivotCell` l.289 — CONFIRMÉE SOUS CONDITION (zéro sur la droite critique (β=1/2))
- **Énoncé** : Sur la droite, la Tour du zéro lit son occurrence (Occ(z) < p_min(z)).
- **Vérités** : V88, V75
- **Repose sur** : théorèmes : `reaches_of_le`, `occurrence_lt_expectedMinimumPrime`, `lineTower_reaches_expected`; définitions/structures : `TrueZero`, `reaches`, `TrueTower.properState`, `lineTowerOf`, `occurrence`, `expectedMinimumPrime`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `lineTower_cell_contains_expected` — `Direct.PivotCell` l.295 — CONFIRMÉE SOUS CONDITION (zéro sur la droite critique (β=1/2))
- **Énoncé** : Sur la droite, C⁻ < p_min(z) ≤ C⁺ : le minimum attendu est dans la cellule.
- **Vérités** : V40, V143
- **Repose sur** : théorèmes : `entry_lt_pivot`, `expectedMinimumPrime_pos`, `pivot_le_lastRay`; définitions/structures : `TrueZero`, `AnalyticContactPair.entryContact`, `TrueTower.toAnalyticContactPair`, `lineTowerOf`, `expectedMinimumPrime`, `AnalyticContactPair.lastRayContact`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `lineTower_readings` — `Direct.PivotCell` l.302 — CONFIRMÉE SOUS CONDITION (zéro sur la droite critique (β=1/2))
- **Énoncé** : Sur la droite, la coordonnée d'entrée est celle du pivot de p_min(z) et le nombre d'étages vaut 1.
- **Vérités** : V43, V32
- **Repose sur** : théorèmes : `pivotPair_entryCoordinate`, `pivotPair_stageCount`; définitions/structures : `TrueZero`, `AnalyticContactPair.entryCoordinate`, `TrueTower.properState`, `lineTowerOf`, `pivotCoordinate`, `expectedMinimumPrime`, `AnalyticContactPair.stageCount`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `lineTower_expected_le_counted` — `Direct.PivotCell` l.309 — CONFIRMÉE SOUS CONDITION (zéro sur la droite critique (β=1/2))
- **Énoncé** : Sur la droite, la cible constatée est au moins le minimum attendu.
- **Vérités** : V38
- **Repose sur** : théorèmes : `pivot_le_counted`, `expectedMinimumPrime_prime`; définitions/structures : `TrueZero`, `expectedMinimumPrime`, `countedPrime`, `TrueTower.properState`, `lineTowerOf`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `pivotPair_mirror_reaches_of_ge` — `Direct.PivotCell` l.323 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : q ≥ p_min(z))
- **Énoncé** : Toute référence q ≥ p_min(z) posée sur la Tour du miroir donne p_min(z) atteint.
- **Vérités** : V99
- **Repose sur** : théorèmes : `pivotPair_reaches_of_le`, `expectedMinimumPrime_pos`; définitions/structures : `TrueZero`, `expectedMinimumPrime`, `reaches`, `mirrorMember`, `pivotPair`. Base rhv3 : aucun.
- **Entraîne** (2) : `lock_imp_pivot_lt_expected`, `pivotCell_mirror_reaches_expected`.

#### `pivotCell_mirror_reaches_expected` — `Direct.PivotCell` l.329 — CONFIRMÉE SOUS CONDITION (zéro de côté bas (β<1/2))
- **Énoncé** : Pour un zéro de côté bas, la cellule du pivot propre du miroir atteint p_min(z) (p_min(z) ≤ Occ(z*) < p_min(z*) ≤ C⁺) : avant l'inversion la Tour droite du miroir lit et la vérification est fausse.
- **Vérités** : V99, V84
- **Repose sur** : théorèmes : `pivotPair_mirror_reaches_of_ge`, `expectedMinimum_le_mirror_occurrence`, `occurrence_lt_expectedMinimumPrime`; définitions/structures : `TrueZero`, `reaches`, `mirrorMember`, `pivotCell`, `expectedMinimumPrime`, `occurrence`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `lock_imp_pivot_lt_expected` — `Direct.PivotCell` l.337 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : pivotPair du miroir à q n'atteint pas p_min(z))
- **Énoncé** : Si la pivotPair du miroir posée à q n'atteint pas p_min(z), alors q < p_min(z) (la vérification force la référence sous p_min(z)).
- **Vérités** : V84
- **Repose sur** : théorèmes : `pivotPair_mirror_reaches_of_ge`; définitions/structures : `TrueZero`, `reaches`, `mirrorMember`, `pivotPair`, `expectedMinimumPrime`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `lock_imp_counted_lt_occurrence` — `Direct.PivotCell` l.344 — CONFIRMÉE SOUS CONDITION (zéro de côté bas) (autres hypothèses : antécédents de la relation énoncée ou conditions de domaine : rang compté > 0 ; la paire n'atteint pas p_min(z))
- **Énoncé** : Pour un zéro de côté bas, si une paire de contacts du miroir à rang compté positif n'atteint pas p_min(z), sa cible constatée est sous l'occurrence du miroir.
- **Vérités** : V84
- **Repose sur** : théorèmes : `reaches_iff_le_countedPrime`, `expectedMinimumPrime_prime`, `expectedMinimum_le_mirror_occurrence`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `mirrorMember`, `countedRank`, `reaches`, `expectedMinimumPrime`, `countedPrime`, `occurrence`, `lock_imp_counted_lt_occurrence._proof_1_1`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `towerPosition_shift_abs_lt_half` — `Direct.PivotCell` l.369 — CONFIRMÉE
- **Énoncé** : Le décalage de phase entre deux Tours propres quelconques, divisé par π, est strictement borné par 1/2.
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : `towerMotion_phase_pos`, `towerMotion_phase_lt_pi_div_two`; définitions/structures : `TrueZero`, `TowerMotion.phase`, `towerMotionOf`. Base rhv3 : aucun.
- **Entraîne** (1) : `pivotCoordinate_sameHeight_shift_le_one`.

#### `pivotCoordinate_sameHeight_shift_le_one` — `Direct.PivotCell` l.381 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : q>0 ; z et w de même hauteur)
- **Énoncé** : Deux Tours de même hauteur T ont des grilles de coordonnées de pivot alignées à un anneau près (écart ≤ 1 pour toute référence q).
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : `towerPosition_shift_abs_lt_half`; définitions/structures : `TrueZero`, `pivotCoordinate`, `TowerMotion.phase`, `towerMotionOf`, `towerPosition`, `pivotCoordinate_sameHeight_shift_le_one._proof_1_1`, `pivotCoordinate_sameHeight_shift_le_one._proof_1_2`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `sameHeight_pivotCoordinate_dichotomy`.


##### Module `RHV6Fresh.Direct.Raccords` (13 théorèmes)

#### `fiberSuccessor_ordinate_eq` — `Direct.Raccords` l.61 — CONFIRMÉE SOUS CONDITION (zéro de côté bas) (autres hypothèses : antécédents de la relation énoncée ou conditions de domaine : z' consécutif à z)
- **Énoncé** : Pour un zéro de côté bas et un successeur consécutif z', T(z') = T(z) : le successeur d'un zéro hors ligne reste dans la fibre de sa hauteur.
- **Vérités** : V50, V66, V68
- **Repose sur** : théorèmes : `mirror_precedes`, `mirrorMember_ordinate`; définitions/structures : `TrueZero`, `mirrorMember`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.PZeroMembersConsecutive`, `RHV3Lean.rZeroHeight`, `RHV3Lean.PZeroMemberPrecedes`, `RHV3Lean.thm_distinctZeroMembers_comparable`, `RHV3Lean.thm_sameFiberInterposition`.
- **Entraîne** (2) : `radial_gt_of_consecutive_lowerSide`, `radial_le_mirror_of_consecutive_lowerSide`.

#### `consecutive_successor_unique` — `Direct.Raccords` l.78 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : z₁ et z₂ tous deux consécutifs à z)
- **Énoncé** : Le successeur consécutif d'un zéro est unique.
- **Vérités** : V8, V50
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`. Base rhv3 : `RHV3Lean.PZeroMembersConsecutive`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.PZeroMemberPrecedes`, `RHV3Lean.thm_distinctZeroMembers_comparable`.
- **Entraîne** (1) : `fiberSuccessor_eq_mirror_of_noInterposition`.

#### `fiberSuccessor_eq_mirror_or_precedes` — `Direct.Raccords` l.90 — CONFIRMÉE SOUS CONDITION (zéro de côté bas) (autres hypothèses : antécédents de la relation énoncée ou conditions de domaine : z' consécutif à z)
- **Énoncé** : Pour un zéro de côté bas, le successeur consécutif est le miroir ou précède strictement le miroir (dichotomie ; n'exclut pas l'interposition par elle-même).
- **Vérités** : V68, V50
- **Repose sur** : théorèmes : `mirror_precedes`; définitions/structures : `TrueZero`, `mirrorMember`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.PZeroMembersConsecutive`, `RHV3Lean.PZeroMemberPrecedes`, `RHV3Lean.thm_distinctZeroMembers_comparable`.
- **Entraîne** (0) : aucun théorème du projet.

#### `fiberSuccessor_eq_mirror_of_noInterposition` — `Direct.Raccords` l.102 — CONFIRMÉE SOUS CONDITION (zéro de côté bas) (autres hypothèses : antécédents de la relation énoncée ou conditions de domaine : z' consécutif ; aucun membre intercalé entre z et le miroir)
- **Énoncé** : Sans membre intercalé entre z et son miroir, le successeur consécutif d'un zéro de côté bas est le miroir.
- **Vérités** : V68
- **Repose sur** : théorèmes : `consecutive_successor_unique`, `mirror_precedes`; définitions/structures : `TrueZero`, `mirrorMember`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.PZeroMembersConsecutive`, `RHV3Lean.PZeroMemberPrecedes`.
- **Entraîne** (0) : aucun théorème du projet.

#### `radial_gt_of_consecutive_lowerSide` — `Direct.Raccords` l.112 — CONFIRMÉE SOUS CONDITION (zéro de côté bas) (autres hypothèses : antécédents de la relation énoncée ou conditions de domaine : z' consécutif)
- **Énoncé** : Pour un zéro de côté bas, tout successeur consécutif a une position radiale strictement supérieure.
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : `fiberSuccessor_radial_gt`, `fiberSuccessor_ordinate_eq`; définitions/structures : `TrueZero`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.PZeroMembersConsecutive`.
- **Entraîne** (0) : aucun théorème du projet.

#### `radial_le_mirror_of_consecutive_lowerSide` — `Direct.Raccords` l.119 — CONFIRMÉE SOUS CONDITION (zéro de côté bas) (autres hypothèses : antécédents de la relation énoncée ou conditions de domaine : z' consécutif)
- **Énoncé** : Pour un zéro de côté bas, tout successeur consécutif a une position radiale au plus 1−β.
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : `fiberSuccessor_radial_le_mirror`, `fiberSuccessor_ordinate_eq`; définitions/structures : `TrueZero`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.PZeroMembersConsecutive`.
- **Entraîne** (0) : aucun théorème du projet.

#### `occurrence_prime` — `Direct.Raccords` l.128 — CONFIRMÉE
- **Énoncé** : L'occurrence d'un zéro est un nombre premier.
- **Vérités** : V27
- **Repose sur** : théorèmes : `occurrence_eq_primeAtRank`; définitions/structures : `TrueZero`, `occurrence`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.thm_primeAtRank_isPrime`.
- **Entraîne** (8) : `localReading_of_riemannHypothesis`, `occurrence_pos`, `reflected_blocked_onLine`, `reflected_mirror_reads_nothing`, `sameHeight_amplitude_inverts_at_raccords`, `secondTower_reads_occurrence_iff_coordinate_lt`, `secondTower_reads_of_gap_ge_pi`, `verticalDominates_of_verticalEnergyPush`.

#### `occurrence_pos` — `Direct.Raccords` l.134 — CONFIRMÉE
- **Énoncé** : L'occurrence d'un zéro est strictement positive.
- **Vérités** : V27
- **Repose sur** : théorèmes : `occurrence_prime`; définitions/structures : `TrueZero`, `occurrence`. Base rhv3 : aucun.
- **Entraîne** (7) : `horizontalRaccords_amplitude_brackets`, `localReading_modeA`, `passage_double_constraint`, `progression_nonneg`, `reaches_occurrence_iff_readCoordinates`, `riemannHypothesis_of_energyBalance`, `succession_invariants`.

#### `nat_le_exp_div_iff` — `Direct.Raccords` l.137 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : T>0 ; p>0)
- **Énoncé** : (Lemme arithmétique) p ≤ exp(a/T) ⟺ T·log p ≤ a, pour T>0 et p>0.
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : aucun. Base rhv3 : aucun.
- **Entraîne** (1) : `reaches_iff_readCoordinates`.

#### `reaches_iff_readCoordinates` — `Direct.Raccords` l.143 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : p>0)
- **Énoncé** : Sur une paire propre, « p atteint » ⟺ T·log p ≤ φ + (k+m)π, avec k,m les lectures (coordonnée d'entrée, nombre d'étages).
- **Vérités** : V43, V52
- **Repose sur** : théorèmes : `AnalyticContactPair.lastRayContact_eq_incidence`, `nat_le_exp_div_iff`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `reaches`, `AnalyticContactPair.entryCoordinate`, `AnalyticContactPair.stageCount`, `AnalyticContactPair.lastRayContact`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rTowerPhase`, `RHV3Lean.rTowerIncidence`, `RHV3Lean.rTowerLogIncidence`, `RHV3Lean.rTowerHeight`.
- **Entraîne** (2) : `not_reaches_iff_readCoordinates`, `reaches_occurrence_iff_readCoordinates`.

#### `not_reaches_iff_readCoordinates` — `Direct.Raccords` l.156 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : p>0)
- **Énoncé** : Sur une paire propre, « p non atteint » ⟺ φ + (k+m)π < T·log p.
- **Vérités** : V43, V52
- **Repose sur** : théorèmes : `reaches_iff_readCoordinates`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `reaches`, `AnalyticContactPair.entryCoordinate`, `AnalyticContactPair.stageCount`. Base rhv3 : `RHV3Lean.rTowerPhase`, `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `reaches_occurrence_iff_readCoordinates` — `Direct.Raccords` l.165 — CONFIRMÉE
- **Énoncé** : L'occurrence est atteinte ⟺ T·log Occ ≤ φ + (k+m)π aux coordonnées lues.
- **Vérités** : V43, V52
- **Repose sur** : théorèmes : `reaches_iff_readCoordinates`, `occurrence_pos`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `reaches`, `occurrence`, `AnalyticContactPair.entryCoordinate`, `AnalyticContactPair.stageCount`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rTowerPhase`.
- **Entraîne** (0) : aucun théorème du projet.

#### `AnalyticContactPair.eq_analyticPairAt_of_one_stage` — `Direct.Raccords` l.174 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : nombre d'étages = 1)
- **Énoncé** : À un seul étage, la paire est la valeur des formules à sa coordonnée lue (analyticPairAt).
- **Vérités** : V32, V43
- **Repose sur** : théorèmes : `AnalyticContactPair.contacts_of_one_stage`, `AnalyticContactPair.ext_contacts`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.stageCount`, `analyticPairAt`, `AnalyticContactPair.entryCoordinate`, `AnalyticContactPair.entryContact`, `contactMinusAt`, `AnalyticContactPair.lastRayContact`, `contactPlusAt`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.


##### Module `RHV6Fresh.Direct.Reached` (15 théorèmes)

#### `AnalyticContactPair.cell_nonempty` — `Direct.Reached` l.34 — CONFIRMÉE
- **Énoncé** : La cellule d'un état propre (intervalle [entrée, dernier rayon]) est non vide.
- **Vérités** : V20, V26
- **Repose sur** : théorèmes : `AnalyticContactPair.ordered`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.cell`, `AnalyticContactPair.entryContact`, `AnalyticContactPair.lastRayContact`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `not_reaches_iff` — `Direct.Reached` l.40 — CONFIRMÉE
- **Énoncé** : Sur un état propre, un entier p n'est pas atteint ssi le dernier rayon est strictement sous p (« atteint » = compté jusqu'au dernier rayon).
- **Vérités** : V52, V84
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `reaches`, `AnalyticContactPair.lastRayContact`. Base rhv3 : aucun.
- **Entraîne** (2) : `not_reaches_expected_of_lastRay_lt`, `not_reaches_of_lastRay_lt`.

#### `reaches_of_le` — `Direct.Reached` l.45 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : p ≤ q ; q atteint)
- **Énoncé** : Si q est atteint par un état propre, tout p ≤ q l'est aussi.
- **Vérités** : V52
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `reaches`, `AnalyticContactPair.lastRayContact`. Base rhv3 : aucun.
- **Entraîne** (3) : `firstTower_reaches_occurrence`, `lineTower_reaches_occurrence`, `pivotPair_reaches_of_le`.

#### `reaches_of_mem_cell` — `Direct.Reached` l.49 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : p dans la cellule)
- **Énoncé** : Tout entier p situé dans la cellule d'un état propre est atteint.
- **Vérités** : V26, V52
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.cell`, `reaches`, `AnalyticContactPair.entryContact`, `AnalyticContactPair.lastRayContact`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `reaches_primeAtRank_iff` — `Direct.Reached` l.52 — CONFIRMÉE
- **Énoncé** : Dualité rang/contact : le premier de rang r est atteint ssi r est strictement sous le rang compté au dernier rayon.
- **Vérités** : V145, V52
- **Repose sur** : théorèmes : `AnalyticContactPair.lastRayContact_pos`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `reaches`, `countedRank`, `AnalyticContactPair.lastRayContact`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.nEdgePrimeRank`, `RHV3Lean.thm_edgeRank_le_iff_lt_primeAtRank`.
- **Entraîne** (4) : `pivot_countedRank_pos`, `reaches_expected_iff`, `reaches_iff_le_countedPrime`, `reaches_occurrence_iff`.

#### `reaches_iff_le_countedPrime` — `Direct.Reached` l.66 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : p premier ; rang compté > 0)
- **Énoncé** : Sur un état propre à compte positif, un premier p est atteint ssi p ≤ premier constaté (cible constatée).
- **Vérités** : V37, V52
- **Repose sur** : théorèmes : `reaches_primeAtRank_iff`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `countedRank`, `reaches`, `countedPrime`, `reaches_iff_le_countedPrime._proof_1_1`, `reaches_iff_le_countedPrime._proof_1_2`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.thm_primeAtRank_surjective_onPrimes`, `RHV3Lean.thm_primeAtRank_strictMono`.
- **Entraîne** (3) : `R1_iff_expected_le_counted`, `lock_imp_counted_lt_occurrence`, `pivot_le_counted`.

#### `reaches_occurrence_iff` — `Direct.Reached` l.87 — CONFIRMÉE
- **Énoncé** : L'occurrence de w est atteinte ssi le rang compté dépasse l'index zéro-source de w (n(w) < π(C⁺)).
- **Vérités** : V145, V49, V27
- **Repose sur** : théorèmes : `occurrence_eq_primeAtRank`, `reaches_primeAtRank_iff`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `reaches`, `occurrence`, `countedRank`. Base rhv3 : `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.fnPrimeAtRank`.
- **Entraîne** (0) : aucun théorème du projet.

#### `reaches_expected_iff` — `Direct.Reached` l.94 — CONFIRMÉE
- **Énoncé** : Le minimum attendu de w est atteint ssi n(w)+1 < π(C⁺).
- **Vérités** : V145, V54
- **Repose sur** : théorèmes : `reaches_primeAtRank_iff`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `reaches`, `expectedMinimumPrime`, `countedRank`. Base rhv3 : `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.fnPrimeSuccessor`.
- **Entraîne** (0) : aucun théorème du projet.

#### `reaches_expected_of_reaches_occurrence` — `Direct.Reached` l.100 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : z et z' consécutifs ; occurrence de z' atteinte)
- **Énoncé** : Sur un passage consécutif z→z', atteindre l'occurrence de z' c'est atteindre le minimum attendu de z (raccord de fermeture, progression compilée, aucune Tour).
- **Vérités** : V54, V56, V69
- **Repose sur** : théorèmes : `progression_occurrence`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `reaches`, `occurrence`, `expectedMinimumPrime`. Base rhv3 : `RHV3Lean.PZeroMembersConsecutive`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `verification_passes`.

#### `reaches_of_le_lastRay` — `Direct.Reached` l.109 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : p ≤ dernier rayon)
- **Énoncé** : « p ≤ C⁺ » est la lecture « atteint ».
- **Vérités** : V52
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.lastRayContact`, `reaches`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `not_reaches_of_lastRay_lt` — `Direct.Reached` l.113 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : dernier rayon < p)
- **Énoncé** : « C⁺ < p » entraîne « p non atteint » (forme négative générique, celle du constat de vérification avec p = p_min(z) sur l'état de z*).
- **Vérités** : V84, V52
- **Repose sur** : théorèmes : `not_reaches_iff`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.lastRayContact`, `reaches`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `reaches_expected_of_le_lastRay` — `Direct.Reached` l.119 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : p_min(w) ≤ dernier rayon)
- **Énoncé** : Si p_min(w) ≤ C⁺, le minimum attendu est atteint (forme exacte de la référence effective sur un état porté).
- **Vérités** : V37, V88
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `expectedMinimumPrime`, `AnalyticContactPair.lastRayContact`, `reaches`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `not_reaches_expected_of_lastRay_lt` — `Direct.Reached` l.124 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : dernier rayon < p_min(w))
- **Énoncé** : Si C⁺ < p_min(w), p_min(w) n'est pas atteint (même zéro).
- **Vérités** : V84
- **Repose sur** : théorèmes : `not_reaches_iff`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.lastRayContact`, `expectedMinimumPrime`, `reaches`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `reaches_and_not_reaches_false` — `Direct.Reached` l.130 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : hypothèses contradictoires (reaches p et ¬reaches p))
- **Énoncé** : Atteint et non atteint sur le même état est contradictoire (forme littérale logique de la fermeture).
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `reaches`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `reaches_analyticPairAt_iff` — `Direct.Reached` l.135 — CONFIRMÉE
- **Énoncé** : À la coordonnée k, « p atteint » s'écrit p ≤ C_{k+1} (contrôle de formule).
- **Vérités** : V52, V20
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `reaches`, `analyticPairAt`, `contactPlusAt`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.


##### Module `RHV6Fresh.Direct.ReadingReduction` (12 théorèmes)

#### `countedPrime_eq_occurrence_iff` — `Direct.ReadingReduction` l.25 — CONFIRMÉE
- **Énoncé** : Le premier compté sur l'état de w est l'occurrence de w ⟺ le rang compté moins un vaut l'index zéro-source.
- **Vérités** : V145, V27
- **Repose sur** : théorèmes : `occurrence_eq_primeAtRank`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `countedPrime`, `occurrence`, `countedRank`. Base rhv3 : `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.thm_primeAtRank_injective`.
- **Entraîne** (2) : `countedPrime_eq_occurrence_iff_of_lt_two`, `countedPrime_eq_occurrence_iff_rank_succ`.

#### `countedPrime_eq_expected_iff` — `Direct.ReadingReduction` l.31 — CONFIRMÉE
- **Énoncé** : Le premier compté est le minimum attendu ⟺ rang compté − 1 = index + 1.
- **Vérités** : V145, V54
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `countedPrime`, `expectedMinimumPrime`, `countedRank`. Base rhv3 : `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.fnPrimeSuccessor`, `RHV3Lean.thm_primeAtRank_injective`.
- **Entraîne** (1) : `countedPrime_eq_expected_iff_rank_succ`.

#### `countedRank_eq_zero_iff` — `Direct.ReadingReduction` l.39 — CONFIRMÉE
- **Énoncé** : Le rang compté est nul ⟺ le dernier rayon est < 2.
- **Vérités** : V52
- **Repose sur** : théorèmes : `AnalyticContactPair.lastRayContact_pos`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `countedRank`, `AnalyticContactPair.lastRayContact`. Base rhv3 : `RHV3Lean.nEdgePrimeRank`, `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.thm_edgeRank_le_iff_lt_primeAtRank`, `RHV3Lean.thm_primeAtRank_zero_eq_two`.
- **Entraîne** (2) : `countedPrime_eq_occurrence_iff_of_lt_two`, `one_le_countedRank_of_two_le`.

#### `one_le_countedRank_of_two_le` — `Direct.ReadingReduction` l.47 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : dernier rayon ≥ 2)
- **Énoncé** : Si le dernier rayon est ≥ 2, le rang compté est ≥ 1.
- **Vérités** : V52
- **Repose sur** : théorèmes : `countedRank_eq_zero_iff`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.lastRayContact`, `countedRank`, `one_le_countedRank_of_two_le._proof_1_1`. Base rhv3 : aucun.
- **Entraîne** (2) : `countedPrime_eq_expected_iff_rank_succ`, `countedPrime_eq_occurrence_iff_rank_succ`.

#### `countedPrime_eq_occurrence_iff_rank_succ` — `Direct.ReadingReduction` l.53 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : dernier rayon ≥ 2)
- **Énoncé** : Pour un dernier rayon ≥ 2, premier compté = occurrence ⟺ rang compté = index + 1.
- **Vérités** : V145, V27
- **Repose sur** : théorèmes : `countedPrime_eq_occurrence_iff`, `one_le_countedRank_of_two_le`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.lastRayContact`, `countedPrime`, `occurrence`, `countedRank`, `countedPrime_eq_occurrence_iff_rank_succ._proof_1_1`. Base rhv3 : `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `countedPrime_eq_occurrence_iff_cell`.

#### `countedPrime_eq_expected_iff_rank_succ` — `Direct.ReadingReduction` l.60 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : dernier rayon ≥ 2)
- **Énoncé** : Pour un dernier rayon ≥ 2, premier compté = minimum attendu ⟺ rang compté = index + 2.
- **Vérités** : V145, V54
- **Repose sur** : théorèmes : `countedPrime_eq_expected_iff`, `one_le_countedRank_of_two_le`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.lastRayContact`, `countedPrime`, `expectedMinimumPrime`, `countedRank`, `countedPrime_eq_expected_iff_rank_succ._proof_1_1`. Base rhv3 : `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `countedPrime_eq_occurrence_iff_of_lt_two` — `Direct.ReadingReduction` l.67 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : dernier rayon < 2)
- **Énoncé** : Pour un dernier rayon < 2, le premier compté est l'occurrence ⟺ l'index zéro-source est nul.
- **Vérités** : V52
- **Repose sur** : théorèmes : `countedPrime_eq_occurrence_iff`, `countedRank_eq_zero_iff`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.lastRayContact`, `countedPrime`, `occurrence`, `countedRank`. Base rhv3 : `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `countedRank_eq_succ_iff` — `Direct.ReadingReduction` l.74 — CONFIRMÉE
- **Énoncé** : Dualité rang/contact : rang compté = n+1 ⟺ p_n ≤ C⁺ < p_{n+1}.
- **Vérités** : V145, V52
- **Repose sur** : théorèmes : `AnalyticContactPair.lastRayContact_pos`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `countedRank`, `AnalyticContactPair.lastRayContact`, `countedRank_eq_succ_iff._proof_1_1`, `countedRank_eq_succ_iff._proof_1_2`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.nEdgePrimeRank`, `RHV3Lean.thm_edgeRank_le_iff_lt_primeAtRank`.
- **Entraîne** (1) : `countedPrime_eq_occurrence_iff_cell`.

#### `countedPrime_eq_occurrence_iff_cell` — `Direct.ReadingReduction` l.95 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : dernier rayon ≥ 2)
- **Énoncé** : C_lecture en forme cellule : premier compté = occurrence ⟺ Occ(w) ≤ C⁺ < p_min(w).
- **Vérités** : V85, V145
- **Repose sur** : théorèmes : `countedPrime_eq_occurrence_iff_rank_succ`, `countedRank_eq_succ_iff`, `occurrence_eq_primeAtRank`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.lastRayContact`, `countedPrime`, `occurrence`, `expectedMinimumPrime`, `countedRank`. Base rhv3 : `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.fnPrimeAtRank`.
- **Entraîne** (1) : `countedPrime_ne_expected_iff_cell`.

#### `countedPrime_ne_expected_iff_cell` — `Direct.ReadingReduction` l.105 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : z,z' consécutifs ; dernier rayon ≥ 2)
- **Énoncé** : Forme cellule du constat de vérification au successeur z' de z : premier compté ≠ p_min(z) ⟺ C⁺(S') hors de [Occ(z'), p_min(z')).
- **Vérités** : V84, V145
- **Repose sur** : théorèmes : `progression_occurrence`, `countedPrime_eq_occurrence_iff_cell`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.lastRayContact`, `countedPrime`, `expectedMinimumPrime`, `occurrence`. Base rhv3 : `RHV3Lean.PZeroMembersConsecutive`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `reads_expected_imp_not_occurrence` — `Direct.ReadingReduction` l.118 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : l'état lit le minimum attendu de w)
- **Énoncé** : Un état qui lit le minimum attendu de w ne lit pas l'occurrence de w.
- **Vérités** : V85
- **Repose sur** : théorèmes : `occurrence_lt_expectedMinimumPrime`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `countedPrime`, `expectedMinimumPrime`, `occurrence`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `reads_expected_imp_ne_previous_expected` — `Direct.ReadingReduction` l.124 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : z,z' consécutifs ; l'état de z' lit p_min(z'))
- **Énoncé** : Si l'état de z' lit son propre minimum attendu, alors il ne lit pas p_min(z) sur un passage consécutif z→z'.
- **Vérités** : V84, V85
- **Repose sur** : théorèmes : `progression_occurrence`, `occurrence_lt_expectedMinimumPrime`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `countedPrime`, `expectedMinimumPrime`, `occurrence`. Base rhv3 : `RHV3Lean.PZeroMembersConsecutive`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.


##### Module `RHV6Fresh.Direct.StateCount` (10 théorèmes)

#### `countedRank_eq_vonMangoldt` — `Direct.StateCount` l.35 — CONFIRMÉE
- **Énoncé** : Le rang compté d'un état propre est le comptage Chebyshev/Von Mangoldt évalué au dernier rayon.
- **Vérités** : V145, V48
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `countedRank`, `AnalyticContactPair.lastRayContact`. Base rhv3 : `RHV3Lean.nPrimeCountingFromJ`, `RHV3Lean.rChebyshevJNat`, `RHV3Lean.nEdgePrimeRank`, `RHV3Lean.thm_edgePrimeRank_eq_primeCountingFromJ`.
- **Entraîne** (1) : `countedPrime_eq_vonMangoldt`.

#### `countedPrime_eq_vonMangoldt` — `Direct.StateCount` l.40 — CONFIRMÉE
- **Énoncé** : Le premier compté d'un état propre est le premier de rang π(⌊dernier rayon⌋)−1 (Chebyshev/Von Mangoldt).
- **Vérités** : V145, V48
- **Repose sur** : théorèmes : `countedRank_eq_vonMangoldt`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `countedPrime`, `AnalyticContactPair.lastRayContact`, `countedRank`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.nPrimeCountingFromJ`, `RHV3Lean.rChebyshevJNat`.
- **Entraîne** (0) : aucun théorème du projet.

#### `countedPrime_prime` — `Direct.StateCount` l.46 — CONFIRMÉE
- **Énoncé** : Le premier compté d'un état propre est un nombre premier.
- **Vérités** : V145, V52
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `countedPrime`, `countedRank`. Base rhv3 : `RHV3Lean.thm_primeAtRank_isPrime`.
- **Entraîne** (0) : aucun théorème du projet.

#### `lastRayContact_eq_contactPlusAt` — `Direct.StateCount` l.50 — CONFIRMÉE
- **Énoncé** : Le dernier rayon d'un état propre est le contact supérieur à la coordonnée k+m−1.
- **Vérités** : V20, V43
- **Repose sur** : théorèmes : `AnalyticContactPair.lastRayContact_eq_incidence`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.lastRayContact`, `contactPlusAt`, `AnalyticContactPair.entryCoordinate`, `AnalyticContactPair.stageCount`, `TowerMotion.incidence`, `towerMotionOf`. Base rhv3 : `RHV3Lean.rTowerIncidence`.
- **Entraîne** (4) : `countedPrime_eq_countedPrimeAt_lastRay`, `countedPrime_le_lastRay`, `countedPrime_lt_expected_of_lastRay`, `countedRank_eq_countedRankAt_lastRay`.

#### `countedPrime_eq_countedPrimeAt_lastRay` — `Direct.StateCount` l.59 — CONFIRMÉE
- **Énoncé** : Le premier compté d'un état est le premier constaté indexé à la coordonnée du dernier rayon (k+m−1).
- **Vérités** : V145, V52
- **Repose sur** : théorèmes : `lastRayContact_eq_contactPlusAt`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `countedPrime`, `countedPrimeAt`, `AnalyticContactPair.entryCoordinate`, `AnalyticContactPair.stageCount`, `countedRank`, `AnalyticContactPair.lastRayContact`, `contactPlusAt`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.nEdgePrimeRank`.
- **Entraîne** (3) : `countedPrime_le_lastRay`, `countedPrime_lt_expected_of_lastRay`, `countedPrime_of_one_stage`.

#### `countedRank_eq_countedRankAt_lastRay` — `Direct.StateCount` l.66 — CONFIRMÉE
- **Énoncé** : Le rang compté d'un état est le rang constaté indexé à la coordonnée du dernier rayon.
- **Vérités** : V145, V52
- **Repose sur** : théorèmes : `lastRayContact_eq_contactPlusAt`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `countedRank`, `countedRankAt`, `AnalyticContactPair.entryCoordinate`, `AnalyticContactPair.stageCount`, `AnalyticContactPair.lastRayContact`, `contactPlusAt`. Base rhv3 : `RHV3Lean.nEdgePrimeRank`.
- **Entraîne** (1) : `countedPrime_le_lastRay`.

#### `countedPrime_of_one_stage` — `Direct.StateCount` l.72 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : nombre d'étages = 1)
- **Énoncé** : À un seul étage, le premier compté est le premier constaté à la coordonnée d'entrée.
- **Vérités** : V145, V32
- **Repose sur** : théorèmes : `countedPrime_eq_countedPrimeAt_lastRay`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.stageCount`, `countedPrime`, `countedPrimeAt`, `AnalyticContactPair.entryCoordinate`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `countedPrime_analyticPairAt` — `Direct.StateCount` l.80 — CONFIRMÉE
- **Énoncé** : Le premier compté de la paire consécutive en k est le premier constaté indexé en k.
- **Vérités** : V145
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `countedPrime`, `analyticPairAt`, `countedPrimeAt`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `countedPrime_lt_expected_of_lastRay` — `Direct.StateCount` l.84 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : dernier rayon < p_min(a))
- **Énoncé** : Si le dernier rayon est sous p_min(a), le premier compté est sous p_min(a).
- **Vérités** : V84, V52
- **Repose sur** : théorèmes : `countedPrime_eq_countedPrimeAt_lastRay`, `countedPrimeAt_lt_expected_of_contact`, `lastRayContact_eq_contactPlusAt`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.lastRayContact`, `expectedMinimumPrime`, `countedPrime`, `countedPrimeAt`, `AnalyticContactPair.entryCoordinate`, `AnalyticContactPair.stageCount`, `contactPlusAt`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `countedPrime_le_lastRay` — `Direct.StateCount` l.95 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : rang compté > 0)
- **Énoncé** : Le premier compté est au plus le dernier rayon (comptage inclusif).
- **Vérités** : V52
- **Repose sur** : théorèmes : `lastPrimeAtStateUpper_le_contact`, `countedRank_eq_countedRankAt_lastRay`, `contactPlusAt_positive`, `countedPrime_eq_countedPrimeAt_lastRay`, `lastRayContact_eq_contactPlusAt`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `countedRank`, `countedPrime`, `AnalyticContactPair.lastRayContact`, `lastPrimeAtStateUpper`, `towerStateAt`, `AnalyticContactPair.entryCoordinate`, `AnalyticContactPair.stageCount`, `countedRankAt`, `countedPrimeAt`, `contactPlusAt`. Base rhv3 : `RHV3Lean.TTrueHarmonicTowerState.contactPlus`.
- **Entraîne** (0) : aucun théorème du projet.


##### Module `RHV6Fresh.Foundation.ZetaReflect` (42 théorèmes)

#### `isNontrivialZero_iff` — `Foundation.ZetaReflect` l.58 — CONFIRMÉE
- **Énoncé** : Un vrai zéro (prédicat de la base) se lit exactement : ζ(ρ)=0 avec 0<β<1 ; la définition zeta23 du zéro non trivial est celle de la base.
- **Vérités** : V7, V2, V12
- **Repose sur** : théorèmes : aucun. Base rhv3 : `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `zeroMult_eq_toNat_multiplicity` — `Foundation.ZetaReflect` l.66 — CONFIRMÉE
- **Énoncé** : La multiplicité zeta23 du support d'un vrai zéro est la multiplicité analytique de la base (convertie en entier naturel).
- **Vérités** : V12
- **Repose sur** : théorèmes : aucun; définitions/structures : `zeroMult`. Base rhv3 : `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.cZeroSupport`, `RHV3Lean.nZeroMultiplicity`.
- **Entraîne** (0) : aucun théorème du projet.

#### `zetaReflect_eq_mirrorSupport` — `Foundation.ZetaReflect` l.72 — CONFIRMÉE
- **Énoncé** : Le support du miroir de la base est exactement la réflexion zeta23 (ρ ↦ 1−ρ̄) du support du zéro.
- **Vérités** : V65, V62, V12
- **Repose sur** : théorèmes : aucun; définitions/structures : `zetaReflect`. Base rhv3 : `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.cZeroSupport`, `RHV3Lean.cMirrorSupport`.
- **Entraîne** (0) : aucun théorème du projet.

#### `zetaReflect_re` — `Foundation.ZetaReflect` l.76 — CONFIRMÉE
- **Énoncé** : Le miroir fonctionnel a pour partie réelle 1−β.
- **Vérités** : V65
- **Repose sur** : théorèmes : aucun; définitions/structures : `zetaReflect`. Base rhv3 : aucun.
- **Entraîne** (6) : `radialOffset_eq_zero_iff_reflect_fixed`, `weilPairTerm_off_neg`, `weilPairTerm_test_eq`, `zetaReflect_centeredPoint`, `zetaReflect_eq_self_iff`, `zeta_reflect_zero`.

#### `zetaReflect_im` — `Foundation.ZetaReflect` l.79 — CONFIRMÉE
- **Énoncé** : Le miroir fonctionnel a la même partie imaginaire T que le zéro.
- **Vérités** : V65
- **Repose sur** : théorèmes : aucun; définitions/structures : `zetaReflect`. Base rhv3 : aucun.
- **Entraîne** (5) : `radialOffset_eq_zero_iff_reflect_fixed`, `weilPairTerm_off_neg`, `weilPairTerm_test_eq`, `zetaReflect_centeredPoint`, `zetaReflect_eq_self_iff`.

#### `tendsto_conj_nhds` — `Foundation.ZetaReflect` l.84 — CONFIRMÉE (privé)
- **Énoncé** : (Lemme technique privé) la conjugaison envoie un voisinage de conj w vers w, continuité pour la limite.
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : aucun. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `analyticAt_conj_conj` — `Foundation.ZetaReflect` l.89 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : f analytique en w) (privé)
- **Énoncé** : (Lemme technique privé) si f est analytique en w, z ↦ conj(f(conj z)) l'est en conj w.
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : aucun; définitions/structures : `_private.RHV6Fresh.Foundation.ZetaReflect.0.RHV6Fresh.tendsto_conj_nhds`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `analyticOrderAt_conj_conj` — `Foundation.ZetaReflect` l.97 — CONFIRMÉE
- **Énoncé** : L'ordre d'annulation de z ↦ conj(f(conj z)) en conj w est celui de f en w.
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : aucun; définitions/structures : `_private.RHV6Fresh.Foundation.ZetaReflect.0.RHV6Fresh.tendsto_conj_nhds`, `_private.RHV6Fresh.Foundation.ZetaReflect.0.RHV6Fresh.analyticAt_conj_conj`. Base rhv3 : aucun.
- **Entraîne** (1) : `analyticOrderAt_zeta_conj`.

#### `analyticOrderAt_zeta_conj` — `Foundation.ZetaReflect` l.125 — CONFIRMÉE
- **Énoncé** : L'ordre d'annulation de zêta en w̄ est celui en w (multiplicité symétrique par conjugaison).
- **Vérités** : V63, V12
- **Repose sur** : théorèmes : `analyticOrderAt_conj_conj`. Base rhv3 : aucun.
- **Entraîne** (2) : `analyticOrderAt_zeta_reflect`, `zeta_mult_functionalReflect`.

#### `two_pi_ne_zero'` — `Foundation.ZetaReflect` l.145 — CONFIRMÉE (privé)
- **Énoncé** : (Lemme technique privé) 2π ≠ 0.
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : aucun; définitions/structures : `_private.RHV6Fresh.Foundation.ZetaReflect.0.RHV6Fresh.two_pi_ne_zero'._simp_1_1`, `_private.RHV6Fresh.Foundation.ZetaReflect.0.RHV6Fresh.two_pi_ne_zero'._simp_1_2`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `Efac_ne_zero` — `Foundation.ZetaReflect` l.149 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : 0<Re s<1) (privé)
- **Énoncé** : (Lemme technique privé) le facteur auxiliaire de l'équation fonctionnelle ne s'annule pas dans la bande ouverte.
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : aucun; définitions/structures : `_private.RHV6Fresh.Foundation.ZetaReflect.0.RHV6Fresh.Efac`, `_private.RHV6Fresh.Foundation.ZetaReflect.0.RHV6Fresh.two_pi_ne_zero'`, `_private.RHV6Fresh.Foundation.ZetaReflect.0.RHV6Fresh.Efac_ne_zero._proof_1_1`, `_private.RHV6Fresh.Foundation.ZetaReflect.0.RHV6Fresh.Efac._proof_1`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `analyticAt_Efac` — `Foundation.ZetaReflect` l.178 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : Re s>0) (privé)
- **Énoncé** : (Lemme technique privé) le facteur auxiliaire de l'équation fonctionnelle est analytique pour Re s>0.
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : aucun; définitions/structures : `_private.RHV6Fresh.Foundation.ZetaReflect.0.RHV6Fresh.Efac`, `_private.RHV6Fresh.Foundation.ZetaReflect.0.RHV6Fresh.two_pi_ne_zero'`, `_private.RHV6Fresh.Foundation.ZetaReflect.0.RHV6Fresh.Efac._proof_1`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `analyticOrderAt_zeta_one_sub` — `Foundation.ZetaReflect` l.201 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : w dans la bande ouverte 0<Re w<1)
- **Énoncé** : Transport de multiplicité par l'équation fonctionnelle : dans la bande ouverte, l'ordre de zêta en 1−w égale celui en w.
- **Vérités** : V63, V12
- **Repose sur** : théorèmes : aucun; définitions/structures : `_private.RHV6Fresh.Foundation.ZetaReflect.0.RHV6Fresh.Efac`, `_private.RHV6Fresh.Foundation.ZetaReflect.0.RHV6Fresh.Efac._proof_1`, `_private.RHV6Fresh.Foundation.ZetaReflect.0.RHV6Fresh.analyticAt_Efac`, `_private.RHV6Fresh.Foundation.ZetaReflect.0.RHV6Fresh.Efac_ne_zero`. Base rhv3 : aucun.
- **Entraîne** (1) : `analyticOrderAt_zeta_reflect`.

#### `zeta_reflect_zero` — `Foundation.ZetaReflect` l.256 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : ρ vrai zéro)
- **Énoncé** : La réflexion ρ ↦ 1−ρ̄ envoie un vrai zéro sur un vrai zéro (le miroir d'un zéro est un zéro).
- **Vérités** : V62, V63, V74
- **Repose sur** : théorèmes : `zetaReflect_re`; définitions/structures : `zetaReflect`. Base rhv3 : `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `zeta_functionalReflect_zero`.

#### `analyticOrderAt_zeta_reflect` — `Foundation.ZetaReflect` l.281 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : ρ dans la bande ouverte)
- **Énoncé** : L'ordre d'annulation de zêta en 1−ρ̄ égale celui en ρ (bande ouverte).
- **Vérités** : V63, V65
- **Repose sur** : théorèmes : `analyticOrderAt_zeta_conj`, `analyticOrderAt_zeta_one_sub`; définitions/structures : `zetaReflect`. Base rhv3 : aucun.
- **Entraîne** (3) : `mirror_multiplicity`, `zeta_mult_functionalReflect`, `zeta_mult_reflect`.

#### `zeta_mult_reflect` — `Foundation.ZetaReflect` l.289 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : ρ vrai zéro)
- **Énoncé** : La multiplicité (zeta23) du miroir 1−ρ̄ égale celle de ρ.
- **Vérités** : V63, V65, V12
- **Repose sur** : théorèmes : `analyticOrderAt_zeta_reflect`; définitions/structures : `zeroMult`, `zetaReflect`. Base rhv3 : `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `mirror_multiplicity` — `Foundation.ZetaReflect` l.297 — CONFIRMÉE
- **Énoncé** : Le miroir de la base conserve la multiplicité analytique du zéro.
- **Vérités** : V65, V63
- **Repose sur** : théorèmes : `analyticOrderAt_zeta_reflect`. Base rhv3 : `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.nZeroMultiplicity`, `RHV3Lean.zMirrorZero`, `RHV3Lean.cZeroSupport`, `RHV3Lean.thm_zeroRadialPosition_positive`, `RHV3Lean.thm_zeroRadialPosition_lt_one`.
- **Entraîne** (1) : `upperMirror_multiplicity`.

#### `upperMirror_multiplicity` — `Foundation.ZetaReflect` l.303 — CONFIRMÉE
- **Énoncé** : Idem sur la branche supérieure (T>0) : le miroir supérieur a la même multiplicité.
- **Vérités** : V65, V63
- **Repose sur** : théorèmes : `mirror_multiplicity`. Base rhv3 : `RHV3Lean.TUpperNonTrivialZetaZero`, `RHV3Lean.nZeroMultiplicity`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.zUpperMirrorZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `upperMirror_support_eq_reflect` — `Foundation.ZetaReflect` l.308 — CONFIRMÉE
- **Énoncé** : Le support du miroir supérieur est la réflexion zeta23 du support du zéro.
- **Vérités** : V65, V62
- **Repose sur** : théorèmes : aucun; définitions/structures : `zetaReflect`. Base rhv3 : `RHV3Lean.TUpperNonTrivialZetaZero`, `RHV3Lean.cZeroSupport`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.zUpperMirrorZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `riemannZeta_analyticOnNhd_compl_one` — `Foundation.ZetaReflect` l.314 — CONFIRMÉE
- **Énoncé** : Zêta est analytique sur ℂ privé de 1.
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : aucun. Base rhv3 : aucun.
- **Entraîne** (3) : `analyticOrderAt_riemannZeta_ne_top`, `one_le_zeroMult`, `riemannZeta_zeros_locallyFinite`.

#### `isConnected_compl_one` — `Foundation.ZetaReflect` l.320 — CONFIRMÉE
- **Énoncé** : ℂ privé de 1 est connexe.
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : aucun. Base rhv3 : aucun.
- **Entraîne** (2) : `analyticOrderAt_riemannZeta_ne_top`, `riemannZeta_zeros_locallyFinite`.

#### `analyticOrderAt_riemannZeta_ne_top` — `Foundation.ZetaReflect` l.324 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : s≠1)
- **Énoncé** : En tout s≠1, l'ordre d'annulation de zêta est fini (zêta n'est nulle sur aucun voisinage).
- **Vérités** : V7
- **Repose sur** : théorèmes : `riemannZeta_analyticOnNhd_compl_one`, `isConnected_compl_one`. Base rhv3 : aucun.
- **Entraîne** (2) : `multiplicity_ne_top`, `one_le_zeroMult`.

#### `multiplicity_ne_top` — `Foundation.ZetaReflect` l.334 — CONFIRMÉE
- **Énoncé** : La multiplicité d'un vrai zéro est finie.
- **Vérités** : V7, V12
- **Repose sur** : théorèmes : `analyticOrderAt_riemannZeta_ne_top`. Base rhv3 : `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.nZeroMultiplicity`, `RHV3Lean.cZeroSupport`, `RHV3Lean.thm_zeroSupport_ne_pole`.
- **Entraîne** (0) : aucun théorème du projet.

#### `one_le_zeroMult` — `Foundation.ZetaReflect` l.338 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : ρ vrai zéro)
- **Énoncé** : Tout vrai zéro (zeta23) a multiplicité au moins 1.
- **Vérités** : V12
- **Repose sur** : théorèmes : `riemannZeta_analyticOnNhd_compl_one`, `analyticOrderAt_riemannZeta_ne_top`; définitions/structures : `zeroMult`, `one_le_zeroMult._proof_1_2`, `one_le_zeroMult._simp_1_1`. Base rhv3 : `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `riemannZeta_zeros_locallyFinite` — `Foundation.ZetaReflect` l.354 — CONFIRMÉE
- **Énoncé** : Les zéros de zêta (hors du pôle) sont localement finis dans ℂ.
- **Vérités** : V12
- **Repose sur** : théorèmes : `riemannZeta_analyticOnNhd_compl_one`, `isConnected_compl_one`. Base rhv3 : aucun.
- **Entraîne** (1) : `zeta_window_finite`.

#### `zeta_window_finite` — `Foundation.ZetaReflect` l.382 — CONFIRMÉE
- **Énoncé** : Il n'y a qu'un nombre fini de vrais zéros d'ordonnée dans une fenêtre (T₁,T₂] (fenêtres finies d'ordonnées).
- **Vérités** : V12, V50
- **Repose sur** : théorèmes : `riemannZeta_zeros_locallyFinite`. Base rhv3 : `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `ZeroConfig.one_le_mult` — `Foundation.ZetaReflect` l.412 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : ρ dans le support de la configuration)
- **Énoncé** : (Champ de structure ZeroConfig) toute multiplicité d'un point de la configuration est ≥1.
- **Vérités** : V12
- **Repose sur** : théorèmes : aucun; définitions/structures : `ZeroConfig`, `ZeroConfig.carrier`, `ZeroConfig.mult`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `ZeroConfig.strip` — `Foundation.ZetaReflect` l.413 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : ρ dans le support de la configuration)
- **Énoncé** : (Champ de structure ZeroConfig) tout point de la configuration est dans la bande fermée 0≤Re≤1.
- **Vérités** : V12
- **Repose sur** : théorèmes : aucun; définitions/structures : `ZeroConfig`, `ZeroConfig.carrier`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `ZeroConfig.reflect_mem` — `Foundation.ZetaReflect` l.414 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : ρ dans le support de la configuration)
- **Énoncé** : (Champ de structure ZeroConfig) la configuration est stable par la réflexion 1−ρ̄.
- **Vérités** : V12, V63
- **Repose sur** : théorèmes : aucun; définitions/structures : `ZeroConfig`, `ZeroConfig.carrier`, `zetaReflect`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `ZeroConfig.mult_reflect` — `Foundation.ZetaReflect` l.415 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : ρ dans le support de la configuration)
- **Énoncé** : (Champ de structure ZeroConfig) la multiplicité est invariante par la réflexion 1−ρ̄.
- **Vérités** : V12, V63
- **Repose sur** : théorèmes : aucun; définitions/structures : `ZeroConfig`, `ZeroConfig.carrier`, `ZeroConfig.mult`, `zetaReflect`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `ZeroConfig.finite_window` — `Foundation.ZetaReflect` l.416 — CONFIRMÉE
- **Énoncé** : (Champ de structure ZeroConfig) toute fenêtre finie d'ordonnées ne contient qu'un nombre fini de points de la configuration.
- **Vérités** : V12
- **Repose sur** : théorèmes : aucun; définitions/structures : `ZeroConfig`, `ZeroConfig.carrier`. Base rhv3 : aucun.
- **Entraîne** (1) : `zeroSideWindow_nonneg_of_onLine`.

#### `zetaZeroConfig_carrier` — `Foundation.ZetaReflect` l.429 — CONFIRMÉE
- **Énoncé** : Le support de la configuration portée zeta est exactement l'ensemble des vrais zéros de la base.
- **Vérités** : V12, V7
- **Repose sur** : théorèmes : aucun; définitions/structures : `ZeroConfig.carrier`, `zetaZeroConfig`. Base rhv3 : `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `allNontrivial_onLine_iff_riemannHypothesis`.

#### `zetaZeroConfig_mult` — `Foundation.ZetaReflect` l.432 — CONFIRMÉE
- **Énoncé** : La multiplicité de la configuration portée est la multiplicité zeta23 des zéros.
- **Vérités** : V12
- **Repose sur** : théorèmes : aucun; définitions/structures : `ZeroConfig.mult`, `zetaZeroConfig`, `zeroMult`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `zeroSupport_mem_zetaZeroConfig` — `Foundation.ZetaReflect` l.434 — CONFIRMÉE
- **Énoncé** : Tout vrai zéro de la base est un point de la configuration portée.
- **Vérités** : V12
- **Repose sur** : théorèmes : aucun; définitions/structures : `ZeroConfig.carrier`, `zetaZeroConfig`. Base rhv3 : `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.cZeroSupport`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `zetaFunctionalReflect_eq_conj_reflect` — `Foundation.ZetaReflect` l.449 — CONFIRMÉE
- **Énoncé** : Le zéro réfléchi (1−ρ) est le conjugué du miroir (1−ρ̄).
- **Vérités** : V63, V80
- **Repose sur** : théorèmes : aucun; définitions/structures : `zetaFunctionalReflect`, `zetaReflect`. Base rhv3 : aucun.
- **Entraîne** (3) : `functionalReflect_support_eq_conj_mirror`, `zeta_functionalReflect_zero`, `zeta_mult_functionalReflect`.

#### `zetaFunctionalReflect_re` — `Foundation.ZetaReflect` l.455 — CONFIRMÉE
- **Énoncé** : Le zéro réfléchi 1−ρ a pour partie réelle 1−β.
- **Vérités** : V63, V80
- **Repose sur** : théorèmes : aucun; définitions/structures : `zetaFunctionalReflect`. Base rhv3 : aucun.
- **Entraîne** (1) : `zeta_functionalReflect_zero`.

#### `zetaFunctionalReflect_im` — `Foundation.ZetaReflect` l.458 — CONFIRMÉE
- **Énoncé** : Le zéro réfléchi 1−ρ a pour partie imaginaire −T.
- **Vérités** : V63, V80
- **Repose sur** : théorèmes : aucun; définitions/structures : `zetaFunctionalReflect`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `zeta_functionalReflect_zero` — `Foundation.ZetaReflect` l.461 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : ρ vrai zéro)
- **Énoncé** : La réflexion ρ ↦ 1−ρ envoie un vrai zéro sur un vrai zéro (équation fonctionnelle et conjugaison) : le zéro réfléchi est un zéro.
- **Vérités** : V63, V62
- **Repose sur** : théorèmes : `zeta_reflect_zero`, `zetaFunctionalReflect_eq_conj_reflect`, `zetaFunctionalReflect_re`; définitions/structures : `zetaFunctionalReflect`, `zetaReflect`. Base rhv3 : `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `reflectedZero_isZero`.

#### `zeta_mult_functionalReflect` — `Foundation.ZetaReflect` l.474 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : ρ vrai zéro)
- **Énoncé** : Le zéro réfléchi 1−ρ conserve la multiplicité.
- **Vérités** : V63, V12
- **Repose sur** : théorèmes : `zetaFunctionalReflect_eq_conj_reflect`, `analyticOrderAt_zeta_conj`, `analyticOrderAt_zeta_reflect`; définitions/structures : `zeroMult`, `zetaFunctionalReflect`, `zetaReflect`. Base rhv3 : `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `functionalReflect_support_eq_conj_mirror` — `Foundation.ZetaReflect` l.481 — CONFIRMÉE
- **Énoncé** : Le zéro réfléchi de z est le conjugué du support du miroir supérieur de z.
- **Vérités** : V63, V80
- **Repose sur** : théorèmes : `zetaFunctionalReflect_eq_conj_reflect`; définitions/structures : `zetaFunctionalReflect`, `zetaReflect`. Base rhv3 : `RHV3Lean.TUpperNonTrivialZetaZero`, `RHV3Lean.cZeroSupport`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.zUpperMirrorZero`.
- **Entraîne** (3) : `functionalReflect_im_eq_neg_mirror`, `functionalReflect_re_eq_mirror`, `reflectedZero_support`.

#### `functionalReflect_re_eq_mirror` — `Foundation.ZetaReflect` l.487 — CONFIRMÉE
- **Énoncé** : La partie réelle du zéro réfléchi est la position radiale (1−β) du miroir supérieur.
- **Vérités** : V80, V65
- **Repose sur** : théorèmes : `functionalReflect_support_eq_conj_mirror`; définitions/structures : `zetaFunctionalReflect`. Base rhv3 : `RHV3Lean.TUpperNonTrivialZetaZero`, `RHV3Lean.cZeroSupport`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.zUpperMirrorZero`.
- **Entraîne** (1) : `reflectedZero_re`.

#### `functionalReflect_im_eq_neg_mirror` — `Foundation.ZetaReflect` l.493 — CONFIRMÉE
- **Énoncé** : La partie imaginaire du zéro réfléchi est l'opposé de la hauteur du miroir supérieur (−T).
- **Vérités** : V80, V63
- **Repose sur** : théorèmes : `functionalReflect_support_eq_conj_mirror`; définitions/structures : `zetaFunctionalReflect`. Base rhv3 : `RHV3Lean.TUpperNonTrivialZetaZero`, `RHV3Lean.cZeroSupport`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroHeight`, `RHV3Lean.zUpperMirrorZero`.
- **Entraîne** (1) : `reflectedZero_im`.


##### Module `RHV6Fresh.Grammar.ExpectedMinimum` (6 théorèmes)

#### `expectedMinimumPrime_prime` — `Grammar.ExpectedMinimum` l.17 — CONFIRMÉE
- **Énoncé** : Le minimum attendu d'un zéro est un nombre premier.
- **Vérités** : V54
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `expectedMinimumPrime`. Base rhv3 : `RHV3Lean.fnPrimeSuccessor`, `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.thm_primeAtRank_isPrime`.
- **Entraîne** (10) : `R1_iff_expected_le_counted`, `expectedMinimumPrime_pos`, `expected_le_counted`, `lineTower_expected_le_counted`, `lock_imp_counted_lt_occurrence`, `reflectedFromOrigin_never_reaches_expectedMinimum`, `sameHeight_amplitude_inverts_at_raccords`, `secondTower_cell_contains_own_expected`, `secondTower_not_reaches_own_expected`, `verticalDominates_of_verticalEnergyPush`.

#### `occurrence_lt_expectedMinimumPrime` — `Grammar.ExpectedMinimum` l.22 — CONFIRMÉE
- **Énoncé** : L'occurrence d'un zéro est strictement inférieure à son minimum attendu.
- **Vérités** : V54, V38
- **Repose sur** : théorèmes : `occurrence_eq_canonicalAnchor`; définitions/structures : `TrueZero`, `occurrence`, `expectedMinimumPrime`. Base rhv3 : `RHV3Lean.nMemberCanonicalAnchor`, `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.fnPrimeSuccessor`, `RHV3Lean.thm_primeAtRank_lt_successor`.
- **Entraîne** (12) : `consecutivePairArithmeticChain`, `expectedMinimumPrime_succ_of_passage`, `expectedMinimum_lt_mirror_expectedMinimum`, `firstTower_reaches_occurrence`, `lineTower_reaches_occurrence`, `pivotCell_mirror_reaches_expected`, `progression_nonneg`, `reads_expected_imp_ne_previous_expected`, `reads_expected_imp_not_occurrence`, `riemannHypothesis_of_energyBalance`, `secondTower_entry_reaches_mirror_occurrence`, `upright_presents_forward`.

#### `expectedMinimumPrime_eq_laterOccurrence` — `Grammar.ExpectedMinimum` l.28 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : hauteurs des deux membres > 0)
- **Énoncé** : Sur tout passage (membres supérieurs), le minimum attendu du membre antérieur est l'occurrence du membre postérieur.
- **Vérités** : V54, V56, V150
- **Repose sur** : théorèmes : `occurrence_successor_of_passage`; définitions/structures : `expectedMinimumPrime`, `occurrence`. Base rhv3 : `RHV3Lean.TZeroPassage`, `RHV3Lean.rZeroHeight`, `RHV3Lean.TZeroPassage.zEarlierMember`, `RHV3Lean.TZeroPassage.zLaterMember`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.fnPrimeSuccessor`, `RHV3Lean.nZeroSourceIndex`.
- **Entraîne** (3) : `expectedMinimumPrime_succ_of_passage`, `passage_event_increment`, `progression_occurrence`.

#### `expectedMinimumPrime_injective` — `Grammar.ExpectedMinimum` l.37 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : minima attendus égaux (forme de l'injectivité))
- **Énoncé** : Le pointeur minimum attendu est injectif : deux zéros de même minimum attendu sont le même zéro (un seul premier en face d'un seul zéro).
- **Vérités** : V149, V182
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `expectedMinimumPrime`, `expectedMinimumPrime_injective._proof_1_1`. Base rhv3 : `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.thm_primeAtRank_injective`, `RHV3Lean.thm_zeroSourceIndex_injective`.
- **Entraîne** (1) : `mirror_expectedMinimum_ne`.

#### `eventIndex_succ_of_passage` — `Grammar.ExpectedMinimum` l.55 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : hauteur du membre antérieur > 0)
- **Énoncé** : Sur tout passage de deux zéros consécutifs, l'index zéro-source du membre postérieur est celui de l'antérieur plus un (EV = EV+1).
- **Vérités** : V57, V150, V56
- **Repose sur** : théorèmes : aucun. Base rhv3 : `RHV3Lean.TZeroPassage`, `RHV3Lean.rZeroHeight`, `RHV3Lean.TZeroPassage.zEarlierMember`, `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TZeroPassage.zLaterMember`, `RHV3Lean.thm_zeroSourceIndex_succ_of_passage`.
- **Entraîne** (1) : `onLine_clock_sync`.

#### `expectedMinimumPrime_succ_of_passage` — `Grammar.ExpectedMinimum` l.65 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : hauteurs des deux membres > 0)
- **Énoncé** : Sur tout passage, le minimum attendu du membre antérieur est strictement inférieur à celui du postérieur, sans hypothèse sur β.
- **Vérités** : V150, V56
- **Repose sur** : théorèmes : `expectedMinimumPrime_eq_laterOccurrence`, `occurrence_lt_expectedMinimumPrime`; définitions/structures : `expectedMinimumPrime`, `occurrence`. Base rhv3 : `RHV3Lean.TZeroPassage`, `RHV3Lean.rZeroHeight`, `RHV3Lean.TZeroPassage.zEarlierMember`, `RHV3Lean.TZeroPassage.zLaterMember`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.


##### Module `RHV6Fresh.Grammar.Mod6Rigidity` (8 théorèmes)

#### `prime_goodMod6` — `Grammar.Mod6Rigidity` l.44 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : p > 3)
- **Énoncé** : Tout premier > 3 est en état A ou B modulo 6 (résidu 5 ou 1).
- **Vérités** : V174
- **Repose sur** : théorèmes : aucun; définitions/structures : `GoodMod6`, `prime_goodMod6._proof_1_1`, `prime_goodMod6._proof_1_2`, `prime_goodMod6._proof_1_3`, `prime_goodMod6._proof_1_4`. Base rhv3 : aucun.
- **Entraîne** (1) : `primeGapClass6_alternates`.

#### `gapClass6_eq_zero_iff` — `Grammar.Mod6Rigidity` l.60 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : m,n à bon état mod 6 ; m ≤ n)
- **Énoncé** : Entre deux nombres à bon état mod 6 (m ≤ n), la classe d'écart est 0 ⟺ les deux ont le même état.
- **Vérités** : V174
- **Repose sur** : théorèmes : aucun; définitions/structures : `GoodMod6`, `gapClass6`, `state6`, `gapClass6_eq_zero_iff._proof_1_1`, `gapClass6_eq_zero_iff._proof_1_2`, `gapClass6_eq_zero_iff._proof_1_3`, `gapClass6_eq_zero_iff._proof_1_4`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `gapClass6_eq_two_iff` — `Grammar.Mod6Rigidity` l.68 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : m,n à bon état mod 6 ; m ≤ n)
- **Énoncé** : La classe d'écart vaut 2 ⟺ transition A→B.
- **Vérités** : V174
- **Repose sur** : théorèmes : aucun; définitions/structures : `GoodMod6`, `gapClass6`, `state6`, `gapClass6_eq_two_iff._proof_1_1`, `gapClass6_eq_two_iff._proof_1_2`, `gapClass6_eq_two_iff._proof_1_3`, `gapClass6_eq_two_iff._proof_1_4`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `gapClass6_eq_four_iff` — `Grammar.Mod6Rigidity` l.76 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : m,n à bon état mod 6 ; m ≤ n)
- **Énoncé** : La classe d'écart vaut 4 ⟺ transition B→A.
- **Vérités** : V174
- **Repose sur** : théorèmes : aucun; définitions/structures : `GoodMod6`, `gapClass6`, `state6`, `gapClass6_eq_four_iff._proof_1_1`, `gapClass6_eq_four_iff._proof_1_2`, `gapClass6_eq_four_iff._proof_1_3`, `gapClass6_eq_four_iff._proof_1_4`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `gapClass6_mem` — `Grammar.Mod6Rigidity` l.84 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : m,n à bon état mod 6 ; m ≤ n)
- **Énoncé** : Entre deux nombres à bon état mod 6, la classe d'écart est toujours 0, 2 ou 4.
- **Vérités** : V174
- **Repose sur** : théorèmes : aucun; définitions/structures : `GoodMod6`, `gapClass6`, `gapClass6_mem._proof_1_1`, `gapClass6_mem._proof_1_2`, `gapClass6_mem._proof_1_3`, `gapClass6_mem._proof_1_4`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `gapClass6_alternates` — `Grammar.Mod6Rigidity` l.92 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : m,n,r à bon état mod 6, ordonnés ; deux transitions non nulles)
- **Énoncé** : Trois nombres m ≤ n ≤ r à bon état mod 6 dont les deux transitions sont non nulles : les deux classes d'écart sont différentes (alternance forcée).
- **Vérités** : V174
- **Repose sur** : théorèmes : aucun; définitions/structures : `GoodMod6`, `gapClass6`, `gapClass6_alternates._proof_1_1`, `gapClass6_alternates._proof_1_2`, `gapClass6_alternates._proof_1_3`, `gapClass6_alternates._proof_1_4`, `gapClass6_alternates._proof_1_5`, `gapClass6_alternates._proof_1_6`, `gapClass6_alternates._proof_1_7`, `gapClass6_alternates._proof_1_8`. Base rhv3 : aucun.
- **Entraîne** (1) : `primeGapClass6_alternates`.

#### `primeGapClass6_alternates` — `Grammar.Mod6Rigidity` l.108 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : p,q,r > 3 ordonnés ; deux transitions non nulles)
- **Énoncé** : Trois premiers > 3 ordonnés dont les deux transitions sont non nulles : classes d'écart différentes (alternance forcée pour les premiers).
- **Vérités** : V174
- **Repose sur** : théorèmes : `gapClass6_alternates`, `prime_goodMod6`; définitions/structures : `gapClass6`. Base rhv3 : aucun.
- **Entraîne** (1) : `expectedMinimumPrime_gapClass6_alternates`.

#### `expectedMinimumPrime_gapClass6_alternates` — `Grammar.Mod6Rigidity` l.120 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : p,q,r > 3 ordonnés ; deux transitions non nulles)
- **Énoncé** : Même énoncé que primeGapClass6_alternates (trois premiers quelconques > 3 ordonnés, transitions non nulles) ; le type ne mentionne pas expectedMinimumPrime : docstring ≠ type.
- **Vérités** : V174, V177
- **Repose sur** : théorèmes : `primeGapClass6_alternates`; définitions/structures : `gapClass6`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.


##### Module `RHV6Fresh.Tower.CanonicalOrigin` (17 théorèmes)

#### `towerMotion_phase_pos` — `Tower.CanonicalOrigin` l.26 — CONFIRMÉE
- **Énoncé** : La phase de la Tour propre d'un zéro est strictement positive (phase déduite de β et T).
- **Vérités** : V16
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `TowerMotion.phase`, `towerMotionOf`. Base rhv3 : `RHV3Lean.thm_rTowerPhase_positive`.
- **Entraîne** (5) : `abs_insertionDepth_lt_half`, `grids_never_coincide`, `one_lt_canonicalOrigin`, `pivotCoordinate_mirror_mem`, `towerPosition_shift_abs_lt_half`.

#### `towerMotion_phase_lt_pi_div_two` — `Tower.CanonicalOrigin` l.29 — CONFIRMÉE
- **Énoncé** : La phase de la Tour propre d'un zéro est strictement inférieure à π/2.
- **Vérités** : V16
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `TowerMotion.phase`, `towerMotionOf`. Base rhv3 : `RHV3Lean.thm_rTowerPhase_lt_piDivTwo`.
- **Entraîne** (5) : `abs_insertionDepth_lt_half`, `grids_never_coincide`, `incidence_neg_one_lt_one`, `pivotCoordinate_mirror_mem`, `towerPosition_shift_abs_lt_half`.

#### `towerMotion_incidence_mono` — `Tower.CanonicalOrigin` l.35 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : k ≤ l)
- **Énoncé** : Les rayons (croisements) de la Tour propre croissent au sens large avec leur coordonnée.
- **Vérités** : V16, V23
- **Repose sur** : théorèmes : `towerMotion_incidence_strictOrder`; définitions/structures : `TrueZero`, `TowerMotion.incidence`, `towerMotionOf`. Base rhv3 : aucun.
- **Entraîne** (5) : `canonicalOrigin_lt_iff_zero_le_pivotCoordinate`, `one_lt_incidence_iff`, `pivotCoordinate_le_of_le_contactPlus`, `secondTower_reads_occurrence_iff_coordinate_lt`, `towerMotion_incidence_lt_iff`.

#### `towerMotion_incidence_lt_iff` — `Tower.CanonicalOrigin` l.41 — CONFIRMÉE
- **Énoncé** : Un rayon est strictement avant un autre exactement quand sa coordonnée est strictement inférieure (rayons strictement croissants).
- **Vérités** : V16, V23
- **Repose sur** : théorèmes : `towerMotion_incidence_mono`, `towerMotion_incidence_strictOrder`; définitions/structures : `TrueZero`, `TowerMotion.incidence`, `towerMotionOf`. Base rhv3 : aucun.
- **Entraîne** (1) : `canonicalOrigin_lt_iff_zero_le_pivotCoordinate`.

#### `canonicalOrigin_eq` — `Tower.CanonicalOrigin` l.54 — CONFIRMÉE
- **Énoncé** : L'origine canonique vaut exp(phase/T) : elle ne dépend que de (β,T), sans premier ni rang.
- **Vérités** : V22, V15
- **Repose sur** : théorèmes : `towerMotion_incidence`; définitions/structures : `TrueZero`, `canonicalOrigin`, `TowerMotion.phase`, `towerMotionOf`, `TowerMotion.incidence`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `one_lt_canonicalOrigin`.

#### `canonicalOrigin_pos` — `Tower.CanonicalOrigin` l.60 — CONFIRMÉE
- **Énoncé** : L'origine canonique est strictement positive.
- **Vérités** : V22
- **Repose sur** : théorèmes : `towerMotion_incidence_positive`; définitions/structures : `TrueZero`, `canonicalOrigin`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `one_lt_canonicalOrigin` — `Tower.CanonicalOrigin` l.63 — CONFIRMÉE
- **Énoncé** : L'origine canonique est après l'abscisse 1.
- **Vérités** : V22
- **Repose sur** : théorèmes : `canonicalOrigin_eq`, `towerMotion_phase_pos`; définitions/structures : `TrueZero`, `canonicalOrigin`, `TowerMotion.phase`, `towerMotionOf`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `one_lt_incidence_iff`.

#### `incidence_neg_one_lt_one` — `Tower.CanonicalOrigin` l.70 — CONFIRMÉE
- **Énoncé** : Le croisement de coordonnée −1 est avant l'abscisse 1.
- **Vérités** : V22
- **Repose sur** : théorèmes : `towerMotion_incidence`, `towerMotion_phase_lt_pi_div_two`; définitions/structures : `TrueZero`, `TowerMotion.incidence`, `towerMotionOf`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `one_lt_incidence_iff`.

#### `one_lt_incidence_iff` — `Tower.CanonicalOrigin` l.83 — CONFIRMÉE
- **Énoncé** : Un croisement dépasse l'abscisse 1 exactement quand sa coordonnée est ≥ 0 : l'origine canonique est le premier croisement après 1.
- **Vérités** : V22
- **Repose sur** : théorèmes : `towerMotion_incidence_mono`, `incidence_neg_one_lt_one`, `one_lt_canonicalOrigin`; définitions/structures : `TrueZero`, `TowerMotion.incidence`, `towerMotionOf`, `one_lt_incidence_iff._proof_1_1`, `canonicalOrigin`. Base rhv3 : aucun.
- **Entraîne** (1) : `canonicalOrigin_isLeast`.

#### `canonicalOrigin_isLeast` — `Tower.CanonicalOrigin` l.99 — CONFIRMÉE
- **Énoncé** : La coordonnée 0 est la plus petite coordonnée dont le rayon dépasse l'abscisse 1 (origine canonique = premier croisement après 1).
- **Vérités** : V22
- **Repose sur** : théorèmes : `one_lt_incidence_iff`; définitions/structures : `TrueZero`, `TowerMotion.incidence`, `towerMotionOf`. Base rhv3 : aucun.
- **Entraîne** (1) : `geometry_of_tower`.

#### `logIncidence_eq_origin_add_halfTurns` — `Tower.CanonicalOrigin` l.105 — CONFIRMÉE
- **Énoncé** : Le log-rayon du croisement k est celui de l'origine canonique plus k demi-tours de π/T : la suite des rayons est déterminée par le zéro seul.
- **Vérités** : V23, V17, V16
- **Repose sur** : théorèmes : `towerMotion_ringJump_logWidth`, `TowerMotion.incidence_eq`; définitions/structures : `TrueZero`, `TowerMotion.logIncidence`, `towerMotionOf`, `canonicalOrigin`, `TowerMotion.incidence`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `halfTurn_logStep` — `Tower.CanonicalOrigin` l.115 — CONFIRMÉE
- **Énoncé** : Le pas de log-rayon entre deux croisements consécutifs vaut π/T : il ne dépend que de T, jamais d'un écart entre premiers.
- **Vérités** : V17, V16
- **Repose sur** : théorèmes : `towerMotion_consecutive_width`; définitions/structures : `TrueZero`, `TowerMotion.incidence`, `towerMotionOf`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `crossing_argument` — `Tower.CanonicalOrigin` l.124 — CONFIRMÉE
- **Énoncé** : L'argument du mouvement au croisement k vaut kπ.
- **Vérités** : V16, V18
- **Repose sur** : théorèmes : `towerMotion_incidence`; définitions/structures : `TrueZero`, `TowerMotion.incidence`, `towerMotionOf`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (3) : `crossing_on_axis`, `crossing_side`, `crossing_side_abs`.

#### `crossing_on_axis` — `Tower.CanonicalOrigin` l.133 — CONFIRMÉE
- **Énoncé** : Le croisement k est sur l'axe algébrique (sinus de l'argument nul).
- **Vérités** : V18, V26
- **Repose sur** : théorèmes : `crossing_argument`; définitions/structures : `TrueZero`, `TowerMotion.incidence`, `towerMotionOf`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `crossing_side` — `Tower.CanonicalOrigin` l.140 — CONFIRMÉE
- **Énoncé** : Le côté du passage au croisement k est (−1)^k.
- **Vérités** : V18
- **Repose sur** : théorèmes : `crossing_argument`; définitions/structures : `TrueZero`, `TowerMotion.incidence`, `towerMotionOf`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (2) : `crossing_side_alternates`, `ray_energy`.

#### `crossing_side_alternates` — `Tower.CanonicalOrigin` l.147 — CONFIRMÉE
- **Énoncé** : D'un croisement au suivant, le côté du passage change de signe : alternance stricte.
- **Vérités** : V18
- **Repose sur** : théorèmes : `crossing_side`; définitions/structures : `TrueZero`, `TowerMotion.incidence`, `towerMotionOf`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `geometry_of_tower`.

#### `crossing_side_abs` — `Tower.CanonicalOrigin` l.156 — CONFIRMÉE
- **Énoncé** : Le côté du passage vaut ±1 (passage franc, jamais tangent).
- **Vérités** : V18
- **Repose sur** : théorèmes : `crossing_argument`; définitions/structures : `TrueZero`, `TowerMotion.incidence`, `towerMotionOf`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.


##### Module `RHV6Fresh.Tower.Incidences` (6 théorèmes)

#### `contactAt_consecutive_logWidth` — `Tower.Incidences` l.23 — CONFIRMÉE
- **Énoncé** : Les deux contacts de la cellule de coordonnée k sont écartés d'un demi-tour de log-rayon π/T.
- **Vérités** : V17, V20
- **Repose sur** : théorèmes : `towerMotion_consecutive_width`; définitions/structures : `TrueZero`, `contactPlusAt`, `contactMinusAt`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (3) : `pivotPair_stageReading`, `sameHeight_pitch_invariant`, `sameRadial_height_changes_pitch`.

#### `contactAt_ordered` — `Tower.Incidences` l.28 — CONFIRMÉE
- **Énoncé** : Pour toute coordonnée k, le contact inférieur est strictement sous le contact supérieur (cellule ordonnée).
- **Vérités** : V20, V26
- **Repose sur** : théorèmes : `towerMotion_incidence_strictOrder`; définitions/structures : `TrueZero`, `contactMinusAt`, `contactPlusAt`, `contactAt_ordered._proof_1_1`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `contactMinusAt_positive` — `Tower.Incidences` l.32 — CONFIRMÉE
- **Énoncé** : Le contact inférieur d'une cellule est strictement positif.
- **Vérités** : V20
- **Repose sur** : théorèmes : `towerMotion_incidence_positive`; définitions/structures : `TrueZero`, `contactMinusAt`. Base rhv3 : aucun.
- **Entraîne** (5) : `pivotCell_amplitude_brackets`, `ray_energy`, `ray_energy_alternates`, `ray_energy_growth`, `ray_zeroTerm_real`.

#### `contactPlusAt_positive` — `Tower.Incidences` l.36 — CONFIRMÉE
- **Énoncé** : Le contact supérieur d'une cellule est strictement positif.
- **Vérités** : V20
- **Repose sur** : théorèmes : `towerMotion_incidence_positive`; définitions/structures : `TrueZero`, `contactPlusAt`. Base rhv3 : aucun.
- **Entraîne** (3) : `contactPlusAt_lt_primeAtRank_counted`, `countedPrime_le_lastRay`, `pivotCell_amplitude_brackets`.

#### `contactAt_tangent_minus` — `Tower.Incidences` l.40 — CONFIRMÉE
- **Énoncé** : Au contact inférieur de toute cellule consécutive, tan(T·log C) = T/β : le contact certifie (T,β) par la loi tangentielle.
- **Vérités** : V45, V20
- **Repose sur** : théorèmes : `TowerMotion.incidence_eq`, `TowerMotion.logIncidence_eq`, `towerMotion_phase`; définitions/structures : `TrueZero`, `contactMinusAt`, `TowerMotion.incidence`, `towerMotionOf`, `TowerMotion.logIncidence`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`.
- **Entraîne** (0) : aucun théorème du projet.

#### `contactAt_tangent_plus` — `Tower.Incidences` l.58 — CONFIRMÉE
- **Énoncé** : Idem au contact supérieur : les deux extrémités certifient le même rapport T/β.
- **Vérités** : V45, V20
- **Repose sur** : théorèmes : `TowerMotion.incidence_eq`, `TowerMotion.logIncidence_eq`, `towerMotion_phase`; définitions/structures : `TrueZero`, `contactPlusAt`, `TowerMotion.incidence`, `towerMotionOf`, `TowerMotion.logIncidence`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`.
- **Entraîne** (0) : aucun théorème du projet.


##### Module `RHV6Fresh.Tower.InvertedTower` (21 théorèmes)

#### `InvertedContactPair.entryContact_pos` — `Tower.InvertedTower` l.40 — CONFIRMÉE
- **Énoncé** : L'entrée de la seconde orientation (le rayon du haut) est strictement positive.
- **Vérités** : V34, V20
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.entryContact`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedContactPair.lastRayContact_pos` — `Tower.InvertedTower` l.41 — CONFIRMÉE
- **Énoncé** : Le dernier rayon de la seconde orientation (le rayon du bas) est strictement positif.
- **Vérités** : V34, V20
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.lastRayContact`. Base rhv3 : aucun.
- **Entraîne** (1) : `InvertedContactPair.reaches_primeAtRank_iff`.

#### `InvertedContactPair.ordered` — `Tower.InvertedTower` l.43 — CONFIRMÉE
- **Énoncé** : Dans la seconde orientation, le dernier rayon est strictement sous l'entrée (contacts inversés).
- **Vérités** : V34, V82
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.lastRayContact`, `InvertedContactPair.entryContact`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedContactPair.rotationLaw` — `Tower.InvertedTower` l.45 — CONFIRMÉE
- **Énoncé** : Le dernier rayon inversé est un rayon de la même rotation que l'entrée.
- **Vérités** : V34, V23
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.entryContact`, `InvertedContactPair.lastRayContact`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedContactPair.tangentLaw` — `Tower.InvertedTower` l.48 — CONFIRMÉE
- **Énoncé** : L'entrée inversée est une incidence de la phase propre du zéro (loi tangentielle).
- **Vérités** : V34, V45
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.entryContact`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rTowerPhase`.
- **Entraîne** (2) : `InvertedContactPair.entryReading_isInt`, `InvertedContactPair.recovers_beta`.

#### `InvertedContactPair.upright_entryContact` — `Tower.InvertedTower` l.71 — CONFIRMÉE
- **Énoncé** : Redressée, la paire inversée a pour entrée le dernier rayon inversé.
- **Vérités** : V34
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair`, `AnalyticContactPair.entryContact`, `InvertedContactPair.upright`, `InvertedContactPair.lastRayContact`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedContactPair.upright_lastRayContact` — `Tower.InvertedTower` l.73 — CONFIRMÉE
- **Énoncé** : Redressée, la paire inversée a pour dernier rayon l'entrée inversée (rôles échangés).
- **Vérités** : V34
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair`, `AnalyticContactPair.lastRayContact`, `InvertedContactPair.upright`, `InvertedContactPair.entryContact`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedContactPair.logDiameter_positive` — `Tower.InvertedTower` l.80 — CONFIRMÉE
- **Énoncé** : Le diamètre logarithmique de la cellule inversée est strictement positif.
- **Vérités** : V34
- **Repose sur** : théorèmes : `AnalyticContactPair.logDiameter_positive`; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.logDiameter`, `InvertedContactPair.upright`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedContactPair.stageReading_isNat` — `Tower.InvertedTower` l.86 — CONFIRMÉE
- **Énoncé** : Le nombre d'étages lu sur une paire inversée est un naturel strictement positif.
- **Vérités** : V43
- **Repose sur** : théorèmes : `AnalyticContactPair.stageReading_isNat`; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.stageReading`, `InvertedContactPair.upright`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedContactPair.stageCount_positive` — `Tower.InvertedTower` l.92 — CONFIRMÉE
- **Énoncé** : Le nombre d'étages d'une paire inversée est strictement positif.
- **Vérités** : V43
- **Repose sur** : théorèmes : `AnalyticContactPair.stageCount_positive`; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.stageCount`, `InvertedContactPair.upright`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedContactPair.stageCount_cast` — `Tower.InvertedTower` l.94 — CONFIRMÉE
- **Énoncé** : Le nombre d'étages lu est le naturel porté par la paire inversée.
- **Vérités** : V43
- **Repose sur** : théorèmes : `AnalyticContactPair.stageCount_cast`; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.stageReading`, `InvertedContactPair.stageCount`, `InvertedContactPair.upright`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedContactPair.entryReading_isInt` — `Tower.InvertedTower` l.100 — CONFIRMÉE
- **Énoncé** : La coordonnée d'entrée lue sur une paire inversée est un entier (loi tangentielle).
- **Vérités** : V43
- **Repose sur** : théorèmes : `InvertedContactPair.tangentLaw`; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.entryReading`, `InvertedContactPair.entryContact`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rTowerPhase`.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedContactPair.recovers_T` — `Tower.InvertedTower` l.115 — CONFIRMÉE
- **Énoncé** : Inversion : T = m·π/(log C_entrée − log C_dernier) sur la paire inversée : les deux contacts redonnent T.
- **Vérités** : V45, V34
- **Repose sur** : théorèmes : `AnalyticContactPair.recovers_T`; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.stageReading`, `InvertedContactPair.logDiameter`, `InvertedContactPair.upright`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedContactPair.recovers_beta` — `Tower.InvertedTower` l.120 — CONFIRMÉE
- **Énoncé** : Inversion tangentielle : β = T/tan(T·log C_entrée) lue sur l'entrée (le rayon du haut) d'une paire inversée.
- **Vérités** : V45, V34
- **Repose sur** : théorèmes : `InvertedContactPair.tangentLaw`; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.entryContact`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroHeight`, `RHV3Lean.thm_zeroRadialPosition_positive`, `RHV3Lean.rTowerPhase`, `RHV3Lean.rTowerHeight`, `RHV3Lean.rTowerRadialPosition`, `RHV3Lean.rTowerPhase.eq_1`.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedContactPair.entryContact_eq_incidence` — `Tower.InvertedTower` l.137 — CONFIRMÉE
- **Énoncé** : L'entrée inversée est le rayon de coordonnée d'entrée de la Tour du zéro.
- **Vérités** : V34, V45
- **Repose sur** : théorèmes : `AnalyticContactPair.lastRayContact_eq_incidence`; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.entryContact`, `InvertedContactPair.entryCoordinate`, `InvertedContactPair.upright`. Base rhv3 : `RHV3Lean.rTowerIncidence`.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedContactPair.lastRayContact_eq_incidence` — `Tower.InvertedTower` l.141 — CONFIRMÉE
- **Énoncé** : Le dernier rayon inversé est le rayon de coordonnée (entrée − nombre d'étages).
- **Vérités** : V34, V45
- **Repose sur** : théorèmes : `AnalyticContactPair.entryContact_eq_incidence`; définitions/structures : `TrueZero`, `InvertedContactPair`, `InvertedContactPair.lastRayContact`, `InvertedContactPair.entryCoordinate`, `InvertedContactPair.stageCount`, `AnalyticContactPair.entryContact`, `InvertedContactPair.upright`, `AnalyticContactPair.entryCoordinate`, `AnalyticContactPair.stageCount`. Base rhv3 : `RHV3Lean.rTowerIncidence`.
- **Entraîne** (0) : aucun théorème du projet.

#### `invertedPairAt_entryContact` — `Tower.InvertedTower` l.164 — CONFIRMÉE
- **Énoncé** : L'entrée de la paire inversée en k est contactPlusAt z k (le contact du haut).
- **Vérités** : V34
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair.entryContact`, `invertedPairAt`, `contactPlusAt`. Base rhv3 : aucun.
- **Entraîne** (1) : `invertedPairAt_eq_reflected`.

#### `invertedPairAt_lastRayContact` — `Tower.InvertedTower` l.167 — CONFIRMÉE
- **Énoncé** : Le dernier rayon de la paire inversée en k est contactMinusAt z k (le contact du bas).
- **Vérités** : V34
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedContactPair.lastRayContact`, `invertedPairAt`, `contactMinusAt`. Base rhv3 : aucun.
- **Entraîne** (1) : `invertedPairAt_eq_reflected`.

#### `invertedPairAt_upright` — `Tower.InvertedTower` l.170 — CONFIRMÉE
- **Énoncé** : Le même anneau lu dans l'orientation croissante est la paire analytique en k.
- **Vérités** : V34, V71
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `InvertedContactPair.upright`, `invertedPairAt`, `analyticPairAt`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedTower.properState_entryContact` — `Tower.InvertedTower` l.187 — CONFIRMÉE
- **Énoncé** : L'état propre d'une Tour inversée a pour entrée celle de la Tour inversée.
- **Vérités** : V34, V26
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedTower`, `InvertedContactPair.entryContact`, `InvertedTower.properState`, `InvertedTower.toInvertedContactPair`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `InvertedTower.properState_lastRayContact` — `Tower.InvertedTower` l.189 — CONFIRMÉE
- **Énoncé** : L'état propre d'une Tour inversée a pour dernier rayon celui de la Tour inversée.
- **Vérités** : V34, V26
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `InvertedTower`, `InvertedContactPair.lastRayContact`, `InvertedTower.properState`, `InvertedTower.toInvertedContactPair`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.


##### Module `RHV6Fresh.Tower.MirrorGeometry` (3 théorèmes)

#### `mirror_ordinate` — `Tower.MirrorGeometry` l.19 — CONFIRMÉE
- **Énoncé** : Le miroir supérieur a la même hauteur T que le zéro.
- **Vérités** : V65
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.zUpperMirrorZero`, `RHV3Lean.thm_mirror_sameHeight`.
- **Entraîne** (1) : `mirror_phase`.

#### `mirror_beta` — `Tower.MirrorGeometry` l.23 — CONFIRMÉE
- **Énoncé** : Le miroir supérieur a pour position radiale 1−β.
- **Vérités** : V65
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.zUpperMirrorZero`, `RHV3Lean.thm_mirror_radialPosition`.
- **Entraîne** (1) : `mirror_phase`.

#### `mirror_phase` — `Tower.MirrorGeometry` l.28 — CONFIRMÉE
- **Énoncé** : La phase de la Tour propre du miroir supérieur est arctan(T/(1−β)) : mêmes formules appliquées à ses coordonnées.
- **Vérités** : V67, V80
- **Repose sur** : théorèmes : `towerMotion_phase`, `mirror_ordinate`, `mirror_beta`; définitions/structures : `TrueZero`, `TowerMotion.phase`, `towerMotionOf`. Base rhv3 : `RHV3Lean.zUpperMirrorZero`, `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`.
- **Entraîne** (0) : aucun théorème du projet.


##### Module `RHV6Fresh.Tower.ProperTower` (26 théorèmes)

#### `AnalyticContactPair.entryContact_pos` — `Tower.ProperTower` l.56 — CONFIRMÉE
- **Énoncé** : L'incidence d'entrée est strictement positive.
- **Vérités** : V20
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.entryContact`. Base rhv3 : aucun.
- **Entraîne** (2) : `AnalyticContactPair.entryContact_eq_incidence`, `AnalyticContactPair.logDiameter_positive`.

#### `AnalyticContactPair.lastRayContact_pos` — `Tower.ProperTower` l.57 — CONFIRMÉE
- **Énoncé** : Le dernier rayon est strictement positif.
- **Vérités** : V20
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.lastRayContact`. Base rhv3 : aucun.
- **Entraîne** (4) : `AnalyticContactPair.lastRayContact_eq_incidence`, `countedRank_eq_succ_iff`, `countedRank_eq_zero_iff`, `reaches_primeAtRank_iff`.

#### `AnalyticContactPair.ordered` — `Tower.ProperTower` l.58 — CONFIRMÉE
- **Énoncé** : Dans la paire propre, l'incidence d'entrée est strictement inférieure au dernier rayon (cellule ordonnée).
- **Vérités** : V20, V26
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.entryContact`, `AnalyticContactPair.lastRayContact`. Base rhv3 : aucun.
- **Entraîne** (2) : `AnalyticContactPair.cell_nonempty`, `AnalyticContactPair.logDiameter_positive`.

#### `AnalyticContactPair.rotationLaw` — `Tower.ProperTower` l.60 — CONFIRMÉE
- **Énoncé** : Le dernier rayon est un rayon de la même rotation que l'entrée (sin(T·Δlog)=0).
- **Vérités** : V20, V23
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.lastRayContact`, `AnalyticContactPair.entryContact`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `AnalyticContactPair.stageReading_isInt`.

#### `AnalyticContactPair.tangentLaw` — `Tower.ProperTower` l.63 — CONFIRMÉE
- **Énoncé** : L'incidence d'entrée est une incidence de la phase propre (loi tangentielle).
- **Vérités** : V20, V45, V16
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.entryContact`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rTowerPhase`.
- **Entraîne** (3) : `AnalyticContactPair.entryReading_isInt`, `AnalyticContactPair.recovers_beta`, `entry_separates_in_fiber`.

#### `AnalyticContactPair.logDiameter_positive` — `Tower.ProperTower` l.75 — CONFIRMÉE
- **Énoncé** : Le diamètre logarithmique de la cellule (log C_dernier − log C_entrée) est strictement positif.
- **Vérités** : V26
- **Repose sur** : théorèmes : `AnalyticContactPair.entryContact_pos`, `AnalyticContactPair.ordered`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.logDiameter`, `AnalyticContactPair.entryContact`, `AnalyticContactPair.lastRayContact`. Base rhv3 : aucun.
- **Entraîne** (3) : `AnalyticContactPair.recovers_T`, `AnalyticContactPair.stageReading_positive`, `InvertedContactPair.logDiameter_positive`.

#### `AnalyticContactPair.entryReading_isInt` — `Tower.ProperTower` l.91 — CONFIRMÉE
- **Énoncé** : La coordonnée d'entrée lue est un entier (loi tangentielle).
- **Vérités** : V43, V20
- **Repose sur** : théorèmes : `AnalyticContactPair.tangentLaw`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.entryReading`, `AnalyticContactPair.entryContact`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rTowerPhase`.
- **Entraîne** (1) : `AnalyticContactPair.entryCoordinate_cast`.

#### `AnalyticContactPair.stageReading_isInt` — `Tower.ProperTower` l.99 — CONFIRMÉE
- **Énoncé** : Le nombre d'étages lu est un entier (loi de rotation).
- **Vérités** : V43, V32
- **Repose sur** : théorèmes : `AnalyticContactPair.rotationLaw`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.stageReading`, `AnalyticContactPair.lastRayContact`, `AnalyticContactPair.entryContact`, `AnalyticContactPair.logDiameter`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rTowerDensity`, `RHV3Lean.rTowerHeight`.
- **Entraîne** (1) : `AnalyticContactPair.stageReading_isNat`.

#### `AnalyticContactPair.stageReading_positive` — `Tower.ProperTower` l.108 — CONFIRMÉE
- **Énoncé** : Le nombre d'étages lu est strictement positif.
- **Vérités** : V43
- **Repose sur** : théorèmes : `AnalyticContactPair.logDiameter_positive`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.stageReading`, `AnalyticContactPair.logDiameter`. Base rhv3 : `RHV3Lean.rTowerDensity`, `RHV3Lean.thm_rTowerDensity_positive`.
- **Entraîne** (1) : `AnalyticContactPair.stageReading_isNat`.

#### `AnalyticContactPair.stageReading_isNat` — `Tower.ProperTower` l.111 — CONFIRMÉE
- **Énoncé** : Le nombre d'étages lu est un naturel strictement positif.
- **Vérités** : V43
- **Repose sur** : théorèmes : `AnalyticContactPair.stageReading_isInt`, `AnalyticContactPair.stageReading_positive`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.stageReading`, `AnalyticContactPair.stageReading_isNat._proof_1_1`, `AnalyticContactPair.stageReading_isNat._proof_1_2`. Base rhv3 : aucun.
- **Entraîne** (3) : `AnalyticContactPair.stageCount_cast`, `AnalyticContactPair.stageCount_positive`, `InvertedContactPair.stageReading_isNat`.

#### `AnalyticContactPair.entryCoordinate_cast` — `Tower.ProperTower` l.124 — CONFIRMÉE
- **Énoncé** : La coordonnée d'entrée lue est la coordonnée entière portée par la paire.
- **Vérités** : V43
- **Repose sur** : théorèmes : `AnalyticContactPair.entryReading_isInt`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.entryReading`, `AnalyticContactPair.entryCoordinate`. Base rhv3 : aucun.
- **Entraîne** (3) : `AnalyticContactPair.entryContact_eq_incidence`, `AnalyticContactPair.lastRayContact_eq_incidence`, `pivotPair_entryCoordinate`.

#### `AnalyticContactPair.stageCount_positive` — `Tower.ProperTower` l.130 — CONFIRMÉE
- **Énoncé** : Le nombre d'étages de la paire est strictement positif.
- **Vérités** : V43, V32
- **Repose sur** : théorèmes : `AnalyticContactPair.stageReading_isNat`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.stageCount`, `AnalyticContactPair.stageReading`. Base rhv3 : aucun.
- **Entraîne** (1) : `InvertedContactPair.stageCount_positive`.

#### `AnalyticContactPair.stageCount_cast` — `Tower.ProperTower` l.133 — CONFIRMÉE
- **Énoncé** : Le nombre d'étages lu est le naturel porté par la paire.
- **Vérités** : V43
- **Repose sur** : théorèmes : `AnalyticContactPair.stageReading_isNat`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.stageReading`, `AnalyticContactPair.stageCount`. Base rhv3 : aucun.
- **Entraîne** (4) : `AnalyticContactPair.lastRayContact_eq_incidence`, `AnalyticContactPair.same_state_same_zero`, `InvertedContactPair.stageCount_cast`, `pivotPair_stageCount`.

#### `AnalyticContactPair.recovers_T` — `Tower.ProperTower` l.138 — CONFIRMÉE
- **Énoncé** : Inversion : T = m·π/(log C_dernier − log C_entrée) : les deux contacts redonnent exactement T par leur rapport (m lu).
- **Vérités** : V45
- **Repose sur** : théorèmes : `AnalyticContactPair.logDiameter_positive`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.stageReading`, `AnalyticContactPair.logDiameter`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rTowerDensity`, `RHV3Lean.rTowerHeight`.
- **Entraîne** (3) : `AnalyticContactPair.same_state_same_zero`, `InvertedContactPair.recovers_T`, `inversion`.

#### `AnalyticContactPair.recovers_beta` — `Tower.ProperTower` l.145 — CONFIRMÉE
- **Énoncé** : Inversion tangentielle : β = T/tan(T·log C_entrée), lu sur le seul contact d'entrée.
- **Vérités** : V45
- **Repose sur** : théorèmes : `AnalyticContactPair.tangentLaw`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.entryContact`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroHeight`, `RHV3Lean.thm_zeroRadialPosition_positive`, `RHV3Lean.rTowerPhase`, `RHV3Lean.rTowerHeight`, `RHV3Lean.rTowerRadialPosition`, `RHV3Lean.rTowerPhase.eq_1`.
- **Entraîne** (2) : `AnalyticContactPair.same_state_same_zero`, `inversion`.

#### `AnalyticContactPair.entryContact_eq_incidence` — `Tower.ProperTower` l.162 — CONFIRMÉE
- **Énoncé** : L'incidence d'entrée est le rayon de coordonnée d'entrée de la Tour du zéro.
- **Vérités** : V20, V45
- **Repose sur** : théorèmes : `AnalyticContactPair.entryCoordinate_cast`, `AnalyticContactPair.entryContact_pos`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.entryContact`, `AnalyticContactPair.entryCoordinate`, `AnalyticContactPair.entryReading`. Base rhv3 : `RHV3Lean.rTowerIncidence`, `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rTowerPhase`, `RHV3Lean.rTowerLogIncidence`, `RHV3Lean.rTowerHeight`.
- **Entraîne** (3) : `AnalyticContactPair.contacts_of_one_stage`, `AnalyticContactPair.ext_readings`, `InvertedContactPair.lastRayContact_eq_incidence`.

#### `AnalyticContactPair.lastRayContact_eq_incidence` — `Tower.ProperTower` l.177 — CONFIRMÉE
- **Énoncé** : Le dernier rayon est le rayon de coordonnée (entrée + nombre d'étages).
- **Vérités** : V20, V45
- **Repose sur** : théorèmes : `AnalyticContactPair.entryCoordinate_cast`, `AnalyticContactPair.stageCount_cast`, `AnalyticContactPair.lastRayContact_pos`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.lastRayContact`, `AnalyticContactPair.entryCoordinate`, `AnalyticContactPair.stageCount`, `AnalyticContactPair.entryContact`, `AnalyticContactPair.entryReading`, `AnalyticContactPair.logDiameter`, `AnalyticContactPair.stageReading`. Base rhv3 : `RHV3Lean.rTowerIncidence`, `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rTowerPhase`, `RHV3Lean.rTowerLogIncidence`, `RHV3Lean.rTowerHeight`.
- **Entraîne** (5) : `AnalyticContactPair.contacts_of_one_stage`, `AnalyticContactPair.ext_readings`, `InvertedContactPair.entryContact_eq_incidence`, `lastRayContact_eq_contactPlusAt`, `reaches_iff_readCoordinates`.

#### `AnalyticContactPair.contacts_of_one_stage` — `Tower.ProperTower` l.205 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : nombre d'étages = 1)
- **Énoncé** : À un seul étage, les deux contacts sont la paire consécutive (contactMinusAt, contactPlusAt) à la coordonnée lue.
- **Vérités** : V32, V20
- **Repose sur** : théorèmes : `AnalyticContactPair.entryContact_eq_incidence`, `AnalyticContactPair.lastRayContact_eq_incidence`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.stageCount`, `AnalyticContactPair.entryContact`, `contactMinusAt`, `AnalyticContactPair.entryCoordinate`, `AnalyticContactPair.lastRayContact`, `contactPlusAt`. Base rhv3 : `RHV3Lean.rTowerIncidence`.
- **Entraîne** (1) : `AnalyticContactPair.eq_analyticPairAt_of_one_stage`.

#### `AnalyticContactPair.same_state_same_zero` — `Tower.ProperTower` l.216 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : mêmes contacts et même nombre d'étages)
- **Énoncé** : Deux états propres de même nombre d'étages et mêmes contacts appartiennent au même zéro : les contacts d'un zéro lui sont propres.
- **Vérités** : V46, V45
- **Repose sur** : théorèmes : `AnalyticContactPair.stageCount_cast`, `AnalyticContactPair.recovers_T`, `AnalyticContactPair.recovers_beta`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.stageCount`, `AnalyticContactPair.entryContact`, `AnalyticContactPair.lastRayContact`, `AnalyticContactPair.logDiameter`, `AnalyticContactPair.stageReading`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.thm_zero_identity_of_sameSupport`, `RHV3Lean.cZeroSupport`.
- **Entraîne** (0) : aucun théorème du projet.

#### `analyticPairAt_entryContact` — `Tower.ProperTower` l.271 — CONFIRMÉE
- **Énoncé** : Pour toute coordonnée k, l'incidence d'entrée de la paire analytique en k est contactMinusAt z k.
- **Vérités** : V20
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair.entryContact`, `analyticPairAt`, `contactMinusAt`. Base rhv3 : aucun.
- **Entraîne** (5) : `canonicalOrigin_lt_iff_zero_le_pivotCoordinate`, `pivotCoordinate_le_of_le_contactPlus`, `pivotPair_entryContact`, `pivotPair_stageReading`, `prime_raccord_has_unique_tower_cell`.

#### `analyticPairAt_lastRayContact` — `Tower.ProperTower` l.274 — CONFIRMÉE
- **Énoncé** : Pour toute coordonnée k, le dernier rayon de la paire analytique en k est contactPlusAt z k.
- **Vérités** : V20
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair.lastRayContact`, `analyticPairAt`, `contactPlusAt`. Base rhv3 : aucun.
- **Entraîne** (4) : `pivotPair_lastRayContact`, `pivotPair_stageReading`, `pivot_le_contactPlus_pivotCoordinate`, `prime_raccord_has_unique_tower_cell`.

#### `entry_separates_in_fiber` — `Tower.ProperTower` l.284 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : même hauteur et même incidence d'entrée)
- **Énoncé** : Deux zéros de même hauteur dont les états propres ont la même incidence d'entrée sont le même zéro (l'entrée sépare dans la fibre).
- **Vérités** : V46, V50
- **Repose sur** : théorèmes : `AnalyticContactPair.tangentLaw`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.entryContact`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rTowerPhase`, `RHV3Lean.thm_rTowerPhase_positive`, `RHV3Lean.thm_rTowerPhase_lt_piDivTwo`, `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.thm_zeroRadialPosition_positive`, `RHV3Lean.thm_zero_identity_of_sameSupport`, `RHV3Lean.cZeroSupport`.
- **Entraîne** (0) : aucun théorème du projet.

#### `TrueTower.properState_entryContact` — `Tower.ProperTower` l.351 — CONFIRMÉE
- **Énoncé** : L'état propre d'une Tour a pour incidence d'entrée celle de la Tour.
- **Vérités** : V20, V26
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `TrueTower`, `AnalyticContactPair.entryContact`, `TrueTower.properState`, `TrueTower.toAnalyticContactPair`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `TrueTower.properState_lastRayContact` — `Tower.ProperTower` l.353 — CONFIRMÉE
- **Énoncé** : L'état propre d'une Tour a pour dernier rayon celui de la Tour.
- **Vérités** : V20, V26
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `TrueTower`, `AnalyticContactPair.lastRayContact`, `TrueTower.properState`, `TrueTower.toAnalyticContactPair`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `TrueTower.phase_eq_motion` — `Tower.ProperTower` l.355 — CONFIRMÉE
- **Énoncé** : La phase portée par une Tour propre est celle du mouvement canonique du zéro.
- **Vérités** : V15, V16
- **Repose sur** : théorèmes : `TowerMotion.phase_eq`, `towerMotion_phase`; définitions/structures : `TrueZero`, `TrueTower`, `TowerMotion.phase`, `TrueTower.toTowerMotion`, `towerMotionOf`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`.
- **Entraîne** (0) : aucun théorème du projet.

#### `TrueTower.incidence_eq_motion` — `Tower.ProperTower` l.359 — CONFIRMÉE
- **Énoncé** : Les rayons portés par une Tour propre sont ceux du mouvement canonique du zéro.
- **Vérités** : V15, V23
- **Repose sur** : théorèmes : `TowerMotion.incidence_eq`, `TowerMotion.logIncidence_eq`, `TowerMotion.phase_eq`, `towerMotion_incidence`, `towerMotion_phase`; définitions/structures : `TrueZero`, `TrueTower`, `TowerMotion.incidence`, `TrueTower.toTowerMotion`, `towerMotionOf`, `TowerMotion.logIncidence`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`.
- **Entraîne** (0) : aucun théorème du projet.


##### Module `RHV6Fresh.Tower.ReflectedMotion` (24 théorèmes)

#### `reflectedPhase_eq_neg` — `Tower.ReflectedMotion` l.34 — CONFIRMÉE
- **Énoncé** : La phase du mouvement réfléchi du zéro w est l'opposée de la phase de sa Tour propre.
- **Vérités** : V80, V35
- **Repose sur** : théorèmes : `towerMotion_phase`; définitions/structures : `TrueZero`, `reflectedPhase`, `TowerMotion.phase`, `towerMotionOf`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`.
- **Entraîne** (1) : `reflectedLogIncidence_eq`.

#### `reflectedLogIncidence_eq` — `Tower.ReflectedMotion` l.48 — CONFIRMÉE
- **Énoncé** : Le log-rayon de coordonnée j du mouvement réfléchi est celui de la Tour propre à la coordonnée −j (identité de conjugaison).
- **Vérités** : V34, V80
- **Repose sur** : théorèmes : `TowerMotion.logIncidence_eq`, `reflectedPhase_eq_neg`; définitions/structures : `TrueZero`, `reflectedLogIncidence`, `TowerMotion.logIncidence`, `towerMotionOf`, `TowerMotion.phase`, `reflectedPhase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (2) : `reflectedIncidence_eq`, `reflected_lastRay_lt_one`.

#### `reflectedIncidence_eq` — `Tower.ReflectedMotion` l.59 — CONFIRMÉE
- **Énoncé** : Le rayon de coordonnée j du mouvement réfléchi est celui de la Tour propre à la coordonnée −j : les rayons du miroir parcourus à l'envers.
- **Vérités** : V34, V80
- **Repose sur** : théorèmes : `reflectedLogIncidence_eq`, `TowerMotion.incidence_eq`; définitions/structures : `TrueZero`, `reflectedIncidence`, `TowerMotion.incidence`, `towerMotionOf`, `reflectedLogIncidence`, `reflectedIncidence.eq_1`, `TowerMotion.logIncidence`. Base rhv3 : aucun.
- **Entraîne** (6) : `reflectedMotion_incidence`, `reflected_entry_eq_contactPlus`, `reflected_lastRay_eq_contactMinus`, `secondTower_entry_eq_reflected`, `secondTower_lastRay_eq_reflected`, `trajectory_reversal`.

#### `reflected_step` — `Tower.ReflectedMotion` l.66 — CONFIRMÉE
- **Énoncé** : Le pas de log-rayon du zéro réfléchi vaut −π/T : la spirale tourne dans l'autre sens.
- **Vérités** : V80, V35
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `reflectedLogIncidence`, `reflectedPhase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `reflectedIncidence_antitone`.

#### `mirror_step_positive` — `Tower.ReflectedMotion` l.75 — CONFIRMÉE
- **Énoncé** : Le pas de log-rayon du miroir supérieur (1−β,T) vaut +π/T : β ↦ 1−β seul ne renverse rien.
- **Vérités** : V35, V81
- **Repose sur** : théorèmes : `TowerMotion.logIncidence_eq`; définitions/structures : `TrueZero`, `TowerMotion.logIncidence`, `towerMotionOf`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `reflectedIncidence_antitone` — `Tower.ReflectedMotion` l.86 — CONFIRMÉE
- **Énoncé** : Les rayons du zéro réfléchi décroissent strictement avec sa coordonnée (orientation opposée).
- **Vérités** : V34, V80
- **Repose sur** : théorèmes : `reflected_step`; définitions/structures : `TrueZero`, `reflectedIncidence`, `reflectedLogIncidence`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `reflected_lastRay_lt_one` — `Tower.ReflectedMotion` l.102 — CONFIRMÉE
- **Énoncé** : Depuis son origine (j ≥ 1), le dernier rayon du mouvement réfléchi est strictement sous l'abscisse 1.
- **Vérités** : V72, V96
- **Repose sur** : théorèmes : `reflectedLogIncidence_eq`, `TowerMotion.logIncidence_eq`, `towerMotion_phase`; définitions/structures : `TrueZero`, `reflectedIncidence`, `reflectedLogIncidence`, `TowerMotion.logIncidence`, `towerMotionOf`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`.
- **Entraîne** (1) : `reflected_no_stop_event`.

#### `reflected_no_stop_event` — `Tower.ReflectedMotion` l.117 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : p ≥ 1 (donnée : entier naturel candidat premier))
- **Énoncé** : Le mouvement réfléchi suivi depuis son origine n'a aucun événement d'arrêt : aucun premier p ≥ 1 n'est atteint par son dernier rayon, pour tout zéro.
- **Vérités** : V72, V96, V139
- **Repose sur** : théorèmes : `reflected_lastRay_lt_one`; définitions/structures : `TrueZero`, `reflectedIncidence`. Base rhv3 : aucun.
- **Entraîne** (2) : `reflectedFromOrigin_never_reaches_expectedMinimum`, `reflected_reads_no_prime`.

#### `reflected_entry_eq_contactPlus` — `Tower.ReflectedMotion` l.128 — CONFIRMÉE
- **Énoncé** : À sa coordonnée −(k+1), l'entrée du zéro réfléchi est le contact du haut de la cellule k de la Tour propre.
- **Vérités** : V34, V80
- **Repose sur** : théorèmes : `reflectedIncidence_eq`; définitions/structures : `TrueZero`, `reflectedIncidence`, `contactPlusAt`, `TowerMotion.incidence`, `towerMotionOf`. Base rhv3 : aucun.
- **Entraîne** (2) : `invertedPairAt_eq_reflected`, `reflection_reverses_existing_ring`.

#### `reflected_lastRay_eq_contactMinus` — `Tower.ReflectedMotion` l.134 — CONFIRMÉE
- **Énoncé** : À sa coordonnée −(k+1), le dernier rayon du zéro réfléchi est le contact du bas de la cellule k.
- **Vérités** : V34, V80
- **Repose sur** : théorèmes : `reflectedIncidence_eq`; définitions/structures : `TrueZero`, `reflectedIncidence`, `contactMinusAt`, `TowerMotion.incidence`, `towerMotionOf`, `TowerMotion`. Base rhv3 : aucun.
- **Entraîne** (2) : `invertedPairAt_eq_reflected`, `reflection_reverses_existing_ring`.

#### `invertedPairAt_eq_reflected` — `Tower.ReflectedMotion` l.143 — CONFIRMÉE
- **Énoncé** : L'inversion des contacts est un théorème : la paire inversée en k est l'anneau du zéro réfléchi à sa coordonnée −(k+1), entrée puis dernier rayon dans son sens de parcours.
- **Vérités** : V34, V80, V82
- **Repose sur** : théorèmes : `invertedPairAt_entryContact`, `invertedPairAt_lastRayContact`, `reflected_entry_eq_contactPlus`, `reflected_lastRay_eq_contactMinus`; définitions/structures : `TrueZero`, `InvertedContactPair.entryContact`, `invertedPairAt`, `reflectedIncidence`, `InvertedContactPair.lastRayContact`, `contactPlusAt`, `contactMinusAt`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `invertedPairAt_coordinate_le_zero` — `Tower.ReflectedMotion` l.153 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : k ≥ 0)
- **Énoncé** : Si la coordonnée avant k est ≥ 0, les deux coordonnées réfléchies −(k+1) et −(k+1)+1 sont ≤ 0 : la seconde Tour place ses contacts hors du domaine j ≥ 1 du mouvement réfléchi depuis son origine.
- **Vérités** : V72
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `invertedPairAt_coordinate_le_zero._proof_1_1`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `reflectedFromOrigin_never_reaches_expectedMinimum` — `Tower.ReflectedMotion` l.167 — RÉFUTATION COMPILÉE (réfute l'hypothèse `hReaches` — « le mouvement réfléchi depuis son origine atteint p_min(z*) » — du schéma de la piste `terminalCollision_conditional_on_reflectedObligation`, CLAUDE.md §4 ; réfutation citée par `Terminal/ReverseEngineeredClosure.lean`)
- **Énoncé** : Le mouvement réfléchi du membre miroir, suivi depuis son origine (j ≥ 1), n'atteint jamais le minimum attendu du miroir p_min(z*), inconditionnellement.
- **Vérités** : V72, V96, V139
- **Repose sur** : théorèmes : `reflected_no_stop_event`, `expectedMinimumPrime_prime`; définitions/structures : `TrueZero`, `expectedMinimumPrime`, `mirrorMember`, `reflectedIncidence`. Base rhv3 : aucun.
- **Entraîne** (5) : `arithmeticChain_and_reflectedFromOrigin_coexist`, `properTowerOfMirror_and_reflectedMotion_coexist`, `reflectedFromOrigin_never_reaches_expectedMinimum_beta_blind`, `reflectedStopSet_own_expectedMinimum_eq_empty`, `terminalCollision_conditional_on_reflectedObligation`.

#### `reflectedFromOrigin_never_reaches_expectedMinimum_beta_blind` — `Tower.ReflectedMotion` l.177 — CONFIRMÉE SOUS CONDITION (β = 1/2)
- **Énoncé** : Même énoncé restreint à un zéro sur la droite (β = 1/2) : le fait est aveugle à β.
- **Vérités** : V72, V96
- **Repose sur** : théorèmes : `reflectedFromOrigin_never_reaches_expectedMinimum`; définitions/structures : `TrueZero`, `expectedMinimumPrime`, `mirrorMember`, `reflectedIncidence`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `reflectedStopSet_own_expectedMinimum_eq_empty` — `Tower.ReflectedMotion` l.201 — RÉFUTATION COMPILÉE (l'ensemble d'arrêt supposé non vide par la transposition de `pivotCoordinate_isLeast` à l'objet réfléchi est vide ; piste « réarchitecture », CLAUDE.md §4)
- **Énoncé** : L'ensemble des coordonnées j où le mouvement réfléchi du miroir atteint p_min(z*) est vide.
- **Vérités** : V72, V96
- **Repose sur** : théorèmes : `reflectedFromOrigin_never_reaches_expectedMinimum`; définitions/structures : `TrueZero`, `expectedMinimumPrime`, `mirrorMember`, `reflectedIncidence`, `reflectedStopSet_own_expectedMinimum_eq_empty._simp_1_1`. Base rhv3 : aucun.
- **Entraîne** (1) : `no_reflectedStopCoordinate_own_expectedMinimum`.

#### `no_reflectedStopCoordinate_own_expectedMinimum` — `Tower.ReflectedMotion` l.212 — RÉFUTATION COMPILÉE (aucune coordonnée d'arrêt `IsLeast` n'existe pour le mouvement réfléchi visant p_min(z*) ; piste « réarchitecture », CLAUDE.md §4)
- **Énoncé** : Le mouvement réfléchi du miroir n'a aucune coordonnée d'arrêt (plus petit j) visant p_min(z*).
- **Vérités** : V72, V96
- **Repose sur** : théorèmes : `reflectedStopSet_own_expectedMinimum_eq_empty`; définitions/structures : `TrueZero`, `expectedMinimumPrime`, `mirrorMember`, `reflectedIncidence`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `ReflectedMotion.phase_eq` — `Tower.ReflectedMotion` l.234 — CONFIRMÉE
- **Énoncé** : (Champ de structure) la phase du mouvement réfléchi est arctan(−T/β).
- **Vérités** : V80
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `ReflectedMotion`, `ReflectedMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`.
- **Entraîne** (0) : aucun théorème du projet.

#### `ReflectedMotion.logIncidence_eq` — `Tower.ReflectedMotion` l.235 — CONFIRMÉE
- **Énoncé** : (Champ de structure) le log-rayon de coordonnée j du mouvement réfléchi vaut (phase + jπ)/(−T).
- **Vérités** : V80
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `ReflectedMotion`, `ReflectedMotion.logIncidence`, `ReflectedMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `ReflectedMotion.incidence_eq` — `Tower.ReflectedMotion` l.237 — CONFIRMÉE
- **Énoncé** : (Champ de structure) le rayon de coordonnée j du mouvement réfléchi est l'exponentielle de son log-rayon.
- **Vérités** : V80
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `ReflectedMotion`, `ReflectedMotion.incidence`, `ReflectedMotion.logIncidence`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `reflectedMotion_incidence` — `Tower.ReflectedMotion` l.248 — CONFIRMÉE
- **Énoncé** : Le rayon de coordonnée j du mouvement réfléchi de w est le rayon de la Tour propre à la coordonnée −j.
- **Vérités** : V34, V80
- **Repose sur** : théorèmes : `reflectedIncidence_eq`; définitions/structures : `TrueZero`, `ReflectedMotion.incidence`, `reflectedMotionOf`, `TowerMotion.incidence`, `towerMotionOf`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `reflectedZero_support` — `Tower.ReflectedMotion` l.254 — CONFIRMÉE
- **Énoncé** : Le support du zéro réfléchi de z est le conjugué du support de son miroir supérieur.
- **Vérités** : V63, V80
- **Repose sur** : théorèmes : `functionalReflect_support_eq_conj_mirror`; définitions/structures : `TrueZero`, `zetaFunctionalReflect`, `mirrorMember`. Base rhv3 : `RHV3Lean.cZeroSupport`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (2) : `quartet_chain`, `reflected_transition_content`.

#### `reflectedZero_isZero` — `Tower.ReflectedMotion` l.259 — CONFIRMÉE
- **Énoncé** : Le zéro réfléchi de z est un zéro non trivial de zêta.
- **Vérités** : V63, V62
- **Repose sur** : théorèmes : `zeta_functionalReflect_zero`; définitions/structures : `TrueZero`, `zetaFunctionalReflect`. Base rhv3 : `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.cZeroSupport`, `RHV3Lean.TNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `reflectedZero_re` — `Tower.ReflectedMotion` l.264 — CONFIRMÉE
- **Énoncé** : La partie réelle du zéro réfléchi est 1−β, celle du miroir supérieur.
- **Vérités** : V80, V63
- **Repose sur** : théorèmes : `functionalReflect_re_eq_mirror`; définitions/structures : `TrueZero`, `zetaFunctionalReflect`, `mirrorMember`. Base rhv3 : `RHV3Lean.cZeroSupport`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`.
- **Entraîne** (0) : aucun théorème du projet.

#### `reflectedZero_im` — `Tower.ReflectedMotion` l.269 — CONFIRMÉE
- **Énoncé** : La partie imaginaire du zéro réfléchi est −T (opposée à celle du miroir supérieur).
- **Vérités** : V80, V63
- **Repose sur** : théorèmes : `functionalReflect_im_eq_neg_mirror`; définitions/structures : `TrueZero`, `zetaFunctionalReflect`, `mirrorMember`. Base rhv3 : `RHV3Lean.cZeroSupport`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroHeight`.
- **Entraîne** (1) : `reflectedZero_not_member`.


##### Module `RHV6Fresh.Tower.TrueTower` (9 théorèmes)

#### `TowerMotion.phase_eq` — `Tower.TrueTower` l.27 — CONFIRMÉE
- **Énoncé** : (Champ de structure) la phase du mouvement de la Tour est arctan(T/β).
- **Vérités** : V16, V15
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `TowerMotion`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`.
- **Entraîne** (3) : `TrueTower.incidence_eq_motion`, `TrueTower.phase_eq_motion`, `towerMotion_phase`.

#### `TowerMotion.logIncidence_eq` — `Tower.TrueTower` l.29 — CONFIRMÉE
- **Énoncé** : (Champ de structure) le log-rayon de coordonnée k vaut (phase + kπ)/T.
- **Vérités** : V16, V17
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `TowerMotion`, `TowerMotion.logIncidence`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (9) : `TrueTower.incidence_eq_motion`, `contactAt_tangent_minus`, `contactAt_tangent_plus`, `mirror_step_positive`, `reflectedLogIncidence_eq`, `reflected_lastRay_lt_one`, `towerMotion_consecutive_width`, `towerMotion_incidence`, `towerMotion_ringJump_logWidth`.

#### `TowerMotion.incidence_eq` — `Tower.TrueTower` l.31 — CONFIRMÉE
- **Énoncé** : (Champ de structure) le rayon de coordonnée k est l'exponentielle de son log-rayon.
- **Vérités** : V16
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `TowerMotion`, `TowerMotion.incidence`, `TowerMotion.logIncidence`. Base rhv3 : aucun.
- **Entraîne** (8) : `TrueTower.incidence_eq_motion`, `contactAt_tangent_minus`, `contactAt_tangent_plus`, `logIncidence_eq_origin_add_halfTurns`, `reflectedIncidence_eq`, `towerMotion_consecutive_width`, `towerMotion_incidence`, `towerMotion_incidence_positive`.

#### `towerMotion_phase` — `Tower.TrueTower` l.42 — CONFIRMÉE
- **Énoncé** : La phase de la Tour propre de z vaut arctan(T/β), déduite du seul couple (β,T).
- **Vérités** : V15, V16
- **Repose sur** : théorèmes : `TowerMotion.phase_eq`; définitions/structures : `TrueZero`, `TowerMotion.phase`, `towerMotionOf`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`.
- **Entraîne** (21) : `TrueTower.incidence_eq_motion`, `TrueTower.phase_eq_motion`, `contactAt_tangent_minus`, `contactAt_tangent_plus`, `contactMinusAt_eq_exp`, `contactMinus_eq_iff_radial_eq`, `cos_phase_eq`, `grids_never_coincide`, `insertionDepth_eq`, `mirrorMember_phase`, `mirror_contacts_interlace`, `mirror_phase` et 9 autres.

#### `towerMotion_incidence` — `Tower.TrueTower` l.47 — CONFIRMÉE
- **Énoncé** : Le rayon de coordonnée k vaut exp((phase + kπ)/T) : suite de rayons déterminée par le zéro seul.
- **Vérités** : V15, V23, V16
- **Repose sur** : théorèmes : `TowerMotion.incidence_eq`, `TowerMotion.logIncidence_eq`; définitions/structures : `TrueZero`, `TowerMotion.incidence`, `towerMotionOf`, `TowerMotion.phase`, `TowerMotion.logIncidence`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (18) : `TrueTower.incidence_eq_motion`, `canonicalOrigin_eq`, `contactMinusAt_eq_exp`, `contactMinus_eq_iff_radial_eq`, `crossing_argument`, `grids_never_coincide`, `incidence_neg_one_lt_one`, `mirrorMember_contactMinusAt`, `mirrorMember_contactPlusAt`, `mirror_contact_ratio_const`, `mirror_contacts_interlace`, `mirror_relative_position` et 6 autres.

#### `towerMotion_incidence_positive` — `Tower.TrueTower` l.53 — CONFIRMÉE
- **Énoncé** : Tout rayon de la Tour propre est strictement positif.
- **Vérités** : V16
- **Repose sur** : théorèmes : `TowerMotion.incidence_eq`; définitions/structures : `TrueZero`, `TowerMotion.incidence`, `towerMotionOf`, `TowerMotion.logIncidence`. Base rhv3 : aucun.
- **Entraîne** (3) : `canonicalOrigin_pos`, `contactMinusAt_positive`, `contactPlusAt_positive`.

#### `towerMotion_consecutive_width` — `Tower.TrueTower` l.58 — CONFIRMÉE
- **Énoncé** : Le pas de log-rayon entre deux rayons consécutifs vaut π/T (ne dépend que de T).
- **Vérités** : V17
- **Repose sur** : théorèmes : `TowerMotion.incidence_eq`, `TowerMotion.logIncidence_eq`; définitions/structures : `TrueZero`, `TowerMotion.incidence`, `towerMotionOf`, `TowerMotion.logIncidence`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (3) : `contactAt_consecutive_logWidth`, `halfTurn_logStep`, `ray_energy_growth`.

#### `towerMotion_incidence_strictOrder` — `Tower.TrueTower` l.70 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : k < l)
- **Énoncé** : Les rayons de la Tour propre sont strictement croissants avec la coordonnée.
- **Vérités** : V16
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `TowerMotion.incidence`, `towerMotionOf`. Base rhv3 : `RHV3Lean.thm_rTowerIncidence_strictOrder`.
- **Entraîne** (4) : `contactAt_ordered`, `countedPrimeAt_mono_oriented`, `towerMotion_incidence_lt_iff`, `towerMotion_incidence_mono`.

#### `towerMotion_ringJump_logWidth` — `Tower.TrueTower` l.76 — CONFIRMÉE
- **Énoncé** : Le log-rayon entre deux coordonnées k₀ et k₁ diffère de (k₁−k₀)·π/T.
- **Vérités** : V17
- **Repose sur** : théorèmes : `TowerMotion.logIncidence_eq`; définitions/structures : `TrueZero`, `TowerMotion.logIncidence`, `towerMotionOf`, `TowerMotion.phase`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (1) : `logIncidence_eq_origin_add_halfTurns`.


##### Module `RHV6Fresh.Tower.TrueTowerStructure` (6 théorèmes)

#### `towerMotion_subsingleton` — `Tower.TrueTowerStructure` l.28 — CONFIRMÉE
- **Énoncé** : Le mouvement de la Tour propre est unique : tous ses champs sont fixés par z.
- **Vérités** : V15, V24
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `TowerMotion`, `TowerMotion.casesOn`, `TowerMotion.mk`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroRadialPosition`.
- **Entraîne** (2) : `TrueTower.ext_pair`, `TrueTower.toTowerMotion_eq`.

#### `TrueTower.toTowerMotion_eq` — `Tower.TrueTowerStructure` l.41 — CONFIRMÉE
- **Énoncé** : Le mouvement porté par toute Tour propre est le mouvement canonique du zéro.
- **Vérités** : V15, V24
- **Repose sur** : théorèmes : `towerMotion_subsingleton`; définitions/structures : `TrueZero`, `TrueTower`, `TowerMotion`, `TrueTower.toTowerMotion`, `towerMotionOf`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.

#### `AnalyticContactPair.ext_contacts` — `Tower.TrueTowerStructure` l.44 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : mêmes contacts d'entrée et de dernier rayon)
- **Énoncé** : Une paire de contacts (état propre) est déterminée par ses deux contacts.
- **Vérités** : V46, V26
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.entryContact`, `AnalyticContactPair.lastRayContact`, `AnalyticContactPair.casesOn`, `AnalyticContactPair.mk`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rTowerPhase`.
- **Entraîne** (2) : `AnalyticContactPair.eq_analyticPairAt_of_one_stage`, `AnalyticContactPair.ext_readings`.

#### `AnalyticContactPair.ext_readings` — `Tower.TrueTowerStructure` l.52 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : mêmes lectures)
- **Énoncé** : Une paire de contacts est déterminée par ses deux lectures (coordonnée d'entrée, nombre d'étages).
- **Vérités** : V43, V46
- **Repose sur** : théorèmes : `AnalyticContactPair.ext_contacts`, `AnalyticContactPair.entryContact_eq_incidence`, `AnalyticContactPair.lastRayContact_eq_incidence`; définitions/structures : `TrueZero`, `AnalyticContactPair`, `AnalyticContactPair.entryCoordinate`, `AnalyticContactPair.stageCount`, `AnalyticContactPair.entryContact`, `AnalyticContactPair.lastRayContact`. Base rhv3 : `RHV3Lean.rTowerIncidence`.
- **Entraîne** (1) : `TrueTower.readings_injective`.

#### `TrueTower.ext_pair` — `Tower.TrueTowerStructure` l.60 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : mêmes paires portées)
- **Énoncé** : Une Tour propre est déterminée par sa paire de contacts.
- **Vérités** : V15, V46
- **Repose sur** : théorèmes : `towerMotion_subsingleton`; définitions/structures : `TrueZero`, `TrueTower`, `AnalyticContactPair`, `TrueTower.toAnalyticContactPair`, `TrueTower.casesOn`, `TowerMotion`, `TrueTower.mk`. Base rhv3 : aucun.
- **Entraîne** (1) : `TrueTower.readings_injective`.

#### `TrueTower.readings_injective` — `Tower.TrueTowerStructure` l.70 — CONFIRMÉE
- **Énoncé** : Les lectures (coordonnée d'entrée, nombre d'étages) identifient une Tour propre.
- **Vérités** : V43, V15
- **Repose sur** : théorèmes : `TrueTower.ext_pair`, `AnalyticContactPair.ext_readings`; définitions/structures : `TrueZero`, `TrueTower`, `AnalyticContactPair.entryCoordinate`, `TrueTower.toAnalyticContactPair`, `AnalyticContactPair.stageCount`. Base rhv3 : aucun.
- **Entraîne** (0) : aucun théorème du projet.


##### Module `RHV6Fresh.Voyage.FiberSuccessor` (3 théorèmes)

#### `exists_fiberSuccessor` — `Voyage.FiberSuccessor` l.21 — CONFIRMÉE SOUS CONDITION (zéro de côté bas (β<1/2))
- **Énoncé** : Pour un zéro de côté bas, il existe un vrai zéro de même hauteur consécutif à z dans l'ordre des membres.
- **Vérités** : V50, V66, V68
- **Repose sur** : théorèmes : `mirrorMember_ordinate`, `mirror_precedes`; définitions/structures : `TrueZero`, `mirrorMember`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroHeight`, `RHV3Lean.PZeroMembersConsecutive`, `RHV3Lean.PZeroMemberPrecedes`, `RHV3Lean.sZeroHeightFiber`, `RHV3Lean.thm_zeroHeightFiber_finite`, `RHV3Lean.fnZeroOrderKey`, `RHV3Lean.thm_sameFiberInterposition`.
- **Entraîne** (0) : aucun théorème du projet.

#### `fiberSuccessor_radial_gt` — `Voyage.FiberSuccessor` l.46 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : z' de même hauteur ; z' consécutif à z)
- **Énoncé** : Un successeur consécutif de même hauteur est strictement plus à droite (β(z)<β(z')).
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`. Base rhv3 : `RHV3Lean.rZeroHeight`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.PZeroMembersConsecutive`, `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.PZeroMemberPrecedes`, `RHV3Lean.thm_zeroMemberPrecedes_iff_height_radial_lex`.
- **Entraîne** (1) : `radial_gt_of_consecutive_lowerSide`.

#### `fiberSuccessor_radial_le_mirror` — `Voyage.FiberSuccessor` l.58 — CONFIRMÉE SOUS CONDITION (zéro de côté bas) (autres hypothèses : antécédents de la relation énoncée ou conditions de domaine : z' de même hauteur ; z' consécutif)
- **Énoncé** : Un successeur consécutif de même hauteur ne dépasse pas le miroir (β(z') ≤ 1−β(z)).
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : `mirror_precedes`, `mirrorMember_ordinate`, `mirrorMember_radial`; définitions/structures : `TrueZero`, `mirrorMember`. Base rhv3 : `RHV3Lean.rZeroRadialPosition`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.rZeroHeight`, `RHV3Lean.PZeroMembersConsecutive`, `RHV3Lean.PZeroMemberPrecedes`, `RHV3Lean.thm_zeroMemberPrecedes_iff_height_radial_lex`.
- **Entraîne** (1) : `radial_le_mirror_of_consecutive_lowerSide`.


##### Module `RHV6Fresh.Voyage.Progression` (4 théorèmes)

#### `progression_occurrence` — `Voyage.Progression` l.25 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : passage consécutif)
- **Énoncé** : Progression obligatoire : sur tout passage consécutif, l'occurrence du membre postérieur est exactement le minimum attendu du membre antérieur.
- **Vérités** : V54, V56, V144
- **Repose sur** : théorèmes : `expectedMinimumPrime_eq_laterOccurrence`; définitions/structures : `TrueZero`, `occurrence`, `expectedMinimumPrime`, `passageOf`. Base rhv3 : `RHV3Lean.PZeroMembersConsecutive`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.TZeroPassage.zEarlierMember`, `RHV3Lean.TZeroPassage.zLaterMember`.
- **Entraîne** (6) : `countedPrime_ne_expected_iff_cell`, `expectedMinimum_eq_mirror_occurrence_of_consecutive`, `mirror_sourceIndex_of_consecutive`, `reached_progression`, `reaches_expected_of_reaches_occurrence`, `reads_expected_imp_ne_previous_expected`.

#### `progression_strict` — `Voyage.Progression` l.32 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : passage consécutif)
- **Énoncé** : L'occurrence avance strictement sur tout passage consécutif.
- **Vérités** : V56, V150
- **Repose sur** : théorèmes : `occurrence_strict_of_passage`; définitions/structures : `TrueZero`, `occurrence`, `passageOf`. Base rhv3 : `RHV3Lean.PZeroMembersConsecutive`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (0) : aucun théorème du projet.

#### `expectedMinimum_eq_succ_occurrence` — `Voyage.Progression` l.38 — CONFIRMÉE
- **Énoncé** : Le minimum attendu d'un membre est le premier qui suit son occurrence : q(a) = p_{n(a)+1}.
- **Vérités** : V54, V27
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `expectedMinimumPrime`. Base rhv3 : `RHV3Lean.fnPrimeSuccessor`, `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`.
- **Entraîne** (2) : `mirror_continuous_progression_pos`, `off_consecutive_continuous_progression_eq_span`.

#### `occurrence_eq_primeAtRank` — `Voyage.Progression` l.43 — CONFIRMÉE
- **Énoncé** : L'occurrence d'un zéro est le premier de rang égal à son index zéro-source.
- **Vérités** : V27, V49
- **Repose sur** : théorèmes : `occurrence_eq_canonicalAnchor`; définitions/structures : `TrueZero`, `occurrence`. Base rhv3 : `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.nMemberCanonicalAnchor`.
- **Entraîne** (12) : `InvertedContactPair.reaches_occurrence_iff`, `countedPrime_eq_occurrence_iff`, `countedPrime_eq_occurrence_iff_cell`, `expectedMinimum_le_mirror_occurrence`, `memberTransition_eq_canonical`, `mirror_continuous_progression_pos`, `mirror_occurrence_strict`, `mirror_sourceIndex_of_consecutive`, `occurrence_prime`, `off_consecutive_continuous_progression_eq_span`, `passage_raccords`, `reaches_occurrence_iff`.


##### Module `RHV6Fresh.Voyage.TowerReading` (9 théorèmes)

#### `producedPrime_eq_vonMangoldt` — `Voyage.TowerReading` l.27 — CONFIRMÉE
- **Énoncé** : Le premier produit par un état harmonique de Tour de la base est le premier de rang π(⌊contact supérieur⌋)−1 (comptage Chebyshev/Von Mangoldt).
- **Vérités** : V145, V52
- **Repose sur** : théorèmes : `primeCountAtStateUpper_eq_vonMangoldt`; définitions/structures : `TrueZero`, `producedPrime`, `lastPrimeAtStateUpper`, `primeCountAtStateUpper`. Base rhv3 : `RHV3Lean.TTrueHarmonicTowerState`, `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.nPrimeCountingFromJ`, `RHV3Lean.rChebyshevJNat`, `RHV3Lean.TTrueHarmonicTowerState.contactPlus`.
- **Entraîne** (1) : `countedPrimeAt_eq_vonMangoldt`.

#### `producedPrime_prime` — `Voyage.TowerReading` l.33 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : compte au contact supérieur > 0)
- **Énoncé** : Le premier produit par un état de Tour à compte positif est un nombre premier.
- **Vérités** : V52, V145
- **Repose sur** : théorèmes : `lastPrimeAtStateUpper_prime`; définitions/structures : `TrueZero`, `primeCountAtStateUpper`, `producedPrime`. Base rhv3 : `RHV3Lean.TTrueHarmonicTowerState`.
- **Entraîne** (0) : aucun théorème du projet.

#### `primeCountAtStateUpper_mono` — `Voyage.TowerReading` l.37 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : contact supérieur de S ≤ celui de S')
- **Énoncé** : Le comptage au contact supérieur est monotone en ce contact.
- **Vérités** : V52
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `primeCountAtStateUpper`, `primeCountAtStateUpper_mono._proof_1_1`. Base rhv3 : `RHV3Lean.TTrueHarmonicTowerState`, `RHV3Lean.TTrueHarmonicTowerState.contactPlus`, `RHV3Lean.nEdgePrimeRank`.
- **Entraîne** (1) : `producedPrime_mono`.

#### `producedPrime_mono` — `Voyage.TowerReading` l.47 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : contact supérieur de S ≤ celui de S')
- **Énoncé** : Le premier produit est monotone en le contact supérieur.
- **Vérités** : V52
- **Repose sur** : théorèmes : `primeCountAtStateUpper_mono`; définitions/structures : `TrueZero`, `producedPrime`, `lastPrimeAtStateUpper`, `primeCountAtStateUpper`. Base rhv3 : `RHV3Lean.TTrueHarmonicTowerState`, `RHV3Lean.TTrueHarmonicTowerState.contactPlus`, `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.thm_primeAtRank_strictMono`.
- **Entraîne** (1) : `countedPrimeAt_mono_oriented`.

#### `primeCountAtStateUpper_pos_of_two_le` — `Voyage.TowerReading` l.56 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : contact supérieur ≥ 2)
- **Énoncé** : Une cellule dont le contact supérieur atteint 2 compte au moins un premier.
- **Vérités** : V52
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `primeCountAtStateUpper`, `primeCountAtStateUpper_pos_of_two_le._proof_1_1`. Base rhv3 : `RHV3Lean.TTrueHarmonicTowerState`, `RHV3Lean.TTrueHarmonicTowerState.contactPlus`, `RHV3Lean.nEdgePrimeRank`, `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.thm_edgeRank_le_iff_lt_primeAtRank`, `RHV3Lean.TTrueHarmonicTowerState.contactPlus_pos`, `RHV3Lean.thm_primeAtRank_zero_eq_two`.
- **Entraîne** (0) : aucun théorème du projet.

#### `three_le_expectedMinimumPrime` — `Voyage.TowerReading` l.68 — CONFIRMÉE
- **Énoncé** : Le minimum attendu de tout zéro est au moins 3.
- **Vérités** : `AJOUT` (aucune Vi)
- **Repose sur** : théorèmes : aucun; définitions/structures : `TrueZero`, `expectedMinimumPrime`, `three_le_expectedMinimumPrime._proof_1_1`. Base rhv3 : `RHV3Lean.fnPrimeSuccessor`, `RHV3Lean.nZeroSourceIndex`, `RHV3Lean.TNonTrivialZetaZero`, `RHV3Lean.PIsNonTrivialZetaZero`, `RHV3Lean.fnPrimeAtRank`.
- **Entraîne** (2) : `count_pos_of_reaches`, `countedPrimeAt_lt_expected_of_contact`.

#### `count_pos_of_reaches` — `Voyage.TowerReading` l.74 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : p_min(a) ≤ premier produit)
- **Énoncé** : Atteindre un minimum attendu force un comptage positif.
- **Vérités** : V52, V54
- **Repose sur** : théorèmes : `three_le_expectedMinimumPrime`; définitions/structures : `TrueZero`, `expectedMinimumPrime`, `producedPrime`, `primeCountAtStateUpper`, `count_pos_of_reaches._proof_1_1`, `lastPrimeAtStateUpper`, `count_pos_of_reaches._proof_1_2`. Base rhv3 : `RHV3Lean.TTrueHarmonicTowerState`, `RHV3Lean.fnPrimeAtRank`, `RHV3Lean.thm_primeAtRank_zero_eq_two`.
- **Entraîne** (0) : aucun théorème du projet.

#### `expectedMinimum_le_produced_iff` — `Voyage.TowerReading` l.88 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : compte > 0)
- **Énoncé** : À compte positif, le premier produit atteint p_min(a) exactement quand le contact supérieur l'atteint.
- **Vérités** : V52, V84
- **Repose sur** : théorèmes : `expectedMinimum_le_stateReadout_iff`; définitions/structures : `TrueZero`, `primeCountAtStateUpper`, `expectedMinimumPrime`, `producedPrime`. Base rhv3 : `RHV3Lean.TTrueHarmonicTowerState`, `RHV3Lean.TTrueHarmonicTowerState.contactPlus`.
- **Entraîne** (0) : aucun théorème du projet.

#### `produced_lt_expectedMinimum_iff` — `Voyage.TowerReading` l.96 — CONFIRMÉE (hypothèses : antécédent de la relation énoncée ou condition de domaine : compte > 0)
- **Énoncé** : À compte positif, le premier produit est sous p_min(a) exactement quand le contact supérieur l'est.
- **Vérités** : V52, V84
- **Repose sur** : théorèmes : `stateReadout_lt_expectedMinimum_iff`; définitions/structures : `TrueZero`, `primeCountAtStateUpper`, `producedPrime`, `expectedMinimumPrime`. Base rhv3 : `RHV3Lean.TTrueHarmonicTowerState`, `RHV3Lean.TTrueHarmonicTowerState.contactPlus`.
- **Entraîne** (2) : `countedPrimeAt_lt_expected_of_contact`, `mirror_counted_lt_expected_iff`.

### Lot B2 — B2 (Terminal actifs A–L)

##### `Terminal/ArithmeticClosure`

#### `expected_le_counted_lt_expected_false` — `Terminal/ArithmeticClosure` l.25 — CONFIRMÉE
- **Énoncé** : Deux entiers ne peuvent être à la fois ordonnés `p_attendu ≤ p_compté` et `p_compté < p_attendu` : lemme d'ordre sur ℕ, sans zéro ni Tour dans l'énoncé.
- **Vérités** : `AJOUT` (lemme d'ordre total sur ℕ, sans phrase correspondante dans le maître) | touche : V93 (le docstring le présente comme noyau arithmétique conservé du maître Lean §10 ; le graphe ne montre aucun théorème du projet qui l'utilise, `Entraîne` vide)
- **Repose sur** : (aucun) ; base rhv3 : (aucun)
- **Entraîne** : (aucun)


##### `Terminal/ConsecutiveChainContradiction`

#### `consecutivePairArithmeticChain` — `Terminal/ConsecutiveChainContradiction` l.39 — CONFIRMÉE SOUS CONDITION (zéro de côté bas, β < 1/2 ; consécutivité stricte du zéro et de son miroir)
- **Énoncé** : Sous consécutivité stricte d'un zéro de côté bas et de son miroir : la place du miroir est celle du zéro plus un, l'occurrence du miroir est exactement le minimum attendu du zéro, l'occurrence du zéro est strictement sous ce minimum attendu, et le minimum attendu du zéro est strictement sous celui du miroir (chaîne arithmétique).
- **Vérités** : V144, V69, V56 | touche : V54
- **Repose sur** : `TrueZero`, `mirrorMember`, `occurrence`, `expectedMinimumPrime`, `mirror_sourceIndex_of_consecutive`, `expectedMinimum_eq_mirror_occurrence_of_consecutive`, `occurrence_lt_expectedMinimumPrime`, `expectedMinimum_lt_mirror_expectedMinimum` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `PZeroMembersConsecutive`, `nZeroSourceIndex`
- **Entraîne** : `arithmeticChain_and_reflectedFromOrigin_coexist`, `secondTowerOwnContacts_meets_arithmeticChain`

#### `arithmeticChain_and_reflectedFromOrigin_coexist` — `Terminal/ConsecutiveChainContradiction` l.70 — CONFIRMÉE SOUS CONDITION (zéro de côté bas ; consécutivité stricte du zéro et de son miroir)
- **Énoncé** : Sous les mêmes conditions et pour tout `j`, deux faits coexistent : la partie de la chaîne arithmétique `Occ(z) < p_min(z) < p_min(z*)`, et la non-atteinte de `p_min(z*)` par le mouvement réfléchi du miroir à la coordonnée `j+1`. Terme habité : les deux conjoints ne se contredisent pas.
- **Vérités** : V144, V72 | touche : T6 (les deux descriptions de la seconde Tour) ; O23 (la contradiction « relationnelle » n'est pas établie par cette composition : le type est une conjonction, pas `False`)
- **Repose sur** : `TrueZero`, `mirrorMember`, `occurrence`, `expectedMinimumPrime`, `reflectedIncidence`, `consecutivePairArithmeticChain`, `reflectedFromOrigin_never_reaches_expectedMinimum` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `PZeroMembersConsecutive`, `nZeroSourceIndex`
- **Entraîne** : (aucun)

#### `terminalCollision_conditional_on_reflectedObligation` — `Terminal/ConsecutiveChainContradiction` l.86 — RÉFUTATION COMPILÉE
- **Énoncé** : Pour tout zéro `z`, il n'existe aucun `j` tel que le mouvement réfléchi du miroir atteigne son minimum attendu `p_min(z*)` à la coordonnée `j+1` : l'obligation « la seconde Tour atteint `p_min(z*)` par le mouvement réfléchi » est réfutée (l'hypothèse `∃ j …` conduit à `False`).
- **Vérités** : V96, V72 | touche : T6 ; O23 ; V106 (la contradiction relationnelle n'est compilée que sous la forme de ce schéma logique, dont la prémisse `∃ j` est réfutée). Nom promet plus que le type : « collision terminale » — le type n'énonce que la non-atteinte réfléchie (la preuve, d'après le graphe, n'emploie que `reflectedFromOrigin_never_reaches_expectedMinimum`)
- **Repose sur** : `TrueZero`, `expectedMinimumPrime`, `mirrorMember`, `reflectedIncidence`, `reflectedFromOrigin_never_reaches_expectedMinimum` ; base rhv3 : (aucun)
- **Entraîne** : `riemannHypothesis_of_hReaches_is_vacuous`

#### `properTowerOfMirror_and_reflectedMotion_coexist` — `Terminal/ConsecutiveChainContradiction` l.117 — CONFIRMÉE
- **Énoncé** : Pour tout zéro `z` (tout β) et tout `j` : la Tour propre du membre miroir contient son minimum attendu (`entrée < p_min(z*) ≤ dernier rayon`), ET le mouvement réfléchi du miroir n'atteint pas `p_min(z*)` à la coordonnée `j+1`. Les deux tiennent ensemble, sans aucune hypothèse.
- **Vérités** : V143, V72, V96 | touche : T6 ; T5 (deux sens de « atteindre » / de « seconde Tour ») ; V153 (constat numérique dont ceci est la face compilée : Tour propre du miroir atteint son pivot, mouvement réfléchi jamais)
- **Repose sur** : `TrueZero`, `AnalyticContactPair.entryContact`, `mirrorMember`, `TrueTower.toAnalyticContactPair`, `firstTowerOf`, `expectedMinimumPrime`, `AnalyticContactPair.lastRayContact`, `reflectedIncidence`, `firstTower_cell_contains_expected`, `reflectedFromOrigin_never_reaches_expectedMinimum` ; base rhv3 : (aucun)
- **Entraîne** : (aucun)

#### `secondTowerOwnContacts_meets_arithmeticChain` — `Terminal/ConsecutiveChainContradiction` l.157 — CONFIRMÉE SOUS CONDITION (zéro de côté bas ; consécutivité stricte du zéro et de son miroir)
- **Énoncé** : Sous ces conditions, l'entrée de la seconde Tour de `z` dépasse strictement l'occurrence du miroir, et son dernier rayon reste strictement sous le minimum attendu du miroir.
- **Vérités** : V144, V82 | touche : O11 (le type ne compare pas l'occurrence du miroir au dernier rayon de la seconde Tour : la lecture reste hors de cet énoncé) ; V85
- **Repose sur** : `TrueZero`, `mirrorMember`, `occurrence`, `InvertedContactPair.entryContact`, `InvertedTower.properState`, `secondTowerOf`, `InvertedContactPair.lastRayContact`, `expectedMinimumPrime`, `consecutivePairArithmeticChain`, `InvertedTower.toInvertedContactPair`, `secondTower_cell_contains_own_expected` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `PZeroMembersConsecutive`, `nZeroSourceIndex`
- **Entraîne** : (aucun)


##### `Terminal/ContinuousProgression`

#### `phase_increment_pos` — `Terminal/ContinuousProgression` l.37 — CONFIRMÉE
- **Énoncé** : Pour tout zéro et tout rang `n`, la progression continue (terme hors maître : accroissement `π·(position de Tour en p_{n+1} − position de Tour en p_n)`, noté ΔΘ_n) est strictement positive, sans hypothèse sur β.
- **Vérités** : `AJOUT` (positivité de la progression continue d'un événement)
- **Repose sur** : `TrueZero`, `towerPosition`, `phase_increment_eq_pi_span` ; base rhv3 : `fnPrimeSuccessor`, `fnPrimeAtRank`, `TowerPrimeGapSpan`, `rTowerHeight`, `rPrimeGapLogRatio`, `rZeroHeight`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `thm_upperZeroHeight_positive`, `thm_primeGapLogRatio_pos`
- **Entraîne** : `mirror_continuous_progression_pos`

#### `phase_increment_eq_of_sameHeight` — `Terminal/ContinuousProgression` l.51 — CONFIRMÉE (même hauteur ⟹ même ΔΘ_n : la relation énoncée)
- **Énoncé** : Deux zéros de même hauteur ont la même progression continue ΔΘ_n à tout rang `n` : elle ne dépend que de la hauteur et du rang, jamais de β.
- **Vérités** : V158 | touche : V17
- **Repose sur** : `TrueZero`, `towerPosition`, `phase_increment_eq_pi_span` ; base rhv3 : `rZeroHeight`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `fnPrimeSuccessor`, `fnPrimeAtRank`, `TowerPrimeGapSpan`, `rTowerHeight`, `rPrimeGapLogRatio`
- **Entraîne** : (aucun)

#### `primeSuccessor_le_two_mul` — `Terminal/ContinuousProgression` l.66 — CONFIRMÉE
- **Énoncé** : Sur l'histoire première, le premier de rang `n+1` est au plus le double du premier de rang `n` (borne de Bertrand).
- **Vérités** : `AJOUT` (borne de Bertrand sur l'histoire première)
- **Repose sur** : (aucun) ; base rhv3 : `fnPrimeSuccessor`, `fnPrimeAtRank`, `thm_primeAtRank_pos`
- **Entraîne** : `phase_increment_le_height_mul_log_two`

#### `phase_increment_le_height_mul_log_two` — `Terminal/ContinuousProgression` l.80 — CONFIRMÉE
- **Énoncé** : La progression continue ΔΘ_n d'un zéro est bornée par `T·log 2`, pour tout rang.
- **Vérités** : `AJOUT` (borne supérieure `T·log 2` de la progression continue)
- **Repose sur** : `TrueZero`, `towerPosition`, `primeSuccessor_le_two_mul`, `TowerMotion.phase`, `towerMotionOf`, `pi_mul_towerPosition` ; base rhv3 : `fnPrimeSuccessor`, `fnPrimeAtRank`, `rZeroHeight`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `thm_primeAtRank_pos`, `thm_upperZeroHeight_positive`
- **Entraîne** : `consecutive_continuous_signature`

#### `primeGap_ge_one` — `Terminal/ContinuousProgression` l.105 — CONFIRMÉE
- **Énoncé** : L'écart entre deux premiers consécutifs de l'histoire première est au moins 1, à tout rang.
- **Vérités** : `AJOUT` (restatement local d'un théorème de base (`thm_primeGap_positive`))
- **Repose sur** : (aucun) ; base rhv3 : `nPrimeGap`, `thm_primeGap_positive`
- **Entraîne** : `phase_increment_ge_height_mul_log_one_add_inv`

#### `primeGap_ge_two_of_two_lt` — `Terminal/ContinuousProgression` l.110 — CONFIRMÉE (`p_n > 2` : condition de domaine)
- **Énoncé** : Au-delà du premier 2, l'écart entre deux premiers consécutifs est au moins 2 (écart pair non nul).
- **Vérités** : `AJOUT` (écart minimal 2 après le premier premier)
- **Repose sur** : (aucun) ; base rhv3 : `fnPrimeAtRank`, `nPrimeGap`, `fnPrimeSuccessor`, `thm_primeAtRank_lt_successor`, `thm_primeAtRank_isPrime`, `thm_primeGap_positive`
- **Entraîne** : `phase_increment_ge_height_mul_log_one_add_two_div`

#### `phase_increment_ge_height_mul_log_one_add_inv` — `Terminal/ContinuousProgression` l.130 — CONFIRMÉE
- **Énoncé** : La progression continue ΔΘ_n est au moins `T·log(1 + 1/p_n)` : plancher qui se contracte avec `p_n`.
- **Vérités** : `AJOUT` (plancher mobile de la progression continue)
- **Repose sur** : `TrueZero`, `towerPosition`, `primeGap_ge_one`, `phase_increment_eq_pi_span` ; base rhv3 : `rZeroHeight`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `fnPrimeAtRank`, `fnPrimeSuccessor`, `thm_primeAtRank_pos`, `thm_upperZeroHeight_positive`, `nPrimeGap`, `rPrimeGapLogRatio`, `thm_primeGapLogRatio_eq_log_one_add` et 2 autres
- **Entraîne** : (aucun)

#### `phase_increment_ge_height_mul_log_one_add_two_div` — `Terminal/ContinuousProgression` l.154 — CONFIRMÉE (`p_n > 2` : condition de domaine)
- **Énoncé** : Au-delà du premier 2, la progression continue ΔΘ_n est au moins `T·log(1 + 2/p_n)`.
- **Vérités** : `AJOUT` (plancher renforcé de la progression continue après le premier 2)
- **Repose sur** : `TrueZero`, `towerPosition`, `primeGap_ge_two_of_two_lt`, `phase_increment_eq_pi_span` ; base rhv3 : `fnPrimeAtRank`, `rZeroHeight`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `fnPrimeSuccessor`, `thm_primeAtRank_pos`, `thm_upperZeroHeight_positive`, `nPrimeGap`, `rPrimeGapLogRatio`, `thm_primeGapLogRatio_eq_log_one_add` et 2 autres
- **Entraîne** : (aucun)

#### `height_lower_bound_of_phase_quantum` — `Terminal/ContinuousProgression` l.180 — CONFIRMÉE (implication : minorant local de ΔΘ_n ⟹ borne locale de T ; `c` n'est pas une prémisse globale)
- **Énoncé** : Si `c ≤ ΔΘ_n` pour un zéro et un rang donnés, alors `c / log(p_{n+1}/p_n) ≤ T` : borne inférieure locale sur la hauteur (terme hors maître : « quantum de phase », `c` n'est pas une prémisse globale).
- **Vérités** : `AJOUT` (borne locale de la hauteur déduite d'un minorant local de la progression continue)
- **Repose sur** : `TrueZero`, `towerPosition`, `phase_increment_eq_pi_span` ; base rhv3 : `fnPrimeSuccessor`, `fnPrimeAtRank`, `rPrimeGapLogRatio`, `rZeroHeight`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `thm_primeGapLogRatio_pos`, `TowerPrimeGapSpan`
- **Entraîne** : (aucun)

#### `quantum_pair_satisfiable_at_same_height` — `Terminal/ContinuousProgression` l.201 — CONFIRMÉE
- **Énoncé** : Pour tout réel `c` et tout rang `n`, il existe un seuil `T₀` au-delà duquel une seule hauteur `T` satisfait `c ≤ T·log ratio(n)` et `c ≤ T·log ratio(n+1)` : une seule hauteur suffit aux deux arêtes consécutives.
- **Vérités** : `AJOUT` (un seuil de hauteur satisfait deux arêtes consécutives d'un minorant de progression)
- **Repose sur** : (aucun) ; base rhv3 : `rPrimeGapLogRatio`, `thm_primeGapLogRatio_pos`
- **Entraîne** : (aucun)

#### `mirror_continuous_progression_pos` — `Terminal/ContinuousProgression` l.220 — CONFIRMÉE
- **Énoncé** : La progression continue du second événement du miroir (de son occurrence à son minimum attendu) est strictement positive, pour tout zéro, sans hypothèse.
- **Vérités** : `AJOUT` (positivité de la progression continue du membre miroir)
- **Repose sur** : `TrueZero`, `towerPosition`, `mirrorMember`, `expectedMinimumPrime`, `occurrence`, `expectedMinimum_eq_succ_occurrence`, `occurrence_eq_primeAtRank`, `phase_increment_pos` ; base rhv3 : `fnPrimeSuccessor`, `nZeroSourceIndex`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `fnPrimeAtRank`
- **Entraîne** : `consecutive_continuous_signature`

#### `off_consecutive_continuous_progression_eq_span` — `Terminal/ContinuousProgression` l.234 — CONFIRMÉE SOUS CONDITION (consécutivité stricte du zéro et de son miroir)
- **Énoncé** : Sous consécutivité stricte, la progression continue du second événement du miroir vaut exactement `π` fois la portée première (terme hors maître) du rang `n(z)+1` du zéro `z` : une fonction de la hauteur et du rang seuls.
- **Vérités** : `AJOUT` (valeur exacte de la progression continue du second événement du miroir) | touche : V158
- **Repose sur** : `TrueZero`, `mirrorMember`, `towerPosition`, `expectedMinimumPrime`, `occurrence`, `expectedMinimum_eq_succ_occurrence`, `occurrence_eq_primeAtRank`, `phase_increment_eq_pi_span`, `mirror_sourceIndex_of_consecutive`, `mirror_span_eq` ; base rhv3 : `PZeroMembersConsecutive`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `TowerPrimeGapSpan`, `nZeroSourceIndex`, `fnPrimeSuccessor`, `fnPrimeAtRank`
- **Entraîne** : `consecutive_continuous_signature`

#### `consecutive_continuous_signature` — `Terminal/ContinuousProgression` l.251 — CONFIRMÉE SOUS CONDITION (consécutivité stricte du zéro et de son miroir)
- **Énoncé** : Sous consécutivité stricte : la place du miroir avance de un, la hauteur du miroir est celle du zéro, la progression continue du second événement est strictement positive, elle vaut `T·log(p_{n+2}/p_{n+1})` (fonction de `(T, n)` seuls) et elle est bornée par `T·log 2`.
- **Vérités** : V56, V65 ; `AJOUT` (valeur et borne de la progression continue du second événement) | touche : signature de la progression continue : partie AJOUT (valeur exacte et borne)
- **Repose sur** : `TrueZero`, `mirrorMember`, `towerPosition`, `expectedMinimumPrime`, `occurrence`, `mirror_sourceIndex_of_consecutive`, `mirrorMember_ordinate`, `mirror_continuous_progression_pos`, `off_consecutive_continuous_progression_eq_span`, `phase_increment_eq_pi_span`, `phase_increment_le_height_mul_log_two` ; base rhv3 : `PZeroMembersConsecutive`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `nZeroSourceIndex`, `rZeroHeight`, `rPrimeGapLogRatio`, `TowerPrimeGapSpan`, `rTowerHeight`, `fnPrimeSuccessor`, `fnPrimeAtRank`
- **Entraîne** : (aucun)

#### `mirror_translation_over_next_progression_lt` — `Terminal/ContinuousProgression` l.287 — CONFIRMÉE SOUS CONDITION (zéro de côté bas (β < 1/2) ; consécutivité stricte)
- **Énoncé** : Sous ces conditions, pour tout `q > 0`, la translation miroir (terme hors maître) `π·(θ(z*,q) − θ(z,q))` divisée par `π·portée(z, n(z)+1)` est strictement majorée par `(1−2β)/(T²·log ratio(n(z)+1))`.
- **Vérités** : `AJOUT` (rapport entre translation miroir et progression continue suivante) | touche : docstring cite `phase_increment_eq_pi_span`, absent de `deps_project` (la portée figure directement dans le type)
- **Repose sur** : `TrueZero`, `mirrorMember`, `towerPosition`, `mirror_translation_lt` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `PZeroMembersConsecutive`, `TowerPrimeGapSpan`, `nZeroSourceIndex`, `rZeroHeight`, `rPrimeGapLogRatio`, `thm_primeGapLogRatio_pos`, `rTowerHeight`
- **Entraîne** : (aucun)


##### `Terminal/EnergyIdentity`

#### `geometry_selects_raccord_prime` — `Terminal/EnergyIdentity` l.32 — CONFIRMÉE
- **Énoncé** : Sur tout passage (hauteurs positives : condition de domaine), l'occurrence du membre postérieur est le minimum attendu de l'antérieur ; chacun des deux minimums attendus (`p_min(e)`, `p_min(l)`) est encadré par les deux contacts de la cellule de la Tour concernée (`C⁻ < p ≤ C⁺`, coordonnée de pivot) ; et toute coordonnée dont la cellule contient `p_min(e)` est cette coordonnée du pivot (unicité).
- **Vérités** : V143, V54, V36
- **Repose sur** : `TrueZero`, `occurrence`, `expectedMinimumPrime`, `contactMinusAt`, `pivotCoordinate`, `contactPlusAt`, `passage_raccords`, `prime_raccord_has_unique_tower_cell`, `expectedMinimumPrime_pos`, `pivotCoordinate_unique` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `fnPrimeAtRank`, `nZeroSourceIndex`
- **Entraîne** : (aucun)

#### `log_amplitude_ratio_eq` — `Terminal/EnergyIdentity` l.55 — CONFIRMÉE
- **Énoncé** : Pour deux zéros `e`, `l` et `q > 0` (condition de domaine), `log‖terme(l,q)‖ − log‖terme(e,q)‖ = H − V`, où `H = (β_l − β_e)·log q` est l'énergie horizontale et `V = log‖ρ_l‖ − log‖ρ_e‖` l'énergie verticale (terme du maître : « énergie », Lean non nommé).
- **Vérités** : `AJOUT` (identité exacte log-amplitude = énergie horizontale − énergie verticale) | touche : V167 (appariement de chaque terme à sa norme de support) ; V102
- **Repose sur** : `TrueZero`, `zeroTerm`, `horizontalEnergy`, `verticalEnergy`, `zeroPoint`, `zeroPoint_ne_zero`, `zeroTerm_norm` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `amplitude_le_iff_horizontal_le_vertical`

#### `amplitude_le_iff_horizontal_le_vertical` — `Terminal/EnergyIdentity` l.68 — CONFIRMÉE
- **Énoncé** : Pour `q > 0`, l'amplitude du terme du zéro postérieur est au plus celle du zéro antérieur si et seulement si l'énergie horizontale est au plus l'énergie verticale.
- **Vérités** : `AJOUT` (équivalence amplitude ≤ ⟺ H ≤ V) | touche : O17 (le docstring nomme « résidu P7 » cette condition `H ≤ V`)
- **Repose sur** : `TrueZero`, `zeroTerm`, `horizontalEnergy`, `verticalEnergy`, `zeroPoint`, `zeroTerm_norm`, `zeroPoint_ne_zero`, `log_amplitude_ratio_eq` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `sameHeight_horizontal_dominates`, `verticalDominates_of_verticalEnergyPush`

#### `sameHeight_horizontal_dominates` — `Terminal/EnergyIdentity` l.81 — CONFIRMÉE SOUS CONDITION (β_e < β_l ; `q > 0` ; `q` au-delà du seuil `exp(V/Δβ)`)
- **Énoncé** : Si la position radiale du zéro antérieur est strictement inférieure à celle du postérieur, et `q` dépasse `exp(V/(β_l−β_e))`, alors l'amplitude du terme de l'antérieur est strictement inférieure à celle du postérieur.
- **Vérités** : `AJOUT` (domination de l'énergie horizontale au-delà d'un seuil explicite) | touche : V170 ; V173 ; docstring ≠ type : le docstring dit « à même hauteur », le type n'a aucune hypothèse de hauteur
- **Repose sur** : `TrueZero`, `verticalEnergy`, `zeroTerm`, `horizontalEnergy`, `amplitude_le_iff_horizontal_le_vertical` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : (aucun)

#### `verticalDominates_of_verticalEnergyPush` — `Terminal/EnergyIdentity` l.108 — CONFIRMÉE (implication entre deux prémisses énergétiques ; `PVerticalEnergyPush` est ⟺ RH par `verticalEnergyPush_iff_riemannHypothesis`, hors lot)
- **Énoncé** : La poussée verticale énergétique (∀ q ≥ 1) donne `H ≤ V` aux deux raccords `Occ(l)` et `p_min(l)` de tout passage (prémisse `PVerticalDominatesAtRaccord`) : sens facile seulement.
- **Vérités** : `AJOUT` (implication entre deux prémisses énergétiques) | touche : O17 ; I13
- **Repose sur** : `PVerticalEnergyPush`, `PVerticalDominatesAtRaccord`, `occurrence`, `occurrence_prime`, `expectedMinimumPrime`, `expectedMinimumPrime_prime`, `horizontalEnergy`, `verticalEnergy`, `zeroTerm`, `amplitude_le_iff_horizontal_le_vertical` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : (aucun)


##### `Terminal/EventHeightProgression`

#### `passage_event_increment` — `Terminal/EventHeightProgression` l.35 — CONFIRMÉE
- **Énoncé** : Sur tout passage consécutif de membres supérieurs (hauteurs positives : condition de domaine), la place avance de un, l'occurrence du membre postérieur est le minimum attendu de l'antérieur, et l'occurrence progresse strictement.
- **Vérités** : V56, V57, V150, V54
- **Repose sur** : `occurrence`, `expectedMinimumPrime`, `expectedMinimumPrime_eq_laterOccurrence`, `occurrence_strict_of_passage` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroSourceIndex`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `thm_zeroSourceIndex_succ_of_passage`
- **Entraîne** : `grammar_hypotheses_of_passage`, `off_event_increment_without_height`, `onLine_passage_shares_grammar_context`, `passage_double_constraint`, `passage_raccords`, `rank_grammar_unconditional`, `regime_captive_of_prime`

#### `passage_height_lt_of_onLine` — `Terminal/EventHeightProgression` l.48 — CONFIRMÉE SOUS CONDITION (passage dont les deux extrémités sont sur la ligne critique)
- **Énoncé** : Sur un passage dont les deux membres sont sur la ligne, la hauteur du membre postérieur est strictement supérieure à celle de l'antérieur (ordre : hauteur puis position radiale, positions radiales égales).
- **Vérités** : V57, V8 | touche : V181
- **Repose sur** : (aucun) ; base rhv3 : `TZeroPassage`, `rZeroRadialPosition`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroHeight`, `PZeroMemberPrecedes`, `thm_zeroMemberPrecedes_iff_height_radial_lex`, `TZeroPassage.precedes`
- **Entraîne** : `nullPassage_offLine`, `offPassages_heightProgression_iff_riemannHypothesis`, `onLine_clock_sync`, `onLine_passage_pure_vertical`, `onLine_passage_shares_grammar_context`, `passage_height_lt_of_riemannHypothesis`

#### `passage_height_lt_of_riemannHypothesis` — `Terminal/EventHeightProgression` l.59 — CONFIRMÉE (implication : l'antécédent RH est un terme de la vérité, sens direct de l'équivalence de `heightProgression_iff_riemannHypothesis`)
- **Énoncé** : Sous RH, tout passage fait progresser la hauteur.
- **Vérités** : V58 | touche : V57 (sens facile de l'équivalence, la conclusion n'est pas RH)
- **Repose sur** : `passage_height_lt_of_onLine` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `thm_zeroRadialPosition_half_of_riemannHypothesis`
- **Entraîne** : `grammar_forces_mode_A`, `heightProgression_iff_riemannHypothesis`, `noNullPassage_iff_riemannHypothesis`

#### `nullPassage_offLine` — `Terminal/EventHeightProgression` l.66 — CONFIRMÉE (implication : passage nul ⟹ extrémité hors ligne)
- **Énoncé** : Un passage nul (terme hors maître : même hauteur aux deux extrémités) a une extrémité hors ligne.
- **Vérités** : `AJOUT` (un passage nul a une extrémité hors ligne) | touche : V58 (préalable : passages à extrémité hors ligne) ; V66
- **Repose sur** : `passage_height_lt_of_onLine` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `PIsOffCriticalLine`, `rZeroRadialPosition`
- **Entraîne** : `nullPassage_horizontal`

#### `off_event_increment_without_height` — `Terminal/EventHeightProgression` l.83 — CONFIRMÉE SOUS CONDITION (pour un zéro hors ligne)
- **Énoncé** : Un zéro hors ligne produit un passage réel de même hauteur, dont la place avance de un, dont l'occurrence avance au premier minimal attendu, et dont la hauteur n'avance pas.
- **Vérités** : V57, V50 | touche : V66 ; V58
- **Repose sur** : `TrueZero`, `occurrence`, `expectedMinimumPrime`, `passage_event_increment` ; base rhv3 : `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroSourceIndex`, `rZeroPassageHeightGap`, `thm_offCriticalLine_existsNullPassage` et 2 autres
- **Entraîne** : `heightProgression_iff_riemannHypothesis`, `noNullPassage_iff_riemannHypothesis`, `offPassage_full_context`, `off_clock_slip`, `off_excess_zero`, `off_heightEventIndex_lt_sourceIndex`, `rank_grammar_forces_no_displacement`, `riemannHypothesis_of_energyBalance`, `riemannHypothesis_of_localReading`

#### `heightProgression_iff_riemannHypothesis` — `Terminal/EventHeightProgression` l.106 — ÉQUIVALENTE À RH (le côté gauche est « sur tout passage de membres supérieurs, la hauteur progresse »)
- **Énoncé** : « La place avance donc la hauteur avance », sur tout passage de membres supérieurs, est équivalent à RH.
- **Vérités** : V58
- **Repose sur** : `riemannHypothesis_of_noOff`, `TrueZero`, `occurrence`, `expectedMinimumPrime`, `off_event_increment_without_height`, `passage_height_lt_of_riemannHypothesis` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `nZeroSourceIndex`
- **Entraîne** : `interTowerExcess_pos_iff_riemannHypothesis`, `noNullPassage_iff_heightProgression`, `offPassages_heightProgression_iff_riemannHypothesis`, `riemannHypothesis_of_PHeightProgression`

#### `offPassages_heightProgression_iff_riemannHypothesis` — `Terminal/EventHeightProgression` l.122 — ÉQUIVALENTE À RH (progression de la hauteur sur les seuls passages à extrémité hors ligne)
- **Énoncé** : Exiger la progression de la hauteur sur les seuls passages ayant une extrémité hors ligne est encore équivalent à RH.
- **Vérités** : V58
- **Repose sur** : `heightProgression_iff_riemannHypothesis`, `passage_height_lt_of_onLine` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `PIsOffCriticalLine`, `TZeroPassage.zLaterMember`, `rZeroRadialPosition`
- **Entraîne** : `offPassages_interTowerExcess_pos_iff_riemannHypothesis`

#### `heightEventIndex_le_sourceIndex` — `Terminal/EventHeightProgression` l.140 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, l'index par hauteurs est majoré par l'index par membres (place par hauteurs ≤ place par membres).
- **Vérités** : `AJOUT` (majoration inconditionnelle de l'index par hauteurs par l'index par membres) | touche : V59 (préalable de l'équivalence des deux grammaires)
- **Repose sur** : `TrueZero` ; base rhv3 : `nZeroHeightEventIndex`, `tZeroHeightEvent`, `nZeroSourceIndex`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `sZeroHeightsBelow`, `thm_zeroHeightsBelow_finite`, `rZeroHeight`, `sUpperZerosBelow`, `thm_upperZerosBelow_finite` et 5 autres
- **Entraîne** : `clock_h_le_n`, `heightEventIndex_lt_sourceIndex_of_off_below`, `mirror_heightEventIndex_lt_sourceIndex`, `mirror_transport_refuted`, `off_heightEventIndex_lt_sourceIndex`

#### `sourceIndex_eq_heightEventIndex_of_riemannHypothesis` — `Terminal/EventHeightProgression` l.161 — CONFIRMÉE (implication : l'antécédent RH est un terme de la vérité, sens direct de `grammarsAgree_iff_riemannHypothesis`)
- **Énoncé** : Sous RH, l'index par membres et l'index par hauteurs coïncident pour tout zéro.
- **Vérités** : V59
- **Repose sur** : `TrueZero` ; base rhv3 : `nZeroSourceIndex`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `nZeroHeightEventIndex`, `tZeroHeightEvent`, `sZeroHeightsBelow`, `thm_zeroHeightsBelow_finite`, `rZeroHeight`, `sUpperZerosBelow`, `thm_upperZerosBelow_finite` et 8 autres
- **Entraîne** : `grammarsAgree_iff_riemannHypothesis`

#### `off_heightEventIndex_lt_sourceIndex` — `Terminal/EventHeightProgression` l.203 — CONFIRMÉE SOUS CONDITION (pour un zéro hors ligne)
- **Énoncé** : Si un zéro est hors ligne, il existe un zéro dont l'index par hauteurs est strictement inférieur à l'index par membres.
- **Vérités** : V59 | touche : V131
- **Repose sur** : `TrueZero`, `occurrence`, `expectedMinimumPrime`, `off_event_increment_without_height`, `heightEventIndex_le_sourceIndex` ; base rhv3 : `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `nZeroHeightEventIndex`, `tZeroHeightEvent`, `nZeroSourceIndex`, `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember` et 1 autres
- **Entraîne** : `grammarsAgree_iff_riemannHypothesis`

#### `off_mirror_two_grammars` — `Terminal/EventHeightProgression` l.218 — CONFIRMÉE SOUS CONDITION (pour un zéro hors ligne)
- **Énoncé** : Pour un zéro hors ligne, son miroir a le même événement de hauteur (même premier par hauteurs) que lui, mais une occurrence par membres distincte de la sienne.
- **Vérités** : V131, V127
- **Repose sur** : `TrueZero`, `mirrorMember`, `occurrence`, `occurrence_eq_canonicalAnchor` ; base rhv3 : `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `nHeightEventMZOccurrence`, `tZeroHeightEvent`, `thm_offMirror_sameHeightEvent_samePrime`, `nZeroSourceIndex`, `thm_primeAtRank_injective`, `nMemberCanonicalAnchor`, `thm_zeroSourceIndex_injective` et 1 autres
- **Entraîne** : (aucun)

#### `grammarsAgree_iff_riemannHypothesis` — `Terminal/EventHeightProgression` l.232 — ÉQUIVALENTE À RH (côté gauche : index par membres = index par hauteurs pour tout zéro)
- **Énoncé** : Les deux grammaires (par membres, par hauteurs) coïncident sur tout zéro si et seulement si RH.
- **Vérités** : V59, V128
- **Repose sur** : `TrueZero`, `riemannHypothesis_of_noOff`, `off_heightEventIndex_lt_sourceIndex`, `sourceIndex_eq_heightEventIndex_of_riemannHypothesis` ; base rhv3 : `nZeroSourceIndex`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `nZeroHeightEventIndex`, `tZeroHeightEvent`, `PIsOffCriticalLine`
- **Entraîne** : `clock_agree_iff_riemannHypothesis`, `displacement_forced_iff_grammarByHeight`, `grammarByHeight_iff_riemannHypothesis`, `grammar_forces_displacement`, `grammar_forces_mode_A`, `occurrences_agree_iff_riemannHypothesis`, `pastOnLine_all_iff_riemannHypothesis`

#### `occurrences_agree_iff_riemannHypothesis` — `Terminal/EventHeightProgression` l.246 — ÉQUIVALENTE À RH (occurrence par membres = occurrence par hauteurs pour tout zéro)
- **Énoncé** : La même équivalence lue sur les premiers : l'occurrence par membres et l'occurrence par hauteurs sont le même premier pour tout zéro si et seulement si RH.
- **Vérités** : V59
- **Repose sur** : `TrueZero`, `occurrence`, `grammarsAgree_iff_riemannHypothesis`, `occurrence_eq_canonicalAnchor` ; base rhv3 : `nHeightEventMZOccurrence`, `tZeroHeightEvent`, `nZeroSourceIndex`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `nZeroHeightEventIndex`, `nMemberCanonicalAnchor`, `nHeightEventCanonicalPrime`, `thm_heightEventMZOccurrence_eq_canonicalPrime_unconditional`, `fnPrimeAtRank` et 1 autres
- **Entraîne** : (aucun)


##### `Terminal/ExpectedObserved`

#### `primeCountAtStateUpper_eq_vonMangoldt` — `Terminal/ExpectedObserved` l.18 — CONFIRMÉE
- **Énoncé** : Pour tout état de Tour d'un zéro, le comptage de premiers à son contact supérieur est exactement le comptage de Chebyshev/Von Mangoldt évalué en la partie entière de ce contact.
- **Vérités** : V145, V52
- **Repose sur** : `TrueZero`, `primeCountAtStateUpper` ; base rhv3 : `TTrueHarmonicTowerState`, `nPrimeCountingFromJ`, `rChebyshevJNat`, `TTrueHarmonicTowerState.contactPlus`, `nEdgePrimeRank`, `thm_edgePrimeRank_eq_primeCountingFromJ`
- **Entraîne** : `producedPrime_eq_vonMangoldt`

#### `lastPrimeAtStateUpper_prime` — `Terminal/ExpectedObserved` l.29 — CONFIRMÉE (comptage strictement positif : condition de domaine)
- **Énoncé** : Si le comptage à un état est strictement positif, le dernier premier lu à cet état est bien un nombre premier.
- **Vérités** : V145
- **Repose sur** : `TrueZero`, `primeCountAtStateUpper`, `lastPrimeAtStateUpper` ; base rhv3 : `TTrueHarmonicTowerState`, `thm_primeAtRank_isPrime`
- **Entraîne** : `producedPrime_prime`

#### `lastPrimeAtStateUpper_le_contact` — `Terminal/ExpectedObserved` l.36 — CONFIRMÉE (comptage strictement positif, contact supérieur positif : conditions de domaine)
- **Énoncé** : Le dernier premier lu à l'état est au plus le contact supérieur (comptage inclusif).
- **Vérités** : V52 | touche : V37 (cible constatée = dernier premier atteint)
- **Repose sur** : `TrueZero`, `primeCountAtStateUpper`, `lastPrimeAtStateUpper` ; base rhv3 : `TTrueHarmonicTowerState`, `TTrueHarmonicTowerState.contactPlus`, `fnPrimeAtRank`, `nEdgePrimeRank`
- **Entraîne** : `countedPrime_le_lastRay`


##### `Terminal/ExplicitFormulaLink`

#### `zeroPoint_re` — `Terminal/ExplicitFormulaLink` l.42 — CONFIRMÉE
- **Énoncé** : La partie réelle du point complexe `ρ` associé à un zéro est sa position radiale β.
- **Vérités** : `AJOUT` (lemme de support : ρ = β + iT) | touche : V100 (préalable)
- **Repose sur** : `TrueZero`, `zeroPoint` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `cpow_zeroPoint_im`, `cpow_zeroPoint_re`, `zeroPoint_norm_sq`, `zeroTerm_im`, `zeroTerm_norm`, `zeroTerm_re`

#### `zeroPoint_im` — `Terminal/ExplicitFormulaLink` l.44 — CONFIRMÉE
- **Énoncé** : La partie imaginaire du point `ρ` d'un zéro est sa hauteur T.
- **Vérités** : `AJOUT` (lemme de support : ρ = β + iT) | touche : V100 (préalable)
- **Repose sur** : `TrueZero`, `zeroPoint` ; base rhv3 : `rZeroHeight`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `cpow_zeroPoint_im`, `cpow_zeroPoint_re`, `zeroPoint_norm_sq`, `zeroTerm_im`, `zeroTerm_re`

#### `zeroPoint_re_pos` — `Terminal/ExplicitFormulaLink` l.46 — CONFIRMÉE
- **Énoncé** : La partie réelle du point `ρ` d'un zéro est strictement positive.
- **Vérités** : V7
- **Repose sur** : `TrueZero`, `zeroPoint` ; base rhv3 : `thm_zeroRadialPosition_positive`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `zeroPoint_add_one_ne_zero`, `zeroPoint_isNontrivial`, `zeroPoint_ne_zero`

#### `zeroPoint_ne_zero` — `Terminal/ExplicitFormulaLink` l.49 — CONFIRMÉE
- **Énoncé** : Le point `ρ` d'un zéro est non nul.
- **Vérités** : `AJOUT` (lemme de support : non-nullité de ρ (dénominateur du terme))
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroPoint_re_pos` ; base rhv3 : (aucun)
- **Entraîne** : `amplitude_le_iff_horizontal_le_vertical`, `amplitude_ratio_sameHeight`, `energy_balance_two_primes_false`, `log_amplitude_ratio_eq`, `mirror_amplitude_ratio`, `pivotCell_amplitude_brackets`, `zeroPoint_norm_pos`, `zeroTerm_im_eq_sin_towerPosition`, `zeroTerm_is_derivative_of_explicit_term`, `zeroTerm_real_iff_sin`

#### `zeroPoint_add_one_ne_zero` — `Terminal/ExplicitFormulaLink` l.55 — CONFIRMÉE
- **Énoncé** : `ρ + 1` est non nul pour tout zéro.
- **Vérités** : `AJOUT` (lemme de support : non-nullité de ρ+1)
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroPoint_re_pos` ; base rhv3 : (aucun)
- **Entraîne** : `zeroPoint_ne_neg_one`, `zeroTerm_is_derivative_of_explicit_term`

#### `zeroPoint_ne_neg_one` — `Terminal/ExplicitFormulaLink` l.61 — CONFIRMÉE
- **Énoncé** : `ρ` n'est jamais égal à −1.
- **Vérités** : `AJOUT` (lemme de support : ρ ≠ −1)
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroPoint_add_one_ne_zero` ; base rhv3 : (aucun)
- **Entraîne** : `zeroTerm_is_derivative_of_explicit_term`

#### `pi_mul_towerPosition` — `Terminal/ExplicitFormulaLink` l.72 — CONFIRMÉE
- **Énoncé** : Pour tout zéro et tout `q`, `π·(position de Tour en q) = T·log q − phase` : la position de Tour est l'argument du terme, décalé de la phase, avançant avec le logarithme de l'abscisse à la vitesse fixée par T.
- **Vérités** : V16 | touche : V100
- **Repose sur** : `TrueZero`, `towerPosition`, `TowerMotion.phase`, `towerMotionOf` ; base rhv3 : `rZeroHeight`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `mirror_phase_increment_eq`, `mirror_phase_offset_const`, `offPassage_full_context`, `phase_increment_eq_pi_span`, `phase_increment_le_height_mul_log_two`, `ray_energy`, `zeroTerm_im_eq_sin_towerPosition`, `zeroTerm_re_eq_cos_towerPosition`

#### `cpow_zeroPoint_re` — `Terminal/ExplicitFormulaLink` l.77 — CONFIRMÉE
- **Énoncé** : Pour `q > 0`, la partie réelle de `q^ρ` est `q^β·cos(T·log q)`.
- **Vérités** : `AJOUT` (lemme de support : décomposition de q^ρ) | touche : V100 (préalable)
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroPoint_re`, `zeroPoint_im` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : `zeroTerm_im`, `zeroTerm_re`

#### `cpow_zeroPoint_im` — `Terminal/ExplicitFormulaLink` l.85 — CONFIRMÉE
- **Énoncé** : Pour `q > 0`, la partie imaginaire de `q^ρ` est `q^β·sin(T·log q)`.
- **Vérités** : `AJOUT` (lemme de support : décomposition de q^ρ) | touche : V100 (préalable)
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroPoint_re`, `zeroPoint_im` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : `zeroTerm_im`, `zeroTerm_re`

#### `zeroTerm_im` — `Terminal/ExplicitFormulaLink` l.93 — CONFIRMÉE
- **Énoncé** : Pour `q > 0`, la partie imaginaire du terme explicite `q^ρ/ρ` du zéro vaut `q^β·(β·sin θ − T·cos θ)/‖ρ‖²`, `θ = T·log q`.
- **Vérités** : `AJOUT` (partie imaginaire du terme explicite) | touche : V100 (préalable)
- **Repose sur** : `TrueZero`, `zeroTerm`, `zeroPoint`, `cpow_zeroPoint_re`, `cpow_zeroPoint_im`, `zeroPoint_re`, `zeroPoint_im` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : `zeroTerm_im_eq_sin_towerPosition`

#### `phase_identity` — `Terminal/ExplicitFormulaLink` l.104 — CONFIRMÉE
- **Énoncé** : Pour tout zéro et tout `θ`, `β·sin θ − T·cos θ = (β / cos φ)·sin(θ − φ)` où `φ` est la phase de la Tour (`arctan(T/β)`).
- **Vérités** : V16 | touche : V100
- **Repose sur** : `TrueZero`, `TowerMotion.phase`, `towerMotionOf`, `towerMotion_phase` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `rZeroHeight`, `thm_zeroRadialPosition_positive`
- **Entraîne** : `zeroTerm_im_eq_sin_towerPosition`

#### `zeroTerm_im_eq_sin_towerPosition` — `Terminal/ExplicitFormulaLink` l.123 — CONFIRMÉE
- **Énoncé** : Pour `q > 0`, la partie imaginaire du terme du zéro vaut `q^β·β·sin(π·position de Tour en q) / (‖ρ‖²·cos φ)` : la Tour est l'argument du terme.
- **Vérités** : V100
- **Repose sur** : `TrueZero`, `zeroTerm`, `towerPosition`, `zeroPoint`, `TowerMotion.phase`, `towerMotionOf`, `zeroTerm_im`, `phase_identity`, `pi_mul_towerPosition`, `towerMotion_phase`, `zeroPoint_ne_zero` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : `zeroTerm_real_iff_sin`

#### `zeroTerm_real_iff_sin` — `Terminal/ExplicitFormulaLink` l.136 — CONFIRMÉE
- **Énoncé** : Pour `q > 0`, le terme du zéro est réel exactement quand `sin(π·position de Tour en q) = 0`, c'est-à-dire quand la position de Tour est entière.
- **Vérités** : V100
- **Repose sur** : `TrueZero`, `zeroTerm`, `towerPosition`, `zeroPoint`, `TowerMotion.phase`, `towerMotionOf`, `zeroTerm_im_eq_sin_towerPosition`, `towerMotion_phase`, `zeroPoint_ne_zero` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `rZeroHeight`, `thm_zeroRadialPosition_positive`
- **Entraîne** : `ray_zeroTerm_real`, `zeroTerm_real_iff_ray`

#### `towerPosition_contactMinusAt` — `Terminal/ExplicitFormulaLink` l.155 — CONFIRMÉE
- **Énoncé** : La position de Tour du rayon `C_k` est l'entier `k`.
- **Vérités** : V100 | touche : V23 (les rayons sont numérotés par demi-tours)
- **Repose sur** : `TrueZero`, `towerPosition`, `contactMinusAt`, `TowerMotion.phase`, `towerMotionOf`, `TowerMotion.incidence`, `towerMotion_incidence` ; base rhv3 : `rZeroHeight`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `ray_zeroTerm_real`

#### `ray_zeroTerm_real` — `Terminal/ExplicitFormulaLink` l.164 — CONFIRMÉE
- **Énoncé** : Pour tout zéro et tout entier `k`, le terme du zéro est réel en le rayon `C_k` de sa Tour : les rayons sont des points réels du terme.
- **Vérités** : V100
- **Repose sur** : `TrueZero`, `zeroTerm`, `contactMinusAt`, `towerPosition`, `zeroTerm_real_iff_sin`, `contactMinusAt_positive`, `towerPosition_contactMinusAt` ; base rhv3 : (aucun)
- **Entraîne** : `pivotCell_entry_zeroTerm_real`, `pivotCell_lastRay_zeroTerm_real`, `ray_zeroTerm_eq`, `zeroTerm_real_iff_ray`

#### `zeroTerm_real_iff_ray` — `Terminal/ExplicitFormulaLink` l.171 — CONFIRMÉE
- **Énoncé** : Réciproque : un réel `q > 0` où le terme du zéro est réel est un rayon `C_k` de la Tour de ce zéro.
- **Vérités** : V100
- **Repose sur** : `TrueZero`, `zeroTerm`, `contactMinusAt`, `towerPosition`, `zeroTerm_real_iff_sin`, `TowerMotion.phase`, `towerMotionOf`, `TowerMotion.incidence`, `towerMotion_incidence`, `ray_zeroTerm_real` ; base rhv3 : `rZeroHeight`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : (aucun)

#### `conjugate_term_eq_conj` — `Terminal/ExplicitFormulaLink` l.197 — CONFIRMÉE
- **Énoncé** : Pour `q > 0`, le terme du zéro conjugué `ρ̄` est le conjugué du terme de `ρ`.
- **Vérités** : V101
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroTerm` ; base rhv3 : (aucun)
- **Entraîne** : `conjugate_term_im`, `pair_term_real`

#### `conjugate_term_im` — `Terminal/ExplicitFormulaLink` l.206 — CONFIRMÉE
- **Énoncé** : Pour `q > 0`, la partie imaginaire du terme du conjugué est l'opposée de celle du terme de `ρ` : l'inversion est la conjugaison.
- **Vérités** : V101
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroTerm`, `conjugate_term_eq_conj` ; base rhv3 : (aucun)
- **Entraîne** : (aucun)

#### `pair_term_real` — `Terminal/ExplicitFormulaLink` l.212 — CONFIRMÉE
- **Énoncé** : Pour `q > 0`, la somme des termes de `ρ` et de son conjugué est réelle : `2·Re(q^ρ/ρ)`.
- **Vérités** : V101
- **Repose sur** : `TrueZero`, `zeroTerm`, `zeroPoint`, `conjugate_term_eq_conj` ; base rhv3 : (aucun)
- **Entraîne** : (aucun)

#### `zeroTerm_norm` — `Terminal/ExplicitFormulaLink` l.220 — CONFIRMÉE
- **Énoncé** : Pour `q > 0`, l'amplitude du terme du zéro est `‖terme‖ = q^β / ‖ρ‖` : la position radiale β est l'exposant réel de l'amplitude.
- **Vérités** : V102, V173 | touche : O17 ; V167
- **Repose sur** : `TrueZero`, `zeroTerm`, `zeroPoint`, `zeroPoint_re` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `amplitude_inverts_of_radial_lt`, `amplitude_le_iff_horizontal_le_vertical`, `amplitude_lt_of_height_lt`, `amplitude_ratio_sameHeight`, `energyRatio_eq`, `energy_balance_two_primes_false`, `horizontal_energy_action`, `log_amplitude_ratio_eq`, `mirror_amplitude_ratio`, `mirror_zeroTerm_norm`, `pivotCell_amplitude_brackets`, `ray_energy_growth` et 2 autres

#### `mirror_zeroTerm_norm` — `Terminal/ExplicitFormulaLink` l.225 — CONFIRMÉE
- **Énoncé** : Pour `q > 0`, l'amplitude du terme du miroir est `q^{1−β} / ‖ρ_miroir‖`.
- **Vérités** : V102
- **Repose sur** : `TrueZero`, `zeroTerm`, `mirrorMember`, `zeroPoint`, `zeroTerm_norm`, `mirrorMember_radial` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `mirror_amplitude_ratio`

#### `mirror_amplitude_exponent_dominates` — `Terminal/ExplicitFormulaLink` l.230 — CONFIRMÉE SOUS CONDITION (zéro de côté bas ; `q ≥ 1`)
- **Énoncé** : Hors ligne (β < 1/2) et pour `q ≥ 1`, l'exposant d'amplitude du zéro est majoré par celui du miroir : `q^β ≤ q^{1−β}`.
- **Vérités** : V102
- **Repose sur** : `TrueZero` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `explicitFormula_counts_members`

#### `onLine_amplitude_exponents_equal` — `Terminal/ExplicitFormulaLink` l.236 — CONFIRMÉE SOUS CONDITION (β = 1/2)
- **Énoncé** : Sur la droite, l'exposant d'amplitude du zéro est égal à celui du miroir (`β = 1 − β`).
- **Vérités** : V102
- **Repose sur** : `TrueZero` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : (aucun)

#### `zeroPoint_isNontrivial` — `Terminal/ExplicitFormulaLink` l.244 — CONFIRMÉE
- **Énoncé** : Le point `ρ` de tout membre est un zéro non trivial au sens de la formule explicite compilée de la base.
- **Vérités** : `AJOUT` (lemme de support : un membre est un zéro non trivial de la formule explicite) | touche : V100 (préalable) ; V121
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroPoint_re_pos` ; base rhv3 : `IsNontrivialZetaZero`, `IsTrivialZetaZero`, `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `IsTrivialZetaZero._proof_1`, `thm_zeroRadialPosition_lt_one`
- **Entraîne** : `explicit_term_derivative`, `explicit_term_of_member`

#### `explicit_term_of_member` — `Terminal/ExplicitFormulaLink` l.259 — CONFIRMÉE
- **Énoncé** : Le terme du membre dans le canal des zéros de la formule explicite compilée vaut `−m(ρ)·Perron.f(x, ρ)` (m : multiplicité).
- **Vérités** : V100 | touche : V127 ; T9 (le terme d'un seul zéro est ici un objet isolé ; aucun énoncé du lot n'isole un terme dans la somme sur les zéros)
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroPoint_isNontrivial` ; base rhv3 : `nontrivialZeroResidueTerm`, `IsNontrivialZetaZero`, `zetaZeroMultiplicity`, `Perron.f`
- **Entraîne** : (aucun)

#### `liaison_analytic` — `Terminal/ExplicitFormulaLink` l.264 — CONFIRMÉE (`2 ≤ x` : domaine de ψ)
- **Énoncé** : Pour `x ≥ 2`, la fonction de Chebyshev ψ(x) est exactement reconstruite depuis les zéros (`psiRecoveredFromZeros x = ψ(x)`) : forme analytique compilée de la liaison des deux grammaires.
- **Vérités** : V103, V121, V48
- **Repose sur** : (aucun) ; base rhv3 : `psiRecoveredFromZeros`, `psiRecoveredFromZeros_eq_psi`
- **Entraîne** : (aucun)

#### `zeroTerm_is_derivative_of_explicit_term` — `Terminal/ExplicitFormulaLink` l.270 — CONFIRMÉE
- **Énoncé** : Pour `x > 0`, le terme de la Tour du zéro est la dérivée en `x` de `x·Perron.f(x, ρ)` (le terme lissé du zéro dans la formule explicite).
- **Vérités** : V103, V100
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroTerm`, `zeroPoint_ne_neg_one`, `zeroPoint_ne_zero`, `zeroPoint_add_one_ne_zero` ; base rhv3 : `Perron.f`
- **Entraîne** : `explicit_term_derivative`

#### `explicit_term_derivative` — `Terminal/ExplicitFormulaLink` l.289 — CONFIRMÉE
- **Énoncé** : Pour `x > 0`, la dérivée du terme du membre dans le canal compilé est `−m(ρ)` fois le terme de la Tour.
- **Vérités** : V103 | touche : T9 (terme d'un seul zéro, objet isolé)
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroPoint_isNontrivial`, `zeroTerm`, `zeroTerm_is_derivative_of_explicit_term` ; base rhv3 : `nontrivialZeroResidueTerm`, `IsNontrivialZetaZero`, `zetaZeroMultiplicity`, `Perron.f`
- **Entraîne** : (aucun)


##### `Terminal/GeometricEnergyRaccord`

#### `prime_raccord_has_unique_tower_cell` — `Terminal/GeometricEnergyRaccord` l.37 — CONFIRMÉE
- **Énoncé** : Pour tout zéro et `q > 0`, le premier `q` est encadré par les deux contacts de la cellule de sa coordonnée de pivot : `C⁻ < q ≤ C⁺`.
- **Vérités** : V143 | touche : V26 ; V36
- **Repose sur** : `TrueZero`, `contactMinusAt`, `pivotCoordinate`, `contactPlusAt`, `AnalyticContactPair.entryContact`, `pivotPair`, `entry_lt_pivot`, `AnalyticContactPair.lastRayContact`, `pivot_le_lastRay`, `analyticPairAt`, `analyticPairAt_entryContact`, `analyticPairAt_lastRayContact` ; base rhv3 : (aucun)
- **Entraîne** : `geometry_selects_raccord_prime`, `passage_double_constraint`, `pivotCell_amplitude_brackets`, `succession_invariants`, `tower_reads_any_prime`

#### `pivotCell_entry_zeroTerm_real` — `Terminal/GeometricEnergyRaccord` l.52 — CONFIRMÉE
- **Énoncé** : Le contact d'entrée de la cellule du premier `q` est un rayon authentique : le terme du zéro y est réel.
- **Vérités** : V100 | touche : V20
- **Repose sur** : `TrueZero`, `zeroTerm`, `contactMinusAt`, `pivotCoordinate`, `ray_zeroTerm_real` ; base rhv3 : (aucun)
- **Entraîne** : (aucun)

#### `pivotCell_lastRay_zeroTerm_real` — `Terminal/GeometricEnergyRaccord` l.58 — CONFIRMÉE
- **Énoncé** : Le dernier rayon de la cellule du premier `q` est un rayon authentique : le terme du zéro y est réel.
- **Vérités** : V100 | touche : V20
- **Repose sur** : `TrueZero`, `zeroTerm`, `contactPlusAt`, `pivotCoordinate`, `ray_zeroTerm_real` ; base rhv3 : (aucun)
- **Entraîne** : (aucun)

#### `pivotCell_amplitude_brackets` — `Terminal/GeometricEnergyRaccord` l.65 — CONFIRMÉE
- **Énoncé** : Pour `q > 0`, l'amplitude du terme en `q` est strictement supérieure à celle au contact d'entrée de sa cellule et au plus égale à celle au dernier rayon : encadrement par les amplitudes des deux contacts propres.
- **Vérités** : `AJOUT` (encadrement de l'amplitude au premier `q` par celles de ses deux contacts propres) | touche : O17 ; V170
- **Repose sur** : `TrueZero`, `zeroTerm`, `contactMinusAt`, `pivotCoordinate`, `contactPlusAt`, `prime_raccord_has_unique_tower_cell`, `contactMinusAt_positive`, `contactPlusAt_positive`, `zeroPoint`, `zeroPoint_ne_zero`, `zeroTerm_norm` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `thm_zeroRadialPosition_positive`
- **Entraîne** : `horizontalRaccords_amplitude_brackets`, `sameCell_four_contacts_bracket`

#### `horizontalRaccords_amplitude_brackets` — `Terminal/GeometricEnergyRaccord` l.92 — CONFIRMÉE
- **Énoncé** : Pour deux zéros quelconques `e`, `l`, l'amplitude de chacun aux deux raccords (`Occ(l)` et `p_min(l)`) est encadrée par ses amplitudes à ses deux contacts propres : fait vrai pour toute hauteur et tout β, ne forçant aucune égalité.
- **Vérités** : `AJOUT` (encadrement aux deux raccords, sans égalité forcée) | touche : O17 ; V170 ; V173
- **Repose sur** : `TrueZero`, `zeroTerm`, `contactMinusAt`, `pivotCoordinate`, `occurrence`, `contactPlusAt`, `expectedMinimumPrime`, `pivotCell_amplitude_brackets`, `occurrence_pos`, `expectedMinimumPrime_pos` ; base rhv3 : (aucun)
- **Entraîne** : (aucun)

#### `sameHeight_pivotCoordinate_dichotomy` — `Terminal/GeometricEnergyRaccord` l.130 — CONFIRMÉE (même hauteur : antécédent de la relation énoncée)
- **Énoncé** : Deux zéros de même hauteur lisent, pour tout premier `q`, la même coordonnée de pivot ou des coordonnées voisines à ±1.
- **Vérités** : `AJOUT` (écart de coordonnée de pivot au plus 1 entre deux zéros de même hauteur) | touche : V158
- **Repose sur** : `TrueZero`, `pivotCoordinate`, `pivotCoordinate_sameHeight_shift_le_one` ; base rhv3 : `rZeroHeight`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `horizontal_cell_dichotomy_at_raccords`

#### `sameCell_four_contacts_bracket` — `Terminal/GeometricEnergyRaccord` l.141 — CONFIRMÉE (même coordonnée de pivot et `q > 0` : antécédent de la relation énoncée)
- **Énoncé** : Si deux zéros lisent la même coordonnée de pivot au premier `q`, l'amplitude de chacun en `q` est encadrée par SES deux contacts propres, indexés par le même entier.
- **Vérités** : `AJOUT` (encadrement à quatre contacts quand la coordonnée est partagée) | touche : O17
- **Repose sur** : `TrueZero`, `pivotCoordinate`, `zeroTerm`, `contactMinusAt`, `contactPlusAt`, `pivotCell_amplitude_brackets` ; base rhv3 : (aucun)
- **Entraîne** : (aucun)

#### `horizontal_cell_dichotomy_at_raccords` — `Terminal/GeometricEnergyRaccord` l.155 — CONFIRMÉE (même hauteur : antécédent de la relation énoncée)
- **Énoncé** : Pour deux zéros de même hauteur, à chacun des deux raccords (`Occ(l)` et `p_min(l)`), la coordonnée de pivot de `l` est celle de `e` ou diffère d'un cran.
- **Vérités** : `AJOUT` (dichotomie de cellule aux deux raccords pour un couple de même hauteur) | touche : V158 ; V163
- **Repose sur** : `TrueZero`, `pivotCoordinate`, `occurrence`, `expectedMinimumPrime`, `sameHeight_pivotCoordinate_dichotomy` ; base rhv3 : `rZeroHeight`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : (aucun)


##### `Terminal/GrammarForcesStop`

#### `grammar_forces_displacement` — `Terminal/GrammarForcesStop` l.39 — CONFIRMÉE SOUS CONDITION (prémisse `PGrammarByHeight` (index par membres = index par hauteurs pour tout zéro), ⟺ RH par `grammarByHeight_iff_riemannHypothesis` ; hauteurs positives)
- **Énoncé** : Sous la grammaire par hauteurs, l'excès inter-Tours (terme hors maître : `J(p)`, écart entre la progression de phase des deux Tours et celle des premiers) est strictement positif sur tout passage.
- **Vérités** : V58, V59
- **Repose sur** : `PGrammarByHeight`, `interTowerExcess`, `interTowerExcess_pos_iff_riemannHypothesis`, `TrueZero`, `grammarsAgree_iff_riemannHypothesis` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroSourceIndex`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `nZeroHeightEventIndex`, `tZeroHeightEvent`
- **Entraîne** : `grammar_determines_stop_ray`

#### `grammar_forces_mode_A` — `Terminal/GrammarForcesStop` l.47 — CONFIRMÉE SOUS CONDITION (prémisse `PGrammarByHeight`, ⟺ RH par `grammarByHeight_iff_riemannHypothesis`)
- **Énoncé** : Sous la grammaire par hauteurs, tout passage est en « mode A » (terme hors maître : hauteurs strictement croissantes et les deux extrémités à β = 1/2).
- **Vérités** : V58, V59 | touche : V181
- **Repose sur** : `PGrammarByHeight`, `TrueZero`, `grammarsAgree_iff_riemannHypothesis`, `passage_height_lt_of_riemannHypothesis` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroRadialPosition`, `nZeroSourceIndex`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `nZeroHeightEventIndex`, `tZeroHeightEvent` et 1 autres
- **Entraîne** : `grammar_determines_stop_ray`

#### `grammar_determines_stop_ray` — `Terminal/GrammarForcesStop` l.58 — CONFIRMÉE SOUS CONDITION (prémisse `PGrammarByHeight`, ⟺ RH par `grammarByHeight_iff_riemannHypothesis` ; hauteurs positives)
- **Énoncé** : Sous la grammaire par hauteurs, sur tout passage, le membre postérieur est sur la ligne, sa hauteur dépasse celle de l'antérieur, l'excès inter-Tours est positif, son minimum attendu est `p_{n+2}` et il est encadré par les deux contacts de sa cellule unique.
- **Vérités** : V143, V59, V56
- **Repose sur** : `PGrammarByHeight`, `interTowerExcess`, `expectedMinimumPrime`, `contactMinusAt`, `pivotCoordinate`, `contactPlusAt`, `grammar_forces_mode_A`, `occurrence`, `passage_raccords`, `AnalyticContactPair.entryContact`, `TrueTower.toAnalyticContactPair`, `firstTowerOf`, `AnalyticContactPair.lastRayContact`, `firstTower_cell_contains_expected`, `grammar_forces_displacement` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `fnPrimeAtRank`, `nZeroSourceIndex`
- **Entraîne** : (aucun)

#### `rank_grammar_forces_no_displacement` — `Terminal/GrammarForcesStop` l.84 — CONFIRMÉE SOUS CONDITION (pour un zéro hors ligne)
- **Énoncé** : Un zéro hors ligne fournit un passage qui satisfait toute la grammaire par rang (place +1, raccord, occurrence strictement croissante) avec un excès inter-Tours nul.
- **Vérités** : V57 | touche : V58
- **Repose sur** : `TrueZero`, `occurrence`, `expectedMinimumPrime`, `interTowerExcess`, `off_event_increment_without_height`, `interTowerExcess_eq_zero_iff` ; base rhv3 : `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroSourceIndex`
- **Entraîne** : (aucun)

#### `displacement_forced_iff_grammarByHeight` — `Terminal/GrammarForcesStop` l.99 — ÉQUIVALENTE À RH (`PGrammarByHeight` ⟺ RH par `grammarByHeight_iff_riemannHypothesis`, même fichier)
- **Énoncé** : « L'excès inter-Tours est strictement positif sur tout passage » est équivalent à la grammaire par hauteurs.
- **Vérités** : V58, V59
- **Repose sur** : `interTowerExcess`, `PGrammarByHeight`, `interTowerExcess_pos_iff_riemannHypothesis`, `TrueZero`, `grammarsAgree_iff_riemannHypothesis` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroSourceIndex`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `nZeroHeightEventIndex`, `tZeroHeightEvent`
- **Entraîne** : (aucun)

#### `grammarByHeight_iff_riemannHypothesis` — `Terminal/GrammarForcesStop` l.108 — ÉQUIVALENTE À RH (`PGrammarByHeight` ⟺ RH)
- **Énoncé** : La grammaire par hauteurs (index par membres = index par hauteurs pour tout zéro) est équivalente à RH.
- **Vérités** : V59, V128
- **Repose sur** : `PGrammarByHeight`, `grammarsAgree_iff_riemannHypothesis` ; base rhv3 : (aucun)
- **Entraîne** : (aucun)

#### `rank_grammar_unconditional` — `Terminal/GrammarForcesStop` l.112 — CONFIRMÉE (hauteurs positives : condition de domaine ; aucune hypothèse sur β)
- **Énoncé** : La grammaire par rang (place +1, raccord `Occ(l) = p_min(e)`, occurrence strictement croissante) est vraie sur tout passage, sans condition : elle ne sépare pas ON de OFF.
- **Vérités** : V57, V56
- **Repose sur** : `occurrence`, `expectedMinimumPrime`, `passage_event_increment` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroSourceIndex`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : (aucun)


##### `Terminal/GridNeverCoincide`

#### `grids_never_coincide` — `Terminal/GridNeverCoincide` l.20 — CONFIRMÉE (même hauteur et positions radiales distinctes : antécédent de la relation énoncée)
- **Énoncé** : Aucun étage de la Tour d'un zéro ne coïncide avec aucun étage de la Tour d'un autre zéro de même hauteur et de position radiale différente, à indices `k`, `k'` quelconques.
- **Vérités** : V163 | touche : V46
- **Repose sur** : `TrueZero`, `contactMinusAt`, `TowerMotion.phase`, `towerMotionOf`, `TowerMotion.incidence`, `towerMotion_incidence`, `towerMotion_phase_pos`, `towerMotion_phase_lt_pi_div_two`, `towerMotion_phase` ; base rhv3 : `rZeroHeight`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `rZeroRadialPosition`, `thm_zeroRadialPosition_positive`
- **Entraîne** : `mirror_grid_never_coincides`

#### `mirror_grid_never_coincides` — `Terminal/GridNeverCoincide` l.66 — CONFIRMÉE SOUS CONDITION (zéro de côté bas)
- **Énoncé** : Hors ligne, aucun étage de la Tour du miroir ne coïncide avec aucun étage de la Tour du zéro, à tout décalage d'indice.
- **Vérités** : V163 | touche : V184
- **Repose sur** : `TrueZero`, `contactMinusAt`, `mirrorMember`, `grids_never_coincide`, `mirrorMember_ordinate`, `mirrorMember_radial` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : (aucun)


##### `Terminal/HorizontalExclusion`

#### `nullPassage_horizontal` — `Terminal/HorizontalExclusion` l.64 — CONFIRMÉE (implication : passage nul ⟹ HMR)
- **Énoncé** : Un passage nul réalise la « réalisation miroir horizontale » (terme hors maître, HMR : même hauteur, position radiale strictement croissante, extrémité hors ligne).
- **Vérités** : V165 | touche : V66
- **Repose sur** : `HorizontalMirrorRealization`, `nullPassage_offLine` ; base rhv3 : `TZeroPassage`, `PZeroPassageRelationNull`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `thm_zeroPassage_null_iff_sameHeight`, `rZeroRadialPosition`, `PIsOffCriticalLine`, `PZeroMemberPrecedes`, `thm_zeroMemberPrecedes_iff_height_radial_lex` et 1 autres
- **Entraîne** : `heightProgression_of_horizontalExclusion`, `horizontalExclusion_iff_riemannHypothesis`, `offPassage_full_context`, `riemannHypothesis_of_energyBalance`, `riemannHypothesis_of_localReading`

#### `horizontal_nullPassage` — `Terminal/HorizontalExclusion` l.76 — CONFIRMÉE (implication : HMR ⟹ passage nul)
- **Énoncé** : Réciproque : un passage qui réalise HMR est nul (même hauteur).
- **Vérités** : V165
- **Repose sur** : `HorizontalMirrorRealization` ; base rhv3 : `TZeroPassage`, `PZeroPassageRelationNull`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `thm_zeroPassage_null_iff_sameHeight`, `rZeroRadialPosition`, `PIsOffCriticalLine`
- **Entraîne** : `horizontalExclusion_iff_riemannHypothesis`

#### `horizontalExclusion_iff_riemannHypothesis` — `Terminal/HorizontalExclusion` l.84 — ÉQUIVALENTE À RH (« aucun passage ne réalise HMR » ⟺ RH)
- **Énoncé** : L'exclusion horizontale (aucun passage ne réalise HMR) est équivalente à RH.
- **Vérités** : V188 | touche : V189
- **Repose sur** : `HorizontalMirrorRealization`, `PNoNullPassage`, `noNullPassage_iff_riemannHypothesis`, `nullPassage_horizontal`, `horizontal_nullPassage` ; base rhv3 : `TZeroPassage`, `PZeroPassageRelationNull`
- **Entraîne** : `premise_ladder_tfae`

#### `heightProgression_of_horizontalExclusion` — `Terminal/HorizontalExclusion` l.95 — CONFIRMÉE (implication : HME ⟹ progression de la hauteur ; HME est ⟺ RH par `horizontalExclusion_iff_riemannHypothesis`)
- **Énoncé** : Sous l'exclusion horizontale, tout passage progresse strictement en hauteur (poussée verticale comme conséquence de l'exclusion horizontale).
- **Vérités** : V165 | touche : V188
- **Repose sur** : `HorizontalMirrorRealization`, `passage_height_le`, `nullPassage_horizontal` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `PZeroPassageRelationNull`, `thm_zeroPassage_null_iff_sameHeight`
- **Entraîne** : (aucun)

#### `contactMinus_eq_iff_radial_eq` — `Terminal/HorizontalExclusion` l.108 — CONFIRMÉE (caractérisation : même hauteur, coïncidence ⟺ même position radiale)
- **Énoncé** : Deux zéros de même hauteur ont le même contact `C_k` si et seulement si leurs positions radiales coïncident.
- **Vérités** : V163, V46
- **Repose sur** : `TrueZero`, `contactMinusAt`, `TowerMotion.incidence`, `towerMotionOf`, `TowerMotion.phase`, `towerMotion_incidence`, `towerMotion_phase` ; base rhv3 : `rZeroHeight`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `rZeroRadialPosition`, `thm_zeroRadialPosition_positive`
- **Entraîne** : `mirror_contact_eq_iff_onLine`, `onLine_of_mirror_phase_shift_eq_zero`

#### `mirror_contact_eq_iff_onLine` — `Terminal/HorizontalExclusion` l.134 — CONFIRMÉE
- **Énoncé** : Le contact `C_k` du membre miroir coïncide avec celui de `z` si et seulement si `z` est sur la ligne critique.
- **Vérités** : V163, V161
- **Repose sur** : `TrueZero`, `contactMinusAt`, `mirrorMember`, `contactMinus_eq_iff_radial_eq`, `mirrorMember_ordinate`, `mirrorMember_radial` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `mirror_contacts_never_coincide`, `onLine_of_mirror_contact_eq`, `raySuperposed_iff`

#### `mirror_contacts_never_coincide` — `Terminal/HorizontalExclusion` l.144 — RÉFUTATION COMPILÉE
- **Énoncé** : Hors ligne (β < 1/2), le contact `C_k` du miroir ne coïncide jamais avec le contact `C_k` de `z` : réfute, comme déclencheur, le candidat « (B) » (docstring : partage d'un contact réel par le passage horizontal).
- **Vérités** : V163 | touche : V184
- **Repose sur** : `TrueZero`, `contactMinusAt`, `mirrorMember`, `mirror_contact_eq_iff_onLine` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : (aucun)

#### `mirror_amplitude_ratio` — `Terminal/HorizontalExclusion` l.154 — CONFIRMÉE
- **Énoncé** : Pour `q > 0`, `‖terme(miroir,q)‖·‖ρ_miroir‖ = q^{1−2β}·(‖terme(z,q)‖·‖ρ‖)` : chaque terme apparié à SA norme de support.
- **Vérités** : V102, V167
- **Repose sur** : `TrueZero`, `zeroTerm`, `mirrorMember`, `zeroPoint`, `zeroPoint_ne_zero`, `mirror_zeroTerm_norm`, `zeroTerm_norm` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : (aucun)

#### `amplitude_exponents_eq_iff_onLine` — `Terminal/HorizontalExclusion` l.168 — CONFIRMÉE (`q > 1` : condition de domaine ; caractérisation)
- **Énoncé** : Pour `q > 1`, les exposants d'amplitude du zéro et de son miroir sont égaux si et seulement si le zéro est sur la ligne.
- **Vérités** : V102
- **Repose sur** : `TrueZero` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : (aucun)

#### `offPassage_full_context` — `Terminal/HorizontalExclusion` l.187 — CONFIRMÉE SOUS CONDITION (pour un zéro hors ligne)
- **Énoncé** : Un zéro hors ligne produit un passage qui cumule : même hauteur, place +1, raccord, occurrence croissante, excès inter-Tours nul, même index par hauteurs aux deux extrémités, portées égales, accroissements de phase égaux, ET la réalisation HMR : ces faits sont consistants entre eux.
- **Vérités** : V57, V66, V162 | touche : V160
- **Repose sur** : `TrueZero`, `occurrence`, `expectedMinimumPrime`, `interTowerExcess`, `towerPosition`, `HorizontalMirrorRealization`, `off_event_increment_without_height`, `interTowerExcess_eq_zero_iff`, `TowerMotion.phase`, `towerMotionOf`, `pi_mul_towerPosition`, `nullPassage_horizontal` ; base rhv3 : `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroSourceIndex`, `nZeroHeightEventIndex`, `tZeroHeightEvent` et 6 autres
- **Entraîne** : `riemannHypothesis_of_verticalEnergyPush`

#### `onLine_passage_shares_grammar_context` — `Terminal/HorizontalExclusion` l.238 — CONFIRMÉE SOUS CONDITION (passage dont les deux extrémités sont sur la ligne ; hauteurs positives)
- **Énoncé** : Un passage ON partage toute la grammaire (place +1, raccord, occurrence croissante), sa hauteur progresse strictement et il ne réalise pas HMR.
- **Vérités** : V181, V57
- **Repose sur** : `occurrence`, `expectedMinimumPrime`, `HorizontalMirrorRealization`, `passage_event_increment`, `passage_height_lt_of_onLine` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroRadialPosition`, `nZeroSourceIndex`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `PIsOffCriticalLine`
- **Entraîne** : (aucun)

#### `amplitude_ratio_sameHeight` — `Terminal/HorizontalExclusion` l.266 — CONFIRMÉE
- **Énoncé** : Pour deux zéros quelconques `e`, `l` et `q > 0`, `‖terme(l,q)‖·‖ρ_l‖ = q^{β_l−β_e}·(‖terme(e,q)‖·‖ρ_e‖)` : rapport d'amplitude exact, chaque terme apparié à SA norme.
- **Vérités** : V167, V102 | touche : nom promet plus que le type : « sameHeight » — le type n'a aucune hypothèse de hauteur
- **Repose sur** : `TrueZero`, `zeroTerm`, `zeroPoint`, `zeroPoint_ne_zero`, `zeroTerm_norm` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `energy_balance_two_primes_false`

#### `energy_balance_two_primes_false` — `Terminal/HorizontalExclusion` l.282 — RÉFUTATION COMPILÉE
- **Énoncé** : Si `β_e < β_l` et `q₁ < q₂`, les deux égalités de normes `‖terme(e,q₁)‖ = ‖terme(l,q₁)‖` et `‖terme(e,q₂)‖ = ‖terme(l,q₂)‖` sont incompatibles (`False`) : deux raccords distincts forcent l'égalité des positions radiales.
- **Vérités** : V170 | touche : O17 ; O18 (le théorème vaut pour deux premiers quelconques ; les valeurs numériques des raccords précis restent hors de son énoncé)
- **Repose sur** : `TrueZero`, `zeroTerm`, `zeroPoint`, `zeroPoint_ne_zero`, `zeroTerm_norm`, `amplitude_ratio_sameHeight` ; base rhv3 : `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `riemannHypothesis_of_energyBalance`

#### `riemannHypothesis_of_energyBalance` — `Terminal/HorizontalExclusion` l.337 — IMPLIQUE RH SOUS PRÉMISSE (`PEnergyBalanceAtRaccords` : sur tout passage HMR, égalité des normes aux raccords `Occ(l)` et `p_min(l)` ; ⟺ RH par `energyBalance_iff_riemannHypothesis`)
- **Énoncé** : La prémisse d'équilibre énergétique aux deux raccords entraîne RH : un zéro hors ligne fournit un passage nul (donc HMR), et les deux égalités de normes contredisent `energy_balance_two_primes_false`.
- **Vérités** : V170 | touche : O17 ; O24 ; I13
- **Repose sur** : `PEnergyBalanceAtRaccords`, `riemannHypothesis_of_noOff`, `TrueZero`, `occurrence`, `expectedMinimumPrime`, `off_event_increment_without_height`, `HorizontalMirrorRealization`, `nullPassage_horizontal`, `zeroTerm`, `occurrence_pos`, `occurrence_lt_expectedMinimumPrime`, `energy_balance_two_primes_false` ; base rhv3 : `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroSourceIndex`, `PZeroPassageRelationNull`, `thm_zeroPassage_null_iff_sameHeight` et 1 autres
- **Entraîne** : `energyBalance_iff_riemannHypothesis`

#### `energyBalance_iff_riemannHypothesis` — `Terminal/HorizontalExclusion` l.355 — ÉQUIVALENTE À RH (`PEnergyBalanceAtRaccords` ⟺ RH)
- **Énoncé** : La prémisse d'équilibre énergétique aux deux raccords est exactement RH (réciproque : sous RH, aucun passage ne réalise HMR).
- **Vérités** : V170, V188 | touche : O17 ; I13
- **Repose sur** : `PEnergyBalanceAtRaccords`, `riemannHypothesis_of_energyBalance`, `HorizontalMirrorRealization`, `zeroTerm`, `occurrence`, `expectedMinimumPrime` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `PIsOffCriticalLine`, `rZeroRadialPosition`, `thm_zeroRadialPosition_half_of_riemannHypothesis`
- **Entraîne** : (aucun)


##### `Terminal/IndependentContactComparison`

#### `expectedMinimum_le_stateReadout_iff` — `Terminal/IndependentContactComparison` l.16 — CONFIRMÉE (comptage à l'état > 0 : condition de domaine ; caractérisation)
- **Énoncé** : Pour un état de Tour d'un zéro `b` et le minimum attendu d'un zéro `a`, le dernier premier lu à l'état atteint ce minimum attendu si et seulement si le contact supérieur de l'état atteint ce minimum attendu.
- **Vérités** : V37 | touche : V135 (équivalence entre un constat et une position d'anneau)
- **Repose sur** : `TrueZero`, `primeCountAtStateUpper`, `expectedMinimumPrime`, `lastPrimeAtStateUpper` ; base rhv3 : `TTrueHarmonicTowerState`, `TTrueHarmonicTowerState.contactPlus`, `nZeroSourceIndex`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `fnPrimeSuccessor`, `fnPrimeAtRank`, `thm_primeAtRank_strictMono`, `nEdgePrimeRank`, `thm_edgeRank_le_iff_lt_primeAtRank` et 1 autres
- **Entraîne** : `expectedMinimum_le_produced_iff`, `stateReadout_lt_expectedMinimum_iff`

#### `stateReadout_lt_expectedMinimum_iff` — `Terminal/IndependentContactComparison` l.35 — CONFIRMÉE (comptage à l'état > 0 : condition de domaine ; caractérisation)
- **Énoncé** : Pour les mêmes objets, le dernier premier lu à l'état est strictement sous le minimum attendu de `a` si et seulement si le contact supérieur de l'état est strictement sous ce minimum attendu.
- **Vérités** : V37 | touche : V135
- **Repose sur** : `TrueZero`, `primeCountAtStateUpper`, `lastPrimeAtStateUpper`, `expectedMinimumPrime`, `expectedMinimum_le_stateReadout_iff` ; base rhv3 : `TTrueHarmonicTowerState`, `TTrueHarmonicTowerState.contactPlus`
- **Entraîne** : `produced_lt_expectedMinimum_iff`


##### `Terminal/InterTowerExcess`

#### `later_sourceIndex_eq` — `Terminal/InterTowerExcess` l.55 — CONFIRMÉE
- **Énoncé** : Sur tout passage (hauteur du membre antérieur positive : domaine), la place du membre postérieur est celle de l'antérieur plus un.
- **Vérités** : V56, V150
- **Repose sur** : (aucun) ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `nZeroSourceIndex`, `TZeroPassage.zLaterMember`, `thm_zeroSourceIndex_succ_of_passage`
- **Entraîne** : (aucun)

#### `interTowerExcess_eq` — `Terminal/InterTowerExcess` l.63 — CONFIRMÉE
- **Énoncé** : L'excès inter-Tours `J(p)` (défini plus haut ; V155 ne le cite que par nom de fichier) vaut `(T_l − T_e)·log(p_{n+2}/p_{n+1})` : identité de base transportée, sans mention de RH.
- **Vérités** : `AJOUT` (identité exacte de l'excès inter-Tours) | touche : V155 (fichier cité ; contenu non énoncé dans le maître)
- **Repose sur** : `interTowerExcess`, `towerPosition`, `phase_increment_eq_pi_span`, `phaseIncrement` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rPrimeGapLogRatio`, `nZeroSourceIndex`, `fnPrimeAtRank`, `thm_primeAtRank_pos`, `fnPrimeSuccessor`, `TNonTrivialZetaZero` et 3 autres
- **Entraîne** : `double_constraint_required_displacement`, `interTowerExcess_eq_zero_iff`, `interTowerExcess_nonneg`, `interTowerExcess_pos_iff`

#### `interTowerExcess_pos_iff` — `Terminal/InterTowerExcess` l.112 — CONFIRMÉE
- **Énoncé** : `J(p) > 0` si et seulement si `T_e < T_l`.
- **Vérités** : `AJOUT` (signe de l'excès inter-Tours ⟺ progression de la hauteur) | touche : V155
- **Repose sur** : `interTowerExcess`, `interTowerExcess_eq` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rPrimeGapLogRatio`, `nZeroSourceIndex`, `thm_primeGapLogRatio_pos`
- **Entraîne** : `interTowerExcess_pos_iff_riemannHypothesis`, `offPassages_interTowerExcess_pos_iff_riemannHypothesis`

#### `interTowerExcess_eq_zero_iff` — `Terminal/InterTowerExcess` l.128 — CONFIRMÉE
- **Énoncé** : `J(p) = 0` si et seulement si `T_e = T_l`.
- **Vérités** : `AJOUT` (nullité de l'excès inter-Tours ⟺ même hauteur) | touche : V155
- **Repose sur** : `interTowerExcess`, `interTowerExcess_eq` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rPrimeGapLogRatio`, `nZeroSourceIndex`, `thm_primeGapLogRatio_pos`
- **Entraîne** : `double_constraint_required_displacement`, `offPassage_full_context`, `off_excess_zero`, `rank_grammar_forces_no_displacement`

#### `passage_height_le` — `Terminal/InterTowerExcess` l.140 — CONFIRMÉE
- **Énoncé** : Sur tout passage, la hauteur de l'antérieur est au plus celle du postérieur (ordre lexicographique hauteur puis position radiale).
- **Vérités** : V8
- **Repose sur** : (aucun) ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroRadialPosition`, `PZeroMemberPrecedes`, `thm_zeroMemberPrecedes_iff_height_radial_lex`, `TZeroPassage.precedes`
- **Entraîne** : `heightProgression_of_horizontalExclusion`, `interTowerExcess_nonneg`, `interTowerExcess_pos_iff_riemannHypothesis`, `offPassages_interTowerExcess_pos_iff_riemannHypothesis`, `passage_deltaT_nonneg`, `verticalEnergyPush_of_riemannHypothesis`

#### `interTowerExcess_nonneg` — `Terminal/InterTowerExcess` l.147 — CONFIRMÉE
- **Énoncé** : L'excès inter-Tours est toujours positif ou nul.
- **Vérités** : `AJOUT` (positivité large de l'excès inter-Tours) | touche : V155
- **Repose sur** : `interTowerExcess`, `interTowerExcess_eq`, `passage_height_le` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rPrimeGapLogRatio`, `nZeroSourceIndex`, `thm_primeGapLogRatio_pos`
- **Entraîne** : `passage_double_constraint`, `succession_invariants`

#### `off_excess_zero` — `Terminal/InterTowerExcess` l.155 — CONFIRMÉE SOUS CONDITION (pour un zéro hors ligne)
- **Énoncé** : Un zéro hors ligne produit un passage qui satisfait les trois hypothèses grammaticales (place +1, raccord, occurrence stricte) avec un excès inter-Tours nul.
- **Vérités** : V57 | touche : V66 ; V155
- **Repose sur** : `TrueZero`, `occurrence`, `expectedMinimumPrime`, `interTowerExcess`, `off_event_increment_without_height`, `interTowerExcess_eq_zero_iff` ; base rhv3 : `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroSourceIndex`
- **Entraîne** : (aucun)

#### `interTowerExcess_pos_iff_riemannHypothesis` — `Terminal/InterTowerExcess` l.169 — ÉQUIVALENTE À RH (`∀ passage, 0 < J(p)` ⟺ RH)
- **Énoncé** : Exiger un excès inter-Tours strictement positif sur tout passage est équivalent à RH.
- **Vérités** : V58 | touche : V155
- **Repose sur** : `interTowerExcess`, `heightProgression_iff_riemannHypothesis`, `passage_height_le`, `interTowerExcess_pos_iff` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`
- **Entraîne** : `displacement_forced_iff_grammarByHeight`, `grammar_forces_displacement`, `interTowerExcess_pos_of_grammar_iff_riemannHypothesis`, `noNullPassage_iff_interTowerExcess_pos`

#### `offPassages_interTowerExcess_pos_iff_riemannHypothesis` — `Terminal/InterTowerExcess` l.182 — ÉQUIVALENTE À RH (restriction aux passages à extrémité hors ligne)
- **Énoncé** : La même exigence sur les seuls passages à extrémité hors ligne est encore équivalente à RH.
- **Vérités** : V58 | touche : V155
- **Repose sur** : `interTowerExcess`, `offPassages_heightProgression_iff_riemannHypothesis`, `passage_height_le`, `interTowerExcess_pos_iff` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `PIsOffCriticalLine`
- **Entraîne** : (aucun)

#### `grammar_hypotheses_of_passage` — `Terminal/InterTowerExcess` l.198 — CONFIRMÉE
- **Énoncé** : Les trois hypothèses grammaticales (place +1, raccord `Occ(l) = p_min(e)`, occurrence strictement croissante) tiennent sur tout passage.
- **Vérités** : V56, V57
- **Repose sur** : `occurrence`, `expectedMinimumPrime`, `passage_event_increment` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroSourceIndex`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `interTowerExcess_pos_of_grammar_iff_riemannHypothesis`

#### `interTowerExcess_pos_of_grammar_iff_riemannHypothesis` — `Terminal/InterTowerExcess` l.207 — ÉQUIVALENTE À RH (les trois hypothèses grammaticales sont inconditionnelles ; l'énoncé reste ⟺ RH)
- **Énoncé** : Ajouter les trois hypothèses grammaticales à « excès strictement positif » ne change rien : l'énoncé reste équivalent à RH.
- **Vérités** : V58 | touche : V60
- **Repose sur** : `occurrence`, `expectedMinimumPrime`, `interTowerExcess`, `interTowerExcess_pos_iff_riemannHypothesis`, `grammar_hypotheses_of_passage` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroSourceIndex`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : (aucun)

#### `noNullPassage_iff_riemannHypothesis` — `Terminal/InterTowerExcess` l.232 — ÉQUIVALENTE À RH (`PNoNullPassage` (aucun passage nul) ⟺ RH)
- **Énoncé** : L'absence de passage nul est équivalente à RH.
- **Vérités** : V188 | touche : V189
- **Repose sur** : `PNoNullPassage`, `riemannHypothesis_of_noOff`, `TrueZero`, `occurrence`, `expectedMinimumPrime`, `off_event_increment_without_height`, `passage_height_lt_of_riemannHypothesis` ; base rhv3 : `TZeroPassage`, `PZeroPassageRelationNull`, `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroSourceIndex`, `thm_zeroPassage_null_iff_sameHeight`
- **Entraîne** : `horizontalExclusion_iff_riemannHypothesis`, `noNullPassage_iff_heightProgression`, `noNullPassage_iff_interTowerExcess_pos`, `premise_ladder_tfae`, `riemannHypothesis_of_noNullPassage`

#### `riemannHypothesis_of_noNullPassage` — `Terminal/InterTowerExcess` l.247 — IMPLIQUE RH SOUS PRÉMISSE (`PNoNullPassage`, ⟺ RH par `noNullPassage_iff_riemannHypothesis`)
- **Énoncé** : `PNoNullPassage` entraîne RH.
- **Vérités** : V188 | touche : V189 ; I3
- **Repose sur** : `PNoNullPassage`, `noNullPassage_iff_riemannHypothesis` ; base rhv3 : (aucun)
- **Entraîne** : (aucun)

#### `noNullPassage_iff_heightProgression` — `Terminal/InterTowerExcess` l.251 — ÉQUIVALENTE À RH (`PNoNullPassage` ⟺ RH par `noNullPassage_iff_riemannHypothesis`)
- **Énoncé** : L'absence de passage nul est la même prémisse que « la hauteur progresse sur tout passage ».
- **Vérités** : V58, V188
- **Repose sur** : `PNoNullPassage`, `noNullPassage_iff_riemannHypothesis`, `heightProgression_iff_riemannHypothesis` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`
- **Entraîne** : (aucun)

#### `noNullPassage_iff_interTowerExcess_pos` — `Terminal/InterTowerExcess` l.257 — ÉQUIVALENTE À RH (`PNoNullPassage` ⟺ RH par `noNullPassage_iff_riemannHypothesis`)
- **Énoncé** : L'absence de passage nul est la même prémisse que « l'excès inter-Tours est strictement positif sur tout passage ».
- **Vérités** : V188 | touche : V155
- **Repose sur** : `PNoNullPassage`, `interTowerExcess`, `noNullPassage_iff_riemannHypothesis`, `interTowerExcess_pos_iff_riemannHypothesis` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`
- **Entraîne** : (aucun)


##### `Terminal/LocalReading`

#### `localReading_modeA` — `Terminal/LocalReading` l.49 — CONFIRMÉE SOUS CONDITION (hauteur strictement croissante et positions radiales égales (mode A) ; hauteurs positives)
- **Énoncé** : En mode A (au sens de ce fichier : hauteur croissante, même position radiale), la « lecture orientée » (terme hors maître) tient : l'amplitude du terme postérieur au raccord `Occ(l)` est au plus celle du terme antérieur au même point.
- **Vérités** : `AJOUT` (lecture énergétique orientée au raccord en mode A) | touche : V181
- **Repose sur** : `zeroTerm`, `occurrence`, `occurrence_pos`, `amplitude_lt_of_height_lt` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : (aucun)

#### `localReading_fails_modeC` — `Terminal/LocalReading` l.61 — CONFIRMÉE SOUS CONDITION (même hauteur, `β_e < β_l`, `T_e ≥ 2` (mode C))
- **Énoncé** : En mode C, à hauteur `T ≥ 2`, la lecture orientée est fausse au raccord `Occ(l)` : l'amplitude du terme antérieur y est strictement inférieure à celle du postérieur.
- **Vérités** : V170 ; `AJOUT` (la lecture orientée échoue au raccord dès T ≥ 2 en mode C) | touche : V165
- **Repose sur** : `zeroTerm`, `occurrence`, `expectedMinimumPrime`, `sameHeight_amplitude_inverts_at_raccords` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroRadialPosition`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `riemannHypothesis_of_localReading`

#### `localReading_of_riemannHypothesis` — `Terminal/LocalReading` l.73 — CONFIRMÉE (implication : RH ⟹ `PLocalReadingOrientation`, les deux termes de la vérité)
- **Énoncé** : RH entraîne la lecture orientée au raccord (prémisse `PLocalReadingOrientation`).
- **Vérités** : `AJOUT` (RH ⟹ lecture orientée locale)
- **Repose sur** : `PLocalReadingOrientation`, `occurrence`, `occurrence_prime`, `verticalEnergyPush_of_riemannHypothesis` ; base rhv3 : `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`
- **Entraîne** : `localReading_iff_riemannHypothesis`

#### `riemannHypothesis_of_localReading` — `Terminal/LocalReading` l.81 — IMPLIQUE RH SOUS PRÉMISSE (`PNoLowOffZero` (tout zéro hors ligne a T ≥ 2, fait classique hors base) et `PLocalReadingOrientation` ; non déchargées dans le projet)
- **Énoncé** : Sous `PNoLowOffZero`, la lecture orientée au seul raccord `Occ(l)` entraîne RH.
- **Vérités** : `AJOUT` (fermeture conditionnelle par lecture locale) | touche : I3 ; O17
- **Repose sur** : `PNoLowOffZero`, `PLocalReadingOrientation`, `riemannHypothesis_of_noOff`, `TrueZero`, `occurrence`, `expectedMinimumPrime`, `off_event_increment_without_height`, `HorizontalMirrorRealization`, `nullPassage_horizontal`, `zeroTerm`, `localReading_fails_modeC` ; base rhv3 : `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `PIsNonTrivialZetaZero`, `TZeroPassage`, `rZeroHeight`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroSourceIndex`, `PZeroPassageRelationNull`, `thm_zeroPassage_null_iff_sameHeight` et 1 autres
- **Entraîne** : `localReading_iff_riemannHypothesis`

#### `localReading_iff_riemannHypothesis` — `Terminal/LocalReading` l.91 — ÉQUIVALENTE À RH (modulo `PNoLowOffZero` : `PLocalReadingOrientation` ⟺ RH)
- **Énoncé** : Modulo `PNoLowOffZero`, la prémisse de lecture orientée locale est exactement RH.
- **Vérités** : `AJOUT` (équivalence lecture orientée locale ⟺ RH modulo PNoLowOffZero) | touche : I3
- **Repose sur** : `PNoLowOffZero`, `PLocalReadingOrientation`, `riemannHypothesis_of_localReading`, `localReading_of_riemannHypothesis` ; base rhv3 : (aucun)
- **Entraîne** : (aucun)

### Lot B3 — B3 (Terminal actifs M–Z)

##### Terminal.MirrorDegeneracy

#### `mirror_radial_shift` — `Terminal.MirrorDegeneracy` l.35 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, β(miroir) − β = 1 − 2β.
- **Vérités** : V65
- **Repose sur** : `TrueZero`, `mirrorMember`, `mirrorMember_radial` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `mirror_radial_shift_eq_zero_iff` (1)

#### `mirror_radial_shift_eq_zero_iff` — `Terminal.MirrorDegeneracy` l.41 — CONFIRMÉE
- **Énoncé** : Δβ = 0 si et seulement si β = 1/2.
- **Vérités** : V65 ; V161
- **Repose sur** : `TrueZero`, `mirrorMember`, `mirror_radial_shift` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `mirror_degeneracy_of_onLine`, `mirror_degeneracy_tfae` (2)

#### `mirror_contact_ratio_const` — `Terminal.MirrorDegeneracy` l.50 — CONFIRMÉE
- **Énoncé** : Pour tout k, le rayon k du miroir vaut le rayon k de z multiplié par le facteur unique exp((φ* − φ)/T), indépendant de k.
- **Vérités** : V184 (mécanisme de la translation) ; AJOUT pour le facteur exact
- **Repose sur** : `TowerMotion.incidence`, `TowerMotion.phase`, `TrueZero`, `contactMinusAt`, `mirrorMember`, `mirrorMember_ordinate`, `towerMotionOf`, `towerMotion_incidence` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : `mirror_contact_eq_depth`, `onLine_of_mirror_phase_shift_eq_zero` (2)

#### `mirror_translation_factor_eq_one_iff` — `Terminal.MirrorDegeneracy` l.64 — CONFIRMÉE
- **Énoncé** : Le facteur de translation vaut 1 si et seulement si Δφ = 0.
- **Vérités** : AJOUT
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `mirrorMember`, `towerMotionOf` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : `mirror_all_contacts_shift_of_offLine`, `onLine_of_mirror_phase_shift_eq_zero` (2)

#### `mirror_phase_shift_eq_zero_of_onLine` — `Terminal.MirrorDegeneracy` l.79 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sur la ligne (β = 1/2), Δφ = 0.
- **Vérités** : V161 ; V77
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `mirrorMember`, `mirrorMember_eq_self_of_onLine`, `towerMotionOf` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `mirror_degeneracy_of_onLine`, `mirror_degeneracy_tfae` (2)

#### `mirror_contacts_eq_of_onLine` — `Terminal.MirrorDegeneracy` l.85 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sur la ligne, les deux contacts de chaque cellule du miroir coïncident avec ceux de z, pour tout k.
- **Vérités** : V161 ; V77
- **Repose sur** : `TrueZero`, `contactMinusAt`, `contactPlusAt`, `mirrorMember`, `mirrorMember_eq_self_of_onLine` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `mirror_degeneracy_of_onLine`, `mirror_degeneracy_tfae` (2)

#### `mirror_zeroTerm_eq_of_onLine` — `Terminal.MirrorDegeneracy` l.92 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sur la ligne, le terme explicite du miroir égale celui du zéro en tout q.
- **Vérités** : V161 ; V101 (terme explicite)
- **Repose sur** : `TrueZero`, `mirrorMember`, `mirrorMember_eq_self_of_onLine`, `zeroTerm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `horizontal_energy_action_zero_of_onLine`, `mirror_degeneracy_of_onLine` (2)

#### `mirror_degeneracy_of_onLine` — `Terminal.MirrorDegeneracy` l.98 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sur la ligne, Δβ = 0, Δφ = 0, tous les contacts et tous les termes coïncident : le mécanisme miroir horizontal est dégénéré.
- **Vérités** : V161 ; V77
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `contactMinusAt`, `contactPlusAt`, `mirrorMember`, `mirror_contacts_eq_of_onLine`, `mirror_phase_shift_eq_zero_of_onLine`, `mirror_radial_shift_eq_zero_iff`, `mirror_zeroTerm_eq_of_onLine`, `towerMotionOf`, `zeroTerm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)

#### `onLine_of_mirror_phase_shift_eq_zero` — `Terminal.MirrorDegeneracy` l.112 — CONFIRMÉE
- **Énoncé** : Si Δφ = 0 alors β = 1/2.
- **Vérités** : V161 (réciproque) ; V185 (D = 0 ⟺ ligne)
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `contactMinusAt`, `contactMinus_eq_iff_radial_eq`, `mirrorMember`, `mirrorMember_ordinate`, `mirrorMember_radial`, `mirror_contact_ratio_const`, `mirror_translation_factor_eq_one_iff`, `towerMotionOf` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : `mirror_all_contacts_shift_of_offLine`, `mirror_degeneracy_tfae` (2)

#### `onLine_of_mirror_contact_eq` — `Terminal.MirrorDegeneracy` l.121 — CONFIRMÉE
- **Énoncé** : Si un seul rayon du miroir coïncide avec le rayon de même indice de z, alors β = 1/2.
- **Vérités** : V162 ; V184
- **Repose sur** : `TrueZero`, `contactMinusAt`, `mirrorMember`, `mirror_contact_eq_iff_onLine` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `mirror_all_contacts_shift_of_offLine`, `mirror_degeneracy_tfae` (2)

#### `mirror_degeneracy_tfae` — `Terminal.MirrorDegeneracy` l.128 — CONFIRMÉE
- **Énoncé** : β = 1/2 ⟺ Δβ = 0 ⟺ Δφ = 0 ⟺ (∃k, ΔC_k = 0) ⟺ (∀k, ΔC_k = 0).
- **Vérités** : V161 ; V185
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `contactMinusAt`, `contactPlusAt`, `mirrorMember`, `mirror_contacts_eq_of_onLine`, `mirror_phase_shift_eq_zero_of_onLine`, `mirror_radial_shift_eq_zero_iff`, `onLine_of_mirror_contact_eq`, `onLine_of_mirror_phase_shift_eq_zero`, `towerMotionOf` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `insertionDepth_eq_zero_iff` (1)

#### `mirror_all_contacts_shift_of_offLine` — `Terminal.MirrorDegeneracy` l.146 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Hors ligne, le facteur de translation est ≠ 1 et aucun rayon k du miroir n'égale le rayon k de z.
- **Vérités** : V162 ; V163 (cas de même indice k seulement) ; V184
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `contactMinusAt`, `mirrorMember`, `mirror_translation_factor_eq_one_iff`, `onLine_of_mirror_contact_eq`, `onLine_of_mirror_phase_shift_eq_zero`, `towerMotionOf` ; base rhv3 : `PIsNonTrivialZetaZero`, `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : (aucun) (0)

#### `sameHeight_grid_rigid_translation` — `Terminal.MirrorDegeneracy` l.163 — CONFIRMÉE
- **Énoncé** : À même hauteur, la grille de w est celle de z translatée par le facteur unique exp((φ_w − φ_z)/T).
- **Vérités** : V184 ; V158 ; AJOUT (énoncé pour tout couple de même hauteur)
- **Repose sur** : `TowerMotion.incidence`, `TowerMotion.phase`, `TrueZero`, `contactMinusAt`, `towerMotionOf`, `towerMotion_incidence` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : `passage_grid_translation_of_sameHeight` (1)

#### `sameHeight_pitch_invariant` — `Terminal.MirrorDegeneracy` l.177 — CONFIRMÉE
- **Énoncé** : À même hauteur, le pas logarithmique entre deux rayons consécutifs est identique pour z et w : il ne voit pas β.
- **Vérités** : V17 ; V158
- **Repose sur** : `TrueZero`, `contactAt_consecutive_logWidth`, `contactMinusAt`, `contactPlusAt` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : (aucun) (0)

#### `sameRadial_height_changes_pitch` — `Terminal.MirrorDegeneracy` l.185 — CONFIRMÉE
- **Énoncé** : Si deux zéros ont des hauteurs distinctes, leurs pas logarithmiques diffèrent à tout rayon.
- **Vérités** : V17 ; V158
- **Repose sur** : `TrueZero`, `contactAt_consecutive_logWidth`, `contactMinusAt`, `contactPlusAt` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : (aucun) (0)

#### `horizontal_energy_action` — `Terminal.MirrorDegeneracy` l.198 — CONFIRMÉE
- **Énoncé** : Pour deux zéros quelconques w, z et q > 0, log‖E_w(q)‖ − log‖E_z(q)‖ = Δβ·log q − log(‖ρ_w‖/‖ρ_z‖) (docstring ≠ type : la docstring dit « même hauteur », le type ne l'exige pas).
- **Vérités** : V173 (exposant réel de l'amplitude) ; V102
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroPoint_norm_pos`, `zeroTerm`, `zeroTerm_norm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)

#### `horizontal_energy_action_zero_of_onLine` — `Terminal.MirrorDegeneracy` l.211 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sur la ligne, log‖E_{z*}(q)‖ − log‖E_z(q)‖ = 0 pour tout q.
- **Vérités** : V102 (sur la droite amplitudes égales) ; V161
- **Repose sur** : `TrueZero`, `mirrorMember`, `mirror_zeroTerm_eq_of_onLine`, `zeroTerm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)


##### Terminal.MirrorFrequency

#### `phase_increment_eq_pi_span` — `Terminal.MirrorFrequency` l.28 — CONFIRMÉE
- **Énoncé** : La portée de Tour TowerPrimeGapSpan z n égale l'accroissement de phase π·ΔΘ du terme explicite de z entre les deux premiers de la place n.
- **Vérités** : V100 (position de Tour = argument du terme) ; AJOUT (portée = accroissement de phase)
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `pi_mul_towerPosition`, `towerMotionOf`, `towerPosition` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `TowerPrimeGapSpan`, `fnPrimeAtRank`, `fnPrimeSuccessor`, `rPrimeGapLogRatio`, `rTowerHeight`, `rZeroHeight`, `thm_primeAtRank_pos`
- **Entraîne** : `consecutive_continuous_signature`, `height_lower_bound_of_phase_quantum`, `interTowerExcess_eq`, `off_consecutive_continuous_progression_eq_span`, `phase_increment_eq_of_sameHeight`, `phase_increment_ge_height_mul_log_one_add_inv`, `phase_increment_ge_height_mul_log_one_add_two_div`, `phase_increment_pos` (8)

#### `mirror_phase_increment_eq` — `Terminal.MirrorFrequency` l.45 — CONFIRMÉE
- **Énoncé** : Le miroir progresse en phase exactement comme z sur tout intervalle [q1, q2].
- **Vérités** : V65 ; V158 ; AJOUT
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `mirrorMember`, `mirrorMember_ordinate`, `pi_mul_towerPosition`, `towerMotionOf`, `towerPosition` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : `off_consecutive_translation_signature`, `off_mirror_same_frequency` (2)

#### `mirror_phase_offset_const` — `Terminal.MirrorFrequency` l.57 — CONFIRMÉE
- **Énoncé** : À q fixé, le déphasage entre le terme de z et celui du miroir ne dépend que des deux phases tangentielles, non de q.
- **Vérités** : AJOUT
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `mirrorMember`, `mirrorMember_ordinate`, `pi_mul_towerPosition`, `towerMotionOf`, `towerPosition` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : (aucun) (0)

#### `mirror_span_eq` — `Terminal.MirrorFrequency` l.67 — CONFIRMÉE
- **Énoncé** : Le miroir lit la même portée première S_n que z sur tout rang n.
- **Vérités** : V65 ; V159
- **Repose sur** : `TrueZero`, `mirrorMember`, `mirrorMember_ordinate` ; base rhv3 : `TowerPrimeGapSpan`, `rTowerHeight`, `thm_towerPrimeGapSpan_eq_iff_height_eq`
- **Entraîne** : `off_consecutive_continuous_progression_eq_span`, `off_consecutive_translation_signature`, `off_mirror_same_frequency`, `onLine_mirror_trivial` (4)

#### `member_index_lt_of_lowerSide` — `Terminal.MirrorFrequency` l.78 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour un zéro de côté bas (β < 1/2), l'index de membre de z est strictement inférieur à celui de son miroir.
- **Vérités** : V68 ; V74
- **Repose sur** : `TrueZero`, `mirrorMember`, `sourceIndex_lt_mirror` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `nZeroSourceIndex`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)

#### `off_member_index_lt_mirror` — `Terminal.MirrorFrequency` l.83 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour un zéro hors ligne, l'un des deux membres de la paire précède strictement l'autre dans l'index de membre (celui de côté bas, z ou son miroir).
- **Vérités** : V68 ; V74
- **Repose sur** : `TrueZero`, `mirrorMember`, `off_lowerSide`, `sourceIndex_lt_mirror` ; base rhv3 : `PIsNonTrivialZetaZero`, `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `nZeroSourceIndex`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)

#### `member_index_succ_of_consecutive` — `Terminal.MirrorFrequency` l.92 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous consécutivité stricte de z et de son miroir, l'index du miroir vaut celui de z plus un.
- **Vérités** : V68 ; V144
- **Repose sur** : `TrueZero`, `mirrorMember`, `mirror_sourceIndex_of_consecutive` ; base rhv3 : `PIsNonTrivialZetaZero`, `PZeroMembersConsecutive`, `TNonTrivialZetaZero`, `nZeroSourceIndex`
- **Entraîne** : (aucun) (0)

#### `mirror_heightEventIndex_eq` — `Terminal.MirrorFrequency` l.102 — CONFIRMÉE
- **Énoncé** : L'événement de hauteur du miroir est celui de z.
- **Vérités** : V127 ; V131
- **Repose sur** : `TrueZero`, `mirrorMember`, `mirror_sameHeightIndex` ; base rhv3 : `nZeroHeightEventIndex`, `tZeroHeightEvent`
- **Entraîne** : `off_consecutive_translation_signature`, `off_mirror_same_frequency`, `onLine_mirror_trivial` (3)

#### `off_mirror_same_frequency` — `Terminal.MirrorFrequency` l.112 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour un zéro hors ligne, le miroir a même hauteur, même événement de hauteur, même portée première sur tout rang et même progression de phase sur tout intervalle, mais une position radiale et un index de membre distincts.
- **Vérités** : V127 ; V131 ; V159 ; V162 ; V64
- **Repose sur** : `TrueZero`, `mirrorMember`, `mirrorMember_ordinate`, `mirrorMember_radial`, `mirror_heightEventIndex_eq`, `mirror_phase_increment_eq`, `mirror_span_eq`, `towerPosition` ; base rhv3 : `PIsNonTrivialZetaZero`, `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `TowerPrimeGapSpan`, `nZeroHeightEventIndex`, `nZeroSourceIndex`, `rZeroHeight`, `rZeroRadialPosition`, `tZeroHeightEvent`, `thm_offCriticalLine_mirror_distinct`, `thm_zeroSourceIndex_injective`
- **Entraîne** : `off_mirror_same_frequency_of_consecutive` (1)

#### `off_mirror_same_frequency_of_consecutive` — `Terminal.MirrorFrequency` l.136 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous consécutivité stricte, hors ligne : le paquet précédent, plus n(z*) = n(z) + 1 et Occ(z*) = p_min(z).
- **Vérités** : V144 ; V69 ; V64
- **Repose sur** : `TrueZero`, `expectedMinimumPrime`, `expectedMinimum_eq_mirror_occurrence_of_consecutive`, `mirrorMember`, `mirror_sourceIndex_of_consecutive`, `occurrence`, `off_mirror_same_frequency`, `towerPosition` ; base rhv3 : `PIsNonTrivialZetaZero`, `PIsOffCriticalLine`, `PZeroMembersConsecutive`, `TNonTrivialZetaZero`, `TowerPrimeGapSpan`, `nZeroHeightEventIndex`, `nZeroSourceIndex`, `rZeroHeight`, `rZeroRadialPosition`, `tZeroHeightEvent`
- **Entraîne** : (aucun) (0)

#### `onLine_mirror_trivial` — `Terminal.MirrorFrequency` l.157 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sur la ligne, le miroir est le zéro lui-même : toutes les différences (hauteur, événement, portée, position radiale, index) sont triviales.
- **Vérités** : V77 ; V161
- **Repose sur** : `TrueZero`, `mirrorMember`, `mirrorMember_eq_self_of_onLine`, `mirrorMember_ordinate`, `mirror_heightEventIndex_eq`, `mirror_span_eq` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `TowerPrimeGapSpan`, `nZeroHeightEventIndex`, `nZeroSourceIndex`, `rZeroHeight`, `rZeroRadialPosition`, `tZeroHeightEvent`
- **Entraîne** : (aucun) (0)


##### Terminal.PairedZerosExperiment

#### `control_two_onLine_towers_unique` — `Terminal.PairedZerosExperiment` l.167 — CONFIRMÉE
- **Énoncé** : Pour deux zéros de la ligne, toute coordonnée dont la cellule contient le minimum attendu du zéro est la coordonnée d'entrée de sa Tour propre (la preuve n'utilise que firstTower_contactPair_unique ; l'hypothèse β = 1/2 y est superflue).
- **Vérités** : V143 ; V15
- **Repose sur** : `AnalyticContactPair.entryCoordinate`, `TrueTower.properState`, `TrueZero`, `contactMinusAt`, `contactPlusAt`, `expectedMinimumPrime`, `firstTowerOf`, `firstTower_contactPair_unique` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)

#### `off_pair_towers_unique_like_control` — `Terminal.PairedZerosExperiment` l.183 — CONFIRMÉE
- **Énoncé** : Pour un zéro et son miroir, toute coordonnée dont la cellule contient le minimum attendu est la coordonnée d'entrée de la Tour propre : unicité identique au contrôle ON, sans hypothèse sur β.
- **Vérités** : V143 ; V15 ; V25
- **Repose sur** : `AnalyticContactPair.entryCoordinate`, `TrueTower.properState`, `TrueZero`, `contactMinusAt`, `contactPlusAt`, `expectedMinimumPrime`, `firstTowerOf`, `firstTower_contactPair_unique`, `mirrorMember` ; base rhv3 : (aucun)
- **Entraîne** : (aucun) (0)

#### `forcing_shared_expectedMinimum_is_collage` — `Terminal.PairedZerosExperiment` l.200 — CONFIRMÉE
- **Énoncé** : Deux zéros de même minimum attendu ont même index de membre.
- **Vérités** : V149 ; V182
- **Repose sur** : `TrueZero`, `expectedMinimumPrime` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `fnPrimeAtRank`, `nZeroSourceIndex`, `thm_primeAtRank_strictMono`
- **Entraîne** : (aucun) (0)

#### `secondTower_inversion_is_unconditional` — `Terminal.PairedZerosExperiment` l.215 — CONFIRMÉE
- **Énoncé** : Les deux contacts de la seconde Tour sont, sans condition, les contacts du zéro réfléchi (mouvement réfléchi du membre miroir) aux coordonnées −(k+1) et −(k+1)+1, k étant la coordonnée de pivot du miroir.
- **Vérités** : V34 ; V80 ; V82 ; touche T6
- **Repose sur** : `InvertedContactPair.entryContact`, `InvertedContactPair.lastRayContact`, `InvertedTower.toInvertedContactPair`, `TrueZero`, `expectedMinimumPrime`, `mirrorMember`, `pivotCoordinate`, `reflectedIncidence`, `secondTowerOf`, `secondTower_entry_eq_reflected`, `secondTower_lastRay_eq_reflected` ; base rhv3 : (aucun)
- **Entraîne** : (aucun) (0)

#### `remaining_open_question_is_readout_only` — `Terminal.PairedZerosExperiment` l.227 — CONFIRMÉE
- **Énoncé** : La seconde Tour atteint l'occurrence du miroir si et seulement si la coordonnée de pivot de Occ(z*) est strictement inférieure à celle de p_min(z*) : c'est le constat de lecture (C_lecture) ; le type n'affirme rien de plus sur le caractère « seule question ouverte ».
- **Vérités** : V85 ; V135 ; O11 (touché : la lecture reste data-dépendante)
- **Repose sur** : `InvertedContactPair.reaches`, `InvertedTower.properState`, `TrueZero`, `expectedMinimumPrime`, `mirrorMember`, `occurrence`, `pivotCoordinate`, `secondTowerOf`, `secondTower_reads_occurrence_iff_coordinate_lt` ; base rhv3 : (aucun)
- **Entraîne** : (aucun) (0)


##### Terminal.RayCapture

#### `insertionDepth_eq` — `Terminal.RayCapture` l.45 — CONFIRMÉE
- **Énoncé** : D(z) = (arctan(T/β) − arctan(T/(1−β)))/π.
- **Vérités** : V185 ; AJOUT (forme explicite)
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `insertionDepth`, `insertionDepth.eq_1`, `mirrorMember`, `mirrorMember_phase`, `towerMotionOf`, `towerMotion_phase` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : `_private.Terminal.RayCapture.0.contact_lt_mirror_iff`, `_private.Terminal.RayCapture.0.mirror_contact_lt_iff`, `insertionDepth_le`, `insertionDepth_pos_iff` (4)

#### `contactMinusAt_eq_exp` — `Terminal.RayCapture` l.51 — CONFIRMÉE
- **Énoncé** : Le rayon k de z vaut exp((arctan(T/β) + kπ)/T).
- **Vérités** : V16 ; V23 ; AJOUT (formule explicite)
- **Repose sur** : `TowerMotion.incidence`, `TowerMotion.phase`, `TrueZero`, `contactMinusAt`, `towerMotionOf`, `towerMotion_incidence`, `towerMotion_phase` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : `_private.Terminal.RayCapture.0.contact_lt_mirror_iff`, `_private.Terminal.RayCapture.0.mirror_contact_lt_iff` (2)

#### `mirror_contact_eq_depth` — `Terminal.RayCapture` l.58 — CONFIRMÉE
- **Énoncé** : C_k(z*) = C_k(z)·exp(−π·D/T) pour tout k.
- **Vérités** : V184 ; V185
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `contactMinusAt`, `insertionDepth`, `mirrorMember`, `mirror_contact_ratio_const`, `towerMotionOf` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : (aucun) (0)

#### `mirror_relative_position` — `Terminal.RayCapture` l.68 — CONFIRMÉE
- **Énoncé** : La position relative logarithmique du rayon k du miroir dans la cellule [C_{k−1}(z), C_k(z)] vaut 1 − D.
- **Vérités** : V183 ; V185
- **Repose sur** : `TowerMotion.incidence`, `TowerMotion.phase`, `TrueZero`, `contactMinusAt`, `insertionDepth`, `mirrorMember`, `mirrorMember_ordinate`, `towerMotionOf`, `towerMotion_incidence` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : (aucun) (0)

#### `phase_lt_iff` — `Terminal.RayCapture` l.84 — CONFIRMÉE
- **Énoncé** : arctan(T/(1−β)) < arctan(T/β) si et seulement si β < 1/2.
- **Vérités** : AJOUT (lemme de signe de D)
- **Repose sur** : `TrueZero` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroRadialPosition_lt_one`, `thm_zeroRadialPosition_positive`
- **Entraîne** : `insertionDepth_pos_iff` (1)

#### `insertionDepth_pos_iff` — `Terminal.RayCapture` l.94 — CONFIRMÉE
- **Énoncé** : D > 0 si et seulement si β < 1/2.
- **Vérités** : V185
- **Repose sur** : `TrueZero`, `_private.Terminal.RayCapture.0.phase_lt_iff`, `insertionDepth`, `insertionDepth_eq` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : `zeroInsertionDepth_iff_riemannHypothesis` (1)

#### `insertionDepth_eq_zero_iff` — `Terminal.RayCapture` l.99 — CONFIRMÉE
- **Énoncé** : D = 0 si et seulement si β = 1/2.
- **Vérités** : V185 ; V188
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `contactMinusAt`, `insertionDepth`, `insertionDepth.eq_1`, `mirrorMember`, `mirrorMember_eq_self_of_onLine`, `mirror_degeneracy_tfae`, `towerMotionOf` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `capture_of_onLine`, `raySuperposed_iff`, `zeroInsertionDepth_iff_riemannHypothesis` (3)

#### `abs_insertionDepth_lt_half` — `Terminal.RayCapture` l.109 — CONFIRMÉE
- **Énoncé** : |D| < 1/2 pour tout zéro.
- **Vérités** : AJOUT
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `insertionDepth`, `mirrorMember`, `towerMotionOf`, `towerMotion_phase_lt_pi_div_two`, `towerMotion_phase_pos` ; base rhv3 : (aucun)
- **Entraîne** : `rayStrictlyInterlaced_iff` (1)

#### `mirror_contact_lt_iff` — `Terminal.RayCapture` l.134 — CONFIRMÉE
- **Énoncé** : Comparaison du rayon k du miroir au rayon j de z : C_k(z*) < C_j(z) ⟺ −D < j − k (hypothèse de notation c = j − k).
- **Vérités** : V183 (mécanisme) ; AJOUT
- **Repose sur** : `TrueZero`, `contactMinusAt`, `contactMinusAt_eq_exp`, `insertionDepth`, `insertionDepth_eq`, `mirrorMember`, `mirrorMember_contactMinusAt` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : `rayStrictlyInterlaced_iff` (1)

#### `contact_lt_mirror_iff` — `Terminal.RayCapture` l.145 — CONFIRMÉE
- **Énoncé** : C_j(z) < C_k(z*) ⟺ j − k < −D (hypothèse de notation c = j − k).
- **Vérités** : V183 (mécanisme) ; AJOUT
- **Repose sur** : `TrueZero`, `contactMinusAt`, `contactMinusAt_eq_exp`, `insertionDepth`, `insertionDepth_eq`, `mirrorMember`, `mirrorMember_contactMinusAt` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : `rayStrictlyInterlaced_iff` (1)

#### `rayStrictlyInterlaced_iff` — `Terminal.RayCapture` l.156 — CONFIRMÉE
- **Énoncé** : Le rayon k est strictement entrelacé si et seulement si D ≠ 0.
- **Vérités** : V185 ; V188
- **Repose sur** : `RayStrictlyInterlaced`, `TrueZero`, `_private.Terminal.RayCapture.0.contact_lt_mirror_iff`, `_private.Terminal.RayCapture.0.mirror_contact_lt_iff`, `abs_insertionDepth_lt_half`, `contactMinusAt`, `insertionDepth`, `mirrorMember` ; base rhv3 : (aucun)
- **Entraîne** : `capture_of_onLine`, `premise_ladder_tfae`, `strictlyInterlaced_uniform`, `superposed_xor_strictlyInterlaced` (4)

#### `raySuperposed_iff` — `Terminal.RayCapture` l.173 — CONFIRMÉE
- **Énoncé** : Le rayon k est superposé si et seulement si D = 0.
- **Vérités** : V185 ; V188
- **Repose sur** : `RaySuperposed`, `TrueZero`, `insertionDepth`, `insertionDepth_eq_zero_iff`, `mirror_contact_eq_iff_onLine` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `capture_of_onLine`, `premise_ladder_tfae`, `superposed_xor_strictlyInterlaced` (3)

#### `superposed_xor_strictlyInterlaced` — `Terminal.RayCapture` l.179 — CONFIRMÉE
- **Énoncé** : Pour tout zéro et tout rayon, exactement un des deux : superposition ou entrelacement strict.
- **Vérités** : V185
- **Repose sur** : `RayStrictlyInterlaced`, `RaySuperposed`, `TrueZero`, `insertionDepth`, `rayStrictlyInterlaced_iff`, `raySuperposed_iff` ; base rhv3 : (aucun)
- **Entraîne** : (aucun) (0)

#### `strictlyInterlaced_uniform` — `Terminal.RayCapture` l.189 — CONFIRMÉE
- **Énoncé** : L'entrelacement strict vaut à un rayon si et seulement s'il vaut à tout autre rayon.
- **Vérités** : V185
- **Repose sur** : `RayStrictlyInterlaced`, `TrueZero`, `insertionDepth`, `rayStrictlyInterlaced_iff` ; base rhv3 : (aucun)
- **Entraîne** : (aucun) (0)

#### `arctan_sub_le` — `Terminal.RayCapture` l.196 — CONFIRMÉE
- **Énoncé** : Pour x ≤ y, arctan y − arctan x ≤ y − x.
- **Vérités** : AJOUT (lemme analytique)
- **Repose sur** : (aucun) ; base rhv3 : (aucun)
- **Entraîne** : `insertionDepth_le` (1)

#### `insertionDepth_le` — `Terminal.RayCapture` l.204 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour β ≤ 1/2 : 0 ≤ D ≤ (1 − 2β)/(π·T).
- **Vérités** : V186
- **Repose sur** : `TrueZero`, `_private.Terminal.RayCapture.0.arctan_sub_le`, `insertionDepth`, `insertionDepth_eq` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroRadialPosition_lt_one`, `thm_zeroRadialPosition_positive`
- **Entraîne** : (aucun) (0)

#### `zeroInsertionDepth_iff_riemannHypothesis` — `Terminal.RayCapture` l.242 — ÉQUIVALENTE À RH
- **Énoncé** : D(z) = 0 pour tout zéro si et seulement si RH (via riemannHypothesis_iff_noLowerSide).
- **Vérités** : V188 ; V189 ; O21
- **Repose sur** : `PZeroInsertionDepth`, `TrueZero`, `insertionDepth`, `insertionDepth_eq_zero_iff`, `insertionDepth_pos_iff`, `mirrorMember`, `mirrorMember_radial`, `riemannHypothesis_iff_noLowerSide` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `premise_ladder_tfae` (1)

#### `premise_ladder_tfae` — `Terminal.RayCapture` l.256 — ÉQUIVALENTE À RH
- **Énoncé** : Les six formes (pas de passage nul, exclusion horizontale, superposition, absence d'entrelacement strict, D ≡ 0, RH) sont équivalentes.
- **Vérités** : V188 ; V189 ; O21
- **Repose sur** : `HorizontalMirrorRealization`, `PNoNullPassage`, `PNoStrictInterlacing`, `PRaySuperposition`, `PZeroInsertionDepth`, `RayStrictlyInterlaced`, `RaySuperposed`, `TrueZero`, `horizontalExclusion_iff_riemannHypothesis`, `insertionDepth`, `noNullPassage_iff_riemannHypothesis`, `rayStrictlyInterlaced_iff` et 2 autres ; base rhv3 : `TZeroPassage`
- **Entraîne** : `capture_forces_pure_verticality` (1)

#### `capture_forces_pure_verticality` — `Terminal.RayCapture` l.284 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la prémisse PNoStrictInterlacing (équivalente à RH par premise_ladder_tfae), tout passage progresse en hauteur, l'énergie horizontale est nulle, l'énergie verticale est positive et ‖E_l(q)‖ < ‖E_e(q)‖ pour tout q > 0.
- **Vérités** : V187 ; V189
- **Repose sur** : `HorizontalMirrorRealization`, `PNoNullPassage`, `PNoStrictInterlacing`, `PRaySuperposition`, `PZeroInsertionDepth`, `horizontalEnergy`, `onLine_passage_pure_vertical`, `premise_ladder_tfae`, `verticalEnergy`, `zeroTerm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroHeight`, `thm_zeroRadialPosition_half_of_riemannHypothesis`
- **Entraîne** : (aucun) (0)

#### `capture_of_onLine` — `Terminal.RayCapture` l.300 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour un zéro de la ligne, tous les rayons sont superposés et aucun n'est strictement entrelacé.
- **Vérités** : V187
- **Repose sur** : `RayStrictlyInterlaced`, `RaySuperposed`, `TrueZero`, `insertionDepth`, `insertionDepth_eq_zero_iff`, `rayStrictlyInterlaced_iff`, `raySuperposed_iff` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)


##### Terminal.RayEnergy

#### `cos_phase_eq` — `Terminal.RayEnergy` l.41 — CONFIRMÉE
- **Énoncé** : cos(phase de la Tour) = β/‖ρ‖.
- **Vérités** : V16 ; AJOUT
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `towerMotionOf`, `towerMotion_phase`, `zeroPoint`, `zeroPoint_norm_sq` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroRadialPosition_positive`
- **Entraîne** : `zeroTerm_re_eq_cos_towerPosition` (1)

#### `zeroTerm_re` — `Terminal.RayEnergy` l.53 — CONFIRMÉE
- **Énoncé** : Pour q > 0, la partie réelle du terme explicite q^ρ/ρ s'écrit exp(β log q)(β cos(T log q) + T sin(T log q))/|ρ|².
- **Vérités** : V100 ; AJOUT
- **Repose sur** : `TrueZero`, `cpow_zeroPoint_im`, `cpow_zeroPoint_re`, `zeroPoint`, `zeroPoint_im`, `zeroPoint_re`, `zeroTerm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : `zeroTerm_re_eq_cos_towerPosition` (1)

#### `phase_identity_cos` — `Terminal.RayEnergy` l.63 — CONFIRMÉE
- **Énoncé** : β cos θ + T sin θ = (β/cos φ)·cos(θ − φ).
- **Vérités** : V16 ; V100
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `towerMotionOf`, `towerMotion_phase` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroRadialPosition_positive`
- **Entraîne** : `zeroTerm_re_eq_cos_towerPosition` (1)

#### `zeroTerm_re_eq_cos_towerPosition` — `Terminal.RayEnergy` l.82 — CONFIRMÉE
- **Énoncé** : Pour q > 0, Re(terme du zéro en q) = q^β·cos(π·position de Tour en q)/‖ρ‖.
- **Vérités** : V100
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `cos_phase_eq`, `phase_identity_cos`, `pi_mul_towerPosition`, `towerMotionOf`, `towerPosition`, `zeroPoint`, `zeroPoint_norm_pos`, `zeroTerm`, `zeroTerm_re` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroRadialPosition_positive`
- **Entraîne** : `ray_energy` (1)

#### `ray_energy` — `Terminal.RayEnergy` l.95 — CONFIRMÉE
- **Énoncé** : Sur le rayon C_k, le terme est réel, de signe (−1)^k et d'amplitude C_k^β/‖ρ‖.
- **Vérités** : V100 ; V18
- **Repose sur** : `TowerMotion.incidence`, `TowerMotion.phase`, `TrueZero`, `contactMinusAt`, `contactMinusAt_positive`, `crossing_side`, `pi_mul_towerPosition`, `towerMotionOf`, `towerPosition`, `zeroPoint`, `zeroTerm`, `zeroTerm_re_eq_cos_towerPosition` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : `ray_energy_alternates`, `ray_zeroTerm_eq`, `succession_invariants` (3)

#### `ray_zeroTerm_eq` — `Terminal.RayEnergy` l.105 — CONFIRMÉE
- **Énoncé** : Le terme sur un rayon est exactement son énergie signée (partie imaginaire nulle).
- **Vérités** : V100
- **Repose sur** : `TrueZero`, `contactMinusAt`, `ray_energy`, `ray_zeroTerm_real`, `zeroPoint`, `zeroTerm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)

#### `ray_energy_alternates` — `Terminal.RayEnergy` l.115 — CONFIRMÉE
- **Énoncé** : Les énergies de deux rayons consécutifs sont de signes opposés.
- **Vérités** : V18
- **Repose sur** : `TrueZero`, `contactMinusAt`, `contactMinusAt_positive`, `ray_energy`, `zeroPoint`, `zeroPoint_norm_pos`, `zeroTerm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)

#### `ray_energy_growth` — `Terminal.RayEnergy` l.135 — CONFIRMÉE
- **Énoncé** : ‖E(C_{k+1})‖ = ‖E(C_k)‖·exp(πβ/T) : facteur fixé par β et T, indépendant de k.
- **Vérités** : V102 ; V17 ; AJOUT (facteur exp(πβ/T))
- **Repose sur** : `TowerMotion.incidence`, `TrueZero`, `contactMinusAt`, `contactMinusAt_positive`, `towerMotionOf`, `towerMotion_consecutive_width`, `zeroPoint`, `zeroTerm`, `zeroTerm_norm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)

#### `tower_reads_any_prime` — `Terminal.RayEnergy` l.157 — CONFIRMÉE
- **Énoncé** : Pour tout rang n, la cellule de coordonnée pivot du n-ième premier contient ce premier (C⁻ < p ≤ C⁺).
- **Vérités** : V143 ; V36 ; V61
- **Repose sur** : `TrueZero`, `contactMinusAt`, `contactPlusAt`, `pivotCoordinate`, `prime_raccord_has_unique_tower_cell` ; base rhv3 : `fnPrimeAtRank`, `thm_primeAtRank_isPrime`
- **Entraîne** : (aucun) (0)

#### `passage_double_constraint` — `Terminal.RayEnergy` l.166 — CONFIRMÉE
- **Énoncé** : Sur tout passage : Occ(l) = p_min(e), Occ(e) < Occ(l), le later tient Occ(l) dans sa cellule, l'earlier tient p_min(e) dans la sienne, et l'excès J ≥ 0.
- **Vérités** : V54 ; V56 ; V143 ; V155 (fichier InterTowerExcess cité)
- **Repose sur** : `contactMinusAt`, `contactPlusAt`, `expectedMinimumPrime`, `expectedMinimumPrime_pos`, `interTowerExcess`, `interTowerExcess_nonneg`, `occurrence`, `occurrence_pos`, `passage_event_increment`, `pivotCoordinate`, `prime_raccord_has_unique_tower_cell` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroSourceIndex`, `rZeroHeight`
- **Entraîne** : (aucun) (0)

#### `double_constraint_required_displacement` — `Terminal.RayEnergy` l.191 — CONFIRMÉE
- **Énoncé** : J = (T_l − T_e)·log(p_{n+2}/p_{n+1}), et J = 0 exactement sur un passage de même hauteur.
- **Vérités** : V155 ; V165 ; AJOUT (formule de J)
- **Repose sur** : `interTowerExcess`, `interTowerExcess_eq`, `interTowerExcess_eq_zero_iff` ; base rhv3 : `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroSourceIndex`, `rPrimeGapLogRatio`, `rZeroHeight`
- **Entraîne** : (aucun) (0)


##### Terminal.ReadingArithmetic

#### `towerPosition_sub` — `Terminal.ReadingArithmetic` l.32 — CONFIRMÉE
- **Énoncé** : Pour q1, q2 > 0, la différence de positions de Tour vaut T·log(q2/q1)/π.
- **Vérités** : V16
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `towerMotionOf`, `towerPosition` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : `coordinate_lt_of_gap_ge_pi`, `sameRing_imp_gap_lt_pi` (2)

#### `sameRing_imp_gap_lt_pi` — `Terminal.ReadingArithmetic` l.39 — CONFIRMÉE
- **Énoncé** : Deux références q1 ≤ q2 de même coordonnée de pivot ont T·log(q2/q1) < π.
- **Vérités** : V17 ; V32 ; AJOUT
- **Repose sur** : `TrueZero`, `pivotCoordinate`, `towerPosition`, `towerPosition_sub` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : (aucun) (0)

#### `coordinate_lt_of_gap_ge_pi` — `Terminal.ReadingArithmetic` l.55 — CONFIRMÉE
- **Énoncé** : Si T·log(q2/q1) ≥ π, la coordonnée de pivot de q1 est strictement inférieure à celle de q2.
- **Vérités** : V17 ; AJOUT
- **Repose sur** : `TrueZero`, `pivotCoordinate`, `towerPosition`, `towerPosition_sub` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : `secondTower_reads_of_gap_ge_pi` (1)

#### `secondTower_reads_of_gap_ge_pi` — `Terminal.ReadingArithmetic` l.72 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Si π ≤ T·log(p_min(z*)/Occ(z*)), la seconde Tour lit l'occurrence du miroir (condition suffisante pour C_lecture).
- **Vérités** : V85 ; O11
- **Repose sur** : `InvertedContactPair.reaches`, `InvertedTower.properState`, `TrueZero`, `coordinate_lt_of_gap_ge_pi`, `expectedMinimumPrime`, `expectedMinimumPrime_pos`, `mirrorMember`, `mirrorMember_ordinate`, `occurrence`, `occurrence_prime`, `pivotCoordinate`, `secondTowerOf` et 1 autres ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : (aucun) (0)

#### `mirror_phase_lt` — `Terminal.ReadingArithmetic` l.88 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour β < 1/2, la phase du miroir est strictement inférieure à celle de z.
- **Vérités** : AJOUT
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `mirrorMember`, `mirrorMember_ordinate`, `mirrorMember_radial`, `towerMotionOf` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rTowerHeight`, `rTowerPhase`, `rTowerRadialPosition`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroRadialPosition_positive`
- **Entraîne** : `mirror_phase_gap_lt`, `pivotCoordinate_mirror_mem` (2)

#### `towerPosition_mirror_sub` — `Terminal.ReadingArithmetic` l.98 — CONFIRMÉE
- **Énoncé** : À tout q, position(miroir) − position(z) = (φ_z − φ_{z*})/π.
- **Vérités** : AJOUT ; V184
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `mirrorMember`, `mirrorMember_ordinate`, `towerMotionOf`, `towerPosition` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : `mirror_translation_lt`, `pivotCoordinate_mirror_mem` (2)

#### `pivotCoordinate_mirror_mem` — `Terminal.ReadingArithmetic` l.105 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour β < 1/2 et toute référence q, la coordonnée de pivot du miroir est celle de z ou la suivante.
- **Vérités** : AJOUT ; touche O11
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `mirrorMember`, `mirror_phase_lt`, `pivotCoordinate`, `towerMotionOf`, `towerMotion_phase_lt_pi_div_two`, `towerMotion_phase_pos`, `towerPosition`, `towerPosition_mirror_sub` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `mirror_pivot_decomposition_of_consecutive` (1)

#### `riemannHypothesis_iff_noLowerSide` — `Terminal.ReadingArithmetic` l.132 — ÉQUIVALENTE À RH
- **Énoncé** : RH si et seulement si aucun zéro n'est de côté bas (β < 1/2).
- **Vérités** : V117 ; V126 ; I3
- **Repose sur** : `TrueZero`, `riemannHypothesis_of_noLowerSide` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`, `thm_zeroRadialPosition_half_of_riemannHypothesis`
- **Entraîne** : `reflectedReading_iff_riemannHypothesis`, `zeroInsertionDepth_iff_riemannHypothesis` (2)


##### Terminal.ReflectedObligation

#### `reflected_reads_no_prime` — `Terminal.ReflectedObligation` l.24 — CONFIRMÉE
- **Énoncé** : Aucun anneau du mouvement réfléchi d'un zéro, parcouru depuis son origine, n'atteint un premier.
- **Vérités** : V96 ; V72
- **Repose sur** : `TrueZero`, `reflectedIncidence`, `reflected_no_stop_event` ; base rhv3 : (aucun)
- **Entraîne** : `reflected_blocked_onLine`, `reflected_mirror_reads_nothing`, `reflection_creates_no_prime_event` (3)

#### `reflected_blocked_onLine` — `Terminal.ReflectedObligation` l.29 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour un zéro de la ligne, le mouvement réfléchi n'atteint pas son occurrence.
- **Vérités** : V96 ; V77
- **Repose sur** : `TrueZero`, `occurrence`, `occurrence_prime`, `reflectedIncidence`, `reflected_reads_no_prime` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)

#### `reflected_mirror_reads_nothing` — `Terminal.ReflectedObligation` l.34 — CONFIRMÉE
- **Énoncé** : Le mouvement réfléchi du membre miroir n'atteint pas l'occurrence du miroir.
- **Vérités** : V96 ; V72
- **Repose sur** : `TrueZero`, `mirrorMember`, `occurrence`, `occurrence_prime`, `reflectedIncidence`, `reflected_reads_no_prime` ; base rhv3 : (aucun)
- **Entraîne** : `reflectedReading_iff_noLowerSide` (1)

#### `mirror_ownTower_reads` — `Terminal.ReflectedObligation` l.39 — CONFIRMÉE
- **Énoncé** : La Tour propre du membre miroir atteint son occurrence et son minimum attendu.
- **Vérités** : V75 ; V88 ; V97
- **Repose sur** : `TrueTower.properState`, `TrueZero`, `expectedMinimumPrime`, `firstTowerOf`, `firstTower_reaches_expected`, `firstTower_reaches_occurrence`, `mirrorMember`, `occurrence`, `reaches` ; base rhv3 : (aucun)
- **Entraîne** : (aucun) (0)

#### `reflectedReading_iff_noLowerSide` — `Terminal.ReflectedObligation` l.47 — ÉQUIVALENTE À RH
- **Énoncé** : Exiger de tout zéro de côté bas que le mouvement réfléchi de son miroir atteigne l'occurrence du miroir équivaut à l'absence de zéro de côté bas (côté droit ⟺ RH par riemannHypothesis_iff_noLowerSide).
- **Vérités** : V97 ; V117
- **Repose sur** : `TrueZero`, `mirrorMember`, `occurrence`, `reflectedIncidence`, `reflected_mirror_reads_nothing` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `reflectedReading_iff_riemannHypothesis` (1)

#### `reflectedReading_iff_riemannHypothesis` — `Terminal.ReflectedObligation` l.61 — ÉQUIVALENTE À RH
- **Énoncé** : La même obligation de lecture sur la réflexion est équivalente à RH.
- **Vérités** : V97 ; V117
- **Repose sur** : `TrueZero`, `mirrorMember`, `occurrence`, `reflectedIncidence`, `reflectedReading_iff_noLowerSide`, `riemannHypothesis_iff_noLowerSide` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)


##### Terminal.RegimeCapture

#### `regimeCapture_of_riemannHypothesis` — `Terminal.RegimeCapture` l.44 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous RH, la capture de régime (β_e = 1/2 ⟹ β_l = 1/2 sur tout passage) est vraie.
- **Vérités** : AJOUT (capture de régime : terme hors maître)
- **Repose sur** : `PRegimeCapture` ; base rhv3 : `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroRadialPosition_half_of_riemannHypothesis`
- **Entraîne** : `regimeCapture_iff_riemannHypothesis` (1)

#### `regime_captive_of_prime` — `Terminal.RegimeCapture` l.48 — CONFIRMÉE
- **Énoncé** : Sur tout passage, Occ(l) = p_min(e) et la cellule de l contient son propre minimum attendu.
- **Vérités** : V54 ; V143 ; AJOUT (captivité)
- **Repose sur** : `contactMinusAt`, `contactPlusAt`, `expectedMinimumPrime`, `firstTower_cell_contains_expected`, `occurrence`, `passage_event_increment`, `pivotCoordinate` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroSourceIndex`, `rZeroHeight`
- **Entraîne** : (aucun) (0)

#### `height_pos_of_precedes` — `Terminal.RegimeCapture` l.63 — CONFIRMÉE
- **Énoncé** : Si w précède u dans l'ordre des membres et h(w) > 0, alors h(u) > 0.
- **Vérités** : V8
- **Repose sur** : (aucun) ; base rhv3 : `PZeroMemberPrecedes`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroMemberPrecedes_iff_height_radial_lex`
- **Entraîne** : `exists_consecutive_predecessor` (1)

#### `exists_consecutive_predecessor` — `Terminal.RegimeCapture` l.69 — CONFIRMÉE
- **Énoncé** : Tout membre dont l'ensemble des zéros supérieurs en dessous est non vide a un prédécesseur consécutif, d'index strictement inférieur.
- **Vérités** : V8 ; V68 ; AJOUT
- **Repose sur** : `_private.Terminal.RegimeCapture.0.height_pos_of_precedes` ; base rhv3 : `PZeroMemberPrecedes`, `PZeroMembersConsecutive`, `TNonTrivialZetaZero`, `nZeroSourceIndex`, `rZeroHeight`, `sUpperZerosBelow`, `thm_upperZerosBelow_finite`, `thm_zeroSourceIndex_strictMono`
- **Entraîne** : `allOnLine_of_regimeCapture` (1)

#### `allOnLine_of_regimeCapture` — `Terminal.RegimeCapture` l.87 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous PLowestZeroOnLine et PRegimeCapture, tout zéro est sur la ligne (récurrence forte sur l'index).
- **Vérités** : AJOUT ; touche O7
- **Repose sur** : `PLowestZeroOnLine`, `PRegimeCapture`, `TrueZero`, `exists_consecutive_predecessor` ; base rhv3 : `PIsNonTrivialZetaZero`, `PZeroMembersConsecutive`, `TNonTrivialZetaZero`, `TZeroPassage.mk`, `nZeroSourceIndex`, `rZeroHeight`, `rZeroRadialPosition`, `sUpperZerosBelow`
- **Entraîne** : `off_enters_regime`, `riemannHypothesis_of_regimeCapture` (2)

#### `riemannHypothesis_of_regimeCapture` — `Terminal.RegimeCapture` l.104 — IMPLIQUE RH SOUS PRÉMISSE
- **Énoncé** : Sous PLowestZeroOnLine et PRegimeCapture, RH.
- **Vérités** : AJOUT ; V119 ; I2 (prémisses non déchargées)
- **Repose sur** : `PLowestZeroOnLine`, `PRegimeCapture`, `TrueZero`, `allOnLine_of_regimeCapture`, `riemannHypothesis_of_noOff` ; base rhv3 : `PIsNonTrivialZetaZero`, `PIsOffCriticalLine`, `TNonTrivialZetaZero`
- **Entraîne** : `regimeCapture_iff_riemannHypothesis` (1)

#### `regimeCapture_iff_riemannHypothesis` — `Terminal.RegimeCapture` l.109 — ÉQUIVALENTE À RH
- **Énoncé** : Modulo PLowestZeroOnLine, la capture de régime équivaut à RH.
- **Vérités** : AJOUT ; V119
- **Repose sur** : `PLowestZeroOnLine`, `PRegimeCapture`, `regimeCapture_of_riemannHypothesis`, `riemannHypothesis_of_regimeCapture` ; base rhv3 : (aucun)
- **Entraîne** : (aucun) (0)

#### `off_enters_regime` — `Terminal.RegimeCapture` l.114 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous PLowestZeroOnLine, un zéro hors ligne (s'il existe) apparaît comme successeur d'un zéro de β = 1/2 dans un passage authentique.
- **Vérités** : AJOUT
- **Repose sur** : `PLowestZeroOnLine`, `TrueZero`, `allOnLine_of_regimeCapture` ; base rhv3 : `PIsNonTrivialZetaZero`, `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)


##### Terminal.ReverseEngineeredClosure

#### `riemannHypothesis_of_PHeightProgression` — `Terminal.ReverseEngineeredClosure` l.56 — IMPLIQUE RH SOUS PRÉMISSE
- **Énoncé** : PHeightProgression (tout passage consécutif de membres supérieurs fait progresser T) entraîne RH ; PHeightProgression est elle-même équivalente à RH (heightProgression_iff_riemannHypothesis).
- **Vérités** : V58 ; V119 ; I2
- **Repose sur** : `PHeightProgression`, `heightProgression_iff_riemannHypothesis` ; base rhv3 : `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroHeight`
- **Entraîne** : (aucun) (0)

#### `riemannHypothesis_of_hReaches_is_vacuous` — `Terminal.ReverseEngineeredClosure` l.65 — IMPLIQUE RH SOUS PRÉMISSE
- **Énoncé** : Si le mouvement réfléchi du miroir atteignait p_min(z*), RH suivrait ; la prémisse est déjà réfutée par reflectedFromOrigin_never_reaches_expectedMinimum (hors lot).
- **Vérités** : V96 ; V72 ; O1 (hReaches)
- **Repose sur** : `TrueZero`, `expectedMinimumPrime`, `mirrorMember`, `reflectedIncidence`, `terminalCollision_conditional_on_reflectedObligation` ; base rhv3 : (aucun)
- **Entraîne** : (aucun) (0)


##### Terminal.SuccessionInvariants

#### `passage_trichotomy_ABC` — `Terminal.SuccessionInvariants` l.45 — CONFIRMÉE
- **Énoncé** : Tout passage est soit vertical pur (T_e < T_l, β égaux), soit mixte (T_e < T_l, β différents), soit horizontal pur (T_e = T_l, β_e < β_l).
- **Vérités** : V165 ; V8
- **Repose sur** : (aucun) ; base rhv3 : `PZeroMemberPrecedes`, `TZeroPassage`, `TZeroPassage.precedes`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroMemberPrecedes_iff_height_radial_lex`
- **Entraîne** : `succession_invariants` (1)

#### `passage_deltaT_nonneg` — `Terminal.SuccessionInvariants` l.61 — CONFIRMÉE
- **Énoncé** : ΔT ≥ 0 sur tout passage.
- **Vérités** : V8 ; V165
- **Repose sur** : `passage_height_le` ; base rhv3 : `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroHeight`
- **Entraîne** : (aucun) (0)

#### `passage_grid_translation_of_sameHeight` — `Terminal.SuccessionInvariants` l.66 — CONFIRMÉE
- **Énoncé** : Sur un passage de même hauteur, la grille du later est celle de l'earlier translatée par exp(Δφ/T).
- **Vérités** : V184 ; AJOUT
- **Repose sur** : `TowerMotion.phase`, `contactMinusAt`, `sameHeight_grid_rigid_translation`, `towerMotionOf` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroHeight`
- **Entraîne** : (aucun) (0)

#### `energyRatio_eq` — `Terminal.SuccessionInvariants` l.83 — CONFIRMÉE
- **Énoncé** : R_E(q) = q^{Δβ}·‖ρ_e‖/‖ρ_l‖ pour tout couple de zéros et q > 0.
- **Vérités** : V173 ; V102
- **Repose sur** : `TrueZero`, `energyRatio`, `zeroPoint`, `zeroPoint_norm_pos`, `zeroTerm`, `zeroTerm_norm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `energyRatio_const_iff`, `energyRatio_const_of_deltaBeta_zero`, `energyRatio_unbounded_of_deltaBeta_pos`, `succession_invariants` (4)

#### `energyRatio_const_of_deltaBeta_zero` — `Terminal.SuccessionInvariants` l.96 — CONFIRMÉE
- **Énoncé** : Si β_e = β_l, le rapport énergétique est constant en q, égal à ‖ρ_e‖/‖ρ_l‖.
- **Vérités** : V181 ; V102
- **Repose sur** : `TrueZero`, `energyRatio`, `energyRatio_eq`, `zeroPoint` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `energyRatio_const_iff`, `energyRatio_lt_one_of_vertical` (2)

#### `energyRatio_lt_one_of_vertical` — `Terminal.SuccessionInvariants` l.102 — CONFIRMÉE
- **Énoncé** : Si β_e = β_l et T_e < T_l, le rapport énergétique est < 1 en tout q > 0.
- **Vérités** : V181
- **Repose sur** : `TrueZero`, `energyRatio`, `energyRatio_const_of_deltaBeta_zero`, `zeroPoint`, `zeroPoint_norm_lt_of_height_lt`, `zeroPoint_norm_pos` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)

#### `energyRatio_const_iff` — `Terminal.SuccessionInvariants` l.111 — CONFIRMÉE
- **Énoncé** : Le rapport énergétique est constant en q si et seulement si Δβ = 0.
- **Vérités** : V102 ; V158
- **Repose sur** : `TrueZero`, `energyRatio`, `energyRatio_const_of_deltaBeta_zero`, `energyRatio_eq`, `zeroPoint`, `zeroPoint_norm_pos` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `succession_invariants` (1)

#### `energyRatio_unbounded_of_deltaBeta_pos` — `Terminal.SuccessionInvariants` l.141 — CONFIRMÉE
- **Énoncé** : Si β_e < β_l, le rapport énergétique dépasse tout M au-delà d'un seuil q0.
- **Vérités** : V102 ; V167
- **Repose sur** : `TrueZero`, `energyRatio`, `energyRatio_eq`, `zeroPoint`, `zeroPoint_norm_pos` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)

#### `passage_raccords` — `Terminal.SuccessionInvariants` l.170 — CONFIRMÉE
- **Énoncé** : Sur tout passage : Occ(l) = p_min(e) = p_{n_e+1} et p_min(l) = p_{n_e+2}.
- **Vérités** : V54 ; V56 ; V150 ; V170 (raccords)
- **Repose sur** : `expectedMinimumPrime`, `occurrence`, `occurrence_eq_primeAtRank`, `passage_event_increment` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `fnPrimeAtRank`, `nZeroSourceIndex`, `rZeroHeight`
- **Entraîne** : `geometry_selects_raccord_prime`, `grammar_determines_stop_ray`, `succession_invariants` (3)

#### `succession_invariants` — `Terminal.SuccessionInvariants` l.186 — CONFIRMÉE
- **Énoncé** : Paquet sur tout passage : trichotomie, formule de R_E, constance ⟺ Δβ = 0, raccords, cellules contenant Occ(l) (pour l) et Occ(l) (pour e), énergie signée sur les rayons du later, J ≥ 0 ; ces invariants sont consistants pour tout passage, ON ou OFF.
- **Vérités** : V165 ; V54 ; V143 ; V102 ; V100 ; V155
- **Repose sur** : `contactMinusAt`, `contactPlusAt`, `energyRatio`, `energyRatio_const_iff`, `energyRatio_eq`, `expectedMinimumPrime`, `interTowerExcess`, `interTowerExcess_nonneg`, `occurrence`, `occurrence_pos`, `passage_raccords`, `passage_trichotomy_ABC` et 5 autres ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `fnPrimeAtRank`, `nZeroSourceIndex`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)


##### Terminal.TranslationVsProgression

#### `mirror_phase_gap_eq_arctan` — `Terminal.TranslationVsProgression` l.29 — CONFIRMÉE
- **Énoncé** : φ_z − φ_{z*} = arctan(T(1−2β)/(β(1−β) + T²)).
- **Vérités** : V185 (valeur exacte de D·π) ; AJOUT
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `mirrorMember`, `mirrorMember_phase`, `mirrorMember_radial`, `towerMotionOf`, `towerMotion_phase` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroRadialPosition_positive`
- **Entraîne** : `mirror_phase_gap_lt` (1)

#### `mirror_phase_gap_lt` — `Terminal.TranslationVsProgression` l.65 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour β < 1/2, 0 < φ_z − φ_{z*} < (1−2β)/T.
- **Vérités** : V186 ; AJOUT
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `mirrorMember`, `mirror_phase_gap_eq_arctan`, `mirror_phase_lt`, `towerMotionOf` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroRadialPosition_positive`
- **Entraîne** : `mirror_translation_lt` (1)

#### `mirror_translation_lt` — `Terminal.TranslationVsProgression` l.98 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour β < 1/2 et tout q, 0 < position(miroir) − position(z) < (1−2β)/(πT).
- **Vérités** : V186 ; V183
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `mirrorMember`, `mirror_phase_gap_lt`, `towerMotionOf`, `towerPosition`, `towerPosition_mirror_sub` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : `mirror_translation_lt_inv_pi_height`, `mirror_translation_over_next_progression_lt`, `off_consecutive_translation_signature` (3)

#### `mirror_translation_lt_inv_pi_height` — `Terminal.TranslationVsProgression` l.114 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour β < 1/2, position(miroir) − position(z) < 1/(πT).
- **Vérités** : V186
- **Repose sur** : `TrueZero`, `mirrorMember`, `mirror_translation_lt`, `towerPosition` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroRadialPosition_positive`
- **Entraîne** : (aucun) (0)

#### `pivotCoordinate_mono` — `Terminal.TranslationVsProgression` l.137 — CONFIRMÉE
- **Énoncé** : La coordonnée de pivot est monotone en la référence.
- **Vérités** : V32 ; AJOUT
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `pivotCoordinate`, `towerMotionOf`, `towerPosition` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`
- **Entraîne** : `progression_nonneg` (1)

#### `progression_nonneg` — `Terminal.TranslationVsProgression` l.152 — CONFIRMÉE
- **Énoncé** : La progression (nombre de frontières d'anneau franchies par l'arête Occ(w) → p_min(w)) est ≥ 0 (progression : terme hors maître).
- **Vérités** : AJOUT ; V54
- **Repose sur** : `TrueZero`, `expectedMinimumPrime`, `occurrence`, `occurrence_lt_expectedMinimumPrime`, `occurrence_pos`, `pivotCoordinate`, `pivotCoordinate_mono`, `progression` ; base rhv3 : (aucun)
- **Entraîne** : `mirror_pivot_mono_of_consecutive` (1)

#### `secondTower_reads_iff_progression_pos` — `Terminal.TranslationVsProgression` l.163 — CONFIRMÉE
- **Énoncé** : La seconde Tour lit l'occurrence du miroir si et seulement si progression(z*) > 0 ; V est progression = 0.
- **Vérités** : V85 ; V147 ; O11 ; T20
- **Repose sur** : `InvertedContactPair.reaches`, `InvertedTower.properState`, `TrueZero`, `expectedMinimumPrime`, `mirrorMember`, `occurrence`, `pivotCoordinate`, `progression`, `secondTowerOf`, `secondTower_reads_occurrence_iff_coordinate_lt` ; base rhv3 : (aucun)
- **Entraîne** : (aucun) (0)

#### `mirror_pivot_decomposition_of_consecutive` — `Terminal.TranslationVsProgression` l.174 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour β < 1/2 et consécutivité stricte, k(z*, p_min(z*)) = k(z, p_min(z)) + progression(z*) + δk, δk ∈ {0,1}.
- **Vérités** : V144 ; AJOUT
- **Repose sur** : `TrueZero`, `expectedMinimumPrime`, `expectedMinimum_eq_mirror_occurrence_of_consecutive`, `mirrorMember`, `occurrence`, `pivotCoordinate`, `pivotCoordinate_mirror_mem`, `progression` ; base rhv3 : `PIsNonTrivialZetaZero`, `PZeroMembersConsecutive`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `mirror_pivot_mono_of_consecutive` (1)

#### `mirror_pivot_mono_of_consecutive` — `Terminal.TranslationVsProgression` l.195 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour β < 1/2 et consécutivité stricte, la coordonnée de pivot du miroir est ≥ celle de z.
- **Vérités** : AJOUT
- **Repose sur** : `TrueZero`, `expectedMinimumPrime`, `mirrorMember`, `mirror_pivot_decomposition_of_consecutive`, `pivotCoordinate`, `progression`, `progression_nonneg` ; base rhv3 : `PIsNonTrivialZetaZero`, `PZeroMembersConsecutive`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `off_consecutive_translation_signature` (1)

#### `off_consecutive_translation_signature` — `Terminal.TranslationVsProgression` l.208 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour β < 1/2 et consécutivité stricte : n(z*) = n(z)+1, même hauteur, même événement de hauteur, même portée, même accroissement de phase, translation dans ]0,(1−2β)/(πT)[, coordonnée de pivot du miroir ≥ celle de z.
- **Vérités** : V64 ; V127 ; V131 ; V144 ; V186
- **Repose sur** : `TrueZero`, `expectedMinimumPrime`, `mirrorMember`, `mirrorMember_ordinate`, `mirror_heightEventIndex_eq`, `mirror_phase_increment_eq`, `mirror_pivot_mono_of_consecutive`, `mirror_sourceIndex_of_consecutive`, `mirror_span_eq`, `mirror_translation_lt`, `pivotCoordinate`, `towerPosition` ; base rhv3 : `PIsNonTrivialZetaZero`, `PZeroMembersConsecutive`, `TNonTrivialZetaZero`, `TowerPrimeGapSpan`, `nZeroHeightEventIndex`, `nZeroSourceIndex`, `rZeroHeight`, `rZeroRadialPosition`, `tZeroHeightEvent`
- **Entraîne** : (aucun) (0)


##### Terminal.TwoClocks

#### `passage_span_eq_log_occurrences` — `Terminal.TwoClocks` l.52 — CONFIRMÉE
- **Énoncé** : Sur un passage (hauteurs des deux extrémités > 0), la portée de Tour de la place n_E du membre précoce vaut T_E/π · log(Occ(L)/Occ(E)), lue sur les deux occurrences du passage.
- **Vérités** : AJOUT (portée de Tour : terme hors maître) ; touche V56 (occurrences du passage)
- **Repose sur** : `occurrence`, `occurrence_eq_canonicalAnchor`, `occurrence_successor_of_passage` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `TowerPrimeGapSpan`, `fnPrimeAtRank`, `fnPrimeSuccessor`, `nMemberCanonicalAnchor`, `nZeroSourceIndex`, `rPrimeGapLogRatio`, `rTowerHeight` et 1 autres
- **Entraîne** : (aucun) (0)

#### `passage_span_pos` — `Terminal.TwoClocks` l.68 — CONFIRMÉE
- **Énoncé** : La portée de Tour de la place franchie par un passage est strictement positive.
- **Vérités** : AJOUT
- **Repose sur** : (aucun) ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TowerPrimeGapSpan`, `nZeroSourceIndex`, `rPrimeGapLogRatio`, `rTowerHeight`, `rZeroHeight`, `thm_primeGapLogRatio_pos`
- **Entraîne** : `off_clock_slip` (1)

#### `passage_heightEventIndex_dichotomy` — `Terminal.TwoClocks` l.78 — CONFIRMÉE
- **Énoncé** : Sur tout passage, ou bien la hauteur croît strictement et l'événement de hauteur avance de un, ou bien la hauteur est égale et l'événement de hauteur ne bouge pas.
- **Vérités** : V57 (voisin : le maître compile la place, non la dichotomie de l'événement de hauteur) ; V59 ; AJOUT pour la dichotomie 0/1
- **Repose sur** : (aucun) ; base rhv3 : `PIsNonTrivialZetaZero`, `PZeroMemberPrecedes`, `TNonTrivialZetaZero`, `TUpperNonTrivialZetaZero`, `TZeroHeightEvent`, `TZeroHeightEvent.height`, `TZeroHeightGap.mk`, `TZeroPassage`, `TZeroPassage.hConsecutive`, `TZeroPassage.precedes`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember` et 7 autres
- **Entraîne** : `off_clock_slip`, `onLine_clock_sync` (2)

#### `clock_h_le_n` — `Terminal.TwoClocks` l.141 — CONFIRMÉE
- **Énoncé** : L'horloge des hauteurs h est toujours inférieure ou égale à l'horloge des membres n d'un zéro.
- **Vérités** : V59 (côté « hauteurs ≤ membres » de l'accord des grammaires) ; AJOUT
- **Repose sur** : `ClockState.h`, `ClockState.n`, `TrueZero`, `clockState`, `heightEventIndex_le_sourceIndex` ; base rhv3 : (aucun)
- **Entraîne** : `clock_ph_le_pn` (1)

#### `clock_pn_eq` — `Terminal.TwoClocks` l.145 — CONFIRMÉE
- **Énoncé** : Le premier lu par l'horloge des membres est le premier de rang n (ancre canonique).
- **Vérités** : V27 (lien rang-occurrence)
- **Repose sur** : `ClockState.n`, `ClockState.pn`, `TrueZero`, `clockState`, `occurrence`, `occurrence_eq_canonicalAnchor` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `fnPrimeAtRank`, `nMemberCanonicalAnchor`, `nZeroSourceIndex`
- **Entraîne** : `clock_ph_le_pn` (1)

#### `clock_ph_eq` — `Terminal.TwoClocks` l.151 — CONFIRMÉE
- **Énoncé** : Le premier lu par l'horloge des hauteurs est le premier de rang h.
- **Vérités** : V59 ; V27
- **Repose sur** : `ClockState.h`, `ClockState.ph`, `TrueZero`, `clockState` ; base rhv3 : `fnPrimeAtRank`, `nHeightEventCanonicalPrime`, `nHeightEventMZOccurrence`, `nZeroHeightEventIndex`, `tZeroHeightEvent`, `thm_heightEventMZOccurrence_eq_canonicalPrime_unconditional`
- **Entraîne** : `clock_ph_le_pn` (1)

#### `clock_ph_le_pn` — `Terminal.TwoClocks` l.158 — CONFIRMÉE
- **Énoncé** : Le premier de l'horloge des hauteurs est inférieur ou égal à celui de l'horloge des membres.
- **Vérités** : AJOUT
- **Repose sur** : `ClockState.h`, `ClockState.n`, `ClockState.ph`, `ClockState.pn`, `TrueZero`, `clockState`, `clock_h_le_n`, `clock_ph_eq`, `clock_pn_eq` ; base rhv3 : `fnPrimeAtRank`, `thm_primeAtRank_strictMono`
- **Entraîne** : (aucun) (0)

#### `clock_Sn_pos` — `Terminal.TwoClocks` l.165 — CONFIRMÉE
- **Énoncé** : La portée du carré (portée de Tour de la place n) est strictement positive pour tout zéro.
- **Vérités** : AJOUT
- **Repose sur** : `ClockState.Sn`, `TrueZero`, `clockState` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `TowerPrimeGapSpan`, `nZeroSourceIndex`, `rPrimeGapLogRatio`, `rTowerHeight`, `rZeroHeight`, `thm_primeGapLogRatio_pos`
- **Entraîne** : (aucun) (0)

#### `clock_agree_iff_riemannHypothesis` — `Terminal.TwoClocks` l.171 — ÉQUIVALENTE À RH
- **Énoncé** : Les deux horloges (membres, hauteurs) coïncident sur tout zéro si et seulement si RH.
- **Vérités** : V59, V128
- **Repose sur** : `ClockState.h`, `ClockState.n`, `TrueZero`, `clockState`, `grammarsAgree_iff_riemannHypothesis` ; base rhv3 : (aucun)
- **Entraîne** : (aucun) (0)

#### `span_eq_on_sameHeight_fiber` — `Terminal.TwoClocks` l.179 — CONFIRMÉE
- **Énoncé** : Deux zéros de même hauteur lisent la même portée de Tour sur toute place n.
- **Vérités** : V17 ; V159 ; V50 (fibre de même hauteur)
- **Repose sur** : `TrueZero` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `TowerPrimeGapSpan`, `rTowerHeight`, `rZeroHeight`, `thm_towerPrimeGapSpan_eq_iff_height_eq`
- **Entraîne** : (aucun) (0)

#### `onLine_clock_sync` — `Terminal.TwoClocks` l.190 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sur un passage dont les deux extrémités sont sur la ligne critique, l'index de membre et l'index de hauteur avancent tous deux de un.
- **Vérités** : V57 (sur la ligne la hauteur avance) ; V181 (contraste ON)
- **Repose sur** : `eventIndex_succ_of_passage`, `passage_heightEventIndex_dichotomy`, `passage_height_lt_of_onLine` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `nZeroHeightEventIndex`, `nZeroSourceIndex`, `rZeroHeight`, `rZeroRadialPosition`, `tZeroHeightEvent`
- **Entraîne** : (aucun) (0)

#### `off_clock_slip` — `Terminal.TwoClocks` l.205 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour un zéro hors ligne, il existe un passage où l'horloge des membres avance de un, celle des hauteurs ne bouge pas, la hauteur est égale aux deux extrémités et la portée lue à l'arrivée égale celle du départ.
- **Vérités** : V58 (la place avance sans que la hauteur avance : instance hors ligne) ; V66 ; V131
- **Repose sur** : `TrueZero`, `expectedMinimumPrime`, `occurrence`, `off_event_increment_without_height`, `passage_heightEventIndex_dichotomy`, `passage_span_pos` ; base rhv3 : `PIsNonTrivialZetaZero`, `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `TowerPrimeGapSpan`, `nZeroHeightEventIndex`, `nZeroSourceIndex`, `rTowerHeight`, `rZeroHeight`, `tZeroHeightEvent` et 1 autres
- **Entraîne** : (aucun) (0)


##### Terminal.Universalization

#### `riemannHypothesis_of_noOff` — `Terminal.Universalization` l.25 — IMPLIQUE RH SOUS PRÉMISSE
- **Énoncé** : Si aucun zéro n'est hors ligne, RH (universalisation compilée de la base).
- **Vérités** : V110 ; V109 ; V120 ; O23
- **Repose sur** : `TrueZero` ; base rhv3 : `PIsNonTrivialZetaZero`, `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `TUpperNonTrivialZetaZero`, `rZeroRadialPosition`, `thm_riemannHypothesis_of_allUpperOnCriticalLine`
- **Entraîne** : `allNontrivial_onLine_iff_riemannHypothesis`, `fixedLocusSelection_iff_riemannHypothesis`, `grammarsAgree_iff_riemannHypothesis`, `heightProgression_iff_riemannHypothesis`, `noNullPassage_iff_riemannHypothesis`, `riemannHypothesis_of_energyBalance`, `riemannHypothesis_of_localReading`, `riemannHypothesis_of_noLowerSide`, `riemannHypothesis_of_regimeCapture`, `riemannHypothesis_of_verticalEnergyPush`, `xiRealZeros_iff_riemannHypothesis` (11)

#### `riemannHypothesis_of_noLowerSide` — `Terminal.Universalization` l.32 — IMPLIQUE RH SOUS PRÉMISSE
- **Énoncé** : Si aucun zéro n'est de côté bas, RH ; la réciproque est dans riemannHypothesis_iff_noLowerSide.
- **Vérités** : V110 ; V117 ; O23
- **Repose sur** : `TrueZero`, `mirrorMember`, `off_lowerSide`, `riemannHypothesis_of_noOff` ; base rhv3 : `PIsNonTrivialZetaZero`, `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `mirrorEventIdentity_iff_riemannHypothesis`, `mirrorTransport_iff_riemannHypothesis`, `reflectedEquivariance_iff_riemannHypothesis`, `riemannHypothesis_iff_noLowerSide` (4)


##### Terminal.VerticalEnergyPush

#### `zeroPoint_norm_sq` — `Terminal.VerticalEnergyPush` l.44 — CONFIRMÉE
- **Énoncé** : ‖ρ‖² = β² + T².
- **Vérités** : V15
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroPoint_im`, `zeroPoint_re` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : `cos_phase_eq`, `mirror_verticalEnergy_eq_zero_iff`, `mirror_verticalEnergy_pos`, `sameHeight_amplitude_inverts_at_primes`, `zeroPoint_eq_of_phase_norm_eq`, `zeroPoint_norm_eq_of_eq`, `zeroPoint_norm_lt_of_height_lt` (7)

#### `zeroPoint_norm_pos` — `Terminal.VerticalEnergyPush` l.49 — CONFIRMÉE
- **Énoncé** : ‖ρ‖ > 0 pour tout zéro.
- **Vérités** : AJOUT
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroPoint_ne_zero` ; base rhv3 : (aucun)
- **Entraîne** : `amplitude_inverts_of_radial_lt`, `amplitude_lt_of_height_lt`, `energyRatio_const_iff`, `energyRatio_eq`, `energyRatio_lt_one_of_vertical`, `energyRatio_unbounded_of_deltaBeta_pos`, `horizontal_energy_action`, `mirror_verticalEnergy_eq_zero_iff`, `mirror_verticalEnergy_pos`, `onLine_passage_pure_vertical`, `ray_energy_alternates`, `sameHeight_amplitude_inverts_at_primes` et 2 autres (14)

#### `zeroPoint_norm_lt_of_height_lt` — `Terminal.VerticalEnergyPush` l.52 — CONFIRMÉE
- **Énoncé** : À même β, une hauteur strictement plus grande donne une norme de support strictement plus grande.
- **Vérités** : V158
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroPoint_norm_pos`, `zeroPoint_norm_sq` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : `amplitude_lt_of_height_lt`, `energyRatio_lt_one_of_vertical`, `onLine_passage_pure_vertical` (3)

#### `zeroPoint_norm_eq_of_eq` — `Terminal.VerticalEnergyPush` l.62 — CONFIRMÉE
- **Énoncé** : À mêmes β et T, les supports ont même norme.
- **Vérités** : AJOUT
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroPoint_norm_sq` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : `mirror_verticalEnergy_eq_zero_iff`, `verticalEnergyPush_of_riemannHypothesis` (2)

#### `amplitude_lt_of_height_lt` — `Terminal.VerticalEnergyPush` l.72 — CONFIRMÉE
- **Énoncé** : À même β, la Tour la plus haute porte strictement moins d'énergie en tout q > 0.
- **Vérités** : V181 ; V166
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroPoint_norm_lt_of_height_lt`, `zeroPoint_norm_pos`, `zeroTerm`, `zeroTerm_norm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : `localReading_modeA`, `onLine_amplitude_lt_of_height_lt`, `verticalEnergyPush_of_riemannHypothesis` (3)

#### `onLine_amplitude_lt_of_height_lt` — `Terminal.VerticalEnergyPush` l.84 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sur la ligne, deux membres de hauteurs distinctes : la Tour la plus haute porte strictement moins d'énergie en tout q > 0.
- **Vérités** : V181
- **Repose sur** : `TrueZero`, `amplitude_lt_of_height_lt`, `zeroTerm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : `onLine_passage_pure_vertical` (1)

#### `amplitude_inverts_of_radial_lt` — `Terminal.VerticalEnergyPush` l.94 — CONFIRMÉE
- **Énoncé** : Si β_e < β_l (toute hauteur), il existe q0 ≥ 1 tel que ‖E_e(q)‖ < ‖E_l(q)‖ pour tout q > q0.
- **Vérités** : V102 ; V167
- **Repose sur** : `TrueZero`, `zeroPoint`, `zeroPoint_norm_pos`, `zeroTerm`, `zeroTerm_norm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `passage_energy_sign_dichotomy`, `riemannHypothesis_of_verticalEnergyPush` (2)

#### `one_lt_log_four` — `Terminal.VerticalEnergyPush` l.132 — CONFIRMÉE
- **Énoncé** : log 4 > 1.
- **Vérités** : AJOUT (lemme)
- **Repose sur** : (aucun) ; base rhv3 : (aucun)
- **Entraîne** : `one_add_lt_four_rpow` (1)

#### `one_add_lt_four_rpow` — `Terminal.VerticalEnergyPush` l.138 — CONFIRMÉE
- **Énoncé** : 1 + δ < 4^δ pour δ > 0.
- **Vérités** : AJOUT (lemme)
- **Repose sur** : `one_lt_log_four` ; base rhv3 : (aucun)
- **Entraîne** : `sameHeight_amplitude_inverts_at_primes` (1)

#### `sameHeight_amplitude_inverts_at_primes` — `Terminal.VerticalEnergyPush` l.145 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : À même hauteur T ≥ 2 et β_e < β_l, ‖E_e(q)‖ < ‖E_l(q)‖ en tout q ≥ 2 (2 ≤ T non compilé dans la base).
- **Vérités** : V102 ; V167
- **Repose sur** : `TrueZero`, `one_add_lt_four_rpow`, `zeroPoint`, `zeroPoint_norm_pos`, `zeroPoint_norm_sq`, `zeroTerm`, `zeroTerm_norm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroRadialPosition_lt_one`, `thm_zeroRadialPosition_positive`
- **Entraîne** : `offMirror_all_elements_hold_and_vertical_force_fails`, `sameHeight_amplitude_inverts_at_raccords` (2)

#### `sameHeight_amplitude_inverts_at_raccords` — `Terminal.VerticalEnergyPush` l.203 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Mêmes hypothèses : l'inégalité tient à Occ(l) et à p_min(l), les deux raccords.
- **Vérités** : V102 ; V170 (contexte, deux raccords)
- **Repose sur** : `TrueZero`, `expectedMinimumPrime`, `expectedMinimumPrime_prime`, `occurrence`, `occurrence_prime`, `sameHeight_amplitude_inverts_at_primes`, `zeroTerm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : `localReading_fails_modeC` (1)

#### `passage_energy_sign_dichotomy` — `Terminal.VerticalEnergyPush` l.219 — CONFIRMÉE
- **Énoncé** : Sur tout passage, ou bien la hauteur progresse, ou bien (même hauteur) l'énergie du later domine celle de l'earlier au-delà d'un seuil.
- **Vérités** : V165 ; V102 ; AJOUT
- **Repose sur** : `amplitude_inverts_of_radial_lt`, `zeroTerm` ; base rhv3 : `PIsNonTrivialZetaZero`, `PZeroMemberPrecedes`, `TNonTrivialZetaZero`, `TZeroPassage`, `TZeroPassage.precedes`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroMemberPrecedes_iff_height_radial_lex`
- **Entraîne** : (aucun) (0)

#### `riemannHypothesis_of_verticalEnergyPush` — `Terminal.VerticalEnergyPush` l.242 — IMPLIQUE RH SOUS PRÉMISSE
- **Énoncé** : PVerticalEnergyPush (l'énergie du later n'excède jamais celle de l'earlier en q ≥ 1) entraîne RH.
- **Vérités** : AJOUT ; I2
- **Repose sur** : `HorizontalMirrorRealization`, `PVerticalEnergyPush`, `TrueZero`, `amplitude_inverts_of_radial_lt`, `expectedMinimumPrime`, `interTowerExcess`, `occurrence`, `offPassage_full_context`, `riemannHypothesis_of_noOff`, `towerPosition`, `zeroTerm` ; base rhv3 : `PIsNonTrivialZetaZero`, `PIsOffCriticalLine`, `TNonTrivialZetaZero`, `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `TowerPrimeGapSpan`, `nZeroHeightEventIndex`, `nZeroSourceIndex`, `rZeroHeight`, `rZeroRadialPosition`, `tZeroHeightEvent`
- **Entraîne** : `verticalEnergyPush_iff_riemannHypothesis` (1)

#### `verticalEnergyPush_of_riemannHypothesis` — `Terminal.VerticalEnergyPush` l.256 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous RH, PVerticalEnergyPush est vraie.
- **Vérités** : AJOUT
- **Repose sur** : `PVerticalEnergyPush`, `amplitude_lt_of_height_lt`, `passage_height_le`, `zeroPoint`, `zeroPoint_norm_eq_of_eq`, `zeroTerm`, `zeroTerm_norm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroRadialPosition_half_of_riemannHypothesis`
- **Entraîne** : `localReading_of_riemannHypothesis`, `verticalEnergyPush_iff_riemannHypothesis` (2)

#### `verticalEnergyPush_iff_riemannHypothesis` — `Terminal.VerticalEnergyPush` l.274 — ÉQUIVALENTE À RH
- **Énoncé** : PVerticalEnergyPush ⟺ RH.
- **Vérités** : AJOUT ; V189 (même verdict de reformulation)
- **Repose sur** : `PVerticalEnergyPush`, `riemannHypothesis_of_verticalEnergyPush`, `verticalEnergyPush_of_riemannHypothesis` ; base rhv3 : (aucun)
- **Entraîne** : (aucun) (0)


##### Terminal.VerticalForce

#### `mirror_net_horizontal_force_zero` — `Terminal.VerticalForce` l.40 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, (β − 1/2) + (β* − 1/2) = 0.
- **Vérités** : V180
- **Repose sur** : `TrueZero`, `mirrorMember`, `mirrorMember_radial` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `offMirror_all_elements_hold_and_vertical_force_fails` (1)

#### `mirror_horizontal_tension_eq_zero_iff` — `Terminal.VerticalForce` l.45 — CONFIRMÉE
- **Énoncé** : La tension horizontale vaut 2(β − 1/2)² et s'annule si et seulement si β = 1/2.
- **Vérités** : V180
- **Repose sur** : `TrueZero`, `mirrorMember`, `mirrorMember_radial` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `offMirror_all_elements_hold_and_vertical_force_fails` (1)

#### `mirror_verticalEnergy_eq_zero_iff` — `Terminal.VerticalForce` l.65 — CONFIRMÉE
- **Énoncé** : V(z, z*) = 0 si et seulement si β = 1/2.
- **Vérités** : AJOUT (proche V180/V181)
- **Repose sur** : `TrueZero`, `mirrorMember`, `mirrorMember_ordinate`, `mirrorMember_radial`, `verticalEnergy`, `zeroPoint`, `zeroPoint_norm_eq_of_eq`, `zeroPoint_norm_pos`, `zeroPoint_norm_sq` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)

#### `mirror_verticalEnergy_pos` — `Terminal.VerticalForce` l.82 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour β < 1/2, V(z, z*) > 0.
- **Vérités** : AJOUT
- **Repose sur** : `TrueZero`, `mirrorMember`, `mirrorMember_ordinate`, `mirrorMember_radial`, `verticalEnergy`, `zeroPoint`, `zeroPoint_norm_pos`, `zeroPoint_norm_sq` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroRadialPosition_positive`
- **Entraîne** : (aucun) (0)

#### `onLine_passage_pure_vertical` — `Terminal.VerticalForce` l.95 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sur un passage dont les deux extrémités sont sur la ligne : T_e < T_l, énergie horizontale nulle en tout q, énergie verticale > 0, ‖E_l(q)‖ < ‖E_e(q)‖ pour tout q > 0.
- **Vérités** : V181
- **Repose sur** : `horizontalEnergy`, `onLine_amplitude_lt_of_height_lt`, `passage_height_lt_of_onLine`, `verticalEnergy`, `zeroPoint`, `zeroPoint_norm_lt_of_height_lt`, `zeroPoint_norm_pos`, `zeroTerm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `TZeroPassage`, `TZeroPassage.zEarlierMember`, `TZeroPassage.zLaterMember`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : `capture_forces_pure_verticality` (1)

#### `zeroPoint_eq_of_phase_norm_eq` — `Terminal.VerticalForce` l.128 — CONFIRMÉE
- **Énoncé** : Deux zéros de même norme de support et de même phase ont mêmes β et T, donc sont le même zéro.
- **Vérités** : V46 (voisin : le maître parle de contacts) ; AJOUT
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `towerMotionOf`, `towerMotion_phase`, `zeroPoint`, `zeroPoint_norm_sq` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroRadialPosition_positive`
- **Entraîne** : `phase_norm_ne_of_ne` (1)

#### `phase_norm_ne_of_ne` — `Terminal.VerticalForce` l.171 — CONFIRMÉE
- **Énoncé** : Deux zéros distincts ont des couples (phase, norme) distincts.
- **Vérités** : V46 (voisin) ; AJOUT
- **Repose sur** : `TowerMotion.phase`, `TrueZero`, `towerMotionOf`, `zeroPoint`, `zeroPoint_eq_of_phase_norm_eq` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)

#### `mirror_contacts_interlace` — `Terminal.VerticalForce` l.178 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour β < 1/2 et tout k : C_{k−1}(z) < C_k(z*) < C_k(z).
- **Vérités** : V183
- **Repose sur** : `TowerMotion.incidence`, `TowerMotion.phase`, `TrueZero`, `contactMinusAt`, `mirrorMember`, `mirrorMember_contactMinusAt`, `towerMotionOf`, `towerMotion_incidence`, `towerMotion_phase` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`, `thm_zeroRadialPosition_positive`
- **Entraîne** : `offMirror_all_elements_hold_and_vertical_force_fails` (1)

#### `mirror_expectedMinimum_ne` — `Terminal.VerticalForce` l.206 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour β < 1/2, p_min(z*) ≠ p_min(z).
- **Vérités** : V182 ; V149
- **Repose sur** : `TrueZero`, `expectedMinimumPrime`, `expectedMinimumPrime_injective`, `mirrorMember`, `mirrorMember_ne` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroRadialPosition`
- **Entraîne** : `offMirror_all_elements_hold_and_vertical_force_fails` (1)

#### `offMirror_all_elements_hold_and_vertical_force_fails` — `Terminal.VerticalForce` l.213 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Pour β < 1/2 et T ≥ 2 : force horizontale nette nulle, tension > 0, entrelacement de tous les rayons, p_min distincts, ET ‖E_z(q)‖ < ‖E_{z*}(q)‖ en tout q ≥ 2 (la poussée verticale échoue).
- **Vérités** : V180 ; V183 ; V182 ; V167 ; AJOUT (composition)
- **Repose sur** : `TrueZero`, `contactMinusAt`, `expectedMinimumPrime`, `mirrorMember`, `mirrorMember_ordinate`, `mirror_contacts_interlace`, `mirror_expectedMinimum_ne`, `mirror_horizontal_tension_eq_zero_iff`, `mirror_net_horizontal_force_zero`, `mirror_radial_gt`, `sameHeight_amplitude_inverts_at_primes`, `zeroTerm` ; base rhv3 : `PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `rZeroHeight`, `rZeroRadialPosition`
- **Entraîne** : (aucun) (0)

### Lot B4 — B4 (Demonstration, Audit, six pistes parquées)

##### Partie A — RHV6Demonstration et Audit

##### A.1 Bibliothèque RHV6Demonstration (fichier `RHV6Demonstration.lean`, 11 théorèmes)

Cible de build par défaut (lakefile : `defaultTargets = [RHV6Fresh, RHV6Demonstration]`). Le docstring du module dit : « la démonstration SANS l'hypothèse de Riemann », chaque étape est un théorème sur `firstTowerOf z` (aucun miroir, aucune hypothèse, aucun `P…Law`) ; elle suit les maîtres §4–§7, §9 : géométrie (origine canonique, demi-tours, alternance), état propre (règle du pivot, cellule, lectures, inversion), lecture arithmétique (R₁, C_lecture au sens de la première Tour), progression sur un passage consécutif et test de vérification. Sept des onze théorèmes sont suivis d'un `#print axioms` dans le fichier lui-même : geometry_of_tower, stop_event, cell_contains_expected, inversion, expected_le_counted, reached_progression, verification_passes.

#### `geometry_of_tower` — `Demonstration` l.32 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, l'origine canonique (indice 0) est le plus petit indice de croisement dont l'incidence dépasse l'abscisse 1, et le côté du passage change de signe à chaque croisement (demi-tour).
- **Vérités** : V22, V18, V23
- **Repose sur** : théorèmes du projet : canonicalOrigin_isLeast [Tower.CanonicalOrigin], crossing_side_alternates [Tower.CanonicalOrigin]; définitions du projet : TrueZero, TowerMotion.incidence, towerMotionOf, TowerMotion.phase; base rhv3 : rZeroHeight, TNonTrivialZetaZero, PIsNonTrivialZetaZero.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `stop_event` — `Demonstration` l.44 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, la coordonnée d'entrée de la première Tour est le plus petit croisement dont le contact suivant atteint le minimum attendu p_min(z) : la règle du pivot arrête le parcours au premier anneau qui atteint la référence.
- **Vérités** : V32, V33, V143
- **Repose sur** : théorèmes du projet : firstTower_readings [Direct.PairTowers], pivotCoordinate_isLeast [Direct.PivotCell], expectedMinimumPrime_pos [Direct.PivotCell]; définitions du projet : TrueZero, expectedMinimumPrime, contactPlusAt, AnalyticContactPair.entryCoordinate, TrueTower.properState, firstTowerOf, pivotCoordinate, AnalyticContactPair.stageCount; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `cell_contains_expected` — `Demonstration` l.51 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, la cellule de l'état propre de la première Tour contient le minimum attendu : incidence d'entrée C⁻ < p_min(z) ≤ dernier rayon C⁺ (sans hypothèse sur β).
- **Vérités** : V143, V40 (constat numérique ici établi par théorème), V26
- **Repose sur** : théorèmes du projet : entry_lt_pivot [Direct.PivotCell], expectedMinimumPrime_pos [Direct.PivotCell], pivot_le_lastRay [Direct.PivotCell]; définitions du projet : TrueZero, AnalyticContactPair.entryContact, TrueTower.toAnalyticContactPair, firstTowerOf, expectedMinimumPrime, AnalyticContactPair.lastRayContact; base rhv3 : aucun.
- **Entraîne** : expected_mem_cell.

#### `expected_mem_cell` — `Demonstration` l.58 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, le minimum attendu (vu comme réel) appartient à la cellule de l'état propre de la première Tour (reformulation d'appartenance de `cell_contains_expected`).
- **Vérités** : V143, V26
- **Repose sur** : théorèmes du projet : cell_contains_expected; définitions du projet : TrueZero, AnalyticContactPair.cell, TrueTower.properState, firstTowerOf, expectedMinimumPrime, AnalyticContactPair.entryContact, AnalyticContactPair.lastRayContact, TrueTower.toAnalyticContactPair; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `readings` — `Demonstration` l.62 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, la coordonnée d'entrée de l'état propre se lit comme la position `pivotCoordinate` du minimum attendu et le nombre d'étages vaut 1 : deux lectures de l'état, non des entrées.
- **Vérités** : V43, V32
- **Repose sur** : théorèmes du projet : firstTower_readings [Direct.PairTowers]; définitions du projet : TrueZero, AnalyticContactPair.entryCoordinate, TrueTower.properState, firstTowerOf, pivotCoordinate, expectedMinimumPrime, AnalyticContactPair.stageCount; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `inversion` — `Demonstration` l.68 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, les deux contacts de l'état propre redonnent T (par leur rapport, le nombre d'étages et π) puis β (par la loi tangentielle appliquée à l'incidence d'entrée).
- **Vérités** : V45
- **Repose sur** : théorèmes du projet : AnalyticContactPair.recovers_T [Tower.ProperTower], AnalyticContactPair.recovers_beta [Tower.ProperTower]; définitions du projet : TrueZero, AnalyticContactPair.stageReading, TrueTower.properState, firstTowerOf, AnalyticContactPair.logDiameter, AnalyticContactPair.entryContact; base rhv3 : rZeroHeight, TNonTrivialZetaZero, PIsNonTrivialZetaZero, rZeroRadialPosition.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `reaches_expected` — `Demonstration` l.80 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, la première Tour atteint (compte jusqu'à son dernier rayon) le minimum attendu p_min(z).
- **Vérités** : V88, V143
- **Repose sur** : théorèmes du projet : firstTower_reaches_expected [Direct.PairTowers]; définitions du projet : TrueZero, reaches, TrueTower.properState, firstTowerOf, expectedMinimumPrime; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `reaches_occurrence` — `Demonstration` l.85 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, la première Tour atteint son occurrence Occ(z) à son dernier rayon (docstring : « C_lecture », sur la première Tour seulement).
- **Vérités** : V88, V75 (cas de la première Tour d'un zéro quelconque)
- **Repose sur** : théorèmes du projet : firstTower_reaches_occurrence [Direct.PairTowers]; définitions du projet : TrueZero, reaches, TrueTower.properState, firstTowerOf, occurrence; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `expected_le_counted` — `Demonstration` l.90 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, la cible constatée (dernier premier compté au dernier rayon) est au moins la référence p_min(z).
- **Vérités** : V37, V38
- **Repose sur** : théorèmes du projet : pivot_le_counted [Direct.PivotCell], expectedMinimumPrime_prime [Grammar.ExpectedMinimum]; définitions du projet : TrueZero, expectedMinimumPrime, countedPrime, TrueTower.properState, firstTowerOf; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `reached_progression` — `Demonstration` l.97 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la condition « a et b sont deux membres consécutifs » : l'occurrence de b est le minimum attendu de a, et elle est atteinte à l'état propre de b (progression des premiers atteints).
- **Vérités** : V54, V56, V88
- **Repose sur** : théorèmes du projet : progression_occurrence [Voyage.Progression], firstTower_reaches_occurrence [Direct.PairTowers]; définitions du projet : TrueZero, occurrence, expectedMinimumPrime, reaches, TrueTower.properState, firstTowerOf; base rhv3 : PZeroMembersConsecutive, TNonTrivialZetaZero, PIsNonTrivialZetaZero.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `verification_passes` — `Demonstration` l.104 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la condition « a précède b de façon consécutive » : le minimum attendu de a est atteint à l'état propre de la première Tour de b, sur ou hors ligne sans distinction (test de vérification par théorème).
- **Vérités** : V108, V132, V88
- **Repose sur** : théorèmes du projet : reaches_expected_of_reaches_occurrence [Direct.Reached], firstTower_reaches_occurrence [Direct.PairTowers]; définitions du projet : TrueZero, reaches, TrueTower.properState, firstTowerOf, expectedMinimumPrime; base rhv3 : PZeroMembersConsecutive, TNonTrivialZetaZero, PIsNonTrivialZetaZero.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).


##### A.2 Module `RHV6Fresh.Audit` (fichier `RHV6Fresh/Audit.lean`)

- **Théorèmes du module : 0** (aucune ligne du jsonl n'a ce module ; le fichier ne contient aucune déclaration `theorem`/`lemma`/`def`). Le module est un manifeste de fidélité (docstring au format du maître Lean §12) suivi de 158 commandes `#print axioms`.
- Ces commandes ne créent aucune dépendance de preuve (donc rien n'apparaît dans `deps_project`) ; elles font seulement afficher les axiomes de théorèmes nommés. Elles portent sur 23 théorèmes de ce lot, tous dans des pistes parquées : explicitIndex_injective, explicitFormula_counts_members, grammarsAgree_at_iff_onLine_below, pair_characteristic_splits, heightEventIndex_lt_sourceIndex_of_off_below, pastOnLine_all_iff_riemannHypothesis, completedZeta_zetaReflect, onLine_zero_iff_xiReal, centeredPoint_nontrivialZero_iff, fixedLocusSelection_iff_riemannHypothesis, deriv_eq_zero_iff_oddFactor, oddFactor_sign_alternates, scanConstraint_gives_only_height_avoidance, trivial_zero_not_completedZeta_zero, xiRealZeros_iff_riemannHypothesis, weilPairTerm_off_neg, weilPairPositivity_zeta_iff_riemannHypothesis, weilPairPositivity_not_from_config, zeroSideWindow_zeta_nonneg_of_riemannHypothesis, cpow_reflect_product, weilPairTerm_perron_pos, perronFamily_positive_zeta, perronFamily_positivity_not_riemannHypothesis.
- Le manifeste cite dans sa prose (docstring, lignes 91–93) les onze noms de la bibliothèque RHV6Demonstration (« DEMONSTRATION_SANS_RH=COMPILED … ») sans les référencer par `#print axioms` (les théorèmes de RHV6Demonstration ne sont pas importables depuis `RHV6Fresh.Audit`, qui fait partie de la bibliothèque RHV6Fresh).
- Le module importe quatre modules parqués : CriticalityCharacterization, FixedLocusParity, StabilityCriteria, PrimePositivity (lignes 16–19), et est lui-même importé par `RHV6Fresh.lean` (ligne 53).

**Statut de la partie A** : tous les théorèmes de RHV6Demonstration sont compilés avec les seuls axiomes standard, sans `sorry`. Deux d'entre eux ont pour condition la consécutivité de deux membres ; aucun n'énonce RiemannHypothesis.


---

##### Partie B — Ajout : pistes parquées

Cadre (CLAUDE.md §4, bullet « Purge des pistes parquées », auteur, 2026-09-27) : six pistes — collision d'événements (`Terminal/MirrorEventCollision.lean`), équivariance orientée (`Terminal/ReflectedTransition.lean`), réorientation/caractérisation de criticité (`Terminal/CriticalityCharacterization.lean`), parité de ξ et lieu fixe (`Terminal/FixedLocusParity.lean`), critères de stabilité globale (`Terminal/StabilityCriteria.lean`), fonctionnel positif côté premier (`Terminal/PrimePositivity.lean`) — « sont retirées de ce fichier. Elles restent dans le code (aucun fichier supprimé, aucune régression de build) et dans `git log`, qui en tient lieu d'historique (§2) ; aucune d'elles n'a produit de contradiction, aucune n'est sur la voie active actuelle (chaîne arithmétique / C_lecture / injectivité et progression de `pmin`) ». Motif donné par CLAUDE.md : « Les conserver ici entretenait la confusion entre « exploré et parqué sans résultat » et « actif » ». Ce motif porte sur le fichier CLAUDE.md ; le code Lean des six modules reste compilé et est importé par `RHV6Fresh.lean` (lignes 46–51).

**Dépendance des théorèmes actifs envers les pistes parquées (graphe `deps_project` sur les 742 théorèmes)** : `mirror_sameHeightIndex` est utilisé par `mirror_heightEventIndex_eq` (RHV6Fresh.Terminal.MirrorFrequency). Il s'agit du seul lien de ce type. `mirror_heightEventIndex_eq` a lui-même pour dépendants transitifs : off_consecutive_translation_signature, off_mirror_same_frequency, off_mirror_same_frequency_of_consecutive, onLine_mirror_trivial. Au niveau des fichiers : `Terminal/MirrorFrequency.lean` importe `Terminal/MirrorEventCollision.lean` (ligne 4) ; `Terminal/TranslationVsProgression.lean` importe `MirrorFrequency` ; `RHV6Fresh.lean` importe les six modules et `Audit.lean` en importe quatre. Recherche textuelle des 123 noms de théorèmes des six modules dans tous les `.lean` de `RHV6Fresh/` (hors leur module propre) : seuls `Audit.lean` (23 `#print axioms`), `MirrorFrequency.lean` (`mirror_sameHeightIndex`) et les autres pistes parquées les nomment ; aucun autre fichier actif.


##### B — Piste 1 : collision d'événements (`Terminal/MirrorEventCollision.lean`)

**Ce que la piste établit, dans les mots du maître (docstring du module, auteur 2026-09-25)** : la contradiction candidate est « la réflexion ne crée pas un nouvel événement » contre « l'ordre des membres fait avancer l'événement », avec z = (β, T), z* = (1 − β, T), β < 1/2, aucune hypothèse nouvelle. Verdict du compilateur : Cible A (progression stricte des membres) = théorème ; Cible B (le miroir ne consomme aucun événement de hauteur mais consomme un index de membre) = théorèmes, deux grammaires distinctes ; Cible C (`Occ(z*) = Occ(z)`) réfutée par théorème pour tout z de côté bas, l'exiger de tout zéro de côté bas est RH ; le transport « occurrence par hauteur → occurrence par membre » au miroir est réfuté hors ligne ; le maître dit : « Aucun terme `RiemannHypothesis` ne sort de cette route ».

**Statut** : 14 théorèmes ; CONFIRMÉE SOUS CONDITION : 4, CONFIRMÉE : 5, RÉFUTATION COMPILÉE : 3, ÉQUIVALENTE À RH : 2. Aucune contradiction ; deux équivalences à RH sur des prémisses exigées de tout zéro de côté bas (Cible C, transport au miroir) et trois réfutations compilées (Cible C, transport aux deux membres, transport au miroir). Le maître (V131) reprend, hors de ce module, l'énoncé « la grammaire par hauteurs tolère un zéro hors ligne (même premier au membre et à son miroir) », établi ici par `mirror_sameHeightPrime`.

**Pourquoi parquée (CLAUDE.md §4)** : Le module figure dans la liste des six pistes purgées. Ce que CLAUDE.md dit de la route : elle est parquée « sans résultat » (aucune contradiction) ; `mirror_sameHeightIndex` a pourtant un usage actif ci-dessous.

**Un théorème actif en dépend-il ?** Oui, un seul lien : `mirror_sameHeightIndex` est utilisé par `mirror_heightEventIndex_eq` du module actif `Terminal/MirrorFrequency.lean` (importé par `RHV6Fresh.lean` et par `TranslationVsProgression.lean`), dont la preuve l'appelle (`MirrorFrequency.lean` l. 108, `mirror_sameHeightIndex z`). Aucun autre théorème du module n'est utilisé hors du module (dans `deps_project`).

**Théorèmes hors lot sur lesquels la piste s'appuie le plus** : sourceIndex_lt_mirror (3), mirrorMember_ordinate (3), riemannHypothesis_of_noLowerSide (2), occurrence_eq_canonicalAnchor (1), occurrence_eq_primeAtRank (1), heightEventIndex_le_sourceIndex (1).

#### `mirror_occurrence_strict` — `MirrorEventCollision` l.43 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la condition « z de côté bas » : Occ(z) < Occ(z*), les occurrences membres du zéro et de son miroir sont strictement ordonnées (M^Z = M et ordre strict des membres).
- **Vérités** : V74 (partiellement : occurrence avancée ; non « au moins le minimum attendu »), V68
- **Repose sur** : théorèmes du projet : occurrence_eq_primeAtRank [Voyage.Progression], sourceIndex_lt_mirror [Direct.MirrorCount]; définitions du projet : TrueZero, occurrence, mirrorMember; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, fnPrimeAtRank, nZeroSourceIndex, thm_primeAtRank_strictMono.
- **Entraîne** : mirror_event_collision_content, mirror_event_identity_refuted, reflected_transition_content [ReflectedTransition], transport_at_z_gives_nothing.

#### `mirror_consumes_member_index` — `MirrorEventCollision` l.49 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la condition « z de côté bas » : l'index par membres de z est strictement inférieur à celui de z* (le miroir consomme un index de membre).
- **Vérités** : V74, V68, V64
- **Repose sur** : théorèmes du projet : sourceIndex_lt_mirror [Direct.MirrorCount]; définitions du projet : TrueZero, mirrorMember; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, nZeroSourceIndex.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `mirror_sameHeightEvent` — `MirrorEventCollision` l.56 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, le miroir a le même événement de hauteur que z.
- **Vérités** : V127, V131
- **Repose sur** : théorèmes du projet : mirrorMember_ordinate [Direct.MirrorCount]; définitions du projet : TrueZero, mirrorMember; base rhv3 : TZeroHeightEvent, tZeroHeightEvent, thm_sameHeight_sameHeightEvent.
- **Entraîne** : explicitFormula_counts_members [CriticalityCharacterization], mirror_event_collision_content, mirror_no_new_height_event.

#### `mirror_sameHeightIndex` — `MirrorEventCollision` l.60 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, l'index par hauteurs de l'événement du miroir est celui de z.
- **Vérités** : V131
- **Repose sur** : théorèmes du projet : mirrorMember_ordinate [Direct.MirrorCount]; définitions du projet : TrueZero, mirrorMember; base rhv3 : nZeroHeightEventIndex, tZeroHeightEvent, thm_heightEventIndex_eq_of_sameHeight.
- **Entraîne** : mirror_heightEventIndex_eq [Terminal.MirrorFrequency], mirror_heightEventIndex_lt_sourceIndex [CriticalityCharacterization], mirror_heightEventTransition_eq [ReflectedTransition], mirror_no_new_height_event, mirror_transport_refuted — UTILISÉ HORS DU LOT (module actif) : mirror_heightEventIndex_eq [Terminal.MirrorFrequency].

#### `mirror_sameHeightPrime` — `MirrorEventCollision` l.65 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, l'occurrence par hauteurs du miroir est celle de z : même premier au membre et à son miroir dans la grammaire par hauteurs.
- **Vérités** : V131
- **Repose sur** : théorèmes du projet : mirrorMember_ordinate [Direct.MirrorCount]; définitions du projet : TrueZero, mirrorMember; base rhv3 : nHeightEventMZOccurrence, tZeroHeightEvent, thm_sameHeight_sameReconstructedPrime.
- **Entraîne** : mirror_event_collision_content, mirror_no_new_height_event, pair_transport_false, transport_at_z_gives_nothing.

#### `mirror_no_new_height_event` — `MirrorEventCollision` l.70 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, le miroir ne crée aucun événement de hauteur : même événement, même index par hauteurs, même premier par hauteurs que z.
- **Vérités** : V131, V127
- **Repose sur** : théorèmes du projet : mirror_sameHeightEvent, mirror_sameHeightIndex, mirror_sameHeightPrime; définitions du projet : TrueZero, mirrorMember; base rhv3 : TZeroHeightEvent, tZeroHeightEvent, nZeroHeightEventIndex, nHeightEventMZOccurrence.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `mirror_event_identity_refuted` — `MirrorEventCollision` l.81 — RÉFUTATION COMPILÉE
- **Énoncé** : Sous la condition « z de côté bas » : Occ(z*) = Occ(z) est faux. Réfute la « Cible C » (identité des occurrences membres) de la piste de collision d'événements du 2026-09-25.
- **Vérités** : V126 (route réfutée)
- **Repose sur** : théorèmes du projet : mirror_occurrence_strict; définitions du projet : TrueZero, occurrence, mirrorMember; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero.
- **Entraîne** : mirrorEventIdentity_iff_riemannHypothesis, pair_transport_false.

#### `mirrorEventIdentity_iff_riemannHypothesis` — `MirrorEventCollision` l.93 — ÉQUIVALENTE À RH
- **Énoncé** : La prémisse `PMirrorEventIdentity` (Cible C exigée de tout zéro de côté bas) équivaut à RiemannHypothesis : son corps est insatisfiable hors ligne.
- **Vérités** : V117, V126
- **Repose sur** : théorèmes du projet : riemannHypothesis_of_noLowerSide [Terminal.Universalization], mirror_event_identity_refuted; définitions du projet : PMirrorEventIdentity, TrueZero, occurrence, mirrorMember; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, thm_zeroRadialPosition_half_of_riemannHypothesis.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `memberHeightTransport_iff_index` — `MirrorEventCollision` l.110 — CONFIRMÉE
- **Énoncé** : Pour tout zéro w, le transport « occurrence membre = occurrence de l'événement de hauteur » en w équivaut à n(w) = h(w) (égalité des deux index).
- **Vérités** : AJOUT (voisin de V59)
- **Repose sur** : théorèmes du projet : occurrence_eq_canonicalAnchor [CleanTerminal]; définitions du projet : TrueZero, memberHeightTransport, occurrence; base rhv3 : nZeroSourceIndex, TNonTrivialZetaZero, PIsNonTrivialZetaZero, nZeroHeightEventIndex, tZeroHeightEvent, nHeightEventMZOccurrence, nMemberCanonicalAnchor, nHeightEventCanonicalPrime, thm_heightEventMZOccurrence_eq_canonicalPrime_unconditional, fnPrimeAtRank, thm_primeAtRank_injective.
- **Entraîne** : mirror_transport_refuted.

#### `pair_transport_false` — `MirrorEventCollision` l.119 — RÉFUTATION COMPILÉE
- **Énoncé** : Sous les conditions « z de côté bas », transport en z et transport en z* : False (le transport aux deux membres de la paire donne la Cible C, réfutée). Réfute la conjonction des deux transports de la piste.
- **Vérités** : V126
- **Repose sur** : théorèmes du projet : mirror_event_identity_refuted, mirror_sameHeightPrime; définitions du projet : TrueZero, memberHeightTransport, mirrorMember, occurrence; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, nHeightEventMZOccurrence, tZeroHeightEvent.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `mirror_transport_refuted` — `MirrorEventCollision` l.126 — RÉFUTATION COMPILÉE
- **Énoncé** : Sous la condition « z de côté bas » : le transport au miroir z* est faux (l'index par hauteurs de z* est celui de z, au plus n(z) < n(z*)). Réfute le « raccord manquant » que la piste demandait.
- **Vérités** : V126
- **Repose sur** : théorèmes du projet : heightEventIndex_le_sourceIndex [Terminal.EventHeightProgression], sourceIndex_lt_mirror [Direct.MirrorCount], mirror_sameHeightIndex, memberHeightTransport_iff_index; définitions du projet : TrueZero, memberHeightTransport, mirrorMember; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, nZeroHeightEventIndex, tZeroHeightEvent, nZeroSourceIndex.
- **Entraîne** : mirrorTransport_iff_riemannHypothesis.

#### `transport_at_z_gives_nothing` — `MirrorEventCollision` l.136 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous les conditions « z de côté bas » et « transport en z » : l'occurrence par hauteurs du miroir vaut Occ(z) et Occ(z) < Occ(z*) ; le transport en z seul ne dit rien de z*.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : mirror_sameHeightPrime, mirror_occurrence_strict; définitions du projet : TrueZero, memberHeightTransport, mirrorMember, occurrence; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, nHeightEventMZOccurrence, tZeroHeightEvent.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `mirrorTransport_iff_riemannHypothesis` — `MirrorEventCollision` l.150 — ÉQUIVALENTE À RH
- **Énoncé** : La prémisse `PMirrorTransport` (transport au miroir exigé de tout zéro de côté bas) équivaut à RiemannHypothesis.
- **Vérités** : V117, V126
- **Repose sur** : théorèmes du projet : riemannHypothesis_of_noLowerSide [Terminal.Universalization], mirror_transport_refuted; définitions du projet : PMirrorTransport, TrueZero, memberHeightTransport, mirrorMember; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, thm_zeroRadialPosition_half_of_riemannHypothesis.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `mirror_event_collision_content` — `MirrorEventCollision` l.161 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la condition « z de côté bas » : même événement de hauteur, même premier par hauteurs pour z et z*, et Occ(z) < Occ(z*) ; deux fonctions d'index distinctes, aucun False.
- **Vérités** : V131, V127
- **Repose sur** : théorèmes du projet : mirror_sameHeightEvent, mirror_sameHeightPrime, mirror_occurrence_strict; définitions du projet : TrueZero, mirrorMember, occurrence; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, TZeroHeightEvent, tZeroHeightEvent, nHeightEventMZOccurrence.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).


##### B — Piste 2 : équivariance orientée (`Terminal/ReflectedTransition.lean`)

**Ce que la piste établit, dans les mots du maître (docstring du module, auteur 2026-09-25)** : partir du quartet zeta23 (ρ ↦ 1 − ρ̄ puis 1 − ρ̄ ↦ 1 − ρ), utiliser `trajet(1 − ρ) = reverse(trajet(1 − ρ̄))`, projeter l'événement sur la grammaire première ; si l'événement droit donne (p_n, p_{n+1}), sa réflexion pure donne (p_{n+1}, p_n), or M^Z = M dit que les transitions sont toujours orientées p_k → p_{k+1}, d'où p_n < p_{n+1} < p_n. Compilé : la réflexion ne crée aucun événement premier ; quartet et renversement ; la transition d'un membre est canonique ; l'orientation droite présente la transition dans l'ordre, la réflexion à rebours ; l'arithmétique refuse le retour. Le `False` sort de la prémisse « la transition présentée par la réflexion est une transition de la grammaire », réfutée pour tout membre, sur la droite comme hors ligne ; l'exiger de tout zéro de côté bas est RH, de tout zéro est « il n'existe aucun zéro supérieur ». Raison compilée : le zéro réfléchi a une hauteur strictement négative, aucune grammaire de la base n'est définie sur lui. Le maître du module : « Aucun terme `RiemannHypothesis` ne sort de cette route ».

**Statut** : 23 théorèmes ; CONFIRMÉE : 15, RÉFUTATION COMPILÉE : 6, ÉQUIVALENTE À RH : 1, CONFIRMÉE SOUS CONDITION : 1. Aucune contradiction inconditionnelle : le `False` ne distingue pas β < 1/2 de β = 1/2 (`reflected_equivariance_false_onLine`) ; une équivalence à RH (`reflectedEquivariance_iff_riemannHypothesis`). Les théorèmes géométriques du module (`quartet_chain`, `trajectory_reversal`, `reflection_creates_no_prime_event`, `reflection_reverses_existing_ring`, `reflectedZero_not_member`, `upright_presents_forward`, `reflected_presents_reversed`, `reflected_presents_via_functional_reflect`) rejoignent des vérités du maître (V63, V72/V96, V80, V88, V135).

**Pourquoi parquée (CLAUDE.md §4)** : Module de la liste des six pistes purgées ; le maître (V72, V96) cite comme « compilé » le mouvement réfléchi sans événement d'arrêt, avec le fichier `Terminal/ReflectedObligation.lean` (non parqué) et non ce module. CLAUDE.md ajoute, dans le bullet « Mise en garde de l'auteur » (2026-09-26), que la seconde Tour n'est pas obtenue en suivant le mouvement réfléchi depuis son origine (deux objets distincts) ; les théorèmes de ce module manipulent les deux (`reflection_creates_no_prime_event` : mouvement depuis l'origine ; `reflected_presents_reversed`, `reflected_presents_via_functional_reflect` : `secondTowerOf`).

**Un théorème actif en dépend-il ?** Non : aucun des 23 théorèmes du module n'est utilisé par un théorème hors du module (`deps_project`). Le module dépend, lui, de théorèmes actifs (`secondTower_*`, `reflectedIncidence_eq`, `reflected_reads_no_prime`, `occurrence_lt_expectedMinimumPrime`, etc.), voir la liste ci-dessus.

**Théorèmes hors lot sur lesquels la piste s'appuie le plus** : reflectedZero_support (2), occurrence_eq_primeAtRank (1), riemannHypothesis_of_noLowerSide (1), reflectedZero_im (1), secondTower_entry_reaches_mirror_occurrence (1), secondTower_entry_reaches_own_expected (1), secondTower_cell_contains_own_expected (1), secondTower_lastRay_eq_reflected (1), secondTower_entry_eq_reflected (1), reflected_reads_no_prime (1).

#### `primeTransition_forward` — `ReflectedTransition` l.67 — CONFIRMÉE
- **Énoncé** : Toute transition canonique (p_n, p_{n+1}) avance : p_n < p_{n+1}.
- **Vérités** : AJOUT (voisin de V159)
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : primeTransition; base rhv3 : thm_primeAtRank_strictMono.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `reversedTransition_backward` — `ReflectedTransition` l.71 — CONFIRMÉE
- **Énoncé** : La transition renversée (p_{n+1}, p_n) recule : sa seconde composante est inférieure à la première.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : reversedTransition; base rhv3 : thm_primeAtRank_strictMono.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `forward_and_backward_false` — `ReflectedTransition` l.76 — RÉFUTATION COMPILÉE
- **Énoncé** : Sous les conditions a < b et b < a sur des entiers : False. Réfute la double lecture « p_n < p_{n+1} < p_n » de la piste d'équivariance orientée (axiomes utilisés : aucun).
- **Vérités** : V126 (route réfutée)
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : aucune; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `reversedTransition_not_canonical` — `ReflectedTransition` l.80 — RÉFUTATION COMPILÉE
- **Énoncé** : Pour tout n, la transition renversée (p_{n+1}, p_n) n'est la transition canonique d'aucun rang m : réfute que la transition renversée soit une transition de la grammaire première.
- **Vérités** : V126 (route réfutée)
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : primeTransition, reversedTransition; base rhv3 : fnPrimeAtRank, thm_primeAtRank_strictMono.
- **Entraîne** : reflectedHeightTransitionCanonical_refuted, reflectedTransitionCanonical_refuted.

#### `memberTransition_eq_canonical` — `ReflectedTransition` l.100 — CONFIRMÉE
- **Énoncé** : Pour tout membre w, sa transition (Occ(w), p_min(w)) est la transition canonique de son index n(w) (M^Z = M au niveau des transitions).
- **Vérités** : V159 (M^Z = M), O13 (couche transitions)
- **Repose sur** : théorèmes du projet : occurrence_eq_primeAtRank [Voyage.Progression]; définitions du projet : TrueZero, memberTransition, primeTransition, occurrence, expectedMinimumPrime; base rhv3 : nZeroSourceIndex, TNonTrivialZetaZero, PIsNonTrivialZetaZero, fnPrimeAtRank, fnPrimeSuccessor.
- **Entraîne** : reflected_transition_content.

#### `heightEventTransition_fst` — `ReflectedTransition` l.110 — CONFIRMÉE
- **Énoncé** : Pour tout membre w, le premier terme de sa transition par hauteurs est l'occurrence par hauteurs de son événement.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : TrueZero, heightEventTransition, primeTransition; base rhv3 : nHeightEventMZOccurrence, tZeroHeightEvent, nZeroHeightEventIndex, nHeightEventCanonicalPrime, thm_heightEventMZOccurrence_eq_canonicalPrime_unconditional.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `mirror_heightEventTransition_eq` — `ReflectedTransition` l.116 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, z et son miroir ont la même transition par événement de hauteur.
- **Vérités** : V131
- **Repose sur** : théorèmes du projet : mirror_sameHeightIndex [MirrorEventCollision]; définitions du projet : TrueZero, heightEventTransition, mirrorMember, primeTransition; base rhv3 : nZeroHeightEventIndex, tZeroHeightEvent.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `quartet_chain` — `ReflectedTransition` l.125 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, la réflexion zeta23 envoie le support de z sur le support du miroir z*, et la réflexion fonctionnelle envoie le support de z sur le conjugué du support de z* : le quartet ρ, ρ̄, 1 − ρ̄, 1 − ρ.
- **Vérités** : V63, V62
- **Repose sur** : théorèmes du projet : reflectedZero_support [Tower.ReflectedMotion]; définitions du projet : TrueZero, zetaReflect, mirrorMember, zetaFunctionalReflect; base rhv3 : cZeroSupport, TNonTrivialZetaZero, PIsNonTrivialZetaZero.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `trajectory_reversal` — `ReflectedTransition` l.132 — CONFIRMÉE
- **Énoncé** : Pour tout zéro z et tout j entier, l'incidence réfléchie du miroir en j est l'incidence de la Tour du miroir en −j : les rayons du zéro réfléchi sont ceux du membre miroir parcourus à l'envers.
- **Vérités** : V80, V71
- **Repose sur** : théorèmes du projet : reflectedIncidence_eq [Tower.ReflectedMotion]; définitions du projet : TrueZero, reflectedIncidence, mirrorMember, TowerMotion.incidence, towerMotionOf; base rhv3 : aucun.
- **Entraîne** : reflected_transition_content.

#### `reflection_creates_no_prime_event` — `ReflectedTransition` l.138 — CONFIRMÉE
- **Énoncé** : Pour tout membre w, tout j naturel et tout premier p : p n'est pas ≤ à l'incidence réfléchie de w en j+1 : depuis son origine le mouvement réfléchi n'atteint aucun premier à un dernier rayon.
- **Vérités** : V72, V96
- **Repose sur** : théorèmes du projet : reflected_reads_no_prime [Terminal.ReflectedObligation]; définitions du projet : TrueZero, reflectedIncidence; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `reflection_reverses_existing_ring` — `ReflectedTransition` l.145 — CONFIRMÉE
- **Énoncé** : Pour tout membre w et tout k entier : à la coordonnée −(k+1), l'entrée du mouvement réfléchi est le rayon du haut C_{k+1} et son dernier rayon est le rayon du bas C_k de l'anneau k du membre.
- **Vérités** : V80, V34
- **Repose sur** : théorèmes du projet : reflected_entry_eq_contactPlus [Tower.ReflectedMotion], reflected_lastRay_eq_contactMinus [Tower.ReflectedMotion]; définitions du projet : TrueZero, reflectedIncidence, contactPlusAt, contactMinusAt; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `reflectedZero_not_member` — `ReflectedTransition` l.153 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, le zéro réfléchi 1 − ρ a une partie imaginaire strictement négative : il n'est jamais membre.
- **Vérités** : V96, V64
- **Repose sur** : théorèmes du projet : reflectedZero_im [Tower.ReflectedMotion]; définitions du projet : TrueZero, zetaFunctionalReflect, mirrorMember; base rhv3 : cZeroSupport, TNonTrivialZetaZero, PIsNonTrivialZetaZero, rZeroHeight.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `upright_presents_forward` — `ReflectedTransition` l.162 — CONFIRMÉE
- **Énoncé** : Pour tout membre w, la Tour de w atteint Occ(w) puis p_min(w) à son dernier rayon, et Occ(w) < p_min(w) : l'orientation droite présente la transition dans l'ordre.
- **Vérités** : V88, V75
- **Repose sur** : théorèmes du projet : firstTower_reaches_occurrence [Direct.PairTowers], firstTower_reaches_expected [Direct.PairTowers], occurrence_lt_expectedMinimumPrime [Grammar.ExpectedMinimum]; définitions du projet : TrueZero, reaches, TrueTower.properState, firstTowerOf, memberTransition; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `reflected_presents_reversed` — `ReflectedTransition` l.171 — CONFIRMÉE
- **Énoncé** : Pour tout zéro z, sur l'anneau du membre miroir, la seconde Tour a une entrée au moins égale à p_min(z*) et un dernier rayon strictement sous p_min(z*), et Occ(z*) est au plus l'entrée ; que Occ(z*) soit atteint au dernier rayon reste une lecture.
- **Vérités** : V135, V82, O11
- **Repose sur** : théorèmes du projet : secondTower_entry_reaches_own_expected [Direct.PairTowers], secondTower_cell_contains_own_expected [Direct.PairTowers], secondTower_entry_reaches_mirror_occurrence [Direct.PairTowers]; définitions du projet : TrueZero, memberTransition, mirrorMember, InvertedContactPair.entryContact, InvertedTower.properState, secondTowerOf, InvertedContactPair.lastRayContact, InvertedTower.toInvertedContactPair, expectedMinimumPrime; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `reflected_presents_via_functional_reflect` — `ReflectedTransition` l.183 — CONFIRMÉE
- **Énoncé** : Pour tout zéro z, l'entrée et le dernier rayon de la seconde Tour sont les incidences réfléchies du miroir aux coordonnées −(k+1) et −(k+1)+1, k étant la position du minimum attendu du miroir.
- **Vérités** : V80, V34
- **Repose sur** : théorèmes du projet : secondTower_entry_eq_reflected [Direct.PairTowers], secondTower_lastRay_eq_reflected [Direct.PairTowers]; définitions du projet : TrueZero, InvertedContactPair.entryContact, mirrorMember, InvertedTower.toInvertedContactPair, secondTowerOf, reflectedIncidence, pivotCoordinate, expectedMinimumPrime, InvertedContactPair.lastRayContact; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `reflectedTransitionCanonical_refuted` — `ReflectedTransition` l.207 — RÉFUTATION COMPILÉE
- **Énoncé** : Pour tout membre, sur la droite comme hors ligne, la transition renversée n'est pas une transition canonique de la grammaire reconstruite : `reflectedTransitionCanonical w` est faux. Réfute la prémisse d'équivariance orientée de la piste.
- **Vérités** : V126 (route réfutée)
- **Repose sur** : théorèmes du projet : reversedTransition_not_canonical; définitions du projet : TrueZero, reflectedTransitionCanonical; base rhv3 : nZeroSourceIndex, TNonTrivialZetaZero, PIsNonTrivialZetaZero.
- **Entraîne** : reflectedEquivariance_all_iff_noZero, reflected_equivariance_false, reflected_equivariance_false_onLine, reflected_transition_content.

#### `reflectedHeightTransitionCanonical_refuted` — `ReflectedTransition` l.211 — RÉFUTATION COMPILÉE
- **Énoncé** : Même énoncé, version événement de hauteur : `reflectedHeightTransitionCanonical w` est faux pour tout membre.
- **Vérités** : V126 (route réfutée)
- **Repose sur** : théorèmes du projet : reversedTransition_not_canonical; définitions du projet : TrueZero, reflectedHeightTransitionCanonical; base rhv3 : nZeroHeightEventIndex, tZeroHeightEvent.
- **Entraîne** : reflectedHeightEquivariance_all_iff_noZero.

#### `reflected_equivariance_false` — `ReflectedTransition` l.216 — RÉFUTATION COMPILÉE
- **Énoncé** : Sous les conditions « z de côté bas » et « équivariance orientée au miroir de z » : False.
- **Vérités** : V126 (route réfutée)
- **Repose sur** : théorèmes du projet : reflectedTransitionCanonical_refuted; définitions du projet : TrueZero, reflectedTransitionCanonical, mirrorMember; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero.
- **Entraîne** : reflectedEquivariance_iff_riemannHypothesis.

#### `reflected_equivariance_false_onLine` — `ReflectedTransition` l.222 — RÉFUTATION COMPILÉE
- **Énoncé** : Sous les conditions « w sur la droite » et « équivariance orientée en w » : False ; la route ne distingue pas β < 1/2 de β = 1/2.
- **Vérités** : V126 (route réfutée)
- **Repose sur** : théorèmes du projet : reflectedTransitionCanonical_refuted; définitions du projet : TrueZero, reflectedTransitionCanonical; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `reflectedEquivariance_iff_riemannHypothesis` — `ReflectedTransition` l.232 — ÉQUIVALENTE À RH
- **Énoncé** : La prémisse `PReflectedEquivariance` (équivariance orientée exigée au miroir de tout zéro de côté bas) équivaut à RiemannHypothesis : son corps est insatisfiable.
- **Vérités** : V117, V126
- **Repose sur** : théorèmes du projet : riemannHypothesis_of_noLowerSide [Terminal.Universalization], reflected_equivariance_false; définitions du projet : PReflectedEquivariance, TrueZero, reflectedTransitionCanonical, mirrorMember; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, thm_zeroRadialPosition_half_of_riemannHypothesis.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `reflectedEquivariance_all_iff_noZero` — `ReflectedTransition` l.243 — CONFIRMÉE
- **Énoncé** : L'équivariance orientée en tout zéro équivaut à « l'ensemble des zéros supérieurs est vide » (IsEmpty TrueZero) ; équivalence avec un énoncé qui n'est pas RiemannHypothesis.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : reflectedTransitionCanonical_refuted; définitions du projet : TrueZero, reflectedTransitionCanonical; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `reflectedHeightEquivariance_all_iff_noZero` — `ReflectedTransition` l.253 — CONFIRMÉE
- **Énoncé** : Même équivalence pour la version par événement de hauteur : l'équivariance orientée par hauteurs en tout zéro équivaut à IsEmpty TrueZero.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : reflectedHeightTransitionCanonical_refuted; définitions du projet : TrueZero, reflectedHeightTransitionCanonical; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `reflected_transition_content` — `ReflectedTransition` l.264 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la condition « z de côté bas » : le quartet, le trajet renversé, la transition canonique du miroir, Occ(z) < Occ(z*), et la transition renversée du miroir n'est pas canonique ; aucune contradiction.
- **Vérités** : V63, V80, V159, V126
- **Repose sur** : théorèmes du projet : reflectedZero_support [Tower.ReflectedMotion], trajectory_reversal, memberTransition_eq_canonical, mirror_occurrence_strict [MirrorEventCollision], reflectedTransitionCanonical_refuted; définitions du projet : TrueZero, zetaFunctionalReflect, mirrorMember, reflectedIncidence, TowerMotion.incidence, towerMotionOf, memberTransition, primeTransition, occurrence, reflectedTransitionCanonical; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, cZeroSupport, nZeroSourceIndex.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).


##### B — Piste 3 : réorientation, criticité comme caractéristique (`Terminal/CriticalityCharacterization.lean`)

**Ce que la piste établit, dans les mots du maître (docstring du module, auteur 2026-09-25)** : « Toutes les routes « OFF ⟹ False » ont fini sur une prémisse réfutée hors ligne ou équivalente à RH. La cible change de forme : … quelle caractéristique compilée distingue la droite critique ». (1) La formule explicite compilée compte les membres, non les événements : un index par point, une paire hors ligne est deux index à même fréquence, même événement de hauteur, deux amplitudes x^β et x^(1−β) ; sur la droite un seul index. (2) `n(z) = h(z)` si et seulement si tout membre qui précède z est sur la droite : caractéristique globale, position radiale de z sans effet ; z de côté bas au passé sur la droite a n = h et son miroir h < n ; un seul membre hors ligne dans le passé la détruit ; exigée de tout membre, elle est RH. (3) La chaîne « progression ⟹ un événement par étape ⟹ z* = z ⟹ β = 1/2 » a pour maillon central « un membre par hauteur », c'est-à-dire n = h partout, c'est-à-dire RH ; ce qui reste est d'isoler le terme de la paire hors ligne dans la somme (absent de la base et de Mathlib). Le module : « Aucun terme `RiemannHypothesis` ne sort de ce module ».

**Statut** : 17 théorèmes ; CONFIRMÉE : 7, CONFIRMÉE SOUS CONDITION : 8, ÉQUIVALENTE À RH : 2. Aucune contradiction ; une équivalence à RH (`pastOnLine_all_iff_riemannHypothesis`, et son pendant `grammarsAgree_all_iff_pastOnLine_all`). Ce module porte les énoncés que le maître cite comme « Compilé » aux lignes 131 (V127, V128, V129) ; c'est la tension T15 de `VERITES_MAITRE.md` (fichier parqué par CLAUDE.md mais cité comme compilé par le maître) — signalée, non résolue ici.

**Pourquoi parquée (CLAUDE.md §4)** : Module de la liste des six pistes purgées de CLAUDE.md ; mais le maître sémantique (l. 131) cite ses résultats. Le code compilé prime (CLAUDE.md §2) : les théorèmes sont vrais, le rangement « parqué » ne concerne que le statut de piste dans CLAUDE.md.

**Un théorème actif en dépend-il ?** Non : aucun théorème hors du module n'utilise l'un des 17 (`deps_project`). Le module dépend de `mirror_sameHeightEvent` et `mirror_amplitude_exponent_dominates`, `mirror_sameHeightIndex` (MirrorEventCollision), de `grammarsAgree_iff_riemannHypothesis` et d'autres théorèmes actifs.

**Théorèmes hors lot sur lesquels la piste s'appuie le plus** : mirrorMember_ordinate (3), heightEventIndex_le_sourceIndex (2), mirror_amplitude_exponent_dominates (1), mirrorMember_eq_self_of_onLine (1), mirrorMember_radial (1), sourceIndex_lt_mirror (1), grammarsAgree_iff_riemannHypothesis (1).

#### `explicitIndex_val` — `CriticalityCharacterization` l.63 — CONFIRMÉE
- **Énoncé** : La valeur complexe de l'index d'un membre dans la somme de la formule explicite est le point du zéro (`zeroPoint z`).
- **Vérités** : AJOUT (voisin de V127)
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : TrueZero, explicitIndex, zeroPoint; base rhv3 : IsNontrivialZetaZero.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `explicitIndex_term` — `CriticalityCharacterization` l.65 — CONFIRMÉE
- **Énoncé** : Le terme du membre dans la somme sur les zéros est celui de son index : −multiplicité · Perron.f x (point du zéro).
- **Vérités** : V127
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : TrueZero, explicitIndex, zeroPoint; base rhv3 : nontrivialZeroResidueTerm, zetaZeroMultiplicity; autres bases : Perron.f.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `explicitIndex_injective` — `CriticalityCharacterization` l.70 — CONFIRMÉE
- **Énoncé** : L'application membre → index de la somme est injective : deux membres distincts ont deux index distincts, la somme compte les membres.
- **Vérités** : V127
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : TrueZero, explicitIndex, zeroPoint; base rhv3 : IsNontrivialZetaZero, TNonTrivialZetaZero, PIsNonTrivialZetaZero.
- **Entraîne** : explicitIndex_mirror_ne_of_off.

#### `explicitIndex_mirror_im` — `CriticalityCharacterization` l.79 — CONFIRMÉE
- **Énoncé** : Le miroir d'un membre a la même partie imaginaire d'index que le membre : même fréquence.
- **Vérités** : V127, V65
- **Repose sur** : théorèmes du projet : mirrorMember_ordinate [Direct.MirrorCount]; définitions du projet : TrueZero, explicitIndex, mirrorMember; base rhv3 : IsNontrivialZetaZero.
- **Entraîne** : explicitFormula_counts_members.

#### `explicitIndex_mirror_ne_of_off` — `CriticalityCharacterization` l.84 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la condition « le membre est hors ligne » : le miroir occupe un second index, distinct de celui du membre, dans la somme.
- **Vérités** : V127
- **Repose sur** : théorèmes du projet : explicitIndex_injective; définitions du projet : TrueZero, explicitIndex, mirrorMember; base rhv3 : PIsOffCriticalLine, TNonTrivialZetaZero, PIsNonTrivialZetaZero, IsNontrivialZetaZero, thm_offCriticalLine_mirror_distinct.
- **Entraîne** : explicitIndex_mirror_ne.

#### `explicitIndex_mirror_ne` — `CriticalityCharacterization` l.91 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la condition « le membre est de côté bas (β < 1/2) » : l'index du miroir est distinct de celui du membre.
- **Vérités** : V127
- **Repose sur** : théorèmes du projet : explicitIndex_mirror_ne_of_off; définitions du projet : TrueZero, explicitIndex, mirrorMember; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, IsNontrivialZetaZero.
- **Entraîne** : explicitFormula_counts_members.

#### `explicitIndex_mirror_eq_of_onLine` — `CriticalityCharacterization` l.95 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la condition « le membre est sur la droite (β = 1/2) » : l'index du miroir est celui du membre (un seul terme).
- **Vérités** : V127, V77
- **Repose sur** : théorèmes du projet : mirrorMember_eq_self_of_onLine [Direct.MirrorCount]; définitions du projet : TrueZero, explicitIndex, mirrorMember; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, IsNontrivialZetaZero.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `explicitFormula_counts_members` — `CriticalityCharacterization` l.101 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous les conditions « z de côté bas » et x ≥ 1 : la paire z, z* occupe deux index distincts de la somme, à même fréquence, au même événement de hauteur, avec deux amplitudes x^β ≤ x^(1−β).
- **Vérités** : V127, V102
- **Repose sur** : théorèmes du projet : explicitIndex_mirror_ne, explicitIndex_mirror_im, mirror_sameHeightEvent [MirrorEventCollision], mirror_amplitude_exponent_dominates [Terminal.ExplicitFormulaLink]; définitions du projet : TrueZero, explicitIndex, mirrorMember; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, IsNontrivialZetaZero, TZeroHeightEvent, tZeroHeightEvent.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `heightsBelow_subset_image` — `CriticalityCharacterization` l.119 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, l'ensemble des hauteurs distinctes sous z est contenu dans l'image par la hauteur des membres qui précèdent z (énoncé lu avec des preuves de finitude masquées dans le type, `⋯`).
- **Vérités** : AJOUT (support de V128)
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : TrueZero; base rhv3 : sZeroHeightsBelow, tZeroHeightEvent, thm_zeroHeightsBelow_finite, TNonTrivialZetaZero, rZeroHeight, sUpperZerosBelow, PIsNonTrivialZetaZero, thm_upperZerosBelow_finite, TUpperNonTrivialZetaZero, TZeroHeightEvent.height, PZeroMemberPrecedes, rZeroRadialPosition et 1 autres.
- **Entraîne** : grammarsAgree_at_iff_onLine_below.

#### `grammarsAgree_at_iff_onLine_below` — `CriticalityCharacterization` l.135 — CONFIRMÉE
- **Énoncé** : Pour tout zéro z : l'index par membres n(z) égale l'index par hauteurs h(z) si et seulement si tout membre qui précède z est sur la droite ; la position radiale de z n'y entre pas (caractéristique globale).
- **Vérités** : V128
- **Repose sur** : théorèmes du projet : heightsBelow_subset_image, mirrorMember_ordinate [Direct.MirrorCount], mirrorMember_radial [Direct.MirrorCount]; définitions du projet : TrueZero, mirrorMember; base rhv3 : nZeroSourceIndex, TNonTrivialZetaZero, PIsNonTrivialZetaZero, nZeroHeightEventIndex, tZeroHeightEvent, PZeroMemberPrecedes, rZeroRadialPosition, sUpperZerosBelow, thm_upperZerosBelow_finite, rZeroHeight, sZeroHeightsBelow, thm_zeroHeightsBelow_finite et 6 autres.
- **Entraîne** : grammarsAgree_at_iff_pastOnLine, grammarsAgree_at_lowSide_of_onLine_below, heightEventIndex_lt_sourceIndex_of_off_below.

#### `grammarsAgree_at_iff_pastOnLine` — `CriticalityCharacterization` l.220 — CONFIRMÉE
- **Énoncé** : Pour tout zéro z : n(z) = h(z) si et seulement si `PPastOnLine z` (le passé de z est sur la droite) ; même caractéristique que ci-dessus, nommée.
- **Vérités** : V128
- **Repose sur** : théorèmes du projet : grammarsAgree_at_iff_onLine_below; définitions du projet : TrueZero, PPastOnLine; base rhv3 : nZeroSourceIndex, TNonTrivialZetaZero, PIsNonTrivialZetaZero, nZeroHeightEventIndex, tZeroHeightEvent.
- **Entraîne** : grammarsAgree_all_iff_pastOnLine_all.

#### `grammarsAgree_at_lowSide_of_onLine_below` — `CriticalityCharacterization` l.225 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous les conditions « z de côté bas » et « le passé de z est sur la droite » : n(z) = h(z) (la caractéristique est aveugle à la position du membre lui-même).
- **Vérités** : V128, V129
- **Repose sur** : théorèmes du projet : grammarsAgree_at_iff_onLine_below; définitions du projet : TrueZero, PPastOnLine; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, nZeroSourceIndex, nZeroHeightEventIndex, tZeroHeightEvent, PZeroMemberPrecedes.
- **Entraîne** : pair_characteristic_splits.

#### `mirror_heightEventIndex_lt_sourceIndex` — `CriticalityCharacterization` l.232 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la condition « z de côté bas » : le miroir z* a h < n (index par hauteurs de son événement strictement inférieur à son index par membres).
- **Vérités** : V129
- **Repose sur** : théorèmes du projet : mirror_sameHeightIndex [MirrorEventCollision], heightEventIndex_le_sourceIndex [Terminal.EventHeightProgression], sourceIndex_lt_mirror [Direct.MirrorCount]; définitions du projet : TrueZero, mirrorMember; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, nZeroHeightEventIndex, tZeroHeightEvent, nZeroSourceIndex.
- **Entraîne** : pair_characteristic_splits.

#### `pair_characteristic_splits` — `CriticalityCharacterization` l.241 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous les conditions « z de côté bas » et « le passé de z est sur la droite » : à la même hauteur, z a n = h et son miroir a h < n ; la caractéristique sépare z de z* par le passé seul.
- **Vérités** : V129
- **Repose sur** : théorèmes du projet : grammarsAgree_at_lowSide_of_onLine_below, mirror_heightEventIndex_lt_sourceIndex, mirrorMember_ordinate [Direct.MirrorCount]; définitions du projet : TrueZero, PPastOnLine, mirrorMember; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, nZeroSourceIndex, nZeroHeightEventIndex, tZeroHeightEvent, rZeroHeight.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `heightEventIndex_lt_sourceIndex_of_off_below` — `CriticalityCharacterization` l.252 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous les conditions « w précède z » et « w est hors ligne » : h(z) < n(z), un seul membre hors ligne dans le passé détruit l'accord des deux grammaires en z.
- **Vérités** : V129
- **Repose sur** : théorèmes du projet : heightEventIndex_le_sourceIndex [Terminal.EventHeightProgression], grammarsAgree_at_iff_onLine_below; définitions du projet : TrueZero; base rhv3 : PZeroMemberPrecedes, TNonTrivialZetaZero, PIsNonTrivialZetaZero, PIsOffCriticalLine, nZeroHeightEventIndex, tZeroHeightEvent, nZeroSourceIndex, rZeroRadialPosition.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `grammarsAgree_all_iff_pastOnLine_all` — `CriticalityCharacterization` l.262 — ÉQUIVALENTE À RH
- **Énoncé** : L'accord n(z) = h(z) pour tout zéro équivaut à « le passé de tout membre est sur la droite » (équivalence à RH par `pastOnLine_all_iff_riemannHypothesis`).
- **Vérités** : V59, V129
- **Repose sur** : théorèmes du projet : grammarsAgree_at_iff_pastOnLine; définitions du projet : TrueZero, PPastOnLine; base rhv3 : nZeroSourceIndex, TNonTrivialZetaZero, PIsNonTrivialZetaZero, nZeroHeightEventIndex, tZeroHeightEvent.
- **Entraîne** : pastOnLine_all_iff_riemannHypothesis.

#### `pastOnLine_all_iff_riemannHypothesis` — `CriticalityCharacterization` l.267 — ÉQUIVALENTE À RH
- **Énoncé** : « Le passé de tout membre est sur la droite » équivaut à RiemannHypothesis (caractérisation, lecture de `grammarsAgree_iff_riemannHypothesis` dans l'autre sens).
- **Vérités** : V59, V129, O10
- **Repose sur** : théorèmes du projet : grammarsAgree_all_iff_pastOnLine_all, grammarsAgree_iff_riemannHypothesis [Terminal.EventHeightProgression]; définitions du projet : TrueZero, PPastOnLine; base rhv3 : nZeroSourceIndex, TNonTrivialZetaZero, PIsNonTrivialZetaZero, nZeroHeightEventIndex, tZeroHeightEvent.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).


##### B — Piste 4 : parité de ξ et lieu fixe (`Terminal/FixedLocusParity.lean`)

**Ce que la piste établit, dans les mots du maître (docstring du module, auteur 2026-09-25)** : la droite critique est le lieu fixe x = 0 de l'involution x ↦ −x (x = β − 1/2) ; la fonction complétée est réelle sur ce lieu ; sur la droite un zéro est UNE équation réelle (A(0, t) = 0), hors ligne DEUX (A = 0 et G = 0) ; le « théorème candidat » est A = 0 ⟹ G ≠ 0 pour 0 < |x| < 1/2, t > 0. Compilé sur la fonction complétée de Mathlib sans hypothèse : lieu fixe (trois descriptions), parité (A paire, B impaire, Λ(reflect s) = conj Λ(s)), le théorème candidat est RH mot pour mot, G(0, t) est la dérivée (G(0, γ) ≠ 0 est « le zéro est simple ») et la « transversalité radiale » n'est pas distincte de la simplicité, l'alternance + − + − est automatique (analyse réelle élémentaire), le scan ne contraint que l'évitement des hauteurs, les zéros triviaux ne sont pas des zéros de Λ. Le module : « Aucun terme `RiemannHypothesis` ne sort de cette route : le théorème candidat en est la reformulation exacte ».

**Statut** : 44 théorèmes ; CONFIRMÉE : 40, CONFIRMÉE SOUS CONDITION : 3, ÉQUIVALENTE À RH : 1. Aucune contradiction ; une équivalence à RH (`fixedLocusSelection_iff_riemannHypothesis`) ; le reste sont des faits de parité et de dérivation sur Λ, dont la plupart n'ont pas de phrase correspondante dans le maître (AJOUT), sauf le lieu fixe (V77, V161, V62).

**Pourquoi parquée (CLAUDE.md §4)** : Module de la liste des six pistes purgées, « aucune contradiction, aucune sur la voie active ». Le maître ne cite pas ce module.

**Un théorème actif en dépend-il ?** Non : aucun théorème actif n'utilise l'un des 44 théorèmes ; StabilityCriteria en utilise plusieurs (`centeredPoint_nontrivialZero_iff`, `off_member_two_equations`, etc. : voir le tableau des dépendances croisées ci-dessous, calculé).

**Théorèmes hors lot sur lesquels la piste s'appuie le plus** : mirrorMember_radial (2), zetaReflect_re (2), zetaReflect_im (2), riemannHypothesis_of_noOff (1), mirrorMember_eq_self_of_onLine (1).

#### `mirror_radialOffset` — `FixedLocusParity` l.67 — CONFIRMÉE
- **Énoncé** : Le décalage radial x = β − 1/2 du miroir est l'opposé de celui du zéro : l'involution agit par x ↦ −x.
- **Vérités** : AJOUT (voisin de V65, V180)
- **Repose sur** : théorèmes du projet : mirrorMember_radial [Direct.MirrorCount]; définitions du projet : TrueZero, radialOffset, mirrorMember; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero.
- **Entraîne** : mirror_radialOffset_sq.

#### `mirror_radialOffset_sq` — `FixedLocusParity` l.73 — CONFIRMÉE
- **Énoncé** : Le zéro et son miroir ont le même x² : la parité en x identifie la paire (z, z*) en un point (x², T).
- **Vérités** : AJOUT (voisin de V65)
- **Repose sur** : théorèmes du projet : mirror_radialOffset; définitions du projet : TrueZero, radialOffset, mirrorMember; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `radialOffset_eq_zero_iff_onLine` — `FixedLocusParity` l.78 — CONFIRMÉE
- **Énoncé** : Le décalage radial d'un zéro est nul si et seulement si sa position radiale vaut 1/2 (le zéro est sur la droite).
- **Vérités** : AJOUT (voisin de V161)
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : TrueZero, radialOffset; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero.
- **Entraîne** : off_member_two_equations, radialOffset_eq_zero_iff_fixed, radialOffset_eq_zero_iff_reflect_fixed.

#### `radialOffset_eq_zero_iff_fixed` — `FixedLocusParity` l.83 — CONFIRMÉE
- **Énoncé** : Le décalage radial est nul si et seulement si le miroir de z est z : le lieu fixe est le point fixe du miroir.
- **Vérités** : V77, V161
- **Repose sur** : théorèmes du projet : radialOffset_eq_zero_iff_onLine, mirrorMember_eq_self_of_onLine [Direct.MirrorCount], mirrorMember_radial [Direct.MirrorCount]; définitions du projet : TrueZero, radialOffset, mirrorMember; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `radialOffset_eq_zero_iff_reflect_fixed` — `FixedLocusParity` l.94 — CONFIRMÉE
- **Énoncé** : Le décalage radial est nul si et seulement si le support de z est fixé par la réflexion ρ ↦ 1 − ρ̄ du port zeta23.
- **Vérités** : V161, V62
- **Repose sur** : théorèmes du projet : radialOffset_eq_zero_iff_onLine, zetaReflect_re [Foundation.ZetaReflect], zetaReflect_im [Foundation.ZetaReflect]; définitions du projet : TrueZero, radialOffset, zetaReflect; base rhv3 : cZeroSupport, TNonTrivialZetaZero, PIsNonTrivialZetaZero, rZeroRadialPosition.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `completedZeta_eq_mul` — `FixedLocusParity` l.113 — CONFIRMÉE
- **Énoncé** : Sur re s > 0, la zêta complétée vaut ζ(s) · Γ_ℝ(s) (condition de domaine : re s > 0).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : aucune; base rhv3 : aucun.
- **Entraîne** : completedZeta_conj, completedZeta_eq_zero_iff, trivial_zero_not_completedZeta_zero.

#### `Gammaℝ_conj` — `FixedLocusParity` l.123 — CONFIRMÉE
- **Énoncé** : Le facteur Γ_ℝ commute avec la conjugaison complexe.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : aucune; base rhv3 : aucun.
- **Entraîne** : completedZeta_conj.

#### `completedZeta_conj` — `FixedLocusParity` l.136 — CONFIRMÉE
- **Énoncé** : Sur re s > 0, Λ(s̄) = conj Λ(s) (condition de domaine : re s > 0).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : completedZeta_eq_mul, Gammaℝ_conj; définitions du projet : aucune; base rhv3 : aucun.
- **Entraîne** : completedZeta_zetaReflect.

#### `completedZeta_zetaReflect` — `FixedLocusParity` l.143 — CONFIRMÉE
- **Énoncé** : Sur re s > 0, l'involution de zeta23 agit sur la zêta complétée par conjugaison : Λ(1 − s̄) = conj Λ(s) (condition de domaine : re s > 0).
- **Vérités** : AJOUT (voisin de V35)
- **Repose sur** : théorèmes du projet : completedZeta_conj; définitions du projet : zetaReflect; base rhv3 : aucun.
- **Entraîne** : completedZeta_centered_neg.

#### `centeredPoint_re` — `FixedLocusParity` l.152 — CONFIRMÉE
- **Énoncé** : La partie réelle du point centré 1/2 + x + it vaut 1/2 + x.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : centeredPoint; base rhv3 : aucun.
- **Entraîne** : centeredPoint_ne_one, centeredPoint_nontrivialZero_iff, centeredPoint_not_trivial, completedZeta_centered_neg, fixedLocusSelection_iff_riemannHypothesis, hasDerivAt_completedZeta_centered, hasDerivAt_xiReal_height, offPairConfig_not_weilPositive [StabilityCriteria], perronFamily_positive_offPair [PrimePositivity], scanConstraint_of_riemannHypothesis, support_eq_centeredPoint, xiRealZeros_iff_riemannHypothesis [StabilityCriteria] et 1 autres.

#### `centeredPoint_im` — `FixedLocusParity` l.153 — CONFIRMÉE
- **Énoncé** : La partie imaginaire du point centré 1/2 + x + it vaut t.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : centeredPoint; base rhv3 : aucun.
- **Entraîne** : zetaReflect_centeredPoint.

#### `zetaReflect_centeredPoint` — `FixedLocusParity` l.155 — CONFIRMÉE
- **Énoncé** : La réflexion de zeta23 envoie le point centré (x, t) sur le point centré (−x, t).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : zetaReflect_re [Foundation.ZetaReflect], centeredPoint_re, zetaReflect_im [Foundation.ZetaReflect], centeredPoint_im; définitions du projet : zetaReflect, centeredPoint; base rhv3 : aucun.
- **Entraîne** : completedZeta_centered_neg.

#### `support_eq_centeredPoint` — `FixedLocusParity` l.162 — CONFIRMÉE
- **Énoncé** : Tout membre est un point centré : son support est le point centré (x(z), T(z)).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : centeredPoint_re; définitions du projet : TrueZero, centeredPoint, radialOffset; base rhv3 : cZeroSupport, TNonTrivialZetaZero, PIsNonTrivialZetaZero, rZeroHeight, rZeroRadialPosition.
- **Entraîne** : off_member_two_equations.

#### `completedZeta_centered_neg` — `FixedLocusParity` l.177 — CONFIRMÉE
- **Énoncé** : Pour −1/2 < x, Λ au point centré (−x, t) est le conjugué de Λ au point centré (x, t) (condition de domaine : −1/2 < x).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : zetaReflect_centeredPoint, completedZeta_zetaReflect, centeredPoint_re; définitions du projet : centeredPoint, zetaReflect; base rhv3 : aucun.
- **Entraîne** : xiImag_odd, xiReal_even.

#### `xiReal_even` — `FixedLocusParity` l.185 — CONFIRMÉE
- **Énoncé** : Pour −1/2 < x, la partie réelle A(x, t) de Λ est paire en x (condition de domaine : −1/2 < x).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : completedZeta_centered_neg; définitions du projet : xiReal, centeredPoint; base rhv3 : aucun.
- **Entraîne** : deriv_completedZeta_re_onLine, pair_same_conditions.

#### `xiImag_odd` — `FixedLocusParity` l.190 — CONFIRMÉE
- **Énoncé** : Pour −1/2 < x, la partie imaginaire B(x, t) de Λ est impaire en x (condition de domaine : −1/2 < x).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : completedZeta_centered_neg; définitions du projet : xiImag, centeredPoint; base rhv3 : aucun.
- **Entraîne** : pair_same_conditions, xiImag_zero_onLine.

#### `xiImag_zero_onLine` — `FixedLocusParity` l.195 — CONFIRMÉE
- **Énoncé** : Sur le lieu fixe, B(0, t) = 0 : Λ est réelle sur la droite.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : xiImag_odd; définitions du projet : xiImag; base rhv3 : aucun.
- **Entraîne** : onLine_zero_iff_xiReal.

#### `completedZeta_eq_zero_iff` — `FixedLocusParity` l.201 — CONFIRMÉE
- **Énoncé** : Sur re s > 0, les zéros de Λ et de ζ coïncident (condition de domaine : re s > 0).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : completedZeta_eq_mul; définitions du projet : aucune; base rhv3 : aucun.
- **Entraîne** : centeredPoint_nontrivialZero_iff.

#### `centeredPoint_nontrivialZero_iff` — `FixedLocusParity` l.206 — CONFIRMÉE
- **Énoncé** : Pour |x| < 1/2, le point centré (x, t) est un zéro non trivial si et seulement si A(x, t) = 0 et B(x, t) = 0 (condition de domaine : |x| < 1/2).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : centeredPoint_re, completedZeta_eq_zero_iff; définitions du projet : centeredPoint, xiReal, xiImag; base rhv3 : PIsNonTrivialZetaZero.
- **Entraîne** : fixedLocusSelection_iff_riemannHypothesis, off_member_two_equations, onLine_zero_iff_xiReal, scanConstraint_of_riemannHypothesis, xiRealZeros_iff_riemannHypothesis [StabilityCriteria].

#### `onLine_zero_iff_xiReal` — `FixedLocusParity` l.223 — CONFIRMÉE
- **Énoncé** : Sur le lieu fixe, un point centré (0, t) est un zéro non trivial si et seulement si A(0, t) = 0 : une seule équation réelle.
- **Vérités** : AJOUT (voisin de V161)
- **Repose sur** : théorèmes du projet : centeredPoint_nontrivialZero_iff, xiImag_zero_onLine; définitions du projet : centeredPoint, xiReal, xiImag; base rhv3 : PIsNonTrivialZetaZero.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `pair_same_conditions` — `FixedLocusParity` l.229 — CONFIRMÉE
- **Énoncé** : Pour −1/2 < x, la paire (x, t), (−x, t) voit le même A et la même annulation de B (condition de domaine : −1/2 < x).
- **Vérités** : AJOUT (voisin de V65)
- **Repose sur** : théorèmes du projet : xiReal_even, xiImag_odd; définitions du projet : xiReal, xiImag; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `radialOffset_abs_lt` — `FixedLocusParity` l.242 — CONFIRMÉE
- **Énoncé** : Pour tout zéro, |x(z)| < 1/2.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : TrueZero, radialOffset; base rhv3 : rZeroRadialPosition, TNonTrivialZetaZero, PIsNonTrivialZetaZero, thm_zeroRadialPosition_positive, thm_zeroRadialPosition_lt_one.
- **Entraîne** : fixedLocusSelection_iff_riemannHypothesis, off_member_two_equations, scanConstraint_gives_only_height_avoidance, xiRealZeros_iff_riemannHypothesis [StabilityCriteria].

#### `off_member_two_equations` — `FixedLocusParity` l.248 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la condition « le membre est hors ligne » : |x(z)| > 0 et A(x(z), T) = 0 et B(x(z), T) = 0, deux équations réelles au lieu d'une.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : radialOffset_eq_zero_iff_onLine, support_eq_centeredPoint, centeredPoint_nontrivialZero_iff, radialOffset_abs_lt; définitions du projet : TrueZero, radialOffset, xiReal, xiImag, centeredPoint; base rhv3 : PIsOffCriticalLine, TNonTrivialZetaZero, PIsNonTrivialZetaZero, rZeroHeight, rZeroRadialPosition, cZeroSupport.
- **Entraîne** : fixedLocusSelection_iff_riemannHypothesis, scanConstraint_gives_only_height_avoidance, xiRealZeros_iff_riemannHypothesis [StabilityCriteria].

#### `centeredPoint_not_trivial` — `FixedLocusParity` l.261 — CONFIRMÉE
- **Énoncé** : Pour −1/2 < x, le point centré n'est pas un zéro trivial −2(n+1) (condition de domaine : −1/2 < x).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : centeredPoint_re; définitions du projet : centeredPoint; base rhv3 : aucun.
- **Entraîne** : fixedLocusSelection_iff_riemannHypothesis, scanConstraint_of_riemannHypothesis, xiRealZeros_iff_riemannHypothesis [StabilityCriteria].

#### `centeredPoint_ne_one` — `FixedLocusParity` l.271 — CONFIRMÉE
- **Énoncé** : Pour x < 1/2, le point centré est différent de 1 (condition de domaine : x < 1/2).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : centeredPoint_re; définitions du projet : centeredPoint; base rhv3 : aucun.
- **Entraîne** : fixedLocusSelection_iff_riemannHypothesis, hasDerivAt_completedZeta_centered, hasDerivAt_xiReal_height, scanConstraint_of_riemannHypothesis, xiRealZeros_iff_riemannHypothesis [StabilityCriteria].

#### `fixedLocusSelection_iff_riemannHypothesis` — `FixedLocusParity` l.278 — ÉQUIVALENTE À RH
- **Énoncé** : Le « théorème candidat » `PFixedLocusSelection` (hors du lieu fixe, dans la bande, A = 0 ⟹ G ≠ 0) équivaut à RiemannHypothesis, mot pour mot.
- **Vérités** : AJOUT (voisin de O10, V126)
- **Repose sur** : théorèmes du projet : riemannHypothesis_of_noOff [Terminal.Universalization], off_member_two_equations, radialOffset_abs_lt, centeredPoint_nontrivialZero_iff, centeredPoint_not_trivial, centeredPoint_ne_one, centeredPoint_re; définitions du projet : PFixedLocusSelection, TrueZero, radialOffset, xiReal, xiImag, centeredPoint; base rhv3 : PIsOffCriticalLine, TNonTrivialZetaZero, PIsNonTrivialZetaZero, rZeroHeight, thm_upperZeroHeight_positive.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `centeredPoint_eq_add` — `FixedLocusParity` l.297 — CONFIRMÉE
- **Énoncé** : Le point centré y à hauteur t est égal à 1/2 + it + y.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : centeredPoint; base rhv3 : aucun.
- **Entraîne** : hasDerivAt_completedZeta_centered, hasDerivAt_xiImag, hasDerivAt_xiReal.

#### `hasDerivAt_completedZeta_centered` — `FixedLocusParity` l.303 — CONFIRMÉE
- **Énoncé** : Pour |x| < 1/2, Λ est dérivable le long de x ↦ 1/2 + x + it, de dérivée Λ' au point centré (condition de domaine : |x| < 1/2).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : centeredPoint_re, centeredPoint_ne_one, centeredPoint_eq_add; définitions du projet : centeredPoint; base rhv3 : aucun.
- **Entraîne** : hasDerivAt_xiImag, hasDerivAt_xiReal.

#### `hasDerivAt_xiReal` — `FixedLocusParity` l.321 — CONFIRMÉE
- **Énoncé** : Pour |x| < 1/2, ∂_x A(x, t) = Re Λ'(1/2 + x + it) (condition de domaine : |x| < 1/2).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : hasDerivAt_completedZeta_centered, centeredPoint_eq_add; définitions du projet : xiReal, centeredPoint; base rhv3 : aucun.
- **Entraîne** : deriv_completedZeta_re_onLine.

#### `hasDerivAt_xiImag` — `FixedLocusParity` l.328 — CONFIRMÉE
- **Énoncé** : Pour |x| < 1/2, ∂_x B(x, t) = Im Λ'(1/2 + x + it) (condition de domaine : |x| < 1/2).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : hasDerivAt_completedZeta_centered, centeredPoint_eq_add; définitions du projet : xiImag, centeredPoint; base rhv3 : aucun.
- **Entraîne** : oddFactor_eq_deriv_xiImag.

#### `deriv_completedZeta_re_onLine` — `FixedLocusParity` l.339 — CONFIRMÉE
- **Énoncé** : Sur la droite, Λ' est imaginaire pur : sa partie réelle est nulle (dérivée en 0 d'une fonction paire).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : hasDerivAt_xiReal, xiReal_even; définitions du projet : centeredPoint, xiReal; base rhv3 : aucun.
- **Entraîne** : deriv_completedZeta_onLine.

#### `deriv_completedZeta_onLine` — `FixedLocusParity` l.358 — CONFIRMÉE
- **Énoncé** : Sur la droite, Λ' au point centré (0, t) vaut i fois le facteur impair G(0, t).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : deriv_completedZeta_re_onLine; définitions du projet : centeredPoint, xiOddFactorOnLine; base rhv3 : aucun.
- **Entraîne** : deriv_eq_zero_iff_oddFactor, hasDerivAt_xiReal_height.

#### `deriv_eq_zero_iff_oddFactor` — `FixedLocusParity` l.364 — CONFIRMÉE
- **Énoncé** : Sur la droite, Λ' est nulle au point centré (0, t) si et seulement si G(0, t) = 0 (G(0, γ) ≠ 0 traduit « le zéro est simple »).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : deriv_completedZeta_onLine; définitions du projet : centeredPoint, xiOddFactorOnLine; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `oddFactor_eq_deriv_xiImag` — `FixedLocusParity` l.370 — CONFIRMÉE
- **Énoncé** : G(0, t) est la dérivée radiale ∂_x B(0, t) de la partie impaire.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : hasDerivAt_xiImag; définitions du projet : xiImag, xiOddFactorOnLine; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `hasDerivAt_xiReal_height` — `FixedLocusParity` l.375 — CONFIRMÉE
- **Énoncé** : Sur la droite, ∂_t A(0, t) = −G(0, t) (Cauchy–Riemann).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : centeredPoint_re, centeredPoint_ne_one, deriv_completedZeta_onLine; définitions du projet : xiReal, xiOddFactorOnLine, centeredPoint; base rhv3 : aucun.
- **Entraîne** : oddFactor_sign_alternates.

#### `radial_height_derivative_same_norm` — `FixedLocusParity` l.402 — CONFIRMÉE
- **Énoncé** : Pour tout point s, ‖Λ'(s)·i‖ = ‖Λ'(s)‖ : la dérivée radiale et la dérivée en hauteur ont même norme (la « transversalité radiale » n'est pas distincte de la simplicité).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : aucune; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `deriv_nonneg_of_pos_right` — `FixedLocusParity` l.409 — CONFIRMÉE
- **Énoncé** : Hypothèses = antécédent de l'implication énoncée (pas une restriction de domaine) : d'analyse réelle « a < b, f(a) = 0, f > 0 sur (a, b), f dérivable en a » : la dérivée en a est ≥ 0.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : aucune; base rhv3 : aucun.
- **Entraîne** : deriv_sign_alternates_at_consecutive_zeros.

#### `deriv_nonpos_of_pos_left` — `FixedLocusParity` l.426 — CONFIRMÉE
- **Énoncé** : Hypothèses = antécédent de l'implication énoncée (pas une restriction de domaine) : d'analyse réelle « a < b, f(b) = 0, f > 0 sur (a, b), f dérivable en b » : la dérivée en b est ≤ 0.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : aucune; base rhv3 : aucun.
- **Entraîne** : deriv_sign_alternates_at_consecutive_zeros.

#### `constant_sign_of_no_zero` — `FixedLocusParity` l.444 — CONFIRMÉE
- **Énoncé** : Hypothèses = antécédent de l'implication énoncée (pas une restriction de domaine) : « f continue sur [a, b] et sans zéro sur (a, b) » : f garde un signe strict constant sur (a, b).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : aucune; base rhv3 : aucun.
- **Entraîne** : deriv_sign_alternates_at_consecutive_zeros.

#### `deriv_sign_alternates_at_consecutive_zeros` — `FixedLocusParity` l.461 — CONFIRMÉE
- **Énoncé** : Hypothèses = antécédent de l'implication énoncée (pas une restriction de domaine) : d'analyse réelle (deux zéros consécutifs simples a < b d'une fonction continue, dérivables, dérivées non nulles) : les dérivées en a et en b sont de signes opposés.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : constant_sign_of_no_zero, deriv_nonneg_of_pos_right, deriv_nonpos_of_pos_left; définitions du projet : aucune; base rhv3 : aucun.
- **Entraîne** : oddFactor_sign_alternates.

#### `oddFactor_sign_alternates` — `FixedLocusParity` l.479 — CONFIRMÉE
- **Énoncé** : Hypothèses = antécédent de l'implication énoncée (pas une restriction de domaine) : « t₁ < t₂ zéros consécutifs de A(0, ·) sur la droite, G(0, t₁) ≠ 0, G(0, t₂) ≠ 0 » : G(0, t₁)·G(0, t₂) < 0 (alternance + − + − de G).
- **Vérités** : AJOUT (voisin de V18)
- **Repose sur** : théorèmes du projet : hasDerivAt_xiReal_height, deriv_sign_alternates_at_consecutive_zeros; définitions du projet : xiReal, xiOddFactorOnLine; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `scanConstraint_of_riemannHypothesis` — `FixedLocusParity` l.499 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous RiemannHypothesis (prémisse) : la contrainte du scan `PScanConstraint` (aucun zéro hors ligne à la hauteur d'un zéro de la droite) tient. RiemannHypothesis est ici hypothèse, non conclusion.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : centeredPoint_nontrivialZero_iff, centeredPoint_not_trivial, centeredPoint_ne_one, centeredPoint_re; définitions du projet : PScanConstraint, xiReal, xiImag, centeredPoint; base rhv3 : PIsNonTrivialZetaZero.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `scanConstraint_gives_only_height_avoidance` — `FixedLocusParity` l.508 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la prémisse `PScanConstraint` et pour un zéro hors ligne : A(0, T(z)) ≠ 0, c'est-à-dire aucun zéro de la droite à la hauteur du membre hors ligne ; rien de plus.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : off_member_two_equations, radialOffset_abs_lt; définitions du projet : PScanConstraint, TrueZero, xiReal, radialOffset, xiImag; base rhv3 : PIsOffCriticalLine, TNonTrivialZetaZero, PIsNonTrivialZetaZero, rZeroHeight.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `trivial_zero_not_completedZeta_zero` — `FixedLocusParity` l.518 — CONFIRMÉE
- **Énoncé** : Pour tout n, Λ(−2(n+1)) ≠ 0 : les zéros triviaux ne sont pas des zéros de la zêta complétée.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : completedZeta_eq_mul; définitions du projet : aucune; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).


##### B — Piste 5 : critères de stabilité globale (Weil, Laguerre–Pólya, de Branges) (`Terminal/StabilityCriteria.lean`)

**Ce que la piste établit, dans les mots du maître (docstring du module, auteur 2026-09-25)** : trois pistes soumises (positivité de Weil, de Branges / Hermite–Biehler, Laguerre–Pólya) ; verdict remis avant le module : trois équivalents exacts de RH, la flèche « premiers ⟹ positivité » étant l'inconnue. Compilé : Laguerre–Pólya pour Ξ est RH mot pour mot ; le terme de paire de Weil vaut ‖φ(ρ)‖² sur la droite, et hors ligne un test rend négatifs les deux termes de la paire ; la positivité de paire d'une configuration est exactement « tous ses points sont sur la droite », donc RH pour `zetaZeroConfig` (sens facile de Weil) ; une configuration hors ligne satisfait tous les axiomes de `ZeroConfig` et viole la positivité, donc aucune positivité n'est un théorème des axiomes de `ZeroConfig` ; la forme côté zéros d'une configuration sur la droite est positive sur toute fenêtre finie. Le module : « Aucun sorry, aucun admit, aucun axiome nouveau, aucune hypothèse ».

**Statut** : 14 théorèmes ; CONFIRMÉE : 3, ÉQUIVALENTE À RH : 3, CONFIRMÉE SOUS CONDITION : 6, RÉFUTATION COMPILÉE : 2. Aucune contradiction ; trois équivalences à RH (`xiRealZeros_iff_riemannHypothesis`, `allNontrivial_onLine_iff_riemannHypothesis`, `weilPairPositivity_zeta_iff_riemannHypothesis`) ; deux réfutations compilées (`offPairConfig_not_weilPositive`, `weilPairPositivity_not_from_config`) ; deux théorèmes sous prémisse RiemannHypothesis (`zeroSideWindow_zeta_nonneg_of_riemannHypothesis`, et `scanConstraint_of_riemannHypothesis` dans FixedLocusParity).

**Pourquoi parquée (CLAUDE.md §4)** : Module de la liste des six pistes purgées. Le maître ne le cite pas.

**Un théorème actif en dépend-il ?** Non : aucun théorème actif n'utilise l'un des 14 ; `offPairConfig_not_weilPositive` est utilisé par `perronFamily_positivity_not_riemannHypothesis` de PrimePositivity (dépendance entre pistes parquées, voir tableau croisé).

**Théorèmes hors lot sur lesquels la piste s'appuie le plus** : zetaReflect_re (3), zetaReflect_im (3), riemannHypothesis_of_noOff (2), zetaZeroConfig_carrier (1), ZeroConfig.finite_window (1).

#### `completedZeta_centered_eq_zero_iff` — `StabilityCriteria` l.48 — CONFIRMÉE
- **Énoncé** : Pour tous x, t, Λ au point centré (x, t) est nulle si et seulement si A(x, t) = 0 et B(x, t) = 0.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : centeredPoint, xiReal, xiImag; base rhv3 : aucun.
- **Entraîne** : xiRealZeros_iff_riemannHypothesis.

#### `xiRealZeros_iff_riemannHypothesis` — `StabilityCriteria` l.54 — ÉQUIVALENTE À RH
- **Énoncé** : La prémisse `PXiRealZeros` (Laguerre–Pólya pour Ξ : les zéros de Ξ dans la bande sont réels) équivaut à RiemannHypothesis, mot pour mot.
- **Vérités** : AJOUT (voisin de O10, V126)
- **Repose sur** : théorèmes du projet : riemannHypothesis_of_noOff [Terminal.Universalization], off_member_two_equations [FixedLocusParity], completedZeta_centered_eq_zero_iff, radialOffset_abs_lt [FixedLocusParity], centeredPoint_nontrivialZero_iff [FixedLocusParity], centeredPoint_not_trivial [FixedLocusParity], centeredPoint_ne_one [FixedLocusParity], centeredPoint_re [FixedLocusParity]; définitions du projet : PXiRealZeros, TrueZero, radialOffset, xiReal, xiImag, centeredPoint; base rhv3 : PIsOffCriticalLine, TNonTrivialZetaZero, PIsNonTrivialZetaZero, rZeroHeight.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `zetaReflect_eq_self_iff` — `StabilityCriteria` l.80 — CONFIRMÉE
- **Énoncé** : Un point ρ est fixé par la réflexion ρ ↦ 1 − ρ̄ si et seulement si Re ρ = 1/2.
- **Vérités** : V161, V62
- **Repose sur** : théorèmes du projet : zetaReflect_re [Foundation.ZetaReflect], zetaReflect_im [Foundation.ZetaReflect]; définitions du projet : zetaReflect; base rhv3 : aucun.
- **Entraîne** : weilPairTerm_onLine.

#### `weilPairTerm_onLine` — `StabilityCriteria` l.89 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la condition « Re ρ = 1/2 » : le terme de paire de Weil d'un test φ en ρ vaut ‖φ(ρ)‖².
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : zetaReflect_eq_self_iff; définitions du projet : weilPairTerm, zetaReflect; base rhv3 : aucun.
- **Entraîne** : weilPairTerm_nonneg_onLine.

#### `weilPairTerm_nonneg_onLine` — `StabilityCriteria` l.96 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la condition « Re ρ = 1/2 » : le terme de paire de Weil de tout test φ en ρ est positif ou nul.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : weilPairTerm_onLine; définitions du projet : weilPairTerm; base rhv3 : aucun.
- **Entraîne** : weilPairPositivity_iff_onLine, zeroSideWindow_nonneg_of_onLine.

#### `weilPairTerm_test_eq` — `StabilityCriteria` l.104 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la condition « Im σ = Im ρ » : le terme de paire du test centré weilTestOff ρ en σ vaut −(Re σ − 1/2)².
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : zetaReflect_re [Foundation.ZetaReflect], zetaReflect_im [Foundation.ZetaReflect]; définitions du projet : weilPairTerm, weilTestOff, zetaReflect; base rhv3 : aucun.
- **Entraîne** : weilPairTerm_off_neg.

#### `weilPairTerm_off_neg` — `StabilityCriteria` l.112 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la condition « Re ρ ≠ 1/2 » : les deux termes de la paire {ρ, 1 − ρ̄} pour le test weilTestOff ρ sont strictement négatifs.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : weilPairTerm_test_eq, zetaReflect_im [Foundation.ZetaReflect], zetaReflect_re [Foundation.ZetaReflect]; définitions du projet : weilPairTerm, weilTestOff, zetaReflect; base rhv3 : aucun.
- **Entraîne** : weilPairPositivity_iff_onLine.

#### `weilPairPositivity_iff_onLine` — `StabilityCriteria` l.132 — CONFIRMÉE
- **Énoncé** : Pour toute configuration de zéros C : la positivité de paire de C (`PWeilPairPositivity C`) équivaut à « tous les points de C ont Re = 1/2 ».
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : weilPairTerm_off_neg, weilPairTerm_nonneg_onLine; définitions du projet : ZeroConfig, PWeilPairPositivity, ZeroConfig.carrier, weilPairTerm, weilTestOff, zetaReflect; base rhv3 : aucun.
- **Entraîne** : offPairConfig_not_weilPositive, weilPairPositivity_zeta_iff_riemannHypothesis.

#### `allNontrivial_onLine_iff_riemannHypothesis` — `StabilityCriteria` l.143 — ÉQUIVALENTE À RH
- **Énoncé** : « Tous les zéros non triviaux de la configuration zetaZeroConfig ont Re = 1/2 » équivaut à RiemannHypothesis (Mathlib).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : zetaZeroConfig_carrier [Foundation.ZetaReflect], riemannHypothesis_of_noOff [Terminal.Universalization]; définitions du projet : ZeroConfig.carrier, zetaZeroConfig, TrueZero; base rhv3 : PIsNonTrivialZetaZero, PIsOffCriticalLine, TNonTrivialZetaZero, cZeroSupport.
- **Entraîne** : weilPairPositivity_zeta_iff_riemannHypothesis, zeroSideWindow_zeta_nonneg_of_riemannHypothesis.

#### `weilPairPositivity_zeta_iff_riemannHypothesis` — `StabilityCriteria` l.165 — ÉQUIVALENTE À RH
- **Énoncé** : La positivité de paire de Weil pour la configuration de ζ équivaut à RiemannHypothesis (sens facile du critère de Weil).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : weilPairPositivity_iff_onLine, allNontrivial_onLine_iff_riemannHypothesis; définitions du projet : PWeilPairPositivity, zetaZeroConfig, ZeroConfig.carrier; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `offPairConfig_not_weilPositive` — `StabilityCriteria` l.192 — RÉFUTATION COMPILÉE
- **Énoncé** : Sous les conditions « |x| ≤ 1/2 » et « x ≠ 0 » : la configuration hors ligne offPairConfig x t ne satisfait pas la positivité de paire. Réfute que toute configuration de zeta23 soit Weil-positive.
- **Vérités** : AJOUT (support de la piste de stabilité ; V126)
- **Repose sur** : théorèmes du projet : weilPairPositivity_iff_onLine, centeredPoint_re [FixedLocusParity]; définitions du projet : PWeilPairPositivity, offPairConfig, ZeroConfig.carrier, centeredPoint; base rhv3 : aucun.
- **Entraîne** : perronFamily_positivity_not_riemannHypothesis [PrimePositivity], weilPairPositivity_not_from_config.

#### `weilPairPositivity_not_from_config` — `StabilityCriteria` l.201 — RÉFUTATION COMPILÉE
- **Énoncé** : La positivité de paire n'est pas vraie pour toute `ZeroConfig` : les axiomes de la structure de zeta23 admettent des modèles hors ligne. Réfute que la positivité soit un théorème des axiomes de `ZeroConfig`.
- **Vérités** : AJOUT (support de V126)
- **Repose sur** : théorèmes du projet : offPairConfig_not_weilPositive; définitions du projet : ZeroConfig, PWeilPairPositivity, offPairConfig; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `zeroSideWindow_nonneg_of_onLine` — `StabilityCriteria` l.214 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous la condition « tous les points de la configuration C sont sur la droite » : la forme côté zéros sur toute fenêtre (T₁, T₂] est positive ou nulle.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : ZeroConfig.finite_window [Foundation.ZetaReflect], weilPairTerm_nonneg_onLine; définitions du projet : ZeroConfig, ZeroConfig.carrier, zeroSideWindow, ZeroConfig.mult, weilPairTerm; base rhv3 : aucun.
- **Entraîne** : zeroSideWindow_zeta_nonneg_of_riemannHypothesis.

#### `zeroSideWindow_zeta_nonneg_of_riemannHypothesis` — `StabilityCriteria` l.223 — CONFIRMÉE SOUS CONDITION
- **Énoncé** : Sous RiemannHypothesis (prémisse) : la forme côté zéros de ζ est positive ou nulle sur toute fenêtre. RiemannHypothesis est ici hypothèse, non conclusion.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : zeroSideWindow_nonneg_of_onLine, allNontrivial_onLine_iff_riemannHypothesis; définitions du projet : zeroSideWindow, zetaZeroConfig, ZeroConfig.carrier; base rhv3 : aucun.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).


##### B — Piste 6 : fonctionnel positif côté premier (`Terminal/PrimePositivity.lean`)

**Ce que la piste établit, dans les mots du maître (docstring du module, auteur 2026-09-25)** : les découvertes du projet ne servent plus à transporter un zéro vers un premier mais à fabriquer une positivité ou une stabilité globale ; première étape obligée : quelle positivité la formule explicite compilée rend-elle visible, et voit-elle β ? Compilé : le mécanisme `x^ρ · conj(x^{1 − ρ̄}) = x` pour tout ρ (le produit des amplitudes d'une paire est toujours x) ; le terme de paire de la famille compilée (`Perron.f x`) est positif pour tout point de la bande, donc sur la configuration de ζ sans RH ET sur la paire hors ligne. Verdict du module : la positivité que la formule explicite compilée rend visible terme par terme est un théorème et elle est aveugle à β ; un fonctionnel qui voit β exige la formule explicite du noyau convolé `f ∗ f̃`, « ni dans la base ni dans Mathlib ». Le module : « Aucun sorry, aucun admit, aucun axiome nouveau, aucune hypothèse ».

**Statut** : 11 théorèmes ; CONFIRMÉE : 11. Aucune contradiction ; aucune équivalence à RH ; un contre-modèle (`perronFamily_positivity_not_riemannHypothesis`) : le nom promet une relation avec RiemannHypothesis alors que le type ne mentionne pas RiemannHypothesis (voir Incidents).

**Pourquoi parquée (CLAUDE.md §4)** : Module de la liste des six pistes purgées. Le maître ne le cite pas ; sa conclusion (aveuglement à β de la positivité visible terme par terme) rejoint V160 et V167 par le résultat, sans théorème commun.

**Un théorème actif en dépend-il ?** Non : aucun théorème hors du module n'utilise l'un des 11.

**Théorèmes hors lot sur lesquels la piste s'appuie le plus** : .

#### `conj_zetaReflect` — `PrimePositivity` l.45 — CONFIRMÉE
- **Énoncé** : Pour tout ρ, conj(zetaReflect ρ) = 1 − ρ.
- **Vérités** : AJOUT (voisin de V63)
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : zetaReflect; base rhv3 : aucun.
- **Entraîne** : weilPairTerm_perron_eq.

#### `zetaReflect_eq_conj` — `PrimePositivity` l.48 — CONFIRMÉE
- **Énoncé** : Pour tout ρ, zetaReflect ρ = conj(1 − ρ).
- **Vérités** : AJOUT (voisin de V63)
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : zetaReflect; base rhv3 : aucun.
- **Entraîne** : cpow_zetaReflect.

#### `cpow_zetaReflect` — `PrimePositivity` l.51 — CONFIRMÉE
- **Énoncé** : Pour x > 0 réel, x^(1 − ρ̄) = conj(x^(1 − ρ)) (condition de domaine : x > 0).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : zetaReflect_eq_conj; définitions du projet : zetaReflect; base rhv3 : aucun.
- **Entraîne** : cpow_reflect_product.

#### `cpow_reflect_product` — `PrimePositivity` l.59 — CONFIRMÉE
- **Énoncé** : Pour x > 0, x^ρ · conj(x^(1 − ρ̄)) = x quel que soit ρ : le produit des amplitudes x^β · x^(1−β) d'une paire est x (condition de domaine : x > 0).
- **Vérités** : AJOUT (voisin de V102, V167)
- **Repose sur** : théorèmes du projet : cpow_zetaReflect; définitions du projet : zetaReflect; base rhv3 : aucun.
- **Entraîne** : weilPairTerm_perron_eq.

#### `weilPairTerm_perron_eq` — `PrimePositivity` l.72 — CONFIRMÉE
- **Énoncé** : Pour x > 0, le terme de paire de Weil du test Perron.f x en ρ vaut Re(x / D(ρ)), D = ρ(1−ρ)(ρ+1)(2−ρ) (condition de domaine : x > 0).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : conj_zetaReflect, cpow_reflect_product; définitions du projet : weilPairTerm, perronPairDenominator, zetaReflect; base rhv3 : aucun; autres bases : Perron.f.
- **Entraîne** : weilPairTerm_perron_pos.

#### `perronPairDenominator_re_pos` — `PrimePositivity` l.82 — CONFIRMÉE
- **Énoncé** : Pour 0 < Re ρ < 1, Re D(ρ) > 0 (condition de domaine : bande).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : aucun; définitions du projet : perronPairDenominator; base rhv3 : aucun.
- **Entraîne** : perronPairDenominator_ne_zero, weilPairTerm_perron_pos.

#### `perronPairDenominator_ne_zero` — `PrimePositivity` l.94 — CONFIRMÉE
- **Énoncé** : Pour 0 < Re ρ < 1, D(ρ) ≠ 0 (condition de domaine : bande).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : perronPairDenominator_re_pos; définitions du projet : perronPairDenominator; base rhv3 : aucun.
- **Entraîne** : weilPairTerm_perron_pos.

#### `weilPairTerm_perron_pos` — `PrimePositivity` l.101 — CONFIRMÉE
- **Énoncé** : Pour x > 0 et 0 < Re ρ < 1, le terme de paire de la famille Perron.f x est strictement positif (conditions de domaine : x > 0, bande).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : weilPairTerm_perron_eq, perronPairDenominator_re_pos, perronPairDenominator_ne_zero; définitions du projet : weilPairTerm, perronPairDenominator; base rhv3 : aucun; autres bases : Perron.f.
- **Entraîne** : perronFamily_positive_offPair, perronFamily_positive_zeta.

#### `perronFamily_positive_zeta` — `PrimePositivity` l.113 — CONFIRMÉE
- **Énoncé** : Pour x > 0 et tout ρ de la configuration de ζ (zetaZeroConfig), le terme de paire de Perron.f x est strictement positif, sans RH (conditions de domaine : x > 0, ρ dans la configuration).
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : weilPairTerm_perron_pos; définitions du projet : ZeroConfig.carrier, zetaZeroConfig, weilPairTerm; base rhv3 : PIsNonTrivialZetaZero; autres bases : Perron.f.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).

#### `perronFamily_positive_offPair` — `PrimePositivity` l.121 — CONFIRMÉE
- **Énoncé** : Pour |x| < 1/2, q > 0 et tout ρ de la paire hors ligne offPairConfig x t, le terme de paire de Perron.f q est strictement positif : la famille ne distingue pas ON de OFF (conditions de domaine : |x| < 1/2, q > 0).
- **Vérités** : AJOUT (voisin de V160)
- **Repose sur** : théorèmes du projet : weilPairTerm_perron_pos, centeredPoint_re [FixedLocusParity]; définitions du projet : ZeroConfig.carrier, offPairConfig, weilPairTerm, centeredPoint; base rhv3 : aucun; autres bases : Perron.f.
- **Entraîne** : perronFamily_positivity_not_riemannHypothesis.

#### `perronFamily_positivity_not_riemannHypothesis` — `PrimePositivity` l.130 — CONFIRMÉE
- **Énoncé** : Il existe une configuration de zéros dont tous les termes de paire de la famille Perron sont positifs pour tout q > 0 et qui ne satisfait pas `PWeilPairPositivity` (contre-modèle, hors ligne). Le type ne contient pas RiemannHypothesis.
- **Vérités** : AJOUT
- **Repose sur** : théorèmes du projet : perronFamily_positive_offPair, offPairConfig_not_weilPositive [StabilityCriteria]; définitions du projet : ZeroConfig, ZeroConfig.carrier, weilPairTerm, PWeilPairPositivity, offPairConfig; base rhv3 : aucun; autres bases : Perron.f.
- **Entraîne** : aucun (aucun théorème du projet ne l'utilise dans `deps_project`).


##### Dépendances croisées entre pistes parquées (calculées)

- CriticalityCharacterization → MirrorEventCollision : explicitFormula_counts_members utilise mirror_sameHeightEvent, mirror_heightEventIndex_lt_sourceIndex utilise mirror_sameHeightIndex.
- PrimePositivity → FixedLocusParity : perronFamily_positive_offPair utilise centeredPoint_re.
- PrimePositivity → StabilityCriteria : perronFamily_positivity_not_riemannHypothesis utilise offPairConfig_not_weilPositive.
- ReflectedTransition → MirrorEventCollision : mirror_heightEventTransition_eq utilise mirror_sameHeightIndex, reflected_transition_content utilise mirror_occurrence_strict.
- StabilityCriteria → FixedLocusParity : offPairConfig_not_weilPositive utilise centeredPoint_re, xiRealZeros_iff_riemannHypothesis utilise centeredPoint_ne_one, xiRealZeros_iff_riemannHypothesis utilise centeredPoint_nontrivialZero_iff, xiRealZeros_iff_riemannHypothesis utilise centeredPoint_not_trivial, xiRealZeros_iff_riemannHypothesis utilise centeredPoint_re, xiRealZeros_iff_riemannHypothesis utilise off_member_two_equations et 1 autres.

---

## Annexe B — contrôle de complétude

Contrôle exécuté sur le fichier assemblé (script Python : extraction des en-têtes `#### \`nom\` — \`module\` l.N` de l'annexe A, comparaison aux noms de `experiments/audit_semantique/data/RHV6Fresh.jsonl`, préfixe `RHV6Fresh.` retiré) :

- Entrées distinctes dans l'annexe A : **742** ; entrées totales (doublons compris) : 742.
- Lignes du jsonl RHV6Fresh : **742** (noms distincts : 742).
- Noms du jsonl absents de l'annexe : **0** ; noms de l'annexe absents du jsonl : **0**.
- Résultat : **CONFORME (742 = 742, aucun manquant, aucun doublon)**.

