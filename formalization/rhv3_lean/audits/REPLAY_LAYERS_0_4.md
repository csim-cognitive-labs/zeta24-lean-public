# RHV3Lean — replay cumulatif des couches 0–4 sous le standard L–P

    DATE         2026-09-09
    ORDONNE PAR  maître Lean § Q.4
    HEAD         voir audits/tours/T00-BOOTSTRAP.md
    OBJET        reclasser TOUTE surface publique existante sous le nouveau
                 standard, dimension par dimension (§ O.7, O.8), sans qu'aucune
                 mention antérieure « BODY_PRODUCED », « 100 % » ou « couche
                 validée » ne compte comme preuve.

Le replay ne cherche pas à tout déclarer faux (§ Q.5).  Il sépare :

    A. corps Lean corrects et fidèles
    B. corps Lean corrects mais CONDITIONNELS
    C. contrats SANS producteur
    D. objets définis mais PAS ENCORE CONNECTES
    E. dérives réelles de type / signature / dépendance

## Résultat global

    OBJETS_REJOUES              13   (O1..O10, S4, LOI LOCALE, MIROIR)
    DIMENSIONS_CONTROLEES      145
    CLASSE_A                   130
    CLASSE_B                     5
    CLASSE_C                     8
    CLASSE_D                     2
    CLASSE_E                     0
    DERIVES_DE_TYPE              0

    OBLIGATIONS_NOUVELLES_TROUVEES = 2
        LL.SAME_OPERATOR
        OFF.LOCAL_FINITENESS

Les deux obligations nouvelles ont été inscrites IMMEDIATEMENT au registre
(`CONTRACTS.md`) et au manifeste Comparator, conformément à § Q.6.  Le compteur
d'obligations sans réalisateur passe donc de 8 à 10 : ce n'est pas une
régression de la production, c'est une correction du compteur.

## O1 — vrai zéro                                                  CLASSE A

| dimension | réalisateur | verdict |
|---|---|---|
| O1.CARRIER | TNonTrivialZetaZero | EXACT |
| O1.ZERO | thm_zeroProvenance_zeta | EXACT |
| O1.STRIP | thm_zeroRadialPosition_positive, thm_zeroRadialPosition_lt_one | EXACT |
| O1.HEIGHT | rZeroHeight | EXACT |
| O1.RADIAL | rZeroRadialPosition | EXACT |
| O1.MULT | nZeroMultiplicity, thm_zeroMultiplicity_ne_zero | EXACT |
| O1.IDENTITY | thm_zero_identity_of_sameSupport | EXACT |
| O1.RIGIDITY | thm_zeroAttributes_are_functions_of_support | EXACT |
| O1.CONSUMER | rTowerHeight, cMirrorSupport | EXACT |
| O1.CERT | cmp_C0_trueZero_provenance, cmp_C0_zeroMultiplicity_ne_zero, cmp_C0_zeroAttributes_are_functions_of_support | EXACT |

## O2 — axe algébrique                                             CLASSE A

| dimension | réalisateur | verdict |
|---|---|---|
| O2.CARRIER | TAlgebraicInterval | EXACT |
| O2.ORDER | thm_algebraicAxis_log_lt_log_iff | EXACT |
| O2.LOG_EXP | thm_algebraicAxis_exp_log, thm_algebraicAxis_log_exp | EXACT |
| O2.PRIMES_FIXED | thm_foundPrimes_no_prime_is_moved | EXACT |
| O2.INTERVAL | TAlgebraicInterval | EXACT |
| O2.FOUND_SET | sAlgebraicIntervalFoundPrimes | EXACT |
| O2.FINITENESS | Finset par construction | EXACT |
| O2.ORDERED_FOUND_SET | thm_foundPrimes_sorted | EXACT |
| O2.PLURAL_ALLOWED | thm_foundPrimes_generallyPlural | EXACT |
| O2.NO_MOVEMENT | thm_foundPrimes_determined_by_endpoints | EXACT |
| O2.CONSUMER | tCellAlgebraicInterval | EXACT |
| O2.CERT | cmp_C2_foundPrimes_generallyPlural | EXACT |

## O3 — Tour harmonique                                            CLASSE A

| dimension | réalisateur | verdict |
|---|---|---|
| O3.SOURCE | rTowerHeight, rTowerRadialPosition | EXACT |
| O3.STATE | TTowerState | EXACT |
| O3.PHASE | rTowerPhase | EXACT |
| O3.DENSITY | rTowerDensity | EXACT |
| O3.RAYS | rTowerIncidence | EXACT |
| O3.INCIDENCE | rTowerLogIncidence, thm_rTowerLogIncidence_phaseEquation | EXACT |
| O3.INCIDENCE_ORDER | thm_rTowerIncidence_strictOrder | EXACT |
| O3.SOURCE_PRESERVATION | thm_tTowerState_injective, thm_towerCoordinates_are_functions_of_member | EXACT |
| O3.KAPPA_REREAD | thm_kappa_eq_entry_quotient, thm_kappa_quotient_isInteger | EXACT |
| O3.M_REREAD | thm_span_eq_density_mul_logDiameter | EXACT |
| O3.TERMINAL_RAY | kTerminalAddress | EXACT |
| O3.NO_PRIME_SELECTION | garde mécanique `audit_fidelity.sh` § 4c | EXACT |
| O3.CONSUMER | rContactMinus, rContactPlus | EXACT |
| O3.CERT | cmp_C1_incidence_phaseEquation, cmp_C1_kappa_reading, cmp_C1_m_reading | EXACT |

Correction explicite d'un rapport antérieur : « 7/7 attributs prouvés » pour la
Tour était FAUX au moment où il a été écrit, parce que O3.KAPPA_REREAD et
O3.M_REREAD n'avaient aucun réalisateur.  Ils en ont un depuis `4ddf8099`.
Le mot « relecture » est ici littéral : le maître § S4 interdit toute fonction
de recherche pour κ ou m, et aucune n'existe.

## O4 — contacts / cellule                                         CLASSE A

| dimension | réalisateur | verdict |
|---|---|---|
| O4.SAME_TOWER | rContactMinus/rContactPlus prennent le MEME zUpperZero | EXACT |
| O4.CMINUS | rContactMinus | EXACT |
| O4.CPLUS | rContactPlus | EXACT |
| O4.ORDER | thm_contacts_strictOrder | EXACT |
| O4.CELL | sCellCarrier, tCellAlgebraicInterval | EXACT |
| O4.POSITIVE_DIAMETER | thm_cellLogDiameter_positive | EXACT |
| O4.HEIGHT_INVERSION | thm_inversion_recovers_height | EXACT |
| O4.RADIAL_INVERSION | thm_inversion_recovers_radialPosition | EXACT |
| O4.PROVENANCE | TReadingProvenance | EXACT |
| O4.INJECTIVITY | thm_sameContactData_sameMember | EXACT |
| O4.NO_RECOMPUTE | thm_countingReads_doesNotMoveContacts | EXACT |
| O4.CONSUMER | nMemberCentralPrime | EXACT |
| O4.CERT | cmp_C1_contacts_strictOrder, cmp_C1_inversion_recovers_height, cmp_C1_inversion_recovers_radialPosition, cmp_C1_sameContactData_sameMember | EXACT |

REMARQUE DE PLACEMENT DU DEFAUT.  Les théorèmes d'O4 sont énoncés pour une
fenêtre `TTowerWindow` quelconque.  Ce n'est PAS un défaut d'O4 : aucune
dimension d'O4 n'exige que la fenêtre soit produite par le membre.  L'exigence
« une fenêtre par membre » est `S4.ONE_WINDOW_PER_MEMBER`, et son habitation est
`S4.INHABITANT`.  Le défaut est donc localisé en S4, une seule fois, et non
recompté sur chaque objet aval.

## O5 — occurrence première                                        CLASSE A

| dimension | réalisateur | verdict |
|---|---|---|
| O5.PRIME | TPrimeOccurrence.nPrime, TPrimeOccurrence.isPrime | EXACT |
| O5.RANK | TPrimeOccurrence.nRank, hPrimeAtRank | EXACT |
| O5.PREVIOUS_EDGE | nPreviousEdgeStart | EXACT |
| O5.NEXT_EDGE | nNextEdgeEnd | EXACT |
| O5.ORIENTATION | TPrimeOccurrence.orientation | EXACT |
| O5.GAP | nNextGap, thm_occurrence_nextGap_positive | EXACT |
| O5.PROVENANCE | tProvenance, tMemberProvenance | EXACT |
| O5.R_ATT | thm_rATT_sameProvenance_sameMember, thm_rATT_distinctMembers_distinctOccurrences | EXACT |
| O5.R_ATT_LIMIT | thm_rATT_doesNotSeparatePrimes | EXACT |
| O5.SAME_CELL | tMemberProvenance porte tCellAlgebraicInterval du même membre | EXACT |
| O5.CONSUMER | tOperatorPrimeOccurrence | EXACT |
| O5.CERT | cmp_C2_rATT_sameProvenance_sameMember, cmp_C2_rATT_doesNotSeparatePrimes | EXACT |

## O6 — grammaire première                                         CLASSE A

| dimension | réalisateur | verdict |
|---|---|---|
| O6.ENUMERATION | fnPrimeAtRank | EXACT |
| O6.PRIMALITY | thm_primeAtRank_isPrime | EXACT |
| O6.STRICT_ORDER | thm_primeAtRank_strictMono | EXACT |
| O6.SUCCESSOR | fnPrimeSuccessor | EXACT |
| O6.GAP | nPrimeGap | EXACT |
| O6.GAP_POSITIVE | thm_primeGap_positive | EXACT |
| O6.EMPTY_CORRIDOR | thm_noPrimeStrictlyBetweenSuccessivePrimes | EXACT |
| O6.UNIQUE_HISTORY | thm_primeHistory_unique | EXACT |
| O6.RANK_ONLY_RIGIDITY | thm_primeGap_depends_on_rank_alone | EXACT |
| O6.CONSUMER | nPlaceEarlierEndpoint, nPlaceLaterEndpoint | EXACT |
| O6.CERT | cmp_C4_primeGap_positive, cmp_C4_primeHistory_unique | EXACT |

## O7 — grammaire des zéros                                        CLASSE A

| dimension | réalisateur | verdict |
|---|---|---|
| O7.FIBER | sZeroHeightFiber, thm_sameFiber_iff_sameHeight | EXACT |
| O7.MEMBER_ORDER | PZeroMemberPrecedes, thm_zeroMemberPrecedes_iff_height_radial_lex | EXACT |
| O7.ORDER_INJECTIVE | thm_zeroOrderKey_injective | EXACT |
| O7.CONSECUTIVITY | PZeroMembersConsecutive | EXACT |
| O7.GAP | rZeroPairHeightGap | EXACT |
| O7.NONNEGATIVE | thm_zeroPairHeightGap_nonnegative | EXACT |
| O7.ZERO_IFF_SAME_HEIGHT | thm_zeroPairHeightGap_zero_iff_sameFiber | EXACT |
| O7.CONSUMER | TZeroPassage | EXACT |
| O7.CERT | cmp_C0_zeroGap_nonnegative, cmp_C0_zeroGap_null_iff_sameFiber | EXACT |

La positivité STRICTE de l'écart des zéros n'apparaît nulle part comme
attribut : elle est une conclusion de la loi locale.  C'est la lecture du
maître, et elle est tenue.

## O8 — passage / R-PASS                                CLASSE A + 1 × CLASSE C

| dimension | réalisateur | verdict |
|---|---|---|
| O8.CARRIER | TZeroPassage | EXACT |
| O8.EARLIER_ENDPOINT | zEarlierMember | EXACT |
| O8.LATER_ENDPOINT | zLaterMember | EXACT |
| O8.ORDER | TZeroPassage.precedes | EXACT |
| O8.NEIGHBORHOOD | hConsecutive | EXACT |
| O8.NULLITY | PZeroPassageRelationNull | EXACT |
| O8.NONNULLITY | PZeroPassageRelationNonNull, thm_zeroPassage_nonNull_iff_gapPositive | EXACT |
| O8.RPASS_CONTRACT | PIsMemberSensitivePassageTransport | EXACT |
| **O8.RPASS_REAL_TRANSPORT** | **—** | **MISSING (NON COMPENSABLE)** |
| O8.ENDPOINT_PRESERVATION | thm_rpass_endpoints_are_member_own | CONDITIONAL |
| O8.NULLITY_PRESERVATION | thm_rpass_transports_nullity | CONDITIONAL |
| O8.NONNULLITY_PRESERVATION | thm_rpass_transports_nonNullity | CONDITIONAL |
| O8.CONSUMER | thm_triple_twoHeightGaps_positive_of_nonNullImages | EXACT |
| O8.CERT | cmp_C3_rpass_endpoints_are_member_own, cmp_C3_rpass_transports_nullity_and_nonNullity, cmp_C3_rpass_positiveGap_of_nonNullImage | EXACT |

Les trois lignes CONDITIONAL sont correctes : elles prennent `hTransport` en
argument, ce qui est légitime tant que le transport n'est pas produit, et
DEVIENT une dette dès que l'on parle de fermeture.  Elles ne comptent pas comme
producteurs de leur propre hypothèse (§ N.2.C).

## O9 — triple                                                     CLASSE A

| dimension | réalisateur | verdict |
|---|---|---|
| O9.CARRIER | TThreeConsecutiveZeros | EXACT |
| O9.THREE_MEMBERS | zEarlierZero, zMiddleZero, zLaterZero | EXACT |
| O9.PASSAGE_LEFT | tEarlierPassage | EXACT |
| O9.PASSAGE_RIGHT | tLaterPassage | EXACT |
| O9.SAME_MIDDLE | thm_triple_sameMiddleMember (⟨rfl, rfl⟩) | EXACT |
| O9.PAIRWISE_DISTINCT | thm_triple_members_pairwiseDistinct | EXACT |
| O9.GAP_LEFT | rEarlierZeroHeightGap | EXACT |
| O9.GAP_RIGHT | rLaterZeroHeightGap | EXACT |
| O9.NO_AVERAGE_SUBSTITUTION | thm_triple_mean_does_not_determine_pair | EXACT |
| O9.CONSUMER | thm_triple_twoHeightGaps_positive_of_localLaw | EXACT |
| O9.CERT | cmp_C4_triple_sameMiddleMember, cmp_C4_triple_twoHeightGaps_positive | EXACT |

## O10 — comptage                                                  CLASSE A

| dimension | réalisateur | verdict |
|---|---|---|
| O10.INPUT_CELL_ONLY | nCellLeftEdgeRank / nCellRightEdgeRank ne prennent que l'intervalle | EXACT |
| O10.LEFT_RANK | nCellLeftEdgeRank | EXACT |
| O10.RIGHT_RANK | nCellRightEdgeRank | EXACT |
| O10.FOUND_COUNT | nCellFoundCount, thm_cellFoundCount_eq_edgeRankDifference | EXACT |
| O10.RANK_INTERVAL | thm_foundPrimes_eq_image_rankInterval | EXACT |
| O10.CENTRAL_RANK | nCellCentralRank, thm_cellCentralRank_between_edges | EXACT |
| O10.CENTRAL_PRIME | nCellCentralPrime, thm_cellCentralPrime_isPrime | EXACT |
| O10.CENTRAL_PRIME_IN_CELL | thm_cellCentralPrime_in_interval | EXACT |
| O10.NO_CONTACT_MOVEMENT | thm_countingReads_doesNotMoveContacts | EXACT |
| O10.VM_CHEBYSHEV_TRACEABILITY_MODE | **DIRECT_COUNTING_CONSEQUENCE** | ENREGISTRE |
| O10.CONSUMER | nMemberCentralPrime, nOperatorCentralPrime | EXACT |
| O10.CERT | cmp_C2_foundCount_eq_edgeRankDifference, cmp_C2_centralPrime_isPrime_and_in_interval | EXACT |

Le mode de traçabilité est enregistré explicitement, comme le maître l'exige :
la rigidité aux deux bords est obtenue par la dualité `Nat.count` / `Nat.nth`
(`thm_edgeRank_le_iff_lt_primeAtRank`), donc
`DIRECT_COUNTING_CONSEQUENCE`, et NON `EXPLICIT_ANALYTIC_REALISATION`.  Aucun
théorème de RHV3 ne prétend réaliser analytiquement von Mangoldt ou Chebyshev.

## S4 — porteur canonique                              CLASSE D + 1 × CLASSE C

| dimension | réalisateur | verdict |
|---|---|---|
| S4.TYPE | TCanonicalTowerOperator | EXACT |
| **S4.INHABITANT** | **—** | **MISSING (NON COMPENSABLE)** |
| S4.ONE_WINDOW_PER_MEMBER | champ fnWindow : TUpperNonTrivialZetaZero → TTowerWindow | EXACT |
| S4.SAME_OPERATOR_THREADING | toutes les lectures sont des méthodes du même tOperator | EXACT |
| S4.CONTACTS_FROM_OPERATOR | rOperatorContactMinus, rOperatorContactPlus | EXACT |
| S4.CELL_FROM_OPERATOR | tOperatorCell | EXACT |
| S4.CENTRAL_PRIME_FROM_OPERATOR | nOperatorCentralPrime | EXACT |
| S4.OCCURRENCE_FROM_OPERATOR | tOperatorPrimeOccurrence | EXACT |
| S4.NO_DOWNSTREAM_RECHOICE | thm_operatorReadings_are_functions_of_member + garde `audit_fidelity.sh` § 5 | EXACT |
| S4.CERT | cmp_C1_kappa_reading, cmp_C1_m_reading | EXACT |

CLASSE D : le porteur est correctement défini mais n'est PAS ENCORE CONNECTE à
la route, faute d'habitant.  Un type n'est jamais compté comme habitant
(§ N.2.C).

## LOI LOCALE                                          CLASSE B + 2 × CLASSE C

| dimension | réalisateur | verdict |
|---|---|---|
| LL.PLACE_TYPE | TPrimeHistoryPlace | EXACT |
| LL.SUCCESSIVE_ENDPOINTS | nPlaceEarlierEndpoint, nPlaceLaterEndpoint | EXACT |
| LL.NONNULL_PLACE | thm_place_isNeverNull | EXACT |
| LL.EMPTY_CORRIDOR | thm_place_corridorEmpty | EXACT |
| LL.LOCAL_LAW_STATEMENT | PLocalLawTransportsPassageOntoPlace | EXACT |
| **LL.LOCAL_LAW_PRODUCER** | **—** | **MISSING (NON COMPENSABLE)** |
| **LL.SAME_OPERATOR** | **—** | **MISSING — TROUVE PAR CE REPLAY** |
| LL.SAME_PASSAGE | ∀ tPassage, les deux extrémités sont celles DU MEME passage | EXACT |
| LL.ENDPOINT_DISTINCT_DERIVED | thm_endpointsDistinct_of_localLaw | CONDITIONAL |
| LL.CERT | cmp_C4_localLaw_endpointsDistinct, cmp_C4_localLaw_noNullPassage_and_positiveGap | EXACT |

LL.SAME_OPERATOR — DEFAUT REEL, ici nommé pour la première fois.
`PLocalLawTransportsPassageOntoPlace` est paramétrée par une fonction LIBRE
`fnMemberCentralPrime : TNonTrivialZetaZero → ℕ`.  Rien, dans l'énoncé actuel,
n'impose que cette fonction soit `nOperatorCentralPrime` du porteur canonique.
L'énoncé est donc plus faible que le maître, qui exige la loi locale SUR
l'opérateur.  Le défaut est structurel, pas cosmétique : il faut d'abord un
habitant de S4 pour que `nOperatorCentralPrime` soit une fonction du seul
membre, puis énoncer la loi sur lui.

Ordre causal imposé par § P et § Q.7 : S4.INHABITANT précède LL.SAME_OPERATOR,
qui précède LL.LOCAL_LAW_PRODUCER, qui précède O8.RPASS_REAL_TRANSPORT sur la
place, qui précède toute la famille OFF, qui précède le terminal.

## MIROIR                                                          CLASSE A

| dimension | réalisateur | verdict |
|---|---|---|
| MIRROR.SUPPORT | cMirrorSupport, thm_mirrorSupport_re, thm_mirrorSupport_im | EXACT |
| MIRROR.ZETA_ZERO | thm_mirrorSupport_zetaVanishes | EXACT |
| MIRROR.TRUE_ZERO | zMirrorZero | EXACT |
| MIRROR.SAME_HEIGHT | thm_mirror_sameHeight | EXACT |
| MIRROR.RADIAL_REFLECTION | thm_mirror_radialPosition | EXACT |
| MIRROR.DISTINCT_OFF_LINE | thm_offCriticalLine_mirror_distinct | EXACT |
| MIRROR.UPPER_BRANCH_PRESERVED | zUpperMirrorZero | EXACT |
| MIRROR.CERT | cmp_C0_mirror_zetaVanishes, cmp_C0_mirror_sameHeight_complementaryRadial, cmp_C0_off_gives_two_distinct_sameFiber_members | EXACT |

## OFF et TERMINAL — hors périmètre du replay, rappel

    OFF.DISTINCT_PAIR              thm_offCriticalLineUpper_twoDistinctSameFiberMembers
    OFF.SAME_HEIGHT                idem
    OFF.ORDERED_COMPARABILITY      idem
    OFF.LOCAL_FINITENESS           —   (TROUVE PAR CE REPLAY)
    OFF.CONSECUTIVE_PAIR_EXTRACTION —
    OFF.REAL_PASSAGE               —   NON COMPENSABLE
    OFF.ZERO_GAP                   —   (sur un passage réel)
    OFF.SAME_E_FORWARDING          —   NON COMPENSABLE
    TERM.*                         —   aucune ligne réalisée

`TERM.UNIVERSALIZATION` n'est pas comptée séparément : le type attendu du terme
terminal est déjà universellement quantifié, donc son réalisateur est le même
terme que `TERM.RIEMANN_HYPOTHESIS`.  C'est une identité de réalisateur, pas une
fermeture par déclaration (§ Q.8).

## Verdict du replay

    CODE_CORRECT      = true   (aucune dérive de type, aucun trou statique)
    ROUTE_COMPLETE    = false  (10 obligations sans réalisateur)
    CERTIFIED         = false

Les trois ne doivent jamais être confondus (§ Q.5).
