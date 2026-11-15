/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.TowerRaccord
import RHV6Fresh.Terminal.RaccordDetector
import RHV6Fresh.Terminal.ShiftedWorld
import RHV6Fresh.Terminal.PrimalEventRaccord
import RHV6Fresh.Terminal.GlobalRigidSystem
import RHV6Fresh.Terminal.HeightPacket
import RHV6Fresh.Terminal.InverseReading
import RHV6Fresh.Terminal.RegimeChange
import RHV6Fresh.Terminal.RegimeTower
import RHV6Fresh.Terminal.SpectralIdentity
import RHV6Fresh.Terminal.RegimeCell
import RHV6Fresh.Terminal.SpectralUniqueness
import RHV6Fresh.Terminal.RegimeTrigger
import RHV6Fresh.Terminal.ConstraintPacket
import RHV6Fresh.Terminal.DiagonalPassage
import RHV6Fresh.Terminal.EngagedProgression
import RHV6Fresh.Terminal.LinkedProduction
import RHV6Fresh.Terminal.EngagedPersistence
import RHV6Fresh.Terminal.ArithmeticReading
import RHV6Fresh.Terminal.ZetaParameters
import RHV6Fresh.Terminal.NoRegimeChange
import RHV6Fresh.Terminal.GrammarKinematics
import RHV6Fresh.Terminal.SpontaneousRegimeBreak
import RHV6Fresh.Terminal.PrimeWeightResponse
import RHV6Fresh.Terminal.ChangePredictor
import RHV6Fresh.Terminal.CanonicalTransition
import RHV6Fresh.Terminal.EngagedClosureVerdict
import RHV6Fresh.Terminal.EntryPositionArrow
import RHV6Fresh.Terminal.PointedPrimeComparison
import RHV6Fresh.Terminal.OneZeroOnePrime
import RHV6Fresh.Terminal.TowerGrid
import RHV6Fresh.Terminal.TowerWinding
import RHV6Fresh.Terminal.RadialSlope
import RHV6Fresh.Terminal.ClosureRoutes
import RHV6Fresh.Terminal.RemainderExponent
import RHV6Fresh.Terminal.RemainderEnergy
import RHV6Fresh.Terminal.ExactAxisReading
import RHV6Fresh.Terminal.CompensationRigidity
import RHV6Fresh.Terminal.GrammarWordLoad
import RHV6Fresh.Terminal.RegimeWindow
import RHV6Fresh.Terminal.PairCurvature
import RHV6Fresh.Terminal.PairInteraction
import RHV6Fresh.Terminal.LocalFourSectors
import RHV6Fresh.Terminal.TowerFourSectors
import RHV6Fresh.Terminal.MirrorLoop
import RHV6Fresh.Terminal.MirrorAntisymmetry
import RHV6Fresh.Terminal.QuadraticVariation
import RHV6Fresh.Terminal.FirstZeroField
import RHV6Fresh.Terminal.FixedExponentField
import RHV6Fresh.Terminal.EscapeFinancing
import RHV6Fresh.Terminal.TowerHierarchy
import RHV6Fresh.Terminal.FirstTowerHorizon
import RHV6Fresh.Terminal.DoubleRigidity
import RHV6Fresh.Terminal.LocalRaccordCaptivity
import RHV6Fresh.Terminal.EngagedRadialFloor
import RHV6Fresh.Terminal.EngagedNoTranslation
import RHV6Fresh.Terminal.TowerTwoSidedRoom
import RHV6Fresh.Terminal.PersistentCapture
import RHV6Fresh.Terminal.ConsecutiveChainContradiction
import RHV6Fresh.Terminal.ReadingArithmetic
import RHV6Fresh.Grammar.Mod6Rigidity

/-!
# RHV6Fresh — manifeste de la direction unique (2026-09-29)

Une seule direction : le raccord `TowerRaccord e l` entre deux Tours consécutives au premier partagé
`M = p_min(e) = Occ(l)` (`Terminal/TowerRaccord.lean`). Une seule prémisse ouverte, seule
`def P… : Prop` du code (décision de l'auteur, 2026-09-30) : `PNoRegimeChange`, « aucun changement
de régime n'est possible » (`Terminal/NoRegimeChange.lean`), équivalente à RH sans aucune condition
annexe (`noRegimeChange_iff_riemannHypothesis`). Les anciennes `PTowerRaccordOrientation` et
`PNoLowOffZero` sont retirées.

Chaîne compilée, inconditionnelle, qui porte le raccord :
1. la Tour d'un zéro et sa cellule unique pour tout premier (`Tower/`, `Direct/PivotCell.lean`) ;
2. la grammaire : `p_min`, occurrence, injectivité, rigidité mod 6 (`Grammar/`) ;
3. le sens de progression sur tout passage (`passage_direction_rigid`) ;
4. la Tour est le terme `q^ρ/ρ` de la formule explicite, amplitude `q^β/‖ρ‖`
   (`Terminal/ExplicitFormulaLink.lean`) ;
5. le raccord : existence, rigidité, encadrement énergétique dans les deux cellules, transport exact
   (`towerRaccordOf`, `towerRaccord_eq`) ;
6. sous RH le raccord est orienté sur tout passage (`towerRaccord_oriented_of_riemannHypothesis`) ;
7. le détecteur complet (`Terminal/RaccordDetector.lean`) : à hauteur de sortie `≥ 2`, le raccord est
   orienté si et seulement si la hauteur avance strictement (`towerRaccord_oriented_iff_height_lt`),
   cas diagonal compris ; la
   charge radiale d'une fibre `(M₂²/(M₁·M₃))^d`, neutre seulement en ligne
   (`fibre_transport_product_off`, `fibre_charge_eq_one_iff`) ;
8. le monde témoin `ζ(s−δ)ζ(s+δ)` (`Terminal/ShiftedWorld.lean`) : mêmes premiers, tous les zéros
   hors ligne — contrôle, jamais une prémisse ;
9. le raccord grammatical (`Terminal/PrimalEventRaccord.lean`) : le raccord, tous ses champs
   conservés, plus l'événement premier complet de `M` (prédécesseur, successeur, écarts, état et
   classes mod 6, poids), égal à l'événement reconstruit depuis les zéros
   (`reconstructedEvent_eq_primalEvent`) ; l'histoire première gagne exactement cet événement sur
   tout passage (`passage_history_step`) ; existence et unicité (`grammaticalRaccordOf`,
   `grammaticalRaccord_eq`) ; environnement complet (`grammaticalRaccord_environment`) ;
10. ce que l'énergie lit de l'événement : le pas d'un membre `(Occ/p_min)^{β−1/2}`, neutre si et
   seulement si le membre est en ligne (`memberStep_eq_one_iff`) ; transport cumulé d'une histoire
   (`history_transport_product`, `historyCharge_const_one_iff`) ;
11. bornes de la piste : le certificat complet existe sur le passage horizontal hors ligne
   (`off_grammaticalRaccord_complete_and_reversed`) ; un préfixe analytique sépare les deux membres
   d'un passage si et seulement si la hauteur avance (`passage_separated_by_window_iff`) ; le foncteur
   de reconstruction ne reconnaît aucun premier dans le monde témoin
   (`shiftedWorld_reconstructs_no_prime`) ;
12. l'organisme spectral : le membre qui porte la Tour est le terme sommé par la formule explicite
   (`spectral_organism_member`) ; la somme reconstruit `ψ`, l'événement complet, l'histoire et tout
   descripteur de l'histoire (`spectral_organism_reconstructs`). Inconditionnel ;
13. le reste arithmétique et l'incrément d'un passage : à un événement premier le reste avance de
   `log p` moins le fond lisse (`remainder_increment_at_prime`) ; la contribution différentielle d'un
   membre est `x^{ρ−1}` (`zeroTerm_hasDerivAt`) ; une paire hors ligne à même hauteur pèse
   `x^{−1/2}(x^d + x^{−d})`, strictement plus que deux membres en ligne
   (`off_pair_density_norm`, `off_pair_density_exceeds_line`) ;
14. un événement premier appartient à un seul raccord (`grammaticalRaccord_M_injective`) ; la charge
   d'une fibre se lit sur les deux écarts de l'événement central (`primalEvent_charge_by_gaps`) ;
15. le système rigide global (`Terminal/GlobalRigidSystem.lean`) : toutes les couches sur le même
   ensemble de zéros, chaque champ rempli par un théorème, aucune hypothèse (`globalRigidSystem`) ;
   ce qu'un zéro hors ligne y force (`off_inside_globalRigidSystem`) ; les trois égalités du
   diagramme sont conservées en présence d'un zéro hors ligne (`off_conserves_three_equalities`) :
   le système global, seul, ne ferme pas ;
16. paquet de hauteur et compensation forcée (`Terminal/HeightPacket.lean`) : le canal compilé se
   découpe exactement en paquet et complément (`channel_eq_packet_add_complement`), donc
   `ψ(N) = fond + paquet + complément` (`psi_eq_background_add_packet_add_complement`) ; la
   compensation `K := reste exact − paquet` est fournie exactement par le complément, à chaque
   marche, à chaque événement premier et pour tout `x > 1` (`compensation_eq_complement`,
   `eventCompensation_eq_complement`, `compensation_realized_for_all_x`) ; la chaîne complète sur
   un zéro hors ligne (`off_forced_compensation`, `off_packet_explicit`).
17. lecture inverse (`Terminal/InverseReading.lean`) : le résidu arithmétique `ψ − fond` comme objet
   autonome (`exactRemainder_arithmetic_only`), le pont `R_arith = R_spectral`
   (`arithmetic_eq_spectral`), la différence entre deux événements lue des deux côtés
   (`remainderBetween_arithmetic`, `remainderBetween_eq_spectral`) et découpée en paquet et
   complément (`remainderBetween_eq_packet_add_complement`, `complementBetween_forced`) ; chaîne
   sur un zéro hors ligne (`off_inverse_reading`).
18. deux régimes et changement de régime (`Terminal/RegimeChange.lean`) : passage vertical ou
   horizontal, exclusifs et exhaustifs (`passage_regime_dichotomy`, `vertical_regime`,
   `horizontal_regime`) ; lois de jonction (`junction_vertical_vertical`,
   `junction_vertical_horizontal`, `junction_horizontal_vertical`) ; aucun changement de régime
   sur la ligne (`onLine_keeps_regime`, `regimeChange_offLine`) ; un hors-ligne exige l'entrée en
   régime horizontal (`off_forces_regime_entry`) ; l'absence d'entrée équivaut à RH
   (`riemannHypothesis_iff_no_regimeEntry`) ; le régime ne décide que du côté du découpage
   (`passage_split_by_regime`).
19. le régime lu sur la Tour et la verticalité sur la ligne (`Terminal/RegimeTower.lean`) : le pas
   `π/T` ne dépend que de la hauteur (`towerPitch_radial_blind`, `towerPitch_lt_iff`) ; à même
   hauteur un déplacement radial translate rigidement tous les contacts
   (`rigid_translation_of_sameHeight_radial_lt`), à hauteurs différentes aucune translation rigide
   (`no_rigid_translation_of_height_ne`) ; horizontal ⟺ translation rigide, vertical ⟺ pas
   contracté (`horizontal_iff_tower_translation`, `vertical_iff_pitch_contracts`,
   `regime_entry_read_on_towers`) ; sur la ligne la poussée horizontale vaut zéro et tout passage
   entre deux membres en ligne est vertical (`onLine_horizontal_push_zero`,
   `onLine_passage_vertical_signature`, `onLine_exit`, `onLine_entry`).
20. l'identité spectrale, l'unicité de la décomposition et la cellule complète
   (`Terminal/SpectralIdentity.lean`, `Terminal/RegimeCell.lean`,
   `Terminal/SpectralUniqueness.lean`) : aucun membre n'est retirable (`member_term_ne_zero`,
   `no_member_removable`) ; les profils `x^s` sont indépendants (`cpow_finite_independent`) ; la
   somme infinie détermine chaque composante (`cpow_series_fibre_sum_zero`, `cpow_series_unique`) ;
   dans toute représentation du canal chaque zéro figure avec sa multiplicité et aucun intrus n'a
   de poids (`SpectralRepresentation.contains_member`, `SpectralRepresentation.no_intruder`,
   `SpectralRepresentation.recovers_member`) ; l'identité d'un hors-ligne n'est pas effacée
   (`SpectralRepresentation.off_identity_not_erased`) ; RH équivaut à l'existence d'une
   représentation en ligne (`riemannHypothesis_iff_onLine_representation`). Cellule
   vertical → horizontal → vertical : membres centraux miroirs (`RegimeCell.central_mirror`), pas
   et contacts (`RegimeCell.pitch_signature`, `RegimeCell.contact_signature`), verrou de phase
   (`horizontal_term_phase_lock`), charge lue sur la translation
   (`RegimeCell.charge_reads_translation`, `RegimeCell.charge_ne_one`), résidu
   (`RegimeCell.remainder_record`), garde (`RegimeCell.not_riemannHypothesis`).
21. le changement de régime lu par la hauteur, caractérisation et certificat
   (`Terminal/RegimeTrigger.lean`) : un membre en ligne atteint verticalement est quitté
   verticalement (`engaged_regime_kept`) ; la position radiale d'arrivée caractérise le régime du
   passage suivant, sans le construire (`vertical_arrival_characterizes`) ; un passage vertical est pur
   si et seulement si ses deux membres sont en ligne, sinon diagonal (`vertical_pure_iff_onLine`,
   `diagonal_iff_off`) ; toute entrée en régime horizontal est précédée d'un passage diagonal
   (`regime_entry_diagonal`, `regime_entry_from_line`) ; la fibre multiple est le certificat, lu
   par la hauteur, de la présence d'un hors-ligne, pas sa cause (`fibre_onLine_unique`, `fibre_multiple_iff_off`,
   `vertical_arrival_onLine_iff_fibre_singleton`, `vertical_departure_onLine_iff_fibre_singleton`) ;
   la ligne est le lieu fixe de la réflexion, `Λ` y est réelle et un zéro en ligne est une seule
   équation réelle en `T`
   (`completedZeta_mirror`, `completedZeta_real_onLine`, `onLine_zero_iff_lineValue`,
   `fibre_has_onLine_member_iff`), un changement de signe garantit l'existence d'un membre en ligne
   (`onLine_member_of_sign_change` ; détecteur par valeurs intermédiaires, pas générateur du membre
   suivant). Bornes : `riemannHypothesis_iff_fibres_singleton`,
   `riemannHypothesis_iff_no_diagonal`, `lineValue_ne_zero_fibre_off`.
22. le tout en ligne et le paquet de contraintes pris ensemble (`Terminal/ConstraintPacket.lean`) :
   le tout en ligne est en bijection avec les zéros de la fonction réelle (`lineWholeEquiv`,
   `lineWhole_channel_by_height`) ; le reste arithmétique est le tout plus l'écart
   (`remainder_eq_lineWhole_add_deviation`, `lineDeviation_arithmetic`) ; l'écart n'est absorbé
   par aucune repondération des membres en ligne (`lineDeviation_not_absorbed`) ; un membre hors
   ligne dévie (`off_member_deviates`) ; le paquet complet au passage diagonal
   (`regime_entry_packet`, `regime_entry_recorded`). Bornes : `lineDeviation_vanishes_iff`,
   `riemannHypothesis_iff_remainder_eq_lineWhole`.
23. le passage vertical diagonal parti de la ligne (`Terminal/DiagonalPassage.lean`) : tout
   contact est le contact de la Tour de ligne à la même hauteur, fonction de `T` seul, multiplié
   par un facteur radial unique (`contact_eq_line_mul_radial`), égal à `1` si et seulement si le
   membre est en ligne (`radialFactor_eq_one_iff`, `radialFactor_gt_one_iff`,
   `radialFactor_lt_one_iff`) ; garde, tautologie fonctionnelle : une fonction de la hauteur seule ne voit
   aucun déplacement radial (`height_determined_radial_blind`,
   `radial_sensitive_not_height_determined`) ; `contacts_height_determined_iff_onLine` ; la
   fonction réelle ne s'annule pas et garde son signe strictement entre les deux hauteurs d'un
   passage (`lineValue_ne_zero_between`, `lineValue_sign_constant_between`) ; registre complet du
   passage (`diagonal_from_line_ledger`, `regime_entry_diagonal_ledger`). Borne :
   `vertical_exhausts_iff_arrival_onLine`.
24. la progression depuis l'état engagé, sans accorder aucun hors-ligne
   (`Terminal/EngagedProgression.lean`) : état engagé (`EngagedState`, `engagedState_iff_onLine`) ;
   le membre suivant est unique et, depuis la ligne, fonction de la hauteur de départ seule
   (`passage_successor_unique`, `engaged_successor_determined_by_height`) ; ce que les lois de
   progression donnent depuis l'état engagé, avec sur la position radiale la seule inégalité
   `β' ≤ 1/2` (`engaged_progression`) ; pas de propagation (`engaged_propagates`).
25. zêta produit les zéros, ils sont liés (`Terminal/LinkedProduction.lean`) : depuis l'état engagé,
   les liaisons compilées (ordre, miroir, grammaire première, somme, côté arithmétique, fonction
   réelle) tiennent ensemble sur le membre d'arrivée (`engaged_linked_production`) ; sa position
   radiale est écrite dans le côté arithmétique, dans toute représentation du reste
   (`vertical_arrival_written_in_arithmetic`). Borne : équivalence, elle dit où le régime de
   l'arrivée est écrit, pas ce qui y est écrit.
26. le régime engagé perdure, argument de l'auteur maillon par maillon
   (`Terminal/EngagedPersistence.lean`) : seule la position radiale change le régime
   (`regime_change_requires_radial`) ; si seule la hauteur évolue sur le passage, le régime est
   transmis (`heightOnly_step`) ; sous la loi « sur un passage vertical parti de la ligne, seule la
   hauteur évolue » (hypothèse du théorème, aucune `def` de prémisse), tout membre au-dessus d'un
   membre engagé est engagé, atteint et quitté verticalement (`engaged_persists_to_infinity`).
   Borne : la loi n'est pas dérivée ; elle est nécessaire (`heightOnly_of_riemannHypothesis`).
27. la lecture du reste arithmétique lui-même, sans passer par les zéros
   (`Terminal/ArithmeticReading.lean`) : le reste `smoothedRemainder` est écrit avec les seuls
   premiers ; lecture par la croissance, une série de profils bornée par `C · x^θ` ne porte aucun
   exposant de partie réelle `> θ` (`cpow_series_growth_fibre_zero`) ; une borne de croissance du
   reste borne la position radiale de tout zéro (`smoothedRemainder_growth_bounds_zero`,
   `radial_le_of_remainder_growth`) ; le poids de von Mangoldt d'un premier est le poids de son
   événement (`vonMangoldt_prime_eq_event_weight`). Borne : RH ⟺ `∃ C, ∀ x > 1, ‖reste‖ ≤ C·√x`
   (`riemannHypothesis_iff_remainder_sqrt_growth`) ; la borne en `√x` n'est pas dérivée.
28. zêta et ses paramètres (`Terminal/ZetaParameters.lean`) : zêta est engendrée par les premiers
   seuls, aucun paramètre ne dépend de la hauteur (`zeta_generated_by_primes`) ; monde témoin du
   changement de régime, fonction fixe sans paramètre, même miroir, même conjugaison, réelle sur
   la ligne, dont le régime change en montant (`regimeWitness`, `regimeWitness_mirror`,
   `regimeWitness_conj`, `regimeWitness_real_onLine`, `regimeWitness_zero_iff`,
   `regimeWitness_regime_changes`) ; la loi « seule la hauteur évolue » et la persistance du
   régime engagé, dérivées de la borne en `√x` du reste écrit avec les seuls premiers
   (`heightOnly_of_remainder_sqrt_growth`, `engaged_persists_of_remainder_sqrt_growth`).
29. la prémisse : aucun changement de régime n'est possible (`Terminal/NoRegimeChange.lean`) :
   zêta porte deux hauteurs distinctes et le régime vertical est engagé, théorèmes sans hypothèse
   (`exists_two_heights`, `exists_verticalPassage`, par la formule explicite prolongée en
   l'abscisse : `finiteSpectralExtension_real`, `finiteSpectralExtension_differentiableOn`) ;
   prémisse unique `PNoRegimeChange` ; clôture sans condition annexe
   (`riemannHypothesis_of_noRegimeChange`, `noRegimeChange_iff_riemannHypothesis`,
   `allVertical_of_noRegimeChange`) ; la prémisse lue sur un pas : `r' ≥ 1` compilé
   (`arrival_radial_ge_one`), `r' ≤ 1` ⟺ aucun changement de régime à l'arrivée
   (`arrival_radial_le_one_iff_regime_kept`), sous la prémisse `r' = 1`, aucun déplacement radial
   pendant la progression en hauteur (`noRegimeChange_no_radial_displacement`).
30. composition de la grammaire première et de la cinématique des Tours
   (`Terminal/GrammarKinematics.lean`, correction de l'auteur : composer avant de chercher
   `r' ≤ 1`) : position de l'occurrence dans sa Tour, découpée en part de hauteur et part radiale
   (`occurrencePosition_decomposed`) ; registre d'un passage : raccord (cinématique) + progression
   continue (grammaire) = déplacement de la position de l'occurrence (`passage_ledger`,
   `deltaT_from_ledger`, `passage_ledger_radial`) ; chaîne de passages (`ZeroChain`,
   `ZeroChain.ofPassages`, `ZeroChain.sourceIndex`, `ZeroChain.occurrence_eq`,
   `ZeroChain.gapClass6_alternates`) ; registre cumulé, sommation d'Abel, télescopage des termes
   radiaux (`chain_ledger`, `chain_grammar_sum`, `grammar_kinematics_abel`, `chain_raccordShift_eq`) ;
   alternance `2, 4` quantitative : `p_{n+2} ≥ p_n + 6`, plancher à deux pas `T·log(1 + 6/p_n)`
   (`goodMod6_two_step_ge_six`, `primeAtRank_two_step_ge_six`, `primeGapLogRatio_two_step_ge`,
   `chain_two_step_floor`) ; ce que la composition laisse à la position radiale : `T_l·log r_l` =
   écart entre la part déterminée et le déplacement réalisé, `r_l = 1` ⟺ écart nul
   (`diagonal_radial_from_ledger`, `arrival_onLine_iff_ledger_height_determined`,
   `required_eq_realised`). Borne : identité vraie pour toute position radiale, aucune borne
   inférieure sur `ΔT`, les positions radiales intérieures de la chaîne disparaissent.
   Paire hors ligne contre deux membres en ligne, sur le même registre (§6) : le pas grammatical est
   aveugle au régime (`grammar_step_regime_blind`) ; à même hauteur la phase décroît avec `β`
   (`sameHeight_phase_lt`), le raccord est une pure rotation de phase et la part de hauteur est nulle
   (`horizontal_raccordShift`, `horizontal_heightShift_zero`), la position de l'occurrence avance
   strictement plus que la grammaire ne demande (`horizontal_ledger`,
   `horizontal_ledger_exceeds_grammar`) ; entre deux membres en ligne l'écart est exactement la part de
   hauteur (`onLine_pair_ledger`, `off_pair_vs_onLine_pair`) ; autour d'une paire de même hauteur les
   deux événements premiers sont pesés à une seule hauteur, plancher `T·log(1 + 6/p)` conservé
   (`horizontal_two_step_single_height`). Borne : la différence des deux architectures est lue, non
   interdite ; la grammaire n'exige qu'un événement par passage, quel que soit le régime.
   Niveaux de rigidité de l'auteur, transition → deux transitions → alternance → chaîne (§7) : excès
   d'une transition `transitionExcess = Π(l) − Π(e) − ΔΘ_n = H + T_e log r_e − T_l log r_l`
   (`transitionExcess_eq`) ; en ligne → en ligne excès `= H`, diagonale partie de la ligne excès `< H`,
   même hauteur `H = 0` et excès `> 0` (`transition_kinematics_by_configuration`) ; somme des excès sur
   une chaîne = somme des `H` + `T_0 log r_0 − T_m log r_m` (`chain_transitionExcess_sum`) ; première
   configuration hors ligne autorisée par l'ordre (ligne → diagonale → même hauteur) : le déficit de la
   première transition est exactement remboursé par la seconde, somme des excès `= H(0,1) − T_2 log r_2`,
   `> H(0,1)` si l'arrivée est au-dessus de la ligne (`first_off_configuration_two_transitions`), et
   avec l'alternance `Π(2) − Π(0) > H(0,1) + T_0 log(1 + 6/p_n)`
   (`first_off_configuration_alternation_floor`) ; sur toute chaîne partie de la ligne le contenu
   radial est `−T_m log r_m` quelle que soit la longueur (`chain_from_line_radial_content`). Borne : à
   aucun nombre de transitions la liberté radiale n'est confrontée ; seul un énoncé sur `Π` le ferait.
31. E140, test de rupture spontanée du régime engagé (`Terminal/SpontaneousRegimeBreak.lean`,
   correction de l'auteur : chercher « en ligne engagé ⟹ en ligne », pas « hors ligne ⟹ faux ») :
   inventaire du départ, composante radiale nulle pour miroir, poussée horizontale, facteur radial,
   contacts, phase, pas du membre, fonction réelle (`engaged_departure_radial_zero`) ; la grammaire
   est fonction du rang seul (`grammar_event_reads_no_radial`) ; ce qui traverse le passage lit la
   position radiale de l'arrivée, neutre ⟺ arrivée en ligne (`arrival_radial_readings`) ; le
   générateur existe : depuis la ligne, hauteur et position radiale de l'arrivée sont fonction de la
   hauteur de départ seule (`engaged_successor_function`) ; test de l'auteur posé sur lui
   (`radial_generator_test`), récurrence compilée (`engaged_persists_of_generator_fixes_line`,
   `line_invariant_of_radial_preserving_law`) ; monde de contrôle aux mêmes premiers, un membre en
   ligne puis deux jumeaux plus haut (`engagedBreakWorld_line_then_twins`,
   `negLogDeriv_zeta_complex_shift`, `complex_shift_weight_ne_zero_iff`). Borne : aucun mécanisme
   de l'inventaire ne calcule le générateur ; « le générateur fixe la ligne » est la loi « seule la
   hauteur évolue », nécessaire (`radial_preserving_law_of_riemannHypothesis`), non dérivée.
32. réponse radiale aux poids premiers, candidat différentiel de E142, livrée sous le nom E141
   (`Terminal/PrimeWeightResponse.lean`, auteur : construire
   d'abord la famille, dériver ensuite ses coefficients premiers, suivre un zéro, comparer `dβ/dε` à
   `dT/dε`) : famille `ζ(s − ε·c)`, facteurs du monde de contrôle, `Z_0 = ζ`, coefficients
   `Λ(n)·n^{ε·c}` dérivés de la fonction (`weightFamily_primeWeights`), réponse des coefficients
   `Λ(n)·log n·c` (`weightFamily_weight_response`), chaque membre devient `ρ + ε·c`, réponse radiale
   `Re c`, réponse de hauteur `Im c` (`weightFamily_member_response`) ; réponse radiale nulle ⟺ module
   de chaque poids conservé (`weightFamily_radial_zero_iff_weight_modulus`) ; la direction verticale
   conserve la réflexion par rapport à la ligne (`vertical_direction_keeps_reflection`) ; toute
   direction réelle sur la ligne donne, sur un membre simple en ligne, une réponse radiale nulle au
   premier ordre et une réponse de hauteur `Φ(ρ)/Im Ξ'(ρ)` (`reflection_direction_response`,
   `engaged_member_reflection_response`) ; contrôle : même énoncé pour le membre en ligne de la
   fonction fixe sans premiers (`regimeWitness_reflection_response`). Borne : l'annulation vient de la
   réflexion et de la simplicité, pas des poids exacts ; elle porte sur un membre déjà en ligne ;
   existence de la courbe de zéros et théorème de Hamburger non compilés.
33. le résidu de changement et son prédicteur, E141 à E145 dans la numérotation finale de l'auteur
   (`Terminal/ChangePredictor.lean`) : E141, détecteur unique `D = X_réel − X_ligne = −T·log r`, le
   terme premier disparaît (`changeResidue_eq_position_sub`, `changeResidue_eq_radial`), toutes les
   représentations du changement équivalentes à `D = 0` (`change_detector`,
   `passage_change_detector`), fenêtre `−1/(2T) < D < 1/T` (`changeResidueAt_window`), équation du
   registre sur le résidu (`changeResidue_ledger`, `engaged_changeResidue_from_ledger`) ; E142, un
   prédicteur exact existe comme fonction de la hauteur de départ et du rang, par l'existence du
   générateur : la signature ne fait pas une prédiction (`predictor_exists`) ; prédicteur qui ne lit
   aucun zéro, l'exposant de croissance du reste arithmétique, exactitude E143 compilée
   (`changeResidue_enclosed_by_remainder_growth`) ; E144, évaluation à zéro sous la borne en `√x`
   (`changeResidue_zero_of_remainder_sqrt_growth`) ; E145, propagation (`predictor_closes`,
   `engaged_persists_of_predictor`) ; contrôles (`engagedBreakWorld_change_detected`,
   `regimeWitness_change_detected`). Bornes : « un prédicteur exact et nul dans l'état engagé
   existe » ⟺ la loi « seule la hauteur évolue » (`predictor_pair_iff_heightOnly`) ; « résidu nul
   partout » ⟺ borne en `√x` du reste (`changeResidue_vanishes_iff_remainder_sqrt_growth`), non
   dérivée.
   Le bit de changement (auteur : prédire seulement `D = 0` ou `D ≠ 0`, par une donnée disponible
   avant l'arrivée) : sur un passage vertical, `D = 0` ⟺ aucun membre hors ligne n'est atteint avant
   que la fonction réelle sur la ligne ne s'annule (`change_bit_iff_race`) ; un changement de signe
   fixe l'échéance de l'arrivée (`arrival_before_sign_change`). Non compilé : le comptage des
   membres dans la fenêtre.
   Avis de l'auteur : cette démarche n'est pas confirmée, le verrou est dans la flèche (point 34).
34. la flèche entre deux événements canoniques successifs (`Terminal/CanonicalTransition.lean`,
   retour à E140) : objet `CanonicalTransition` (départ engagé, rang + 1, premier partagé), existant
   sur tout passage parti de la ligne ; avant l'arrivée, la position du premier partagé dans la Tour
   de départ est sa position de ligne (`exit_position_fixed_by_departure`) ; dans la Tour d'arrivée,
   les écarts de position ne lisent que la hauteur (`tower_relative_position`) et la cellule d'entrée
   est celle de la Tour de ligne hors d'une marge de `1/(πT)` (`entry_cell_eq_line_cell_of_margin`) ;
   la composante radiale est portée par la position d'entrée du premier partagé, position de ligne
   plus `D/π` dans la fenêtre (`towerPosition_eq_line_add_residue`, `entry_position_window`,
   `entry_position_determines_radial`) ; le déplacement du premier partagé d'une Tour à l'autre est
   sa part de hauteur plus `D`, sans terme de grammaire (`transition_shared_prime_shift`). Borne :
   conservation ⟺ entrée à la position de ligne (`transition_conserves_iff_entry_position`),
   caractérisation ; la liaison lit la position d'entrée, elle ne la fixe pas.
35. verdict compilé sur l'énoncé de clôture de l'auteur (`Terminal/EngagedClosureVerdict.lean`) :
   miroir annulé ⟺ en ligne (`mirror_annulled_iff_onLine`) ; passage entre deux membres au miroir
   annulé sans mouvement radial et vertical (`engaged_passage_height_only`) ; mouvement radial ⟺ un
   membre hors ligne (`radial_motion_iff_off`) ; changement de régime ⟹ mouvement radial et jonction
   hors ligne (`regime_change_creates_radial_motion`) ; RH ⟺ loi de conservation + amorce
   (`riemannHypothesis_iff_conservation_and_base`) ; la loi est violée dans le monde témoin, qui a
   miroir, conjugaison et réalité sur la ligne (`conservation_not_structural`). La loi n'est pas dérivée.
   Portée corrigée : la cible locale (depuis l'état engagé, pas de changement de régime) est, sur un pas
   vertical, « l'arrivée reste en ligne » (`vertical_arrival_onLine_iff_no_regime_change`) ; elle n'est
   pas RH, elle ne la donne qu'avec l'amorce (`conservation_leaves_only_base`).
36. le verrou unique écrit exactement (`Terminal/EntryPositionArrow.lean`) : la flèche « le premier
   partagé entre dans la Tour d'arrivée à sa position de ligne » ⟺ loi locale de conservation sur la
   moitié supérieure (`entry_arrow_iff_upper_conservation`) ; RH ⟺ flèche + amorce
   (`riemannHypothesis_iff_entry_arrow_and_base`) ; forme événementielle : flèche ⟺ module du terme
   d'Euler du premier partagé au membre d'arrivée = `M^{−1/2}` (`local_euler_term_norm`,
   `entry_arrow_iff_local_euler_modulus`) ; le facteur d'Euler d'un premier ne s'annule en aucun membre
   (`local_euler_factor_ne_zero`, `local_euler_factor_at_member_ne_zero`) : il lit l'entrée, il ne la
   fixe pas seul. La flèche n'est pas démontrée. Contrôle E146 (`experiments/e146_*`).
37. premiers pointés, 300 ON contre 150 paires OFF (`Terminal/PointedPrimeComparison.lean`, E147) :
   occurrence, minimum attendu, états et classe modulo 6 sont des fonctions du rang seul
   (`pointed_primes_rank_only`, `pointed_gapClass6_rank_only`) ; position d'un premier dans une Tour
   `(β, T)` (`pointedPosition`, `towerPosition_eq_pointedPosition`) : même Tour = hauteur seule, même
   hauteur = translation rigide, même premier = hauteur + phase (`pointedPosition_step`,
   `pointedPosition_sameHeight_shift`, `pointedPosition_samePrime`) ; pas dans une paire sans part de
   hauteur, pas en ligne avec part de hauteur (`pair_step_position`, `line_step_position`). Lectures.
38. « un zéro = un premier » (`Terminal/OneZeroOnePrime.lean`, E148) : le premier d'un membre est le
   premier de rang « nombre de membres en dessous », étiquette de comptage (`occurrence_is_rank_label`) ;
   tout premier a sa cellule dans la Tour de tout membre (`every_prime_in_every_tower`) ; l'écart à la
   Tour de ligne est le même pour tout réel (`tower_offset_rigid`) ; en ligne ⟺ aucune translation de
   la grille (`onLine_iff_entry_at_point`, `onLine_iff_no_grid_translation`) ; la flèche ne dépend pas
   du premier partagé (`entry_arrow_point_irrelevant`). Réécriture ; verrou inchangé.
39. La Tour, grille infinie (`Terminal/TowerGrid.lean`, E149, audit d'impact) : toute Tour = Tour de ligne
   à sa hauteur translatée de `D/π` (`tower_grid_normal_form`) ; régime de ligne : une grille par hauteur
   (`onLine_grid_eq_iff_height_eq`) ; régime concurrent lu en tout point (`competing_regime_at_any_point`) ;
   passage = part de pas + part de translation (`passage_grid_decomposition`, `engaged_passage_translation`) ;
   transport plat ⟺ même position radiale (`energyRatio_flat_iff`) ; terme d'Euler de tout entier `n > 1`
   (`local_euler_modulus_point_irrelevant`). Caractérisations ; la translation n'est pas interdite.
40. Enroulement à indice fixé (`Terminal/TowerWinding.lean`, E151) : à `k ≥ 1` fixé, le contact décroît
   strictement avec la hauteur pour tout `β > 0`, les initiales des Tours plus hautes sont emboîtées dans
   celles des plus basses (`windingContact_strictAnti_height`, `windingSegment_nested`) ; à même hauteur,
   translation rigide sans enroulement (`windingContact_sameHeight`) ; fenêtre de hauteur d'une cellule
   fixée et cellule vide au-delà de `((k + 1)π + π/2)/log 2` (`cell_height_window`,
   `cell_empty_above_height`) ; tout réel traverse tout indice fixé (`contact_below_of_height`) ; contraction
   `T/T'` de l'indice (`windingContact_position`). Vrai pour toute position radiale : lecture de hauteur.
41. Hauteur → fréquence, position radiale → pente (`Terminal/RadialSlope.lean`, E150) : la position de Tour avance
   par la hauteur seule, le logarithme de l'amplitude par la position radiale seule (`member_coordinates_separate`,
   `amplitude_ratio_eq_rpow`) ; amplitude ramenée à `√x` constante ⟺ en ligne (`rescaled_amplitude_flat_iff`) ;
   membre déplacé de `d` : même hauteur, amplitude × `x^d` (`shifted_member_same_height`,
   `shifted_member_amplitude`) ; horizon `x ≥ (cT)^{1/d}` (`visibility_horizon`). Lecture de la pente, non fixée.
42. Routes de fermeture réunies (`Terminal/ClosureRoutes.lean`, E152) : transports orthogonaux `W` (hauteurs, phases)
   et `D` (positions radiales) (`vertical_transport_eq`, `radial_transport_log_slope`) ; pont : exposant `θ` du reste
   lissé ⟹ bande `[1 − θ, θ]`, `θ ≥ 1/2`, `|D| ≤ 2θ − 1` (`radial_strip_of_remainder_growth`,
   `remainder_exponent_ge_half`, `radial_transport_le_of_remainder_growth`) ; RH ⟺ `∀ ε, x^{1/2+ε}`
   (`riemannHypothesis_iff_remainder_growth_all_eps`) ; ancre miroir : RH ⟺ transports miroirs plats ⟺ tous plats
   (`riemannHypothesis_iff_mirror_transport_flat`, `riemannHypothesis_iff_all_transports_flat`) ; paquet de hauteur
   `x^β + x^{1−β} ≥ 2√x`, égalité ⟺ en ligne (`pair_amplitude_eq_critical_iff`), paquet nu sans les coefficients
   `m/(ρ(ρ+1))` ni les phases. Route `Λ → reste lissé de ψ → θ → β → D` (`Li` n'y figure pas). Caractérisations.
43. Exposant du reste encadré depuis les premiers (`Terminal/RemainderExponent.lean`, E153) : `Λ ≥ 0` et Chebyshev
   donnent `‖A(x)‖ ≤ C·x` (`smoothedVonMangoldtSum_norm_le_psi`, `trivialZeroSum_norm_le`,
   `smoothedRemainder_linear_growth`), d'où la bande fermée `0 ≤ β ≤ 1` et `|D| ≤ 1` par le pont
   (`radial_strip_from_primes`, `radial_transport_le_one_from_primes`) ; `θ* := inf` des exposants admissibles,
   `1/2 ≤ θ* ≤ 1` (`remainderExponent_mem_bracket`), RH ⟺ `θ* = 1/2` (`riemannHypothesis_iff_remainderExponent_eq_half`) ;
   anti-compensation exposant par exposant (lecture du pôle) : `max(β, 1 − β) ≤ θ*` (`mirror_pair_exponent_le`,
   `mirror_pair_exponent_le_remainderExponent`) ; positivité partagée : poids du monde témoin `≥ 2Λ(n) ≥ 0`
   (`shiftedWorld_weight_ge`), égal à celui de `ζ²` ⟺ `δ = 0` (`shiftedWorld_weight_eq_iff`). Borne : `θ* < 1` non dérivé.
44. Énergie quadratique (`Terminal/RemainderEnergy.lean`, E154) : diagonale arithmétique critique depuis les premiers,
   `Σ_{n≤x} Λ(n)² ≤ log x·ψ(x) ≤ (log 4 + 4)·x·log x` (`vonMangoldt_sq_sum_le_log_mul_psi`, `vonMangoldt_sq_sum_linear`) ;
   poids du témoin au carré `≥ 4Λ²`, égalité ⟺ `δ = 0` (`shiftedWorld_weight_sq_ge`, `shiftedWorld_weight_sq_eq_iff`) ;
   cellule de Tour = demi-tour du terme propre (`cell_width_eq`, `ownCellIncrement_eq`, `ownCellIncrement_abs_ge`) ;
   énergie propre par unité de largeur multipliée par `e^{(2β−1)π/T}` par cellule, plate ⟺ `β = 1/2`
   (`ownCellEnergyDensity_succ`, `ownCellEnergyDensity_flat_iff`, caractérisation vraie dans tout monde). Borne : le
   transfert énergie du reste → diagonale arithmétique n'est pas dérivé.
45. Lecture exacte de l'axe algébrique, sans `Li` (`Terminal/ExactAxisReading.lean`, E155) : écart entre deux premiers =
   différence des poids (`prime_gap_eq_weight_difference`) ; trois lectures du même écart, demi-tours par `T`, amplitude
   par `β`, énergie par `2β` (`exact_gap_three_readings`) ; télescopage, extrémités seules, ordre des écarts non lu
   (`chain_reading_telescopes`, `chain_reading_endpoint_only`, `chain_reading_gap_order_blind`), accumulation miroir
   `= log (q_m/q_0)^{2d}` (`mirror_chain_accumulation`) ; exposition au contact (`contact_energy_exposed`) ; diagonale
   aveugle aux signes : tout monde `±Λ` a même valeur absolue, même diagonale, même borne critique
   (`signedWorld_abs_weight`, `diagonal_sign_blind`, `signedWorld_diagonal_linear`). Borne : la diagonale ne contrôle pas
   le transfert (témoin de signes cohérents, E155).
46. Demande exacte d'une marche, réponse collective, diagonale et croisés, dette (`Terminal/CompensationRigidity.lean`,
   E137bis) : marche pure = poids du premier atteint moins l'avance du fond, écart lu par magnitude et classe
   (`pure_step_weight_sum`, `pure_step_demand`, `pure_step_demand_magnitude`) ; carré de la réponse = diagonale + croisés,
   croisés = somme hors diagonale, forcés par la demande, négatifs ⟺ diagonale > demande², nuls de signe pour des
   contributions alignées, diagonale invariante par changement de signes (`stepCross_eq_offDiagonal`,
   `response_sq_eq_diagonal_add_cross`, `stepCross_forced_by_demand`, `stepCross_neg_iff`, `stepCross_nonneg_of_aligned`,
   `stepDiagonal_sign_invariant`) ; un hors-ligne garde son poids dans toute représentation et force `θ* > 1/2`
   (`off_debt_visible_in_exponent`, `compensation_closure_verdict`). Borne : la rigidité de compensation est l'unicité
   spectrale ; `θ* = 1/2` ⟺ RH, non dérivé.
47. La grammaire comme suite de sollicitations (`Terminal/GrammarWordLoad.lean`, E157) : deux changements d'état
   consécutifs avancent de `6(a_n + a_{n+1} + 1)` (`alternating_two_step_gap`), retour d'état ⟺ avance multiple de `6`
   (`state_return_iff_two_step_mod6`) ; verrou des canaux A → B et B → A, différence fixée par les extrémités, au plus
   une unité (`abMinusBa_eq`, `ab_ba_channel_lock`, `ab_ba_channel_lock_abs_le_one`, `prime_ab_ba_channel_lock`) ; dette
   miroir d'un mot `= 4d·log(q_m/q_0)`, sur deux changements `4d·log(1 + 6(a + a' + 1)/p)`, non nulle ⟺ `d ≠ 0`
   (`mirror_word_energy_debt`, `alternating_two_step_mirror_debt`, `mirror_word_debt_pos_iff`). Borne : identités ; la
   dette d'un mot est fixée par ses extrémités, proportionnelle à la profondeur ; la grammaire est la même dans tout
   monde de même support.
48. La fenêtre minimale de changement de régime (`Terminal/RegimeWindow.lean`, E158) : la cellule occupe trois rangs
   au-delà de son départ et trois hauteurs pour quatre membres (`RegimeCell.rank_span`, `RegimeCell.heights_three_for_four`) ;
   lectures centrales d'une marche : même phase, amplitudes `(q/p)^{1/2 ∓ d}`, écart `2d·log(q/p)`
   (`RegimeCell.central_phase_advance_eq`, `RegimeCell.central_amplitude_readings`, `RegimeCell.central_amplitude_gap`) ;
   charge `log = d·(log(M₂/M₁) − log(M₃/M₂))`, impaire en `d`, bornée par `d` fois les écarts relatifs
   (`RegimeCell.log_charge_eq`, `log_rpow_neg_eq`, `RegimeCell.abs_log_charge_le`) ; contribution d'une paire miroir à
   la formule explicite paire en `d`, dérivée nulle en `0` (`mirrorPairTerm_even`, `mirrorPairTerm_first_order_blind`,
   `RegimeCell.central_pair_term`). Borne : identités ; le premier ordre en `d` n'existe que dans les lectures
   individuelles, le côté premier ne lit la profondeur qu'à l'ordre deux.
49. La paire miroir contre le double en ligne (`Terminal/PairCurvature.lean`, E159) : paire − double = terme en ligne ×
   courbure radiale réelle `2(cosh(d log q) − 1)`, de module `√q · 2(cosh(d log q) − 1)`, `≥ (d log q)²`, nulle ⟺
   `d log q = 0` (`pairOverDouble_eq`, `norm_pairOverDouble`, `radialCurvature_ge_sq`, `radialCurvature_eq_zero_iff`) ;
   toute lecture linéaire portée par `1 ≤ n ≤ X` sépare la paire du double d'au plus `2(cosh(d log X) − 1) Σ‖a_n‖√n`
   (`radialCurvature_mono`, `finite_horizon_separation_le`) ; défaut dans `q^ρ/ρ` = atome / point en ligne + corrections
   `≤ (q^{1/2+d} + q^{1/2−d})|d|/T²` (`pairDefect_zero`, `pairDefect_even`, `pairDefect_decomposition`,
   `inv_mirrorPoint_sub_le`, `pairDefect_sub_curvature_le`) ; paire en ligne serrée − double = terme en ligne ×
   `2(cos(h log q) − 1) ≤ 0`, signe opposé à la paire hors ligne (`lineSplitOverDouble_eq`, `lineSplitCurvature_bounds`,
   `regime_sign_of_curvature`). Borne : mesure de séparation ; un horizon fixé confond la paire et le double quand
   `d log X → 0`.
50. Les deux continuations de la configuration dégénérée et leur interaction (`Terminal/PairInteraction.lean`, E160) :
   changement d'interaction `Re(u·v̄)` de la continuation radiale ou verticale avec toute Tour = courbure réelle de la
   continuation × interaction du double avec cette Tour, pour toute famille finie (`interaction_change_radial`,
   `interaction_change_vertical`, `interaction_change_family`) ; paire en la profondeur (`pairOverDouble_even`,
   `interaction_change_even`) ; signes opposés entre continuations (`interaction_changes_opposite`) ; interaction du
   double avec une Tour de hauteur `T' ≠ T` = `q^{1+d'} cos((T − T') log q)`, de signe changeant arbitrairement loin
   (`referenceCross_eq`, `referenceCross_sign_changes`) ; seul terme de signe fixe : le terme propre
   (`self_energy_order`) ; courbure verticale `≥ −4`, radiale non bornée (`lineSplitCurvature_ge_neg_four`,
   `radialCurvature_unbounded`). Borne : identités valables pour toute famille de Tours, sans donnée arithmétique ;
   l'interaction ne sélectionne aucune continuation.
51. Les quatre secteurs autour d'un centre sur l'axe critique (`Terminal/LocalFourSectors.lean`) : toute paire invariante
   par la réflexion de l'axe critique, recentrée en son milieu, a un écart de carré réel (`pair_offset_sq_real`), `≥ 0`
   pour la paire miroir (axe arithmétique), `≤ 0` pour deux membres sur l'axe critique (`mirror_pair_offset_sq_nonneg`,
   `axis_pair_offset_sq_nonpos`) ; la paire recentrée est invariante par les deux réflexions et la symétrie centrale
   (`local_four_sector_symmetry`) ; les deux continuations du double ont le même centre et des carrés d'écart `d²`, `−h²`
   (`continuations_same_center`). Borne : classement d'un seul déplacement recentré, vrai dans tout monde qui a la
   réflexion ; ne porte pas sur la Tour entière (voir 52).
52. Table de symétrie de la Tour entière (`Terminal/TowerFourSectors.lean`, E161) : ramenée à l'échelle `√x`, la Tour est
   `a e^{d u} e^{i(T u − φ)}` (`rescaledTower_eq`) ; opposition centrale = avance d'un demi-tour, réflexions = lectures à
   rebours, indices `k ↦ k + 1, −k, 1 − k` (`towerCurve_central`, `towerCurve_arith_reflect`, `towerCurve_crit_reflect`,
   `contact_index_rules`) ; invariance par chacune ⟺ en ligne (`tower_central_invariant_iff`, `tower_arith_invariant_iff`,
   `tower_crit_invariant_iff`), jamais dans le plan brut (`raw_tower_not_centrally_invariant`) ; seule l'opposition
   centrale conserve l'ordre ; réflexion lue en avant = Tour du conjugué ; hors ligne, échange de profondeur
   (`reflection_forward_is_conjugate`, `arith_reflect_exchanges_depth`). Borne : certificat de la position radiale du
   membre donné ; ne fixe pas la Tour suivante.
53. Trajectoire d'une Tour et boucle miroir remise dans l'ordre arithmétique (`Terminal/MirrorLoop.lean`, E162) : la Tour
   est une trajectoire le long de `u = log x`, `Γ' = (ρ − 1/2)·Γ` (`pointCurve_hasDerivAt`), vitesse angulaire = hauteur,
   taux radial = profondeur ; rayon croissant ⟺ `β > 1/2`, décroissant ⟺ `β < 1/2`, constant ⟺ `β = 1/2`
   (`pointCurve_norm_lt_iff`, `pointCurve_norm_gt_iff`, `pointCurve_norm_eq_iff`) ; boucle (conjugaison puis lecture à
   rebours) : `conj Γ_ρ(−u) = g(ρ)·Γ_{ρ*}(u)`, `g = (1 − ρ̄)/ρ̄` (`mirrorLoop_eq`), `‖g‖ = 1 ⟺ β = 1/2`
   (`norm_loopGauge_eq_one_iff`, `one_lt_norm_loopGauge_iff`), même Tour en ligne, Tour du membre miroir hors ligne
   (`mirrorLoop_onLine`, `mirrorLoop_offLine`, `mirrorLoop_target_isZero`) ; niveau collectif : sur toute famille stable
   par la réflexion, mêmes exposants, coefficients `1/(1 − σ)` (`mirrorLoop_family`), différents de `1/σ` en ligne
   compris, de même module ⟺ en ligne (`loop_coefficient_ne`, `loop_coefficient_norm_eq_iff`). Borne : la boucle
   permute les membres d'une paire miroir ; l'unicité spectrale y lit la stabilité de l'ensemble, pas l'invariance de
   chaque membre ; vrai mot pour mot dans le monde décalé ; l'étalon de boucle est un certificat.
54. Canal antisymétrique d'une paire miroir et côté arithmétique (`Terminal/MirrorAntisymmetry.lean`, E163) : Tour du
   membre moins Tour du miroir, nulle en ligne, impaire par échange, non nulle hors ligne (`pairAntisym_onLine`,
   `pairAntisym_swap`, `pairAntisym_ne_zero_of_offLine`) ; sur toute famille stable, expression originale = expression
   miroir pour tout poids (`mirror_sum_reindex`, `mirror_antisym_collective_zero`) ; poids impair par la réflexion nul
   sur la ligne, poids holomorphe impair nul (`mirror_odd_weight_zero_on_line`, `mirror_odd_entire_weight_zero`) ;
   différence originale − boucle = poids non nul sur la ligne (`loop_difference_onLine_ne_zero`) ; toute paire hors
   ligne : canal collectif nul pour tout poids, canal de Tour non nul (`antisym_channel_not_forced`). Borne : le côté
   arithmétique n'a qu'un canal symétrique ; l'absence d'observable ne force pas la fusion.
55. Variation quadratique locale, paire séparée contre référence fusionnée (`Terminal/QuadraticVariation.lean`) :
   variation = excès propre + 2 × interaction de l'atome avec le complément (`windowVariation_split`) ; excès propre
   ponctuel `q(4κ + κ²) ≥ 0`, nul ⟺ courbure nulle (`pair_self_excess_eq`, `pair_self_excess_eq_zero_iff`,
   `window_self_excess_nonneg`) ; le reste total fixé, le complément s'élimine exactement : variation = 2 × lecture du
   reste par l'atome − énergie de l'atome (`windowVariation_via_remainder`, `complement_cross_eq_remainder_cross`) ;
   lecture = courbure × interaction du terme en ligne de hauteur `T` avec le reste (`remainder_cross_curvature`), paire
   en la profondeur (`remainder_cross_even`), non fixée par l'algèbre (`cross_term_unconstrained`). Borne : le terme
   croisé ne s'annule pas et n'a pas de signe forcé ; il est la lecture du reste arithmétique à la fréquence de la paire.
56. Champ du premier zéro en ligne (`Terminal/FirstZeroField.lean`, auteur) : amplitude de Tour `x^β/‖ρ‖`
   (`norm_zeroTerm_eq`) ; tout zéro en ligne au moins aussi haut est dans le champ (`inside_field_of_onLine`) ; un zéro
   et son miroir dans le champ d'un zéro en ligne sont en ligne (`exponent_le_of_inside`, `inside_field_forces_line`) ;
   aucun zéro hors du champ ⟹ RH (`riemannHypothesis_of_first_field`) ; pour le premier zéro en ligne, « aucun zéro ne
   dépasse son champ » ⟺ RH (`first_field_iff_riemannHypothesis`) ; enroulement à indice fixé pour toutes positions
   radiales dès un écart de hauteur (`prime_axis_nesting_any_depth`).
57. β fixé, amplitude constante (`Terminal/FixedExponentField.lean`, auteur) : rapport d'une Tour au champ = une seule
   puissance de `x`, d'exposant fixé `β_w − β₁` (`tower_field_ratio`) ; même β que le premier zéro ⟹ dans le champ
   (`inside_field_of_same_exponent`), même β pour tous ⟹ RH (`riemannHypothesis_of_same_exponent`) ; un β fixé plus grand
   sort du champ sans changer le long de la Tour (`fixed_exponent_escapes`) ; témoin sans paramètre, premier zéro en
   ligne, Tour de β = 3/4 fixé hors du champ en `x = 16` (`regimeWitness_fixed_exponent_escapes`).
   Chaque Tour prisonnière de la précédente (`TowerPrisoner`) : β ne monte pas sur le passage, la hauteur avance
   (`prisoner_exponent_le`, `prisoner_forces_height`) ; hauteur qui avance sur tout passage ⟹ RH
   (`riemannHypothesis_of_height_always_advances`) ; toutes prisonnières ⟺ RH (`prison_iff_riemannHypothesis`).
58. Financement de l'évasion par le reste exact (`Terminal/EscapeFinancing.lean`, auteur) : une Tour d'exposant plus
   grand dépasse tout multiple du champ (`escape_exceeds_any_multiple`) ; toute borne du reste exact est un mur pour
   chaque Tour (`tower_captive_of_remainder_wall`) ; une Tour d'exposant `β` oblige le reste à dépasser tout `C·x^θ`,
   `θ < β` (`escape_must_be_financed`) ; depuis les poids exacts (positivité, Chebyshev) le mur démontré est `x¹`, il
   couvre le besoin de toute Tour (`financing_ledger`). Règle minimale (`RemainderCaptive`) : le reste exact captif d'une
   Tour et de son miroir ; un seul côté ⟹ Tour au sommet (`captive_one_side_summit`) ; deux côtés ⟹ Tour en ligne, RH
   (`remainderCaptive_onLine`, `riemannHypothesis_of_remainderCaptive`) ; ⟺ RH
   (`remainderCaptive_iff_riemannHypothesis`) ; prison de chaque Tour (`prison_of_remainderCaptive`).
59. Hiérarchie de Tour à Tour, raccord par raccord (`Terminal/TowerHierarchy.lean`, correction de l'auteur : l'objet est
   la dynamique relative de deux Tours successives, pas le reste entier contre la première Tour) : deux Tours en ligne,
   la plus haute est plus faible partout d'un rapport constant, de pas plus petit, de phase plus rapide
   (`onLine_tower_hierarchy`) ; hiérarchie au raccord (`RaccordHierarchy`) : tient sur tout passage où la hauteur avance,
   quelles que soient les positions radiales (`raccordHierarchy_of_height_advance`), force la hauteur à avancer
   (`raccordHierarchy_forces_height`), violée sur ses deux lectures par le passage de même hauteur
   (`sameHeight_breaks_hierarchy`) ; au raccord qui quitte un membre engagé la hauteur avance et la hiérarchie tient (`raccordHierarchy_of_engaged_departure`) ; propagation depuis l'état engagé (`engaged_step_of_next_hierarchy`) ; à tous les
   raccords ⟺ RH, enveloppe de la première Tour (`raccordHierarchy_iff_riemannHypothesis`,
   `first_tower_envelope_of_raccordHierarchy`).
60. Ce que les seuls paramètres fixent, horizon de la première Tour (`Terminal/FirstTowerHorizon.lean`) : la comparaison
   de deux Tours en un point est une inégalité entre positions radiales et supports (`tower_le_iff_parameters`,
   `tower_surpasses_iff_parameters`) ; position radiale non supérieure et support non inférieur ⟹ dans le champ pour
   toujours (`inside_field_of_parameters`) ; sur la ligne, ordre des énergies = ordre des hauteurs
   (`onLine_energy_order_iff_height`) ; horizon garanti `(‖ρ_w‖/‖ρ₁‖)²`, borne uniforme qui remplace la vraie position
   radiale par le pire cas `β_w < 1`, pas l'horizon de la Tour (`tower_inside_below_horizon`, `tower_inside_of_height`) ;
   de tout membre et de son miroir, le membre bas est dans le champ pour toujours (`mirror_pair_has_prisoner`,
   `lower_member_prisoner`) ; membre haut `β_w = 1/2 + δ` : rapport `x^δ·‖ρ₁‖/‖ρ_w‖`, évasion ⟺ `x^δ > ‖ρ_w‖/‖ρ₁‖`, horizon
   exact `(‖ρ_w‖/‖ρ₁‖)^{1/δ}` au moins l'horizon garanti ; un exposant `1/2 + δ` interdit toute borne globale du reste
   d'exposant inférieur (lecture asymptotique globale, sans raccord ni Tour précédente)
   (`upper_member_ratio`, `upper_member_escapes_iff`, `upper_member_exact_horizon`, `uniform_horizon_le_exact`,
   `upper_member_gain_must_be_financed`). Modules individuels seuls : ni poids, ni phases, ni reste.
61. La double rigidité sur un passage (`Terminal/DoubleRigidity.lean`) : liaison premiers–Tour, `M^Z = M`, premier
   partagé premier, poids de von Mangoldt `log M`, formule tangentielle, registre (`prime_tower_bond`,
   `passage_prime_tower_bond`) ; écarts reproduits par la hauteur seule, lecture identique ⟺ même hauteur
   (`gap_reading_height_only`, `gap_readings_agree_iff_height`, `height_recovered_from_gap_reading`) ; la hauteur qui
   avance fait concourir tous les paramètres (`height_advance_concurs`, `vertical_passage_concurs`) ; sur un passage de
   même hauteur les deux rigidités tiennent et la Tour d'arrivée sort (`sameHeight_satisfies_both_rigidities`), modèle
   de paramètres sans zéro (`parameter_model_twin_escapes`) ; « aucun passage de même hauteur » ⟺ RH
   (`no_sameHeight_iff_riemannHypothesis`). Sonde hors build `experiments/double_rigidity_probe/` : l'énoncé sans
   prémisse laisse un but ouvert, `False` sur le passage de même hauteur.
62. Captivité locale au raccord exact, renouvelée de raccord en raccord (`Terminal/LocalRaccordCaptivity.lean`) : rapport de
   deux Tours successives `x^{β_l − β_e}·‖ρ_e‖/‖ρ_l‖` (`successive_tower_ratio`) ; captivité locale définie par l'énergie
   seule au premier de l'événement, sans l'orientation du raccord ; budget local, Tour d'arrivée sous la Tour de départ ⟺
   coût de sortie `(β_l − β_e)·log x` ≤ disponible `log ‖ρ_l‖ − log ‖ρ_e‖` (`tower_le_iff_local_budget`,
   `localCaptivity_iff_budget`) ; position radiale qui ne monte pas, hauteur qui ne recule pas : disponible possiblement
   négatif, excédent `(β_e − β_l)·(log 2 − 1/4)` (`radial_descent_budget_surplus`) ; la hauteur avance : captivité par le
   budget seul (`height_advance_local_budget`) ; même hauteur `T ≥ 2` : coût − disponible ≥ `(β_l − β_e)·(log 2 − 1/4)`,
   captivité locale fausse (`sameHeight_budget_deficit`, `sameHeight_local_budget_refuted`) ; captivité locale ⟺ la hauteur
   avance, les deux sens par le budget (`local_captivity_computed`) ; identification avec l'orientation du raccord, théorème
   séparé (`localCaptivity_iff_oriented`) ; loi répétée le long d'une chaîne, dont le produit des pas vaut au moins 1 : ni
   décroissance cumulée ni prison globale (`zeroTerm_norm_transport`, `captivity_renewed_along_chain`,
   `chain_interior_steps_ge_one`) ; transition première exacte (`ExactPrimeTransition`, `exactPrimeTransitionOf`) : événement
   complet, poids exact, histoire, incrément exact du reste, position de phase, registre, rapport d'énergie, existante sur
   tout passage ; sur le passage de même hauteur elle existe et l'énergie est renversée
   (`sameHeight_exactPrimeTransition_reversed`) ; le lemme cible « même hauteur + transition exacte ⟹ captivité » ⟺ « aucun
   passage de même hauteur » (`sameHeight_capture_target_iff`). Sonde hors build
   `experiments/local_raccord_captivity_probe/` : le lemme cible laisse un but ouvert, l'inégalité du budget, avec sa
   négation et tous les champs de la transition en contexte.
63. Plancher radial de l'arrivée depuis un départ engagé (`Terminal/EngagedRadialFloor.lean`, revue de l'auteur) : l'arrivée
   hypothétique à exclure d'abord est `(T, 1/2) → (T', β' < 1/2)`, `T' > T` (aucune « diagonale » dans zêta : seuls `β` et
   `T`, réalignement de l'auteur), le passage de même hauteur ne vient qu'après ; depuis un départ engagé, `β_l ≤ 1/2` est acquis et arrivée en ligne ⟺ `1/2 ≤ β_l`
   (`engaged_arrival_onLine_iff_radial_floor`) ; le seul plancher compilé sur une arrivée lit le passage suivant
   (`arrival_radial_floor_iff_next_vertical`) ; une arrivée translatée porterait la transition première exacte
   entière, un coût de sortie strictement négatif, le budget tenu avec excédent et la captivité locale
   (`translated_arrival_complete_and_captive`) ; lemme cible « départ engagé + transition exacte ⟹ plancher » ⟺ loi locale
   de conservation depuis l'état engagé (`engaged_radial_floor_target_iff`) ; plancher ⟺ « seule la hauteur évolue »
   (`radial_floor_iff_heightOnly`), nécessaire (`radial_floor_of_riemannHypothesis`) ; sous le plancher le régime engagé
   perdure (`engaged_persists_of_radial_floor`). Sonde hors build `experiments/engaged_radial_floor_probe/` : le lemme
      atomique laisse un but ouvert, `1/2 ≤ β_l`, avec toute la transition et `β_l ≤ 1/2` en contexte.
64. Enroulement imposé, captivité au raccord, succession : la translation de la grille d'arrivée
   (`Terminal/EngagedNoTranslation.lean`, réalignement de l'auteur) : cible = « enroulement + captivité + succession ⟹
   grille d'arrivée non translatée », pas un plancher radial isolé ; composition des théorèmes compilés (succession,
   premier de référence croissant, pas contracté, captivité locale, facteur radial, contacts = annulations de la partie
   imaginaire) sur le même pas (`engaged_step_combined`) ; trois lectures de la translation
   (`grid_translation_readings`) ; `WindingNested`, emboîtement des contacts d'indice `k ≥ 1` ; deux Tours en ligne
   emboîtées (`windingNested_of_onLine`, `lineContact_strictAnti_height`) ; depuis un départ en ligne, emboîtement ⟺
   borne de la translation indice par indice (`windingNested_iff_translation_bound`) ; emboîtement perdu ⟹ grille
   translatée (`translation_of_not_nested`) ; profondeur suffisante ⟹ emboîtement pour toutes positions radiales
   (`windingNested_index_of_depth`) ; fenêtre de la translation capturée (`engaged_nested_translation_window`) ; loi
   locale de conservation ⟺ emboîtement sur tout pas engagé ∧ flèche de non-translation
   (`conservation_iff_nested_and_noTranslation`). Sonde hors build `experiments/engaged_no_translation_probe/` : la
      flèche laisse un but ouvert, facteur radial `= 1`, avec la fenêtre et toute la composition en contexte. Paramètre de
   l'auteur (la Tour s'enroule en laissant la place à la suivante et à toutes les autres) : plancher commun
   (`contact_gt_one`), emboîtement transmis (`windingNested_trans`), espace borné des deux côtés (`tower_room_two_sided`,
   `translation_room_two_sided`) ; la Tour suivante s'enroule ⟺ grille non translatée (`no_translation_iff_next_winds`,
   `next_winding_forces_no_translation`) ; une Tour de même hauteur prend sa place par translation, sans enroulement
   (`sameHeight_successor_translates_inward`) ; enroulement à tous les pas ⟺ RH
   (`winding_to_infinity_iff_riemannHypothesis`). Portée (revue de l'auteur) : l'enroulement de la Tour suivante est une
   hypothèse de ces énoncés, non dérivé ; flèche à démontrer = transmission de la contraction (pas `n` ⟹ pas `n + 1`) ;
   sonde hors build `experiments/contraction_transmission_probe/` : sans prémisse, un but ouvert sur le cas où la
   hauteur n'avance pas au pas suivant (EXIT=1).
65. La Tour bloquée par le haut et par le bas par TOUTES les autres (`Terminal/TowerTwoSidedRoom.lean`, auteur) :
   objet `TowerRoom` (dans toute Tour qui précède, toute Tour qui suit en elle) ; nécessaire sous RH
   (`towerRoom_of_riemannHypothesis`) ; encadrement (`towerRoom_squeeze`) ; le miroir d'un membre bas le suit, en lui,
   pas inchangé (`mirror_takes_room_below`) ; monde des paramètres à paire miroir où chaque Tour a sa place
   (`room_parameter_model_with_mirror_pair`) ; capture renouvelée au raccord SUIVANT ⟺ grille d'arrivée non translatée
   (`renewed_captivity_iff_no_translation`). Sondes hors build `experiments/tower_two_sided_room_probe/` (EXIT=1) :
   place de toute Tour non dérivée (deux buts, écart de hauteur insuffisant) ; place ⟹ non-translation non dérivée ;
   capture du raccord suivant non dérivée (but `LocalCaptivity q` avec `¬ LocalCaptivity q` en contexte, cas de même
   hauteur).
65bis. Enroulement à l'infini de TOUTES les Tours, sans prémisse (`windingNestedAtInfinity_of_precedes`,
   `towerRoomAtInfinity`) : à partir d'un indice, toute Tour qui en suit une s'enroule en elle ; la sonde 1 est fermée
   avec cet énoncé ; l'énoncé à tout `k ≥ 1` reste non dérivé ; ce théorème vaut pour toute assignation radiale.
66. Transport individuel et évasion à un premier (`Terminal/PersistentCapture.lean`, revue de l'auteur) : la persistance
   d'une Tour est l'identité de transport (`spectral_organism_member`, `zeroTerm_norm_transport`), reprise par
   `transported_energy_ratio` ; un passage de même hauteur sort de la Tour de départ en un premier futur
   (`horizontal_escape_at_prime`) ; l'inégalité `PersistentCapture` est de type RH (nécessaire sous RH, partout ⟹ RH),
   elle n'est pas la loi de persistance et n'est pas à démontrer comme telle. Sonde hors build
   `experiments/persistent_capture_probe/` (EXIT=1) : sans prémisse, `¬ HorizontalPassage q` au pas suivant le pas
   engagé laisse le but `False`, avec en contexte le pas engagé, l'évasion individuelle en un premier et la
   reconstruction collective en ce premier (non contredite : elle porte sur la somme de tous les zéros).
   Seconde sonde `NextStepGrammarProbe.lean` (EXIT=1) : avec en plus l'alternance `2, 4` (`primeAtRank_two_step_ge_six`),
   la progression grammaticale, le registre (`passage_ledger`, `horizontal_ledger`, `horizontal_ledger_exceeds_grammar`) et
   le pas grammatical aveugle au régime (`grammar_step_regime_blind`), le but reste `False` : la grammaire fixe `T·log(rapport)`
   avec `T` la hauteur du pas, et `horizontal_two_step_single_height` la satisfait à une seule hauteur.

-/

#print axioms RHV6Fresh.firstTower_cell_contains_expected
#print axioms RHV6Fresh.towerRoomAtInfinity
#print axioms RHV6Fresh.transported_energy_ratio
#print axioms RHV6Fresh.horizontal_escape_at_prime
#print axioms RHV6Fresh.persistent_exponent_le
#print axioms RHV6Fresh.horizontal_escapes_beyond_horizon
#print axioms RHV6Fresh.persistent_next_forces_no_translation
#print axioms RHV6Fresh.riemannHypothesis_of_persistent
#print axioms RHV6Fresh.expectedMinimumPrime_injective
#print axioms RHV6Fresh.consecutivePairArithmeticChain
#print axioms RHV6Fresh.passage_direction_rigid
#print axioms RHV6Fresh.zeroTerm_norm
#print axioms RHV6Fresh.explicitSum_reindex_invariant
#print axioms RHV6Fresh.towerRaccordOf
#print axioms RHV6Fresh.towerRaccord_eq
#print axioms RHV6Fresh.towerRaccord_oriented_of_vertical
#print axioms RHV6Fresh.towerRaccord_reverses_of_sameHeight
#print axioms RHV6Fresh.off_towerRaccord_reverses
#print axioms RHV6Fresh.towerRaccord_oriented_of_riemannHypothesis
#print axioms RHV6Fresh.towerRaccord_oriented_of_height_lt
#print axioms RHV6Fresh.towerRaccord_oriented_iff_height_lt
#print axioms RHV6Fresh.fibre_transport_product_off
#print axioms RHV6Fresh.fibre_charge_eq_one_iff
#print axioms RHV6Fresh.shiftedWorld_pair_off
#print axioms RHV6Fresh.shiftedWorld_negLogDeriv
#print axioms RHV6Fresh.reconstructedEvent_eq_primalEvent
#print axioms RHV6Fresh.primalEvent_certificate
#print axioms RHV6Fresh.grammaticalRaccordOf
#print axioms RHV6Fresh.grammaticalRaccord_eq
#print axioms RHV6Fresh.passage_history_step
#print axioms RHV6Fresh.memberStep_eq_one_iff
#print axioms RHV6Fresh.history_transport_product
#print axioms RHV6Fresh.historyCharge_const_one_iff
#print axioms RHV6Fresh.off_grammaticalRaccord_complete_and_reversed
#print axioms RHV6Fresh.passage_separated_by_window_iff
#print axioms RHV6Fresh.shiftedWorld_reconstructs_no_prime
#print axioms RHV6Fresh.grammaticalRaccord_environment
#print axioms RHV6Fresh.spectral_organism_member
#print axioms RHV6Fresh.spectral_organism_reconstructs
#print axioms RHV6Fresh.remainder_increment_at_prime
#print axioms RHV6Fresh.zeroTerm_hasDerivAt
#print axioms RHV6Fresh.off_pair_density_exceeds_line
#print axioms RHV6Fresh.grammaticalRaccord_M_injective
#print axioms RHV6Fresh.primalEvent_charge_by_gaps
#print axioms RHV6Fresh.globalRigidSystem
#print axioms RHV6Fresh.off_inside_globalRigidSystem
#print axioms RHV6Fresh.off_conserves_three_equalities
#print axioms RHV6Fresh.channel_eq_packet_add_complement
#print axioms RHV6Fresh.psi_eq_background_add_packet_add_complement
#print axioms RHV6Fresh.compensation_eq_complement
#print axioms RHV6Fresh.compensation_realized_for_all_x
#print axioms RHV6Fresh.compensation_difference
#print axioms RHV6Fresh.eventCompensation_eq_complement
#print axioms RHV6Fresh.off_packet_explicit
#print axioms RHV6Fresh.off_forced_compensation
#print axioms RHV6Fresh.arithmetic_eq_spectral
#print axioms RHV6Fresh.remainderBetween_arithmetic
#print axioms RHV6Fresh.remainderBetween_eq_spectral
#print axioms RHV6Fresh.remainderBetween_eq_packet_add_complement
#print axioms RHV6Fresh.complementBetween_forced
#print axioms RHV6Fresh.off_inverse_reading
#print axioms RHV6Fresh.passage_regime_dichotomy
#print axioms RHV6Fresh.vertical_regime
#print axioms RHV6Fresh.horizontal_regime
#print axioms RHV6Fresh.junction_vertical_vertical
#print axioms RHV6Fresh.junction_vertical_horizontal
#print axioms RHV6Fresh.junction_horizontal_vertical
#print axioms RHV6Fresh.regimeChange_offLine
#print axioms RHV6Fresh.onLine_keeps_regime
#print axioms RHV6Fresh.off_forces_regime_entry
#print axioms RHV6Fresh.allVertical_iff_riemannHypothesis
#print axioms RHV6Fresh.riemannHypothesis_iff_no_regimeEntry
#print axioms RHV6Fresh.passage_split_by_regime
#print axioms RHV6Fresh.towerPitch_lt_iff
#print axioms RHV6Fresh.rigid_translation_of_sameHeight_radial_lt
#print axioms RHV6Fresh.no_rigid_translation_of_height_ne
#print axioms RHV6Fresh.horizontal_iff_tower_translation
#print axioms RHV6Fresh.vertical_iff_pitch_contracts
#print axioms RHV6Fresh.vertical_iff_no_tower_translation
#print axioms RHV6Fresh.regime_entry_read_on_towers
#print axioms RHV6Fresh.onLine_horizontal_push_zero
#print axioms RHV6Fresh.onLine_passage_vertical
#print axioms RHV6Fresh.onLine_passage_vertical_signature
#print axioms RHV6Fresh.onLine_exit
#print axioms RHV6Fresh.onLine_entry
#print axioms RHV6Fresh.cpow_finite_independent
#print axioms RHV6Fresh.no_member_removable
#print axioms RHV6Fresh.no_finite_intruder
#print axioms RHV6Fresh.zeroTerm_profile_injective
#print axioms RHV6Fresh.horizontal_term_phase_lock
#print axioms RHV6Fresh.horizontal_pivot_shift
#print axioms RHV6Fresh.RegimeCell.central_mirror
#print axioms RHV6Fresh.RegimeCell.pitch_signature
#print axioms RHV6Fresh.RegimeCell.contact_signature
#print axioms RHV6Fresh.RegimeCell.charge_reads_translation
#print axioms RHV6Fresh.RegimeCell.charge_ne_one
#print axioms RHV6Fresh.RegimeCell.remainder_record
#print axioms RHV6Fresh.RegimeCell.not_riemannHypothesis
#print axioms RHV6Fresh.mellin_vanish
#print axioms RHV6Fresh.cpow_series_fibre_sum_zero
#print axioms RHV6Fresh.cpow_series_unique
#print axioms RHV6Fresh.spectral_weights_unique
#print axioms RHV6Fresh.SpectralRepresentation.contains_member
#print axioms RHV6Fresh.SpectralRepresentation.no_intruder
#print axioms RHV6Fresh.SpectralRepresentation.recovers_member
#print axioms RHV6Fresh.SpectralRepresentation.off_identity_not_erased
#print axioms RHV6Fresh.riemannHypothesis_iff_onLine_representation
#print axioms RHV6Fresh.engaged_regime_kept
#print axioms RHV6Fresh.vertical_arrival_characterizes
#print axioms RHV6Fresh.vertical_pure_iff_onLine
#print axioms RHV6Fresh.diagonal_iff_off
#print axioms RHV6Fresh.regime_entry_diagonal
#print axioms RHV6Fresh.regime_entry_from_line
#print axioms RHV6Fresh.fibre_multiple_iff_off
#print axioms RHV6Fresh.vertical_arrival_onLine_iff_fibre_singleton
#print axioms RHV6Fresh.vertical_departure_onLine_iff_fibre_singleton
#print axioms RHV6Fresh.riemannHypothesis_iff_fibres_singleton
#print axioms RHV6Fresh.riemannHypothesis_iff_no_diagonal
#print axioms RHV6Fresh.completedZeta_real_onLine
#print axioms RHV6Fresh.onLine_zero_iff_lineValue
#print axioms RHV6Fresh.fibre_has_onLine_member_iff
#print axioms RHV6Fresh.lineValue_ne_zero_fibre_off
#print axioms RHV6Fresh.onLine_member_of_sign_change
#print axioms RHV6Fresh.lineWholeEquiv
#print axioms RHV6Fresh.lineWhole_channel_by_height
#print axioms RHV6Fresh.remainder_eq_lineWhole_add_deviation
#print axioms RHV6Fresh.lineDeviation_arithmetic
#print axioms RHV6Fresh.lineDeviation_not_absorbed
#print axioms RHV6Fresh.lineDeviation_vanishes_iff
#print axioms RHV6Fresh.off_member_deviates
#print axioms RHV6Fresh.riemannHypothesis_iff_remainder_eq_lineWhole
#print axioms RHV6Fresh.regime_entry_packet
#print axioms RHV6Fresh.regime_entry_recorded
#print axioms RHV6Fresh.contact_eq_line_mul_radial
#print axioms RHV6Fresh.radialFactor_eq_one_iff
#print axioms RHV6Fresh.radialFactor_gt_one_iff
#print axioms RHV6Fresh.radialFactor_lt_one_iff
#print axioms RHV6Fresh.height_determined_radial_blind
#print axioms RHV6Fresh.radial_sensitive_not_height_determined
#print axioms RHV6Fresh.contacts_height_determined_iff_onLine
#print axioms RHV6Fresh.vertical_exhausts_iff_arrival_onLine
#print axioms RHV6Fresh.lineValue_ne_zero_between
#print axioms RHV6Fresh.lineValue_sign_constant_between
#print axioms RHV6Fresh.diagonal_from_line_ledger
#print axioms RHV6Fresh.regime_entry_diagonal_ledger
#print axioms RHV6Fresh.engagedState_iff_onLine
#print axioms RHV6Fresh.passage_successor_unique
#print axioms RHV6Fresh.engaged_successor_determined_by_height
#print axioms RHV6Fresh.one_le_radialFactor_of_le_half
#print axioms RHV6Fresh.engaged_progression
#print axioms RHV6Fresh.engaged_propagates
#print axioms RHV6Fresh.vertical_arrival_written_in_arithmetic
#print axioms RHV6Fresh.engaged_linked_production
#print axioms RHV6Fresh.regime_change_requires_radial
#print axioms RHV6Fresh.heightOnly_step
#print axioms RHV6Fresh.engaged_persists_to_infinity
#print axioms RHV6Fresh.heightOnly_of_riemannHypothesis
#print axioms RHV6Fresh.cpow_series_growth_fibre_zero
#print axioms RHV6Fresh.smoothedRemainder_growth_bounds_zero
#print axioms RHV6Fresh.radial_le_of_remainder_growth
#print axioms RHV6Fresh.riemannHypothesis_iff_remainder_sqrt_growth
#print axioms RHV6Fresh.zeta_generated_by_primes
#print axioms RHV6Fresh.regimeWitness_regime_changes
#print axioms RHV6Fresh.heightOnly_of_remainder_sqrt_growth
#print axioms RHV6Fresh.engaged_persists_of_remainder_sqrt_growth
#print axioms RHV6Fresh.exists_two_heights
#print axioms RHV6Fresh.exists_verticalPassage
#print axioms RHV6Fresh.riemannHypothesis_of_noRegimeChange
#print axioms RHV6Fresh.noRegimeChange_iff_riemannHypothesis
#print axioms RHV6Fresh.allVertical_of_noRegimeChange
#print axioms RHV6Fresh.arrival_radial_ge_one
#print axioms RHV6Fresh.arrival_radial_le_one_iff_regime_kept
#print axioms RHV6Fresh.noRegimeChange_no_radial_displacement
#print axioms RHV6Fresh.passage_ledger
#print axioms RHV6Fresh.chain_ledger
#print axioms RHV6Fresh.grammar_kinematics_abel
#print axioms RHV6Fresh.chain_raccordShift_eq
#print axioms RHV6Fresh.primeAtRank_two_step_ge_six
#print axioms RHV6Fresh.chain_two_step_floor
#print axioms RHV6Fresh.diagonal_radial_from_ledger
#print axioms RHV6Fresh.arrival_onLine_iff_ledger_height_determined
#print axioms RHV6Fresh.required_eq_realised
#print axioms RHV6Fresh.grammar_step_regime_blind
#print axioms RHV6Fresh.horizontal_ledger_exceeds_grammar
#print axioms RHV6Fresh.off_pair_vs_onLine_pair
#print axioms RHV6Fresh.horizontal_two_step_single_height
#print axioms RHV6Fresh.transition_kinematics_by_configuration
#print axioms RHV6Fresh.first_off_configuration_two_transitions
#print axioms RHV6Fresh.first_off_configuration_alternation_floor
#print axioms RHV6Fresh.chain_from_line_radial_content
#print axioms RHV6Fresh.engaged_departure_radial_zero
#print axioms RHV6Fresh.grammar_event_reads_no_radial
#print axioms RHV6Fresh.arrival_radial_readings
#print axioms RHV6Fresh.engaged_successor_function
#print axioms RHV6Fresh.radial_generator_test
#print axioms RHV6Fresh.engaged_persists_of_generator_fixes_line
#print axioms RHV6Fresh.line_invariant_of_radial_preserving_law
#print axioms RHV6Fresh.radial_preserving_law_of_riemannHypothesis
#print axioms RHV6Fresh.engagedBreakWorld_line_then_twins
#print axioms RHV6Fresh.weightFamily_primeWeights
#print axioms RHV6Fresh.weightFamily_weight_response
#print axioms RHV6Fresh.weightFamily_member_response
#print axioms RHV6Fresh.weightFamily_radial_zero_iff_weight_modulus
#print axioms RHV6Fresh.vertical_direction_keeps_reflection
#print axioms RHV6Fresh.reflection_direction_response
#print axioms RHV6Fresh.engaged_member_reflection_response
#print axioms RHV6Fresh.regimeWitness_reflection_response
#print axioms RHV6Fresh.changeResidue_eq_position_sub
#print axioms RHV6Fresh.changeResidue_eq_radial
#print axioms RHV6Fresh.change_detector
#print axioms RHV6Fresh.changeResidueAt_window
#print axioms RHV6Fresh.changeResidue_ledger
#print axioms RHV6Fresh.passage_change_detector
#print axioms RHV6Fresh.predictor_exists
#print axioms RHV6Fresh.predictor_closes
#print axioms RHV6Fresh.engaged_persists_of_predictor
#print axioms RHV6Fresh.predictor_pair_iff_heightOnly
#print axioms RHV6Fresh.changeResidue_enclosed_by_remainder_growth
#print axioms RHV6Fresh.changeResidue_vanishes_iff_remainder_sqrt_growth
#print axioms RHV6Fresh.engagedBreakWorld_change_detected
#print axioms RHV6Fresh.regimeWitness_change_detected
#print axioms RHV6Fresh.change_bit_iff_race
#print axioms RHV6Fresh.arrival_before_sign_change
#print axioms RHV6Fresh.canonicalTransition_of_passage
#print axioms RHV6Fresh.exit_position_fixed_by_departure
#print axioms RHV6Fresh.tower_relative_position
#print axioms RHV6Fresh.entry_cell_eq_line_cell_of_margin
#print axioms RHV6Fresh.entry_position_window
#print axioms RHV6Fresh.entry_position_determines_radial
#print axioms RHV6Fresh.transition_shared_prime_shift
#print axioms RHV6Fresh.transition_conserves_iff_entry_position
#print axioms RHV6Fresh.canonical_transition_radial_carrier
#print axioms RHV6Fresh.mirror_annulled_iff_onLine
#print axioms RHV6Fresh.engaged_passage_height_only
#print axioms RHV6Fresh.radial_motion_iff_off
#print axioms RHV6Fresh.regime_change_creates_radial_motion
#print axioms RHV6Fresh.riemannHypothesis_iff_conservation_and_base
#print axioms RHV6Fresh.conservation_not_structural
#print axioms RHV6Fresh.vertical_arrival_onLine_iff_no_regime_change
#print axioms RHV6Fresh.conservation_leaves_only_base
#print axioms RHV6Fresh.entry_arrow_iff_upper_conservation
#print axioms RHV6Fresh.riemannHypothesis_iff_entry_arrow_and_base
#print axioms RHV6Fresh.local_euler_term_norm
#print axioms RHV6Fresh.entry_arrow_iff_local_euler_modulus
#print axioms RHV6Fresh.local_euler_factor_ne_zero
#print axioms RHV6Fresh.local_euler_factor_at_member_ne_zero
#print axioms RHV6Fresh.pointed_primes_rank_only
#print axioms RHV6Fresh.pointed_gapClass6_rank_only
#print axioms RHV6Fresh.pair_step_position
#print axioms RHV6Fresh.line_step_position
#print axioms RHV6Fresh.occurrence_is_rank_label
#print axioms RHV6Fresh.tower_offset_rigid
#print axioms RHV6Fresh.onLine_iff_no_grid_translation
#print axioms RHV6Fresh.entry_arrow_point_irrelevant
#print axioms RHV6Fresh.tower_grid_normal_form
#print axioms RHV6Fresh.onLine_grid_eq_iff_height_eq
#print axioms RHV6Fresh.competing_regime_at_any_point
#print axioms RHV6Fresh.passage_grid_decomposition
#print axioms RHV6Fresh.engaged_passage_translation
#print axioms RHV6Fresh.energyRatio_flat_iff
#print axioms RHV6Fresh.engaged_transport_flat_iff_arrival_onLine
#print axioms RHV6Fresh.local_euler_modulus_point_irrelevant
#print axioms RHV6Fresh.riemannHypothesis_iff_noLowerSide
#print axioms RHV6Fresh.windingContact_strictAnti_height
#print axioms RHV6Fresh.windingSegment_nested
#print axioms RHV6Fresh.windingContact_sameHeight
#print axioms RHV6Fresh.cell_height_window
#print axioms RHV6Fresh.cell_empty_above_height
#print axioms RHV6Fresh.contact_below_of_height
#print axioms RHV6Fresh.windingContact_position
#print axioms RHV6Fresh.member_coordinates_separate
#print axioms RHV6Fresh.rescaled_amplitude_flat_iff
#print axioms RHV6Fresh.shifted_member_amplitude
#print axioms RHV6Fresh.visibility_horizon
#print axioms RHV6Fresh.radial_transport_le_of_remainder_growth
#print axioms RHV6Fresh.riemannHypothesis_iff_remainder_growth_all_eps
#print axioms RHV6Fresh.riemannHypothesis_iff_mirror_transport_flat
#print axioms RHV6Fresh.riemannHypothesis_iff_all_transports_flat
#print axioms RHV6Fresh.pair_amplitude_eq_critical_iff
#print axioms RHV6Fresh.smoothedVonMangoldtSum_norm_le_psi
#print axioms RHV6Fresh.trivialZeroResidueTerm_norm_le
#print axioms RHV6Fresh.trivialZeroSum_norm_le
#print axioms RHV6Fresh.smoothedRemainder_linear_growth
#print axioms RHV6Fresh.radial_strip_from_primes
#print axioms RHV6Fresh.radial_transport_le_one_from_primes
#print axioms RHV6Fresh.remainderExponent_mem_bracket
#print axioms RHV6Fresh.riemannHypothesis_iff_remainderExponent_eq_half
#print axioms RHV6Fresh.mirror_pair_exponent_le
#print axioms RHV6Fresh.mirror_pair_exponent_le_remainderExponent
#print axioms RHV6Fresh.shiftedWorld_weight_ge
#print axioms RHV6Fresh.shiftedWorld_weight_eq_iff
#print axioms RHV6Fresh.vonMangoldt_sq_sum_le_log_mul_psi
#print axioms RHV6Fresh.vonMangoldt_sq_sum_linear
#print axioms RHV6Fresh.shiftedWorld_weight_sq_ge
#print axioms RHV6Fresh.shiftedWorld_weight_sq_eq_iff
#print axioms RHV6Fresh.cell_width_eq
#print axioms RHV6Fresh.ownCellIncrement_eq
#print axioms RHV6Fresh.ownCellIncrement_abs_ge
#print axioms RHV6Fresh.ownCellEnergyDensity_succ
#print axioms RHV6Fresh.ownCellEnergyDensity_flat_iff
#print axioms RHV6Fresh.prime_gap_eq_weight_difference
#print axioms RHV6Fresh.exact_gap_three_readings
#print axioms RHV6Fresh.chain_reading_telescopes
#print axioms RHV6Fresh.chain_reading_endpoint_only
#print axioms RHV6Fresh.chain_reading_gap_order_blind
#print axioms RHV6Fresh.mirror_chain_accumulation
#print axioms RHV6Fresh.contact_energy_exposed
#print axioms RHV6Fresh.signedWorld_abs_weight
#print axioms RHV6Fresh.diagonal_sign_blind
#print axioms RHV6Fresh.signedWorld_diagonal_linear
#print axioms RHV6Fresh.pure_step_weight_sum
#print axioms RHV6Fresh.pure_step_demand
#print axioms RHV6Fresh.pure_step_demand_magnitude
#print axioms RHV6Fresh.stepCross_eq_offDiagonal
#print axioms RHV6Fresh.response_sq_eq_diagonal_add_cross
#print axioms RHV6Fresh.stepCross_forced_by_demand
#print axioms RHV6Fresh.stepCross_neg_iff
#print axioms RHV6Fresh.stepCross_nonneg_of_aligned
#print axioms RHV6Fresh.stepDiagonal_sign_invariant
#print axioms RHV6Fresh.off_debt_visible_in_exponent
#print axioms RHV6Fresh.compensation_closure_verdict
#print axioms RHV6Fresh.alternating_two_step_gap
#print axioms RHV6Fresh.state_return_iff_two_step_mod6
#print axioms RHV6Fresh.abMinusBa_eq
#print axioms RHV6Fresh.ab_ba_channel_lock
#print axioms RHV6Fresh.ab_ba_channel_lock_abs_le_one
#print axioms RHV6Fresh.prime_ab_ba_channel_lock
#print axioms RHV6Fresh.mirror_word_energy_debt
#print axioms RHV6Fresh.alternating_two_step_mirror_debt
#print axioms RHV6Fresh.mirror_word_debt_pos_iff
#print axioms RHV6Fresh.RegimeCell.rank_span
#print axioms RHV6Fresh.RegimeCell.heights_three_for_four
#print axioms RHV6Fresh.RegimeCell.central_amplitude_readings
#print axioms RHV6Fresh.RegimeCell.central_amplitude_gap
#print axioms RHV6Fresh.RegimeCell.log_charge_eq
#print axioms RHV6Fresh.RegimeCell.abs_log_charge_le
#print axioms RHV6Fresh.log_rpow_neg_eq
#print axioms RHV6Fresh.mirrorPairTerm_even
#print axioms RHV6Fresh.even_hasDerivAt_zero
#print axioms RHV6Fresh.mirrorPairTerm_first_order_blind
#print axioms RHV6Fresh.RegimeCell.central_pair_term
#print axioms RHV6Fresh.pairOverDouble_eq
#print axioms RHV6Fresh.norm_pairOverDouble
#print axioms RHV6Fresh.radialCurvature_ge_sq
#print axioms RHV6Fresh.radialCurvature_eq_zero_iff
#print axioms RHV6Fresh.radialCurvature_mono
#print axioms RHV6Fresh.finite_horizon_separation_le
#print axioms RHV6Fresh.pairDefect_zero
#print axioms RHV6Fresh.pairDefect_even
#print axioms RHV6Fresh.pairDefect_decomposition
#print axioms RHV6Fresh.inv_mirrorPoint_sub_le
#print axioms RHV6Fresh.pairDefect_sub_curvature_le
#print axioms RHV6Fresh.lineSplitOverDouble_eq
#print axioms RHV6Fresh.lineSplitCurvature_bounds
#print axioms RHV6Fresh.regime_sign_of_curvature
#print axioms RHV6Fresh.interaction_change_radial
#print axioms RHV6Fresh.interaction_change_vertical
#print axioms RHV6Fresh.interaction_change_family
#print axioms RHV6Fresh.pairOverDouble_even
#print axioms RHV6Fresh.interaction_change_even
#print axioms RHV6Fresh.interaction_changes_opposite
#print axioms RHV6Fresh.referenceCross_eq
#print axioms RHV6Fresh.referenceCross_sign_changes
#print axioms RHV6Fresh.self_energy_order
#print axioms RHV6Fresh.lineSplitCurvature_ge_neg_four
#print axioms RHV6Fresh.radialCurvature_unbounded
#print axioms RHV6Fresh.pair_offset_sq_real
#print axioms RHV6Fresh.mirror_pair_offset_sq_nonneg
#print axioms RHV6Fresh.axis_pair_offset_sq_nonpos
#print axioms RHV6Fresh.local_four_sector_symmetry
#print axioms RHV6Fresh.continuations_same_center
#print axioms RHV6Fresh.towerCurve_norm
#print axioms RHV6Fresh.curve_of_point
#print axioms RHV6Fresh.rescaledTower_eq
#print axioms RHV6Fresh.towerCurve_central
#print axioms RHV6Fresh.towerCurve_arith_reflect
#print axioms RHV6Fresh.towerCurve_crit_reflect
#print axioms RHV6Fresh.contact_index_rules
#print axioms RHV6Fresh.towerCurve_contact
#print axioms RHV6Fresh.tower_central_invariant_iff
#print axioms RHV6Fresh.tower_arith_invariant_iff
#print axioms RHV6Fresh.tower_crit_invariant_iff
#print axioms RHV6Fresh.raw_tower_not_centrally_invariant
#print axioms RHV6Fresh.reflection_reverses_order
#print axioms RHV6Fresh.reflection_forward_is_conjugate
#print axioms RHV6Fresh.arith_reflect_exchanges_depth
#print axioms RHV6Fresh.pointCurve_eq
#print axioms RHV6Fresh.pointCurve_eq_towerCurve
#print axioms RHV6Fresh.pointCurve_hasDerivAt
#print axioms RHV6Fresh.pointCurve_norm
#print axioms RHV6Fresh.pointCurve_norm_lt_iff
#print axioms RHV6Fresh.pointCurve_norm_gt_iff
#print axioms RHV6Fresh.pointCurve_norm_eq_iff
#print axioms RHV6Fresh.zetaReflect_involutive
#print axioms RHV6Fresh.mirrorLoop_eq
#print axioms RHV6Fresh.mirrorLoop_coefficient
#print axioms RHV6Fresh.norm_loopGauge
#print axioms RHV6Fresh.norm_loopGauge_eq_one_iff
#print axioms RHV6Fresh.one_lt_norm_loopGauge_iff
#print axioms RHV6Fresh.zetaReflect_eq_self_iff
#print axioms RHV6Fresh.mirrorLoop_onLine
#print axioms RHV6Fresh.mirrorLoop_offLine
#print axioms RHV6Fresh.mirrorLoop_target_isZero
#print axioms RHV6Fresh.mirrorLoop_family
#print axioms RHV6Fresh.loop_coefficient_ne
#print axioms RHV6Fresh.loop_coefficient_norm_eq_iff
#print axioms RHV6Fresh.pairAntisym_onLine
#print axioms RHV6Fresh.pairAntisym_swap
#print axioms RHV6Fresh.pairAntisym_zero
#print axioms RHV6Fresh.pairAntisym_ne_zero_of_offLine
#print axioms RHV6Fresh.mirror_sum_reindex
#print axioms RHV6Fresh.mirror_antisym_collective_zero
#print axioms RHV6Fresh.zetaReflect_onLine
#print axioms RHV6Fresh.mirror_odd_weight_zero_on_line
#print axioms RHV6Fresh.mirror_odd_entire_weight_zero
#print axioms RHV6Fresh.loop_difference_onLine_ne_zero
#print axioms RHV6Fresh.antisym_channel_not_forced
#print axioms RHV6Fresh.windowEnergy_add
#print axioms RHV6Fresh.windowVariation_split
#print axioms RHV6Fresh.pair_self_excess_eq
#print axioms RHV6Fresh.pair_self_excess_eq_zero_iff
#print axioms RHV6Fresh.window_self_excess_nonneg
#print axioms RHV6Fresh.windowVariation_via_remainder
#print axioms RHV6Fresh.complement_cross_eq_remainder_cross
#print axioms RHV6Fresh.remainder_cross_curvature
#print axioms RHV6Fresh.remainder_cross_even
#print axioms RHV6Fresh.cross_term_unconstrained
#print axioms RHV6Fresh.norm_zeroTerm_eq
#print axioms RHV6Fresh.inside_field_of_onLine
#print axioms RHV6Fresh.exponent_le_of_inside
#print axioms RHV6Fresh.inside_field_forces_line
#print axioms RHV6Fresh.riemannHypothesis_of_first_field
#print axioms RHV6Fresh.first_field_iff_riemannHypothesis
#print axioms RHV6Fresh.prime_axis_nesting_any_depth
#print axioms RHV6Fresh.tower_field_ratio
#print axioms RHV6Fresh.inside_field_of_same_exponent
#print axioms RHV6Fresh.riemannHypothesis_of_same_exponent
#print axioms RHV6Fresh.fixed_exponent_escapes
#print axioms RHV6Fresh.regimeWitness_fixed_exponent_escapes
#print axioms RHV6Fresh.prisoner_exponent_le
#print axioms RHV6Fresh.prisoner_forces_height
#print axioms RHV6Fresh.riemannHypothesis_of_height_always_advances
#print axioms RHV6Fresh.prison_iff_riemannHypothesis
#print axioms RHV6Fresh.escape_must_be_financed
#print axioms RHV6Fresh.financing_ledger
#print axioms RHV6Fresh.captive_one_side_summit
#print axioms RHV6Fresh.riemannHypothesis_of_remainderCaptive
#print axioms RHV6Fresh.remainderCaptive_iff_riemannHypothesis
#print axioms RHV6Fresh.onLine_tower_hierarchy
#print axioms RHV6Fresh.raccordHierarchy_of_height_advance
#print axioms RHV6Fresh.sameHeight_breaks_hierarchy
#print axioms RHV6Fresh.engaged_step_of_next_hierarchy
#print axioms RHV6Fresh.raccordHierarchy_of_engaged_departure
#print axioms RHV6Fresh.raccordHierarchy_iff_riemannHypothesis
#print axioms RHV6Fresh.first_tower_envelope_of_raccordHierarchy
#print axioms RHV6Fresh.tower_le_iff_parameters
#print axioms RHV6Fresh.inside_field_of_parameters
#print axioms RHV6Fresh.onLine_energy_order_iff_height
#print axioms RHV6Fresh.tower_inside_below_horizon
#print axioms RHV6Fresh.tower_inside_of_height
#print axioms RHV6Fresh.mirror_pair_has_prisoner
#print axioms RHV6Fresh.lower_member_prisoner
#print axioms RHV6Fresh.upper_member_ratio
#print axioms RHV6Fresh.upper_member_escapes_iff
#print axioms RHV6Fresh.upper_member_exact_horizon
#print axioms RHV6Fresh.uniform_horizon_le_exact
#print axioms RHV6Fresh.upper_member_gain_must_be_financed
#print axioms RHV6Fresh.passage_prime_tower_bond
#print axioms RHV6Fresh.gap_readings_agree_iff_height
#print axioms RHV6Fresh.height_advance_concurs
#print axioms RHV6Fresh.vertical_passage_concurs
#print axioms RHV6Fresh.sameHeight_satisfies_both_rigidities
#print axioms RHV6Fresh.parameter_model_twin_escapes
#print axioms RHV6Fresh.no_sameHeight_iff_riemannHypothesis
#print axioms RHV6Fresh.tower_le_iff_local_budget
#print axioms RHV6Fresh.localCaptivity_iff_budget
#print axioms RHV6Fresh.height_advance_local_budget
#print axioms RHV6Fresh.sameHeight_budget_deficit
#print axioms RHV6Fresh.sameHeight_local_budget_refuted
#print axioms RHV6Fresh.local_captivity_computed
#print axioms RHV6Fresh.captivity_renewed_along_chain
#print axioms RHV6Fresh.radial_descent_budget_surplus
#print axioms RHV6Fresh.localCaptivity_iff_oriented
#print axioms RHV6Fresh.chain_interior_steps_ge_one
#print axioms RHV6Fresh.exactPrimeTransitionOf
#print axioms RHV6Fresh.sameHeight_exactPrimeTransition_reversed
#print axioms RHV6Fresh.sameHeight_capture_target_iff
#print axioms RHV6Fresh.engaged_arrival_onLine_iff_radial_floor
#print axioms RHV6Fresh.arrival_radial_floor_iff_next_vertical
#print axioms RHV6Fresh.translated_arrival_complete_and_captive
#print axioms RHV6Fresh.engaged_radial_floor_target_iff
#print axioms RHV6Fresh.radial_floor_iff_heightOnly
#print axioms RHV6Fresh.radial_floor_of_riemannHypothesis
#print axioms RHV6Fresh.engaged_persists_of_radial_floor
#print axioms RHV6Fresh.grid_translation_readings
#print axioms RHV6Fresh.lineContact_strictAnti_height
#print axioms RHV6Fresh.windingNested_iff_translation_bound
#print axioms RHV6Fresh.windingNested_of_onLine
#print axioms RHV6Fresh.translation_of_not_nested
#print axioms RHV6Fresh.windingNested_index_of_depth
#print axioms RHV6Fresh.engaged_step_combined
#print axioms RHV6Fresh.engaged_nested_translation_window
#print axioms RHV6Fresh.conservation_iff_nested_and_noTranslation
#print axioms RHV6Fresh.contact_gt_one
#print axioms RHV6Fresh.windingNested_trans
#print axioms RHV6Fresh.tower_room_two_sided
#print axioms RHV6Fresh.translation_room_two_sided
#print axioms RHV6Fresh.no_translation_iff_next_winds
#print axioms RHV6Fresh.next_winding_forces_no_translation
#print axioms RHV6Fresh.sameHeight_successor_translates_inward
#print axioms RHV6Fresh.winding_to_infinity_iff_riemannHypothesis
#print axioms RHV6Fresh.contactMinusAt_eq_windingContact
#print axioms RHV6Fresh.towerRoom_of_riemannHypothesis
#print axioms RHV6Fresh.towerRoom_squeeze
#print axioms RHV6Fresh.windingContact_lt_of_radial_lt
#print axioms RHV6Fresh.mirror_takes_room_below
#print axioms RHV6Fresh.room_parameter_model_with_mirror_pair
#print axioms RHV6Fresh.renewed_captivity_iff_no_translation
