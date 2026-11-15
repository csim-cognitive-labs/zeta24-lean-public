# Manifeste de tour — T03-TRUE-STATE

    TOUR_ID = T03-TRUE-STATE
    TIMESTAMP = 2026-09-09
    KIND = SCIENTIFIC_PRODUCTION_MACRO_CYCLE
    REPRISE = § S — macro-cycle unique ; correction de causalité de S4 imposée

    HEAD_BEFORE = 8a1aeb8b8977d39ecb8171d037f7b684ee18e0d8
    HEAD_AFTER = 87f84474db52ad06220f2baa23d81b4d7fbc7d69
    ORIGIN_MAIN_SHA = 87f84474db52ad06220f2baa23d81b4d7fbc7d69

    FILES_CHANGED = RHV3Lean/Objects/TrueTowerState.lean, RHV3Lean/Objects/TrueTowerCarrier.lean, RHV3Lean/Objects/RatioFourStateControl.lean, RHV3Lean/Objects/CanonicalWindowRule.lean, RHV3Lean/Objects/TransportOnOperator.lean, RHV3Lean.lean, Certification/Challenge.lean, Certification/Solution.lean, Certification/comparator.json, Certification/comparator_manifest.json, Certification/CHALLENGE_FROZEN_GIT_BLOB, Certification/PrintAxioms.lean, Certification/run_comparator.sh, CONTRACTS.md, audit_contracts.sh, audit_strength.sh, validate_cycle.sh, audits/CONTROL_ONLY_INHABITANTS.txt, audits/DERIVED_CARRIER_MAPS.txt, audits/RH_EQUIVALENT_CONTRACTS.txt, audits/tours/T02-MACRO-CLOSURE.md, audits/tours/T03-TRUE-STATE.md

    PUBLIC_REALISERS_ADDED = TTrueHarmonicTowerState, recoveredSpan, recoveredKappa, thm_recoveredKappa_isInt, thm_recoveredSpan_isInt, thm_recoveredSpan_positive, thm_recoveredSpan_isNat, recoveredSpanNat, recoveredKappaInt, thm_state_recovers_height, thm_state_recovers_radialPosition, tRecoveredWindow, thm_recoveredWindow_contacts, thm_state_sameContacts_sameMember, TTrueTowerCarrier, rCarrierContactEntry, rCarrierContactTerminal, tCarrierCell, nCarrierCentralPrime, thm_carrierReadings_are_functions_of_member, toOperator, thm_carrier_toOperator_sameContacts, thm_carrier_recoveredWindow_sameCell, thm_carrier_recoveredWindow_sameCentralPrime, fnCarrierMemberCentralPrime, PLocalLawOnCarrier, PRPassOnCarrier, thm_rpass_iff_localLaw_and_noNullPassage_generic, thm_carrier_rpass_iff_localLaw_and_noNullPassage, thm_carrier_rpassClause_order, thm_carrier_rpassClause_endpointsDistinct, thm_carrier_rpassClause_corridorEmpty, thm_carrier_sameE_offCriticalLine_impossible, thm_riemannHypothesis_of_rpassOnCarrier, tRatioFourState, tRatioFourCarrier, thm_ratioFourState_contacts
    PUBLIC_REALISERS_MODIFIED = thm_rpass_iff_localLaw_and_noNullPassage (même énoncé, désormais instance de la forme générique) ; tRatioFourOperator et thm_ratioFourOperator_* (inchangés, RETRACTES du registre et étiquetés CONTROL_ONLY)

    SEMANTIC_STEPS = la Tour d'un membre possède DEJA ses deux rencontres réelles avec l'axe algébrique ; l'adresse d'entrée et le nombre d'étages ne les construisent pas, ils les adressent, et se relisent donc sur elles ; la cellule, le comptage, le premier central et la loi locale sont tous lus sur ce même état
    MATHEMATICAL_STEPS = deux lois portées par l'état — écart angulaire multiple entier du demi-tour, contact d'entrée sur l'incidence de phase ; extraction de l'entier par l'annulation du sinus ; positivité par l'ordre des contacts ; inversions de hauteur et tangentielle ; aller-retour exact vers la fenêtre récupérée

    COMPARATOR_TARGETS = Certification/comparator.json (71 cibles ; 10 nouvelles, famille C8)
    COMPARATOR_DELTA_RESULT = PASS (71/71 ; nanoda et noyau Lean par défaut acceptent)
    COMPARATOR_CUMULATIVE_RESULT = PASS (même cumul, 71/71)
    CONTRACT_AUDIT_RESULT = PASS
    SPECIFICATION_STRENGTH_AUDIT_RESULT = PASS (exécuté en étape 0 de Comparator)
    FIDELITY_AUDIT_RESULT = PASS
    SAME_OBJECT_RESULTS = PASS (détail plus bas)
    AXIOMS_RESULT = [propext, Quot.sound, Classical.choice]
    BUILD_RESULT = PASS

    RH_EQUIVALENT_CONTRACTS = PNoNullZeroPassage

    CHALLENGE_BLOB_BEFORE = b49d66328392410cb053714abecbc6e6d1c2c188
    CHALLENGE_BLOB_AFTER = 909a7dfd70f9cffb1b282337ebdb907ac1f5d7b0

Le blob change par AJOUT seul : préfixe byte-identique à la version gelée en
T02, contrôle `PREFIX_IDENTICAL` positif.  Ce n'est pas une mutation d'énoncé au
sens de § M.2.

    RESIDUAL_OBLIGATIONS_BEFORE = 3
    RESIDUAL_OBLIGATIONS_AFTER = 5

Le compte REMONTE, et c'est le résultat correct : deux réalisateurs inscrits au
tour T02 sont rétractés parce qu'ils n'étaient que des habitants de type.

    NEXT_CONSUMER = la règle de détermination de l'état propre, puis le producteur de la loi locale
    PUSH_STATUS = PASS — HEAD_AFTER_LOCAL = ORIGIN_MAIN_AFTER_PUSH = 87f84474

## La correction de causalité de S4

L'ordre est désormais celui-ci, et il est porté par les types eux-mêmes :

    vrai zéro z
      -> état propre de Tour            TTrueHarmonicTowerState z
        -> deux contacts                 contactEntry, contactTerminal
          -> récupération de T et beta   thm_state_recovers_height,
                                         thm_state_recovers_radialPosition
            -> recoveredKappa / recoveredSpan

 et  ne sont PAS des champs de l'état : ils sont récupérés.  Les deux
lois sont énoncées sans les nommer — la loi de hauteur dit que l'écart angulaire
des deux contacts est un multiple entier du demi-tour, la loi tangentielle dit
que le contact d'entrée est une incidence de la phase propre.  L'entier n'est
donc jamais choisi : il est extrait par l'annulation d'un sinus.

La lecture inverse, indexée par une fenêtre, n'est pas supprimée : elle reste
vraie et sert de DICTIONNAIRE.  Mais elle est désormais obtenue DEPUIS l'état,
par `tRecoveredWindow`, et `thm_recoveredWindow_contacts` établit qu'elle rend
exactement les deux contacts de départ.  Aucun contact n'est reconstruit.

## Les sept fronts

    F1  règle de détermination de l'état propre .... BLOCKED_FOR_EXACT_CLOSURE
    F2  cellule canonique non vide ................. BLOCKED (dépend de F1)
    F3  LL.SAME_OPERATOR ........................... EXACT, et relu sur le porteur d'états
    F4  LL.LOCAL_LAW_PRODUCER ...................... BLOCKED_FOR_EXACT_CLOSURE
    F5  O8.RPASS_REAL_TRANSPORT .................... DECOMPOSE ; producteur BLOCKED
    F6  TERMINAL.SAME_E_CONTRADICTION .............. CONDITIONAL
    F7  TERMINAL.RIEMANN_HYPOTHESIS ................ CONDITIONAL

Aucun front n'a attendu : F2 à F7 ont tous été reproduits sur le porteur d'états
propres, avec leurs bridges, leurs clauses libres, leurs cibles Comparator et
leurs gardes.

## Tableau de fidélité (§ N.3)

| Étape sémantique | Étape mathématique | Réalisateur Lean exact | Nature | Hypothèses résiduelles | SAME-object | Fidélité |
|---|---|---|---|---|---|---|
| la Tour possède déjà ses deux rencontres réelles | deux contacts positifs ordonnés, deux lois | TTrueHarmonicTowerState | STRUCTURE | aucune | SAME_MEMBER PASS | EXACT |
| l'adresse d'entrée est relue, jamais cherchée | annulation du sinus de la loi tangentielle | thm_recoveredKappa_isInt | THEOREM | aucune | SAME_MEMBER PASS | EXACT |
| le nombre d'étages est relu, jamais cherché | annulation du sinus de la loi de hauteur, plus l'ordre des contacts | thm_recoveredSpan_isNat | THEOREM | aucune | SAME_MEMBER PASS | EXACT |
| la hauteur se relit dans la cellule elle-même | T = m·pi/(log C+ − log C−) avec le m récupéré | thm_state_recovers_height | THEOREM | aucune | SAME_MEMBER PASS | EXACT |
| la position radiale se relit sur le contact d'entrée | beta = T/tan(T·log C−), périodicité de la tangente | thm_state_recovers_radialPosition | THEOREM | aucune | SAME_MEMBER PASS | EXACT |
| la causalité est refermée sans rien déplacer | la fenêtre récupérée rend les deux contacts de départ | thm_recoveredWindow_contacts | THEOREM | aucune | SAME_CONTACTS PASS | EXACT |
| même donnée complète de contacts, même membre | inversion (C−, C+, m) → (T, beta) → rho | thm_state_sameContacts_sameMember | THEOREM | aucune | SAME_MEMBER PASS | EXACT |
| la cellule est lue sur l'état propre | intervalle algébrique porté par les deux contacts | tCarrierCell, nCarrierCentralPrime | DEFINITION | aucune | SAME_CELL PASS | EXACT |
| le dictionnaire ne change ni la cellule ni C3 | égalité des deux intervalles de mêmes bords | thm_carrier_recoveredWindow_sameCell | THEOREM | aucune | SAME_CELL PASS | EXACT |
| la loi locale parle du premier central de CE porteur | composition avec le représentant supérieur | PLocalLawOnCarrier | DEFINITION | aucune | SAME_OPERATOR PASS | EXACT |
| le transport se lit clause par clause, sans rien supposer de la lecture centrale | équivalence générique avec (loi locale) ET (absence de passage nul) | thm_rpass_iff_localLaw_and_noNullPassage_generic | THEOREM | aucune | SAME_PASSAGE PASS | EXACT |
| ordre, séparation et corridor de l'image | positivité primitive des écarts entre premiers successifs | thm_carrier_rpassClause_order, thm_carrier_rpassClause_endpointsDistinct, thm_carrier_rpassClause_corridorEmpty | THEOREM | la loi locale (CONTROL_INPUT nommé) | SAME_PLACE PASS | EXACT |
| le zéro hors ligne est impossible, sur LE MEME passage | passage nul de la branche OFF contre place jamais nulle | thm_carrier_sameE_offCriticalLine_impossible | THEOREM | R-PASS sur le porteur d'états (SCIENTIFIC_RESIDUAL_INPUT) | SAME_E_OFF PASS | CONDITIONAL |
| l'énoncé public sous le seul transport | composition avec l'universalisation | thm_riemannHypothesis_of_rpassOnCarrier | THEOREM | R-PASS sur le porteur d'états (SCIENTIFIC_RESIDUAL_INPUT) | SAME_E_OFF PASS | CONDITIONAL |
| le type des états propres n'est pas vide | deux contacts explicites vérifiant les deux lois | tRatioFourState, tRatioFourCarrier | DEFINITION DE CONTROLE, ne réalise aucune obligation | aucune | SAME_OPERATOR PASS | EXACT |
| l'état propre CANONIQUE, déterminé par les maîtres | règle de détermination des deux contacts | aucun | OBLIGATION OUVERTE | § S4 donne C_- = min(C1,C2) sans définir C1 ni C2 | sans objet | MISSING |

    SCIENTIFIC_RESIDUAL_INPUT_COUNT = 1

L'unique entrée scientifique résiduelle reste `PNoNullZeroPassage`, signalée
comme contrat RH-équivalent AVANT l'exécution de Comparator, conformément à la
nouvelle garde STRENGTH.

## SAME-OBJECT (§ N.2.E)

    SAME_MEMBER        PASS  (thm_state_sameContacts_sameMember, thm_carrierReadings_are_functions_of_member)
    SAME_PASSAGE       PASS  (la décomposition porte sur le passage lui-même)
    SAME_MIDDLE        PASS  (thm_carrier_triple_twoHeightGaps_positive, même membre médian)
    SAME_HISTORY       PASS  (la place est indexée dans l'unique histoire première de O6)
    SAME_OPERATOR      PASS  (un seul porteur threadé ; les habitants de contrôle sont déclarés comme tels)
    SAME_WINDOW_OR_EVENT  PASS  (la fenêtre est RECUPEREE de l'état, jamais posée)
    SAME_CONTACTS      PASS  (thm_recoveredWindow_contacts, thm_carrier_toOperator_sameContacts)
    SAME_CELL          PASS  (thm_carrier_recoveredWindow_sameCell)
    SAME_CENTRAL_PRIME PASS  (thm_carrier_recoveredWindow_sameCentralPrime)
    SAME_OCCURRENCE    NOT_APPLICABLE
    SAME_PLACE         PASS  (les deux extrémités sont celles de la place image du MEME passage)
    SAME_E_OFF         PASS  (la contradiction est opposée au passage produit par la branche OFF)

## FIDELITY_NEGATIVE_CHECKS (§ N.4)

    attribut annoncé sans réalisateur ......................... aucun ; 5 obligations restantes recensées
    theorem plus faible que le maître ......................... aucun trouvé ce tour
    hypothèse scientifique cachée dans une signature .......... aucune ; l'entrée résiduelle est nommée et signalée avant Comparator
    habitant présenté comme objet canonique ................... CORRIGE ce tour ; garde SPECIFICATION ajoutée et éprouvée
    contrat RH-équivalent non signalé ......................... CORRIGE ce tour ; garde STRENGTH ajoutée, exécutée avant Comparator
    objet libre remplaçant un objet canonique ................. aucun
    paramètre arbitraire présenté comme donnée propre ......... aucun ; kappa et m ne sont plus des données, ils sont récupérés
    conséquence conditionnelle présentée comme producteur ..... aucune ; plus aucun statut « CLOS conditionnellement »
    changement de membre entre deux étapes .................... aucun
    changement de passage ..................................... aucun
    changement d'opérateur .................................... aucun
    changement de cellule ..................................... aucun ; la cellule du dictionnaire EST celle de l'état
    utilisation d'une loi retirée ............................. aucune
    R-ATT au-delà de sa portée ................................ non utilisé ce tour
    sélection arithmétique a posteriori de la Tour ............ aucune ; aucun premier, rang ou comptage n'entre dans l'état
    recherche de kappa ou de m ................................ aucune ; l'entier est EXTRAIT d'une annulation de sinus
    causalité inversée kappa,m -> contacts .................... CORRIGE ce tour ; les contacts sont la donnée
    contradiction OFF sur un passage différent ................ NON
    positivité de l'écart des zéros supposée quelque part ..... NON ; elle est conclue
    hypothèse de Riemann utilisée ou niée ..................... NON hors du contrôle de mesure déclaré

## Ce que ce tour ne ferme PAS

    S4, règle de détermination de l'état propre
                              BLOCKED_FOR_EXACT_CLOSURE.  Premier statement
                              mathématique exact encore non produit :

                                  def tCanonicalCarrier : TTrueTowerCarrier

                              c'est-à-dire une famille
                              `∀ z, TTrueHarmonicTowerState z` DETERMINEE par
                              les maîtres.  § S4 fixe `C_- = min(C1,C2)` et
                              `C_+ = max(C1,C2)` sans définir `C1` ni `C2`.
    LL.LOCAL_LAW_PRODUCER     Dépend du précédent.
    O8.RPASS_REAL_TRANSPORT   Réduit par la décomposition à `PNoNullZeroPassage`.
    TERMINAL.RIEMANN_HYPOTHESIS
                              Le theorem SANS hypothèse scientifique n'existe
                              pas.  Deux formes conditionnelles existent et sont
                              certifiées.

    LEAN_FINAL_RH_CERTIFIED = false
