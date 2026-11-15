# Manifeste de tour — T02-MACRO-CLOSURE

    TOUR_ID = T02-MACRO-CLOSURE
    TIMESTAMP = 2026-09-09
    KIND = SCIENTIFIC_PRODUCTION_MACRO_CYCLE
    REPRISE = § S — macro-cycle multi-fronts obligatoire, sept fronts attaqués ensemble

    HEAD_BEFORE = d2082db5b696191cf0850c5d4167b6f3c79f5baa
    HEAD_AFTER = 85a68ca53b572dde47f7eddb4d00cf018196a927
    ORIGIN_MAIN_SHA = 85a68ca53b572dde47f7eddb4d00cf018196a927

    FILES_CHANGED = RHV3Lean/Objects/ZetaRealSegment.lean, RHV3Lean/Objects/UpperRepresentative.lean, RHV3Lean/Objects/CanonicalWindowRule.lean, RHV3Lean/Objects/TransportOnOperator.lean, RHV3Lean/Objects/Universalization.lean, RHV3Lean.lean, Certification/Challenge.lean, Certification/Solution.lean, Certification/comparator.json, Certification/comparator_manifest.json, Certification/CHALLENGE_FROZEN_GIT_BLOB, Certification/PrintAxioms.lean, CONTRACTS.md, audits/tours/T02-MACRO-CLOSURE.md

    PUBLIC_REALISERS_ADDED = thm_noRealZetaZeroInOpenUnitSegment, thm_zeroHeight_ne_zero, zConjugateZero, zUpperRepresentativeMember, zUpperRepresentative, thm_upperRepresentative_radialPosition, thm_allRadialPositions_of_upperBranch, nRatioFourSpan, tRatioFourWindow, tRatioFourOperator, thm_ratioFourOperator_one_le_contactMinus, thm_ratioFourOperator_ratio_four, thm_ratioFourInterval_containsTwoPrimes, thm_ratioFourOperator_cellFoundCount_positive, thm_ratioFourOperator_centralPrime_in_cell, fnOperatorMemberCentralPrime, PLocalLawOnOperator, PRPassOnOperator, PNoNullZeroPassage, thm_rpass_iff_localLaw_and_noNullPassage, thm_rpassClause_endpoints, thm_rpassClause_order, thm_rpassClause_corridorEmpty, thm_rpassClause_endpointsDistinct, thm_noNullPassage_iff_allOnCriticalLine, thm_sameE_offCriticalLine_impossible, thm_allUpperOnCriticalLine_of_rpass, thm_inOpenStrip_of_mathlibHypotheses, zNonTrivialZeroOfMathlib, thm_riemannHypothesis_of_allUpperOnCriticalLine, thm_riemannHypothesis_of_rpassOnOperator, thm_riemannHypothesis_of_noNullPassage, thm_noNullPassage_of_riemannHypothesis
    PUBLIC_REALISERS_MODIFIED = aucun ; aucune production antérieure n'est touchée

    SEMANTIC_STEPS = la Tour d'un membre porte une fenêtre propre, et cette fenêtre existe comme terme ; la cellule terminale rencontre réellement l'axe algébrique et y trouve plusieurs nombres ; la loi locale et le transport sont énoncés sur CE porteur ; le transport se décompose en ses clauses constitutives ; la branche supérieure est exhaustive ; la centralité se relit sur l'énoncé public
    MATHEMATICAL_STEPS = plancher du diamètre logarithmique à log 4 ; Bertrand appliqué deux fois ; borne de Mellin sur la fonction complétée entière ; conjugaison ; équation fonctionnelle et racines du cosinus ; équivalence exacte entre R-PASS et (loi locale + absence de passage nul)

    COMPARATOR_TARGETS = Certification/comparator.json (61 cibles ; 17 nouvelles, familles C6 et C7)
    COMPARATOR_CUMULATIVE_RESULT = PASS (même cumul, 61/61)
    COMPARATOR_DELTA_RESULT = PASS (61/61 ; nanoda et noyau Lean par défaut acceptent)
    CONTRACT_AUDIT_RESULT = PASS
    FIDELITY_AUDIT_RESULT = PASS
    SAME_OBJECT_RESULTS = PASS (détail plus bas)
    AXIOMS_RESULT = [propext, Quot.sound, Classical.choice]
    BUILD_RESULT = PASS

    CHALLENGE_BLOB_BEFORE = fefc90e35ae520189050ba0221597b3f0703f22e
    CHALLENGE_BLOB_AFTER = b49d66328392410cb053714abecbc6e6d1c2c188

Le blob change parce que dix-sept cibles sont AJOUTEES.  Aucun énoncé existant
n'est touché : le préfixe du fichier est byte-identique à la version gelée en
T01, et le contrôle mécanique `PREFIX_IDENTICAL` le confirme.  Ce n'est donc pas
une mutation d'énoncé au sens de § M.2.

    RESIDUAL_OBLIGATIONS_BEFORE = 7
    RESIDUAL_OBLIGATIONS_AFTER = 3
    RESIDUAL_OBLIGATIONS_AFTER_CORRECTION_T03 = 5

    NEXT_CONSUMER = le producteur de la loi locale, seul front encore bloqué
    PUSH_STATUS = PASS — HEAD_AFTER_LOCAL = ORIGIN_MAIN_AFTER_PUSH = 85a68ca5

## Les sept fronts de § S.1, un par un

    F1  S4.INHABITANT ................... CLOS   tRatioFourOperator
    F2  S4/O10.CANONICAL_CELL_NONEMPTY ... CLOS   thm_ratioFourOperator_cellFoundCount_positive
    F3  LL.SAME_OPERATOR ................ CLOS   PLocalLawOnOperator sur fnOperatorMemberCentralPrime
    F4  LL.LOCAL_LAW_PRODUCER ........... BLOCKED_FOR_EXACT_CLOSURE
    F5  O8.RPASS_REAL_TRANSPORT ......... DECOMPOSE, producteur BLOCKED_FOR_EXACT_CLOSURE
    F6  TERMINAL.SAME_E_CONTRADICTION ... CLOS conditionnellement à F5
    F7  TERMINAL.RIEMANN_HYPOTHESIS ..... CLOS conditionnellement à F5

Aucun front n'a attendu passivement : F2 à F7 ont tous produit leur type final
fort, leurs bridges de typage, leurs lemmes préparatoires, leurs consommateurs
terminaux, leurs cibles Comparator et leurs gardes SAME-object.

## Tableau de fidélité (§ N.3)

| Étape sémantique | Étape mathématique | Réalisateur Lean exact | Nature | Hypothèses résiduelles | SAME-object | Fidélité |
|---|---|---|---|---|---|---|
| aucun vrai zéro n'est posé sur l'axe réel | borne de Mellin sur la fonction complétée entière, contre 1/x + 1/(1-x) >= 4 | thm_noRealZetaZeroInOpenUnitSegment, thm_zeroHeight_ne_zero | THEOREM | aucune | SAME_MEMBER PASS | EXACT |
| la branche supérieure ne perd aucun membre | conjugaison, qui conserve la position radiale | zUpperRepresentative, thm_upperRepresentative_radialPosition | DEFINITION + THEOREM | aucune | SAME_MEMBER PASS | EXACT |
| la Tour d'un membre porte une fenêtre propre, qui existe | kappa lu à l'origine de l'orbite, m = floor(T log 4 / pi) + 1 | tRatioFourOperator | DEFINITION DE CONTROLE | la règle de détermination de l'état propre, absente des maîtres | SAME_OPERATOR PASS | MISSING |
| la cellule rencontre réellement l'axe algébrique | rapport multiplicatif quatre, Bertrand deux fois | thm_ratioFourOperator_cellFoundCount_positive | THEOREM SUR LE CONTROLE | le porteur canonique, non déterminé | SAME_CELL PASS | MISSING |
| le premier central est réellement dans la cellule | rang central entre les deux rangs aux bords | thm_ratioFourOperator_centralPrime_in_cell | THEOREM SUR LE CONTROLE | le porteur canonique, non déterminé | SAME_CENTRAL_PRIME PASS | MISSING |
| la loi locale parle du premier central DU porteur | composition avec le représentant supérieur | PLocalLawOnOperator, fnOperatorMemberCentralPrime | DEFINITION | aucune | SAME_OPERATOR PASS | EXACT |
| le transport se lit clause par clause | équivalence exacte avec (loi locale) ET (absence de passage nul) | thm_rpass_iff_localLaw_and_noNullPassage | THEOREM | aucune | SAME_PASSAGE PASS | EXACT |
| les extrémités de l'image sont distinctes, ordonnées, sans corridor | positivité primitive des écarts entre premiers successifs | thm_rpassClause_order, thm_rpassClause_endpointsDistinct, thm_rpassClause_corridorEmpty | THEOREM | la loi locale (CONTROL_INPUT nommé) | SAME_PLACE PASS | EXACT |
| la force résiduelle est nommée, pas dissimulée | équivalence compilée avec la centralité de tous les vrais zéros | thm_noNullPassage_iff_allOnCriticalLine, thm_noNullPassage_of_riemannHypothesis | THEOREM | aucune | SAME_E_OFF PASS | EXACT |
| le zéro hors ligne est impossible, sur LE MEME passage | passage nul de la branche OFF contre place jamais nulle | thm_sameE_offCriticalLine_impossible | THEOREM | R-PASS sur le porteur (SCIENTIFIC_RESIDUAL_INPUT) | SAME_E_OFF PASS | CONDITIONAL |
| la centralité se relit sur l'énoncé public | confinement dans la bande ouverte, équation fonctionnelle | thm_riemannHypothesis_of_allUpperOnCriticalLine | THEOREM | la centralité de la branche supérieure (CONTROL_INPUT nommé) | SAME_MEMBER PASS | EXACT |
| l'énoncé public sous le seul transport | composition des deux précédents | thm_riemannHypothesis_of_rpassOnOperator, thm_riemannHypothesis_of_noNullPassage | THEOREM | R-PASS, ou la clause forte (SCIENTIFIC_RESIDUAL_INPUT) | SAME_E_OFF PASS | CONDITIONAL |

    SCIENTIFIC_RESIDUAL_INPUT_COUNT = 1

L'unique entrée scientifique résiduelle est la clause forte du transport,
`PNoNullZeroPassage`, équivalente à la loi locale portée par le porteur une fois
les clauses libres acquises.  Elle est NOMMEE, et son équivalence de force avec
`RiemannHypothesis` est COMPILEE dans les deux sens
(`thm_noNullPassage_iff_allOnCriticalLine` puis
`thm_riemannHypothesis_of_noNullPassage` et
`thm_noNullPassage_of_riemannHypothesis`).  Elle n'est donc pas dissimulée dans
un prédicat opaque, et rien en aval ne la suppose sans la nommer.

Ce n'est pas une circularité : elle n'est DERIVEE de la conclusion nulle part.
Elle est isolée comme le théorème décisif de la route, ce que § 6.1 du fichier
opérationnel autorise explicitement.

## SAME-OBJECT (§ N.2.E)

    SAME_MEMBER        PASS  (thm_upperRepresentative_radialPosition, thm_operatorMemberCentralPrime_functionOfMember)
    SAME_PASSAGE       PASS  (la décomposition de R-PASS porte sur le passage lui-même)
    SAME_MIDDLE        PASS  (thm_triple_twoHeightGaps_positive_on_operator, même membre médian)
    SAME_HISTORY       PASS  (la place est indexée dans l'unique histoire première de O6)
    SAME_OPERATOR      PASS  (fnOperatorMemberCentralPrime est une lecture du porteur ; un seul porteur threadé)
    SAME_WINDOW_OR_EVENT  PASS  (une fenêtre par membre, tRatioFourWindow)
    SAME_CONTACTS      PASS  (thm_ratioFourOperator_contactMinus_formula, fonction du seul membre)
    SAME_CELL          PASS  (tOperatorCell, fonction du seul membre)
    SAME_CENTRAL_PRIME PASS  (thm_ratioFourOperator_centralPrime_mem_found)
    SAME_OCCURRENCE    NOT_APPLICABLE
    SAME_PLACE         PASS  (les deux extrémités sont celles de la place image du MEME passage)
    SAME_E_OFF         PASS  (la contradiction est opposée au passage produit par la branche OFF, jamais à un autre)

## FIDELITY_NEGATIVE_CHECKS (§ N.4)

    attribut annoncé sans réalisateur ......................... aucun ; 3 obligations restantes recensées
    theorem plus faible que le maître ......................... aucun trouvé ce tour
    hypothèse scientifique cachée dans une signature .......... aucune ; la seule entrée résiduelle est nommée et son équivalence est compilée
    objet libre remplaçant un objet canonique ................. aucun ; la loi locale est reportée sur le premier central DU porteur
    paramètre arbitraire présenté comme donnée propre ......... aucun ; kappa et m sont des lectures de l'état de Tour, et le module dit explicitement qu'il ne prétend pas fixer la fenêtre canonique du maître
    conséquence conditionnelle présentée comme producteur ..... aucune ; F4 à F7 sont déclarés conditionnels et le manifeste les enregistre ainsi
    changement de membre entre deux étapes .................... aucun
    changement de passage ..................................... aucun
    changement d'opérateur .................................... aucun ; un seul porteur, threadé
    changement de cellule ..................................... aucun
    utilisation d'une loi retirée ............................. aucune ; la pluralité de l'ensemble trouvé est au contraire PRODUITE
    R-ATT au-delà de sa portée ................................ non utilisé ce tour
    sélection arithmétique a posteriori de la Tour ............ aucune ; aucun premier, rang ou comptage n'entre dans nRatioFourSpan
    recherche de kappa ou de m ................................ aucune ; les deux coordonnées sont des fonctions de la hauteur et de la phase
    contradiction OFF sur un passage différent ................ NON ; le passage est obtenu puis consommé sans substitution
    positivité de l'écart des zéros supposée quelque part ..... NON ; elle est conclue
    hypothèse de Riemann utilisée ou niée ..................... NON ; `RiemannHypothesis` n'apparaît qu'en CONCLUSION, sauf dans thm_noNullPassage_of_riemannHypothesis, qui est la réciproque déclarée servant à mesurer la force résiduelle et n'est consommée par aucun théorème de la route

## Ce que ce tour ne ferme PAS, et pourquoi exactement

    LL.LOCAL_LAW_PRODUCER     BLOCKED_FOR_EXACT_CLOSURE.  Produire la loi locale
                              exige une règle de détermination de la fenêtre
                              CANONIQUE.  Le maître Lean § S4 fixe
                              C_- = min(C1,C2) et C_+ = max(C1,C2) sans définir
                              C1 ni C2 ; aucune règle n'est donc déterminée par
                              les maîtres, et en fabriquer une serait ouvrir un
                              problème, ce que § 6.1 interdit.
    O8.RPASS_REAL_TRANSPORT   Même blocage, par la décomposition : les clauses
                              libres sont acquises, la clause forte reste.
    TERMINAL.RIEMANN_HYPOTHESIS
                              Le theorem SANS hypothèse n'existe pas.  Les deux
                              formes conditionnelles existent et sont
                              certifiées.

    LEAN_FINAL_RH_CERTIFIED = false

---

## CORRECTIONS APPORTEES PAR LE TOUR T03

Trois défauts de ce manifeste sont corrigés ici, et les corrections font
autorité sur ce qui précède.

**1. Deux réalisateurs sont RETRACTES.**  `tRatioFourOperator` avait été inscrit
comme réalisateur de `S4.INHABITANT`, et
`thm_ratioFourOperator_cellFoundCount_positive` comme réalisateur de la cellule
canonique non vide.  Un simple HABITANT d'un type ne réalise jamais un objet que
les maîtres appellent CANONIQUE : il prouve que le type n'est pas vide, il ne
fournit aucune règle de détermination, et c'est la règle qui est l'obligation.
Les deux lignes du registre reviennent à `—`, et le compte d'obligations sans
réalisateur passe de 3 à 5.  Les deux théorèmes restent vrais et compilés, comme
CONTROLES.

**2. `CLOS conditionnellement` est un statut illégal.**  Il n'appartient pas au
vocabulaire de § N.3 et il laisse croire à une fermeture.  F6 et F7 sont
`CONDITIONAL`, et `CONDITIONAL` n'est jamais `EXACT`.

**3. La causalité de S4 était inversée.**  Ce tour lisait les contacts à partir
d'une fenêtre `(kappa, m)` posée.  L'ordre imposé est
`z -> état propre -> deux contacts -> (T, beta) -> recoveredKappa/recoveredSpan`,
et jamais `kappa, m -> contacts`.  Le tour T03 produit l'état propre et
récupère les deux coordonnées ; la lecture indexée par une fenêtre survit
uniquement comme dictionnaire, et `thm_recoveredWindow_contacts` établit qu'elle
rend exactement les deux contacts de départ.
