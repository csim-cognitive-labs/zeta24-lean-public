# Manifeste de tour — T01-OFF-UPPER

    TOUR_ID = T01-OFF-UPPER
    TIMESTAMP = 2026-09-09
    KIND = SCIENTIFIC_PRODUCTION
    REPRISE = autorisée par § Q.10 après T00-BOOTSTRAP

    HEAD_BEFORE = a55ae5dbef72c04df11ceb96868867d347f7dd65
    HEAD_AFTER = 2e081a3b5fe319ad937f9f6bebbba8338faf574a
    ORIGIN_MAIN_SHA = 2e081a3b5fe319ad937f9f6bebbba8338faf574a

    FILES_CHANGED = RHV3Lean/Objects/OffFibreAndPassage.lean, RHV3Lean.lean, Certification/Challenge.lean, Certification/Solution.lean, Certification/comparator.json, Certification/comparator_manifest.json, Certification/CHALLENGE_FROZEN_GIT_BLOB, Certification/PrintAxioms.lean, CONTRACTS.md, audits/tours/T01-OFF-UPPER.md

    PUBLIC_REALISERS_ADDED = thm_zeroHeightFiber_finite, thm_sameFiberInterposition, thm_existsConsecutiveInFiber, thm_offCriticalLine_existsNullPassage, thm_offCriticalLine_existsNullRelationPassage, zUpperOfPositiveHeight, thm_zUpperOfPositiveHeight_sameMember, tPassageUpperEndpoints, thm_passageEndpoints_upperBranch
    PUBLIC_REALISERS_MODIFIED = aucun

    SEMANTIC_STEPS = troisième paragraphe, première partie : le miroir donne deux membres distincts de même hauteur ; la fibre est finie ; deux d'entre eux sont voisins ; leur passage est d'écart nul
    MATHEMATICAL_STEPS = finitude par compacité et discrétion des zéros de zêta ; minimum d'un ensemble fini pour la clé d'ordre ; verrou lexicographique de la fibre ; déduction de la positivité de la hauteur de sortie

    COMPARATOR_TARGETS = Certification/comparator.json (44 cibles ; 6 nouvelles, familles C5 et ROUTE)
    COMPARATOR_DELTA_RESULT = PASS
    CONTRACT_AUDIT_RESULT = PASS
    FIDELITY_AUDIT_RESULT = PASS
    SAME_OBJECT_RESULTS = PASS (détail plus bas)
    AXIOMS_RESULT = [propext, Quot.sound, Classical.choice]
    BUILD_RESULT = PASS

    CHALLENGE_BLOB_BEFORE = aca5654b2aa5b3680d3360d107fae21298389e62
    CHALLENGE_BLOB_AFTER = fefc90e35ae520189050ba0221597b3f0703f22e

Le blob change parce que six cibles sont AJOUTEES.  Aucun énoncé existant n'est
touché : le diff est de 58 insertions et 0 suppression, et le préfixe du
fichier est byte-identique à la version gelée en T00.  Ce n'est donc pas une
mutation d'énoncé au sens de § M.2, dont l'interdiction porte sur la
modification d'un statement pour faire passer une Solution.

    RESIDUAL_OBLIGATIONS_BEFORE = 10
    RESIDUAL_OBLIGATIONS_AFTER = 7

    NEXT_CONSUMER = S4.INHABITANT, puis LL.SAME_OPERATOR
    PUSH_STATUS = PASS — HEAD_AFTER_LOCAL = ORIGIN_MAIN_AFTER_PUSH = 2e081a3b

## Tableau de fidélité (§ N.3)

| Étape sémantique | Étape mathématique | Réalisateur Lean exact | Nature | Hypothèses résiduelles | SAME-object | Fidélité |
|---|---|---|---|---|---|---|
| la fibre de hauteur ne porte qu'un nombre fini de membres | compact [0,1]x{T} inter zéros de zêta, fini | thm_zeroHeightFiber_finite | THEOREM | aucune | SAME_MEMBER PASS | EXACT |
| rien d'étranger ne s'interpose dans une fibre | clause lexicographique | thm_sameFiberInterposition | THEOREM | aucune | SAME_MEMBER PASS | EXACT |
| deux membres de la fibre sont voisins | minimum d'un ensemble fini pour la clé d'ordre | thm_existsConsecutiveInFiber | THEOREM | aucune | SAME_MEMBER PASS | EXACT |
| le zéro hors ligne produit un vrai passage d'écart nul | miroir + finitude + extraction | thm_offCriticalLine_existsNullPassage | THEOREM | aucune | SAME_PASSAGE PASS | EXACT |
| la même conclusion en nullité de relation | définition dérivée de la nullité | thm_offCriticalLine_existsNullRelationPassage | THEOREM | aucune | SAME_PASSAGE PASS | EXACT |
| chaque extrémité du passage porte sa propre Tour | positivité de la hauteur de sortie déduite de l'écart non négatif | tPassageUpperEndpoints, thm_passageEndpoints_upperBranch | DEFINITION + THEOREM | 0 < hauteur de l'extrémité d'entrée (STRUCTURAL_INPUT) | SAME_MEMBER PASS | EXACT |

    SCIENTIFIC_RESIDUAL_INPUT_COUNT = 0

L'hypothèse `0 < rZeroHeight tPassage.zEarlierMember` du bridge est classée
STRUCTURAL_INPUT et non SCIENTIFIC_RESIDUAL_INPUT : c'est le typage en branche
supérieure du membre d'entrée, qui est une donnée du membre déjà produite en
O1, et non une proposition mathématique à démontrer.  La positivité de la
hauteur de SORTIE, elle, n'est pas supposée : elle est déduite.

## SAME-OBJECT (§ N.2.E)

    SAME_MEMBER        PASS  (thm_zUpperOfPositiveHeight_sameMember : .1 = le membre de départ, par rfl)
    SAME_PASSAGE       PASS  (l'écart nul est établi sur LE passage construit, pas sur un autre)
    SAME_MIDDLE        NOT_APPLICABLE
    SAME_HISTORY       NOT_APPLICABLE (aucun premier n'entre dans ce tour)
    SAME_OPERATOR      NOT_APPLICABLE_NO_INHABITANT
    SAME_WINDOW_OR_EVENT  NOT_APPLICABLE
    SAME_CONTACTS      NOT_APPLICABLE
    SAME_CELL          NOT_APPLICABLE
    SAME_CENTRAL_PRIME NOT_APPLICABLE
    SAME_OCCURRENCE    NOT_APPLICABLE
    SAME_PLACE         NOT_APPLICABLE
    SAME_E_OFF         PASS  (le passage retourné est unique et nommé ; aucune contradiction n'est encore formée)

## FIDELITY_NEGATIVE_CHECKS (§ N.4)

    attribut annoncé sans réalisateur ......................... aucun ; 7 obligations restantes recensées
    theorem plus faible que le maître ......................... aucun trouvé ce tour
    hypothèse scientifique cachée dans une signature .......... aucune ; la seule hypothèse du bridge est structurelle
    objet libre remplaçant un objet canonique ................. aucun
    paramètre arbitraire présenté comme donnée propre ......... aucun
    conséquence conditionnelle présentée comme producteur ..... aucune ; les cinq théorèmes OFF sont inconditionnels
    changement de membre entre deux étapes .................... aucun
    changement de passage ..................................... aucun
    changement d'opérateur .................................... sans objet
    changement de cellule ..................................... sans objet
    utilisation d'une loi retirée ............................. aucune (garde mécanique)
    R-ATT au-delà de sa portée ................................ sans objet
    sélection arithmétique a posteriori de la Tour ............ sans objet
    contradiction OFF sur un passage différent ................ sans objet : aucune contradiction n'est formée ce tour
    positivité de l'écart des zéros supposée quelque part ..... NON ; l'écart nul est CONSTRUIT, jamais nié
    hypothèse de Riemann utilisée ou niée ..................... NON ; seule `PIsOffCriticalLine` (beta != 1/2) entre

## Ce que ce tour ne ferme PAS

    OFF.SAME_E_FORWARDING     le passage nul produit ici n'est pas encore
                              relié au passage sur lequel la loi locale conclut
                              la positivité ; c'est la contradiction terminale,
                              et elle exige d'abord S4 et la loi locale.
    TERM.*                    aucune ligne.
