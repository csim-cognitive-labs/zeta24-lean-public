# Manifeste de tour — T00-BOOTSTRAP

    TOUR_ID = T00-BOOTSTRAP
    TIMESTAMP = 2026-09-09
    KIND = INFRASTRUCTURE_BOOTSTRAP
    EXCEPTION_INVOQUEE = maître Lean § N.9, exception unique INFRASTRUCTURE_BOOTSTRAP

Ce tour ne produit AUCUN théorème scientifique et ne ferme AUCUNE obligation de
la route.  Il installe la boucle de validation exigée par les sections L–Q du
maître Lean, puis exécute le replay cumulatif des couches 0–4.

    HEAD_BEFORE = 2664582b8b1dc8813d3f6322257dca5c884467bc
    HEAD_AFTER = aa733d66199b2d243fa0b20ec00007771b0431be
    ORIGIN_MAIN_SHA = aa733d66199b2d243fa0b20ec00007771b0431be

Les deux SHA ont été inscrits par le commit de confirmation qui suit
immédiatement le push, conformément à § N.7 : un SHA ne peut pas être écrit
dans le fichier qu'il identifie.

    FILES_CHANGED = lakefile.toml, Certification/ChallengeDeps.lean, Certification/Challenge.lean, Certification/Solution.lean, Certification/PrintAxioms.lean, Certification/comparator.json, Certification/comparator_manifest.json, Certification/CHALLENGE_FROZEN_GIT_BLOB, Certification/run_comparator.sh, audit_fidelity.sh, validate_cycle.sh, audit_contracts.sh, CONTRACTS.md, audits/REPLAY_LAYERS_0_4.md, audits/tours/T00-BOOTSTRAP.md

    PUBLIC_REALISERS_ADDED = aucun
    PUBLIC_REALISERS_MODIFIED = aucun

Les 38 théorèmes `cmp_*` de `Certification/Challenge.lean` ne sont pas des
réalisateurs nouveaux : ce sont les MEMES énoncés que les théorèmes déjà
produits, gelés sous un blob Git pour interdire toute dérive ultérieure.  Aucun
n'introduit d'hypothèse que le théorème de production n'avait pas.

    SEMANTIC_STEPS = aucune nouvelle ; contrôle de toutes les étapes déjà produites
    MATHEMATICAL_STEPS = aucune nouvelle

    COMPARATOR_TARGETS = Certification/comparator.json (38 cibles, familles C0 C1 C2 C3 C4)
    COMPARATOR_DELTA_RESULT = PASS (38/38, nanoda + noyau Lean)
    CONTRACT_AUDIT_RESULT = PASS
    FIDELITY_AUDIT_RESULT = PASS
    SAME_OBJECT_RESULTS = PASS (détail plus bas)
    AXIOMS_RESULT = [propext, Quot.sound, Classical.choice]
    BUILD_RESULT = PASS

    RESIDUAL_OBLIGATIONS_BEFORE = 8
    RESIDUAL_OBLIGATIONS_AFTER = 10

    NEXT_CONSUMER = S4.INHABITANT — un terme habitant TCanonicalTowerOperator
    PUSH_STATUS = PASS — HEAD_AFTER_LOCAL = ORIGIN_MAIN_AFTER_PUSH = aa733d66

## Tableau de fidélité (§ N.3)

| Étape sémantique | Étape mathématique | Réalisateur Lean exact | Nature | Hypothèses résiduelles | SAME-object | Fidélité |
|---|---|---|---|---|---|---|
| aucune — tour d'infrastructure | aucune | Certification/Challenge.lean (38 cmp_*) | THEOREM (gel d'énoncés) | aucune | NOT_APPLICABLE | EXACT |
| aucune | aucune | Certification/Solution.lean | THEOREM (rejeu) | aucune | NOT_APPLICABLE | EXACT |
| aucune | aucune | audit_fidelity.sh | AUDIT | aucune | NOT_APPLICABLE | EXACT |
| aucune | aucune | validate_cycle.sh | AUDIT | aucune | NOT_APPLICABLE | EXACT |
| aucune | aucune | audits/REPLAY_LAYERS_0_4.md | REPLAY | aucune | NOT_APPLICABLE | EXACT |

Aucune ligne de la ROUTE ne passe de MISSING à EXACT dans ce tour.  La
progression au sens de § N.13 est celle du second cas admis : renforcement de
l'infrastructure de certification sans changer les mathématiques.

## SAME-OBJECT (§ N.2.E)

    SAME_MEMBER        PASS  (aucun changement de membre introduit)
    SAME_PASSAGE       PASS
    SAME_MIDDLE        PASS  (thm_triple_sameMiddleMember reste ⟨rfl, rfl⟩)
    SAME_HISTORY       PASS  (fnPrimeAtRank unique, thm_primeHistory_unique)
    SAME_OPERATOR      NOT_APPLICABLE_NO_INHABITANT
    SAME_WINDOW_OR_EVENT  NOT_APPLICABLE
    SAME_CONTACTS      PASS
    SAME_CELL          PASS
    SAME_CENTRAL_PRIME PASS
    SAME_OCCURRENCE    PASS
    SAME_PLACE         PASS
    SAME_E_OFF         NOT_APPLICABLE

## FIDELITY_NEGATIVE_CHECKS (§ N.4)

    attribut annoncé sans réalisateur ......................... contrôlé, 10 recensés
    theorem plus faible que le maître ......................... 1 TROUVE : LL.SAME_OPERATOR
    hypothèse scientifique cachée dans une signature .......... aucune trouvée
    objet libre remplaçant un objet canonique ................. 1 TROUVE : fnMemberCentralPrime libre dans la loi locale
    paramètre arbitraire présenté comme donnée propre ......... aucun (la fenêtre libre est déclarée comme telle)
    conséquence conditionnelle présentée comme producteur ..... aucune
    changement de membre entre deux étapes .................... aucun
    changement de passage ..................................... aucun
    changement d'opérateur .................................... sans objet, aucun habitant
    changement de cellule ..................................... aucun
    utilisation d'une loi retirée ............................. aucune (garde mécanique § 4a)
    R-ATT au-delà de sa portée ................................ aucune (garde § 4d + thm_rATT_doesNotSeparatePrimes)
    sélection arithmétique a posteriori de la Tour ............ aucune (garde § 4c)
    contradiction OFF sur un passage différent ................ sans objet, aucune contradiction produite

Deux défauts réels trouvés, tous deux inscrits au registre : ils ne sont pas
corrigés par ce tour, ils sont rendus VISIBLES et COMPTES.
