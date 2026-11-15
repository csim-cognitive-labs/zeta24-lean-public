# Manifeste — T10-CANONICAL-CONTACT-PRODUCER

    TOUR_ID = T10-CANONICAL-CONTACT-PRODUCER
    TIMESTAMP = 2026-09-10
    HEAD_BEFORE = 48333255754b3f6f046515db5eed90984735e4c3
    HEAD_AFTER = pending
    ORIGIN_MAIN_SHA = pending push
    FILES_CHANGED = RHV3Lean.lean, RHV3Lean/Objects/CanonicalTrueTowerState.lean
                    (nouveau), Certification/Challenge.lean, Solution.lean,
                    PrintAxioms.lean, comparator.json,
                    Certification/CHALLENGE_FROZEN_GIT_BLOB,
                    audits/CONTROL_ONLY_INHABITANTS.txt, ce manifeste.
    PUBLIC_REALISERS_ADDED = rCanonicalContactThreshold,
                    kCanonicalContactAddress, canonicalTrueTowerState,
                    thm_canonicalContact_consecutive_width,
                    thm_canonicalContact_tangent_law,
                    thm_canonicalContactMinus_ge_two,
                    thm_canonicalTrueTowerState_injective,
                    tCanonicalTrueTowerCarrier,
                    thm_canonicalTrueTowerCarrier_state,
                    PCanonicalCellFoundCountOne (proposition SEULE, non prouvée)
    PUBLIC_REALISERS_MODIFIED = aucun (additif seul)
    SEMANTIC_STEPS = recherche historique exhaustive (rh_gap_criterion,
                    RHV2TrueContacts.lean::canonicalContactAddress) ; portage
                    contacts-only d'une règle de détermination en forme close,
                    sans adresse/rang/comptage exposé dans l'API publique
    MATHEMATICAL_STEPS = instanciation des deux lois génériques déjà prouvées
                    (largeur, tangentielle) à l'adresse
                    kappa*(z) = ceil(max(0,(T*log2-phi)/pi)) ; preuve que le
                    contact d'entrée à cette adresse est >= 2
    COMPARATOR_TARGETS = Certification/comparator.json (+3 :
                    cmp_S4_canonical_contactMinus_ge_two,
                    cmp_S4_canonical_same_contacts_same_member,
                    cmp_S4_canonical_carrier_state)
    COMPARATOR_DELTA_RESULT = voir ci-dessous
    CONTRACT_AUDIT_RESULT = PASS
    FIDELITY_AUDIT_RESULT = voir ci-dessous
    SAME_OBJECT_RESULTS = SAME_MEMBER PASS (thm_canonicalTrueTowerState_injective,
                    spécialisation de thm_same_true_contacts_same_member)
    AXIOMS_RESULT = permitted only [propext, Classical.choice, Quot.sound] ;
                    aucun axiome nouveau ; #print axioms confirmé sur les 3
                    nouvelles cibles
    BUILD_RESULT = PASS
    RH_EQUIVALENT_CONTRACTS =
    RESIDUAL_OBLIGATIONS_BEFORE = T1 NOT_YET_CERTIFIED_LEAN ; « aucun
                    producteur canonique des contacts n'existe » non vérifié
    RESIDUAL_OBLIGATIONS_AFTER = « aucun producteur canonique des contacts
                    n'existe » RÉFUTÉ — un producteur réel, en forme close,
                    est produit et compilé ; T1 reste NOT_YET_CERTIFIED_LEAN
                    sur CET état, sans changement de statut
    NEXT_CONSUMER = thm_canonicalCell_foundCount_eq_one (T1) sur
                    canonicalTrueTowerState — toujours ouvert
    PUSH_STATUS = pending

## Ce que ce tour établit

Recherche historique exhaustive (git log/grep sur tout l'arbre, pas seulement
HEAD) : `formalization/rh_gap_criterion/RiemannHypothesisProof/RHV2TrueContacts.lean`
contient `canonicalContactAddress`, un calcul en forme close de la plus petite
adresse dont l'incidence tangentielle atteint la région de comptage `x>=2`.
Ce n'est ni une recherche de premier, ni une sélection par rang, ni un
habitant arbitraire : c'est une fonction déterministe des seules coordonnées
propres du membre (`T`, `phi`).

Ce tour porte cette règle dans RHV3, contacts-only (aucune adresse ni aucun
`kappa`/`m` n'est exposé publiquement — `kCanonicalContactAddress` reste
interne à la construction de `canonicalTrueTowerState`), et prouve les deux
équations exigées par `TTrueHarmonicTowerState` à cette adresse par pure
INSTANCIATION des deux théorèmes génériques déjà prouvés dans
`ContactsAndCell.lean` (`thm_cellLogDiameter_formula`,
`thm_inversion_recovers_radialPosition`), sans aucune preuve nouvelle des lois
elles-mêmes.

Conclusion précise : le diagnostic du tour précédent (« TTrueHarmonicTowerState
ne produit pas la paire canonique ») reste vrai pour le TYPE seul, mais la
conclusion plus forte « aucun producteur canonique des contacts n'existe »
était FAUSSE et est ici réfutée par un contre-exemple constructif compilé.

## Ce que ce tour n'établit PAS

`thm_canonicalContactMinus_ge_two` prouve seulement `2 <= C-`. Aucun theorem
de ce tour ne prétend, et `PCanonicalCellFoundCountOne` reste une PROPOSITION
non prouvée, exactement comme le corpus historique le faisait déjà pour
l'énoncé analogue `EveryCanonicalCenterHitsPrime`
(`RHV2ContactPrimeReadout.lean`, commentaire explicite : « no claim that its
value is universally 1 or 3 »).

La largeur de la cellule à cette adresse est `pi/T`, qui décroît vers 0
lorsque `T` croît, tandis que le contact d'entrée reste borné près de `2`
(propriété même de l'adresse minimale). C'est un avertissement mathématique
motivant la prudence sur `PCanonicalCellFoundCountOne`, PAS un theorem Lean :
aucune conclusion n'en est tirée dans le code.

`tCanonicalTrueTowerCarrier` est déclaré CONTROL_ONLY dans
`audits/CONTROL_ONLY_INHABITANTS.txt`, avec une note le distinguant des
habitants purement arbitraires (`tRatioFourOperator`, `tPrincipalBranchCarrier`) :
aucun maître actuel ne définit C1/C2, donc rien ne certifie que cette règle
précise est CELLE que les maîtres appellent canonique.

    LEAN_FINAL_RH_CERTIFIED = false
