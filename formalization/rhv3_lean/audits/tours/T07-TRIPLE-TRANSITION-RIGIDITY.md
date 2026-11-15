# T07 — TRIPLE TRANSITION RIGIDITY

    DATE = 2026-09-10
    HEAD_BEFORE = 86d6938d69056acc4fd460a7aa8e193e36925fbc
    ROUTE_BEFORE = SAME_PRIME_MIRROR_COLLISION
    ROUTE_AFTER = TRIPLE_TRANSITION_GRAMMAR_COLLISION

## Correction

Le tour T06 avait réduit la contradiction à une égalité isolée de C3 sur le
couple miroir. Cette réduction perdait l'objet grammatical réellement rigide :
la transition du triple.

T07 remet explicitement :

    Z0 -> Z1 -> Z2
    tauZ0, tauZ1

et :

    p_r -> p_(r+1) -> p_(r+2)
    tauP0, tauP1.

SAME-MIDDLE est matérialisé des deux côtés.

OFF produit une transition zéro source-sensible dont l'observable hauteur a
entrée = sortie. Les transitions premières canoniques restent strictes par
`thm_primeAtRank_strictMono`.

## Réalisateurs ajoutés

    TZeroTransitionEvent
    tZeroTransitionEvent
    tZeroTripleTransitions
    thm_zeroTripleTransitions_sharedMiddle
    thm_zeroTransition_heightDegenerate_iff_sameHeight

    TPrimeTransitionEvent
    tPrimeTransitionAt
    tPrimeTripleTransitions
    nTriplePrime0
    nTriplePrime1
    nTriplePrime2
    thm_primeTripleTransitions_sharedMiddle
    thm_threeCanonicalPrimes_strict
    thm_primeTransition_notDiagonal
    thm_primeTripleTransitions_notDiagonal

    thm_off_existsHeightDegenerateZeroTransition
    thm_off_impossible_of_transitionDegeneracyTransport

## Déclassement

    SamePrimeCollision.lean = LEGACY_DIAGNOSTIC_CONDITIONAL

L'égalité `C3(original)=C3(mirror)` n'est plus une cible scientifique.

## Point mathématique exact restant

Le `M^Z=M` historique égalise la grammaire PREMIERE reconstruite depuis les
zéros avec la grammaire première canonique. Les théorèmes de transition
historiques portent sur `zerosPrimePosition`.

Le raccord encore absent est :

    transition SOURCE-SENSIBLE du passage réel du triple
    =
    occurrence de transition correspondante dans M^Z.

Après ce raccord seulement, `M^Z=M` transporte cette même transition dans M.

    NEXT_BODY = thm_tripleSourceTransition_eq_reconstructedTransition
    NEXT_TRANSPORT = thm_tripleSourceTransition_eq_canonicalTransition
    RIEMANN_HYPOTHESIS_PROVED = false

## Validation

Les modifications sont poussées sur `main` via l'API GitHub. Aucun statut
`lake build`, Comparator ou `#print axioms` nouveau n'est déclaré ici : aucun
runner n'a été exécuté dans ce tour. Le dernier résultat compilé reste celui du
tour précédent jusqu'au prochain replay mécanique.
