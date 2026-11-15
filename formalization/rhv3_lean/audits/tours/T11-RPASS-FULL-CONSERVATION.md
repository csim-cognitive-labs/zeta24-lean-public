# Manifeste — T11-RPASS-FULL-CONSERVATION

    TOUR_ID = T11-RPASS-FULL-CONSERVATION
    TIMESTAMP = 2026-09-10
    HEAD_BEFORE = 17db2bd52215d6e0a7dc03b9da2e93faa9e5d62d
    HEAD_AFTER = pending
    ORIGIN_MAIN_SHA = pending push
    FILES_CHANGED = RHV3Lean.lean, RHV3Lean/Objects/RPassFull.lean (nouveau),
                    Certification/Challenge.lean, Solution.lean,
                    PrintAxioms.lean, comparator.json,
                    Certification/CHALLENGE_FROZEN_GIT_BLOB, CONTRACTS.md,
                    ce manifeste, docs/RHV2_STRATEGIE_LEAN.md (avertissement
                    LEGACY en tête, append-only).
    PUBLIC_REALISERS_ADDED = PIsFullMemberSensitivePassageTransport,
                    thm_fullRpass_is_memberSensitive, thm_fullRpass_null_iff,
                    thm_fullRpass_null_of_sourceNull,
                    thm_fullRpass_nonNull_of_sourceNonNull
    PUBLIC_REALISERS_MODIFIED = aucun (additif seul ; PIsMemberSensitivePassageTransport
                    inchangé, conservé comme premier conjoint)
    SEMANTIC_STEPS = R-PASS complet (maître sémantique §6.2) : le transport
                    canonique conserve, en plus des deux extrémités déjà
                    produites, le statut relationnel nul/non-nul du MÊME
                    passage, comme équivalence exacte.
    MATHEMATICAL_STEPS = Null_Z(E) <-> Null_P(Phi(E)) posé comme second
                    conjoint d'une définition Prop, jamais reçu comme
                    hypothèse terminale ; les deux boxed du maître (Null_Z=>Null_P,
                    NonNull_Z=>NonNull_P) dérivés PUREMENT LOGIQUEMENT de cette
                    équivalence (mp direct, mpr par contraposition) — aucun
                    nouveau fait mathématique, seulement la structure exacte
                    que le futur producteur T2 devra satisfaire.
    COMPARATOR_TARGETS = Certification/comparator.json (+2 :
                    cmp_O8_fullRpass_null_of_sourceNull,
                    cmp_O8_fullRpass_nonNull_of_sourceNonNull)
    COMPARATOR_DELTA_RESULT = voir ci-dessous
    CONTRACT_AUDIT_RESULT = PASS
    FIDELITY_AUDIT_RESULT = voir ci-dessous
    SAME_OBJECT_RESULTS = SAME_PASSAGE PASS — la clause de nullité de
                    `PIsFullMemberSensitivePassageTransport` porte sur le
                    MÊME `tPassage` que la clause d'extrémités héritée ;
                    aucun second passage n'est introduit.
    AXIOMS_RESULT = permitted only [propext, Classical.choice, Quot.sound] ;
                    aucun axiome nouveau
    BUILD_RESULT = PASS
    RH_EQUIVALENT_CONTRACTS =
    RESIDUAL_OBLIGATIONS_BEFORE = R-PASS classé TO_REWRITE (endpoint-only
                    seulement, maître §RH_STRATEGIE_LEAN L18)
    RESIDUAL_OBLIGATIONS_AFTER = l'énoncé exact de R-PASS complet existe et
                    compile ; son PRODUCTEUR (un terme réel de
                    `PIsFullMemberSensitivePassageTransport` sur le transport
                    canonique) reste NOT_YET_CERTIFIED_LEAN, car il dépend de
                    T1/T2/l'occurrence complète, eux-mêmes non produits. Ce
                    tour ne les suppose à aucun moment : `PImageRelationNull`
                    reste un paramètre abstrait, jamais instancié.
    NEXT_CONSUMER = le producteur T2 réel, une fois T1/C3/occurrence produits,
                    devra exhiber un terme de
                    `PIsFullMemberSensitivePassageTransport` et consommer
                    `thm_fullRpass_null_of_sourceNull` /
                    `thm_fullRpass_nonNull_of_sourceNonNull` dans la
                    contradiction terminale §9.
    PUSH_STATUS = pending

## Recherche historique menée ce tour (maître Lean §21)

Recherche par mots-clés (localization, prime count, von Mangoldt, Chebyshev,
explicit formula, Perron, contact cell, unique prime, canonical prime, prime
occurrence, rank reconstruction) dans `formalization/rhv2_fresh` et
`formalization/rh_gap_criterion`, au-delà de la recherche du tour précédent.

**Candidat : `CanonicalOperatorArbitrarinessAudit.lean::thm_arbitraryOperator_violates_canonicalT1`.**
Étape : audit — un opérateur arbitraire échoue T1. Hypothèses : aucune
(théorème inconditionnel de réfutation d'un candidat). Déjà produit en RHV3 :
non porté (audit seulement). Réutilisable : oui, comme avertissement/audit
seulement, jamais comme producteur. Cible RHV3 : aucune — confirme seulement
qu'aucun remplissage naïf des champs ne vaut T1.

**Candidat : `T1T2QuantitativeObstruction.lean::thm_T1_T2_summed_cost`.**
Étape : mesure quantitative du coût conjoint T1+T2 sur une chaîne.
Hypothèses : T1 ponctuel et alignement de rang T2, tous deux FOURNIS en
hypothèse. Déjà produit en RHV3 : non. Réutilisable : théorème pur,
inconditionnel, mais c'est un outil de mesure sur des états fournis, pas un
producteur de T1 ; son propre auteur le classe `NOT_ACTIVE_ROUTE`. Cible
RHV3 : aucune — ne sert ni T1 ni R-PASS ; non porté, conformément à
l'instruction de ne jamais transformer une difficulté T1 en conclusion
mathématique.

**Candidat : `PrimeLocalization.lean::PUniquePrimeLocalizationAt` +
`subPrimeAuditReadout`.** Étape : audit — une fenêtre à gauche du premier
fixe échoue. Hypothèses : aucune. Déjà produit en RHV3 : non. Réutilisable :
audit seulement, même famille que le contrôle ratio-four de T10. Cible RHV3 :
aucune.

**Candidat : `CentralPrimeRoute.lean`.** Étape : route CENTRALITÉ (médiane),
alternative retirée à T1 singleton. Hypothèses : dépend d'un choix
architectural différent (pluralité + médiane). Déjà produit en RHV3 : non —
le maître sémantique actif (§4, `RH_STRATEGIE_SEMANTIQUE.md`) réaffirme
explicitement N_P=1, pas la médiane. Réutilisable : non, sans contredire le
maître actif ; cette route a été explicitement retirée par une version
antérieure puis le maître actif y est revenu. Cible RHV3 : aucune.

**Candidat : `Master/Definitive/CorrespondenceProduction.lean`,
`CanonicalT1.lean`.** Étape : producteurs T1 conditionnels (reçoivent
`hT1`/`placeIndex`). Hypothèses : reçoivent exactement ce qu'ils devraient
produire. Déjà produit en RHV3 : non. Réutilisable : non — prémisse interdite
(§14 du maître : « qui produit un terme ? »). Cible RHV3 : aucune.

Aucun nouveau corps causal inconditionnel de T1 n'a été trouvé ce tour. Ceci
ne requalifie PAS T1 en mathématique ouverte : conformément au maître actif,
le statut reste exactement

    T1_CANONICAL_COUNT_EQ_ONE = NOT_YET_CERTIFIED_LEAN

## Bloc indépendant produit ce tour : R-PASS complet (énoncé)

Le maître §RH_STRATEGIE_LEAN classe L18 (R-PASS complet) `TO_REWRITE`,
indépendamment de T1/T2 au niveau de l'ÉNONCÉ (seul le PRODUCTEUR en dépend).
Ce tour produit l'énoncé exact et ses deux conséquences logiques immédiates,
sans aucune instance fournie ni supposée.

    LEAN_FINAL_RH_CERTIFIED = false
