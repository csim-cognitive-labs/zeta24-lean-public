# Manifeste de tour — T06-SAME-PRIME-COLLISION

    TOUR_ID = T06-SAME-PRIME-COLLISION
    TIMESTAMP = 2026-09-10
    KIND = ACTIVE_ROUTE_ALIGNMENT_AND_CONDITIONAL_CONSUMERS
    HEAD_BEFORE = a30eecf990d7718ce4be49b0b797a8baf2654f8f
    HEAD_AFTER = 97e9d93ec5b8264ae039486ba6bc8488b9bbebb3
    ORIGIN_MAIN_SHA = 97e9d93ec5b8264ae039486ba6bc8488b9bbebb3
    FILES_CHANGED = SamePrimeCollision, RHV3Lean root, Comparator, contracts, audits, E60 control
    PUBLIC_REALISERS_ADDED = exact OFF original/mirror wrappers; same-height and distinction; collision, centrality and RH consumers conditional on the two named upstream producers
    PUBLIC_REALISERS_MODIFIED = active terminal route changed from passage nullity/gap to same-prime mirror collision
    SEMANTIC_STEPS = genuine OFF upper member -> genuine functional mirror -> distinct same-height members -> supplied Y.3 same C3 -> supplied canonical injectivity -> contradiction
    MATHEMATICAL_STEPS = no contacts or cells identified; no global same-height same-C3 premise; E60 remains proof_premise=false
    COMPARATOR_TARGETS = Certification/comparator.json
    COMPARATOR_DELTA_RESULT = PASS
    COMPARATOR_CUMULATIVE_RESULT = PASS
    CONTRACT_AUDIT_RESULT = PASS with 17 honestly absent realisers
    SPECIFICATION_STRENGTH_AUDIT_RESULT = PASS including E60 and forbidden-dependency checks
    FIDELITY_AUDIT_RESULT = PASS for produced/conditional/missing classification
    SAME_OBJECT_RESULTS = SAME_MEMBER PASS; SAME_MIRROR PASS; SAME_HEIGHT PASS; DISTINCT_CONTACT_SYSTEMS_ALLOWED PASS; DISTINCT_CELLS_ALLOWED PASS; SAME_CANONICAL_PRIME MISSING; SAME_CANONICAL_HISTORY CONDITIONAL; NO_SYNTHETIC_ZERO PASS; NO_EMPIRICAL_PREMISE PASS
    AXIOMS_RESULT = [propext, Quot.sound, Classical.choice]
    BUILD_RESULT = PASS 3619 jobs
    RH_EQUIVALENT_CONTRACTS =
    RESIDUAL_OBLIGATIONS_BEFORE = 14
    RESIDUAL_OBLIGATIONS_AFTER = 17 including explicit active Y producers
    NEXT_CONSUMER = first exact missing body is thm_offMirror_sameCentralPrime_from_canonicalEvent; placeIndex must also be produced from contacts-only geometry
    PUSH_STATUS = PASS — implementation commit verified on origin/main

## Tableau de fidélité

| Étape sémantique | Étape mathématique | Réalisateur Lean exact | Fidélité |
|---|---|---|---|
| Tour propre par membre | contacts exacts membre-sensibles | TTrueHarmonicTowerState, TTrueTowerCarrier | EXACT |
| Décodage contacts | contacts vers hauteur, radial et membre | thm_decodedHeight_eq_zeroHeight, thm_decodedRadialPosition_eq_zeroRadialPosition, thm_contacts_decode_same_member | EXACT |
| Miroir fonctionnel OFF | vrai miroir supérieur, même hauteur, distinct | offOriginalUpperMember, offMirrorUpperMember, thm_offMirror_sameHeight, thm_offMirror_distinct | EXACT |
| Déformation autorisée | aucune égalité contacts/cellules dans le cône collision | audit_strength.sh | EXACT |
| Reconstruction arithmétique | cellule vers Lambda/psi/J/pi/C3 | thm_vonMangoldtChebyshev_reads_same_interval | EXACT |
| Progression première | rangs et premiers strictement ordonnés | thm_primeAtRank_strictMono, thm_primeAtRank_injective | EXACT |
| Provenance placeIndex contacts-only | C3 injectif sur les membres supérieurs | — | MISSING |
| Collision miroir Y.3 | vrai couple OFF vers même C3 malgré cellules propres | — | MISSING |
| Contradiction OFF | même C3 et injectivité contre membres distincts | thm_off_impossible_by_samePrimeCollision | CONDITIONAL |
| Universalisation | absence OFF vers centralité puis RH | thm_allUpperCentral_by_samePrimeCollision, riemannHypothesis_of_samePrimeCollision | CONDITIONAL |
| RiemannHypothesis fermé | theorem sans prémisse scientifique | — | MISSING |

## SAME-object et contrôle E60

    SAME_MEMBER = PASS
    SAME_MIRROR = PASS
    SAME_HEIGHT = PASS
    DISTINCT_CONTACT_SYSTEMS_ALLOWED = PASS
    DISTINCT_CELLS_ALLOWED = PASS
    SAME_CANONICAL_PRIME = MISSING_Y3_BODY
    SAME_CANONICAL_HISTORY = CONDITIONAL_ON_PLACEINDEX_PRODUCER
    NO_SYNTHETIC_ZERO = PASS
    NO_EMPIRICAL_PREMISE = PASS
    E60_CONTROL_RESULT = PASS
    LEAN_FINAL_RH_CERTIFIED = false
