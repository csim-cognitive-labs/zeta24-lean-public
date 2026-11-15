# Manifeste — T09-DIRECT-CONTACTS-T1-FRONTIER

    TOUR_ID = T09-DIRECT-CONTACTS-T1-FRONTIER
    TIMESTAMP = 2026-09-10
    HEAD_BEFORE = 22f77a6189fa9331bb4fd7d333e1089ce22eaeec
    HEAD_AFTER = 3f436bfb
    ORIGIN_MAIN_SHA = pending push
    FILES_CHANGED = masters, contracts, TrueTowerState, PrimeOccurrence, CountingRigidity, certification, audits and hand-over
    PUBLIC_REALISERS_ADDED = terminalCell, terminalCell_endpoints, terminalCell_decodes_source, thm_cellFoundCount_eq_one_iff_existsUniquePrime
    PUBLIC_REALISERS_MODIFIED = tTrueStateCell now aliases the direct state cell
    SEMANTIC_STEPS = zero Tower state -> direct contacts -> exact inversion -> same cell; O-ADR removed
    MATHEMATICAL_STEPS = direct Ioc cell and exact equivalence N_P=1 iff unique prime
    COMPARATOR_TARGETS = Certification/comparator.json
    COMPARATOR_DELTA_RESULT = PASS
    CONTRACT_AUDIT_RESULT = PASS
    FIDELITY_AUDIT_RESULT = PASS
    SAME_OBJECT_RESULTS = SAME_MEMBER PASS; SAME_CONTACTS PASS; SAME_CELL PASS
    AXIOMS_RESULT = permitted only; no new axiom
    BUILD_RESULT = PASS 3618 jobs
    RH_EQUIVALENT_CONTRACTS =
    RESIDUAL_OBLIGATIONS_BEFORE = O-ADR regression plus T1
    RESIDUAL_OBLIGATIONS_AFTER = O-ADR removed; unconditional T1 remains NOT_YET_CERTIFIED_LEAN
    NEXT_CONSUMER = thm_canonicalCell_foundCount_eq_one, then C3 and occurrence
    PUSH_STATUS = pending

| Étape | Corps | Réalisateur | Fidélité |
|---|---|---|---|
| contacts vers cellule | mêmes contacts, mêmes bords | terminalCell, terminalCell_endpoints | EXACT |
| cellule vers membre | inversion T et beta | terminalCell_decodes_source | EXACT |
| occurrence vers cellule | aucune seconde construction | tTrueStateCell | EXACT |
| forme logique de T1 | cardinal un iff unique premier | thm_cellFoundCount_eq_one_iff_existsUniquePrime | EXACT |
| T1 sur cellule propre | produire N_P=1 sans entrée scientifique | — | MISSING |
| C3 et occurrence | consommateurs de T1 sur le même objet | — | MISSING |

    LEAN_FINAL_RH_CERTIFIED = false
