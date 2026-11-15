# Manifeste de tour — T05-CONTACT-REGRESSION

    TOUR_ID = T05-CONTACT-REGRESSION
    TIMESTAMP = 2026-09-10
    KIND = FIDELITY_RETRACTION_AND_KERNEL_AUDIT
    HEAD_BEFORE = ea8f83b6e85f645c47c57beae65f453881775c57
    HEAD_AFTER = 2b73301e3b1976cc901ee86b3e07cd2482736de6
    ORIGIN_MAIN_SHA = 2b73301e3b1976cc901ee86b3e07cd2482736de6
    FILES_CHANGED = TrueTowerState, TrueTowerCarrier, VonMangoldtChebyshev, RHV3Lean root, certification, contracts, audits, contact regression
    PUBLIC_REALISERS_ADDED = complete trace cards and mechanical 18-field audit; no new scientific producer
    PUBLIC_REALISERS_MODIFIED = principal-branch state and carrier reclassified CONTROL_ONLY; false canonical names removed
    SEMANTIC_STEPS = supplied true contact pair -> exact decoding -> generic direct cell/readout; canonical contact event remains without a Lean producer
    MATHEMATICAL_STEPS = Z1-Z4 replay identifies historical incidences 4,10,14,22; inversion theorems preserved; historical missing localization and transport inputs audited
    COMPARATOR_TARGETS = Certification/comparator.json
    COMPARATOR_DELTA_RESULT = PASS
    COMPARATOR_CUMULATIVE_RESULT = PASS
    CONTRACT_AUDIT_RESULT = PASS with 14 honestly absent realisers after the R-PASS circularity retraction
    SPECIFICATION_STRENGTH_AUDIT_RESULT = PASS including CONTACT_REGRESSION_Z1_Z4
    FIDELITY_AUDIT_RESULT = PASS for the produced/conditional classification
    SAME_OBJECT_RESULTS = SAME_MEMBER PASS; SAME_PASSAGE PASS; SAME_MIDDLE PASS; SAME_CELL generic PASS; SAME_HISTORY PASS; SAME_E_OFF conditional
    AXIOMS_RESULT = [propext, Quot.sound, Classical.choice]
    BUILD_RESULT = PASS
    RH_EQUIVALENT_CONTRACTS =
    RESIDUAL_OBLIGATIONS_BEFORE = 4 (two were hidden by the invalid canonical-carrier claim)
    RESIDUAL_OBLIGATIONS_AFTER = 14
    NEXT_CONSUMER = requires an actual contacts-only event selector/proof and canonical-cell localization before any terminal consumer
    PUSH_STATUS = PASS — implementation commit verified on origin/main

## Tableau de fidélité

| Étape sémantique | Étape mathématique | Réalisateur Lean exact | Fidélité |
|---|---|---|---|
| état contacts-only fourni | deux contacts positifs, ordonnés et lois exactes | TTrueHarmonicTowerState | EXACT |
| inversion contacts vers membre | largeur pi/T puis loi tangentielle | thm_decodedHeight_eq_zeroHeight, thm_decodedRadialPosition_eq_zeroRadialPosition, thm_contacts_decode_same_member | EXACT |
| rigidité d'une même paire | égalité de T et beta puis du support | thm_same_true_contacts_same_member | EXACT |
| contrôle branche principale | incidence zéro analytique | tPrincipalBranchTowerState, tPrincipalBranchCarrier | CONTRADICTS_MASTER |
| régression historique Z1--Z4 | incidences diagnostiques 4,10,14,22 rendent exactement les quatre références | contact_regression.sh | EXACT |
| producteur du vrai événement | sélectionner la paire historique sans branche, premier, floor ou ceil | — | MISSING |
| cellule canonique non vide | capturer au moins un premier entre les vrais contacts | — | MISSING |
| C3/occurrence canonique | centralité dans cette même cellule | — | MISSING |
| Lambda vers psi vers J vers pi | reconstruction de l'histoire première sur une cellule fournie | thm_psiJump_eq_vonMangoldt, thm_jJump_mul_log_eq_vonMangoldt, thm_primeCountingFromJ_eq_primeCounting | EXACT |
| succession de deux C3 | transport membre-sensible du même passage | — | MISSING |
| R-PASS corrigé | transport des deux extrémités propres vers la même place | PIsMemberSensitivePassageTransport, thm_rpass_iff_localLaw_generic | EXACT |
| conservation de nullité et SAME-E | theorem dérivé attendu, absent de R-PASS | — | MISSING |
| OFF et universalisation | E_OFF produit ; raccord terminal après conservation dérivée | thm_offCriticalLine_existsNullRelationPassage, thm_riemannHypothesis_of_allUpperOnCriticalLine | CONDITIONAL |
| conclusion Mathlib | theorem sans hypothèse RiemannHypothesis_proved | — | MISSING |

## SAME-object

    SAME_MEMBER = PASS
    SAME_PASSAGE = PASS_FOR_EXISTING_CONSUMERS
    SAME_MIDDLE = PASS
    SAME_CELL = PASS_FOR_GENERIC_SUPPLIED_CARRIER
    SAME_HISTORY = PASS
    SAME_E_OFF = CONDITIONAL_ON_UNPRODUCED_TRANSPORT
    CONTACT_REGRESSION_Z1_Z4 = PASS
    LEAN_FINAL_RH_CERTIFIED = false
