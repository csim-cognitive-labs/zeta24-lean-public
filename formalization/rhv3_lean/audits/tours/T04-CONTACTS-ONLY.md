# Manifeste de tour — T04-CONTACTS-ONLY

> **RÉTRACTÉ PAR T05.** La certification technique enregistrée ci-dessous est
> historique. Elle ne certifie plus S4 : le producteur `exp(phi/T)` choisissait
> la branche principale et échoue contre les contacts Z1--Z4 publiés.

    TOUR_ID = T04-CONTACTS-ONLY
    TIMESTAMP = 2026-09-09
    KIND = SCIENTIFIC_PRODUCTION_MACRO_CYCLE
    HEAD_BEFORE = 43243cf2712087ddd3b9277e8ed8313eecea501b
    HEAD_AFTER = f8a880b40dfb823b8daefe2efcdae065520f3c60
    ORIGIN_MAIN_SHA = f8a880b40dfb823b8daefe2efcdae065520f3c60
    FILES_CHANGED = TrueTowerState, TrueTowerCarrier, PrimeOccurrence, VonMangoldtChebyshev, certification, contracts and audits
    PUBLIC_REALISERS_ADDED = contacts-only decoders, canonical carrier, direct cell/C3/occurrence, Lambda-psi-J-pi reconstruction, carrier passage place
    PUBLIC_REALISERS_MODIFIED = TReadingProvenance and R-ATT are contacts-only; legacy discrete/operator families removed from active Comparator
    SEMANTIC_STEPS = zero -> true consecutive contacts -> same cell -> pi ranks -> C3 -> occurrence -> passage place -> existing triple/OFF/SAME-E/universalization consumers
    MATHEMATICAL_STEPS = exact consecutive width and tangent inversion; finite Chebyshev reconstruction; unique prime history; first passage endpoint at its C3 rank
    COMPARATOR_TARGETS = Certification/comparator.json
    COMPARATOR_DELTA_RESULT = PASS (50/50; nanoda et noyau Lean)
    COMPARATOR_CUMULATIVE_RESULT = PASS (50/50; nanoda et noyau Lean)
    CONTRACT_AUDIT_RESULT = PASS
    SPECIFICATION_STRENGTH_AUDIT_RESULT = PASS
    FIDELITY_AUDIT_RESULT = PASS
    SAME_OBJECT_RESULTS = SAME_MEMBER SAME_PASSAGE SAME_MIDDLE SAME_CELL SAME_HISTORY SAME_E_OFF audited
    AXIOMS_RESULT = [propext, Quot.sound, Classical.choice]
    BUILD_RESULT = PASS
    RH_EQUIVALENT_CONTRACTS = PNoNullZeroPassage
    RESIDUAL_OBLIGATIONS_BEFORE = 5
    RESIDUAL_OBLIGATIONS_AFTER = 4
    NEXT_CONSUMER = body C3(later)=successor at fnCarrierPassagePlace, then same-passage nullity conservation and terminal theorem
    PUSH_STATUS = PASS — HEAD_AFTER = ORIGIN_MAIN_SHA

## Tableau de fidélité

| Étape sémantique | Étape mathématique | Réalisateur Lean exact | Fidélité |
|---|---|---|---|
| vrais contacts consécutifs | largeur pi/T et incidence tangentielle | TTrueHarmonicTowerState | EXACT |
| contacts vers le même zéro | inversion de T puis beta | thm_decodedHeight_eq_zeroHeight, thm_decodedRadialPosition_eq_zeroRadialPosition | EXACT |
| paire identique vers membre identique | injectivité du support complexe | thm_same_true_contacts_same_member | EXACT |
| porteur canonique contacts-only | transcription exp(phi/T), exp((phi+pi)/T) | réalisateur rétracté | CONTRADICTS_MASTER |
| cellule canonique propre | intervalle (C-,C+] du vrai événement | aucun réalisateur canonique | MISSING |
| occurrence propre | provenance C-, C+ et cellule réellement localisée | aucun réalisateur canonique | MISSING |
| R-ATT | mêmes contacts vrais, même membre | thm_rATT_sameProvenance_sameMember | EXACT |
| Von Mangoldt/Chebyshev | Lambda vers psi vers J vers pi | thm_psiJump_eq_vonMangoldt, thm_jJump_mul_log_eq_vonMangoldt, thm_primeCountingFromJ_eq_primeCounting | EXACT |
| même cellule et C3 | différences de pi aux deux bords ; localisation exige non-vacuité | thm_carrierVonMangoldtChebyshev_sameCell | CONDITIONAL |
| place du passage | occurrence d'entrée égale à p_r sur un porteur fourni | fnCarrierPassagePlace, thm_carrierPassagePlace_earlierEndpoint | CONDITIONAL |
| succession locale | occurrence de sortie égale à p_(r+1) | corps Lean restant | MISSING |
| transport membre-sensible | conservation de la nullité du même passage | corps Lean restant | MISSING |
| SAME-E puis universalisation | contradiction OFF et RiemannHypothesis sans hypothèse | consommateurs produits; corps producteur restant | CONDITIONAL |

## SAME-object

    SAME_MEMBER = PASS
    SAME_PASSAGE = PASS
    SAME_MIDDLE = PASS
    SAME_CELL = PASS
    SAME_HISTORY = PASS
    SAME_E_OFF = PASS

    LEAN_FINAL_RH_CERTIFIED = false
