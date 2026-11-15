# Manifeste — T12-ZERO-SOURCE-RECONSTRUCTION

    TOUR_ID = T12-ZERO-SOURCE-RECONSTRUCTION
    TIMESTAMP = 2026-09-11
    HEAD_BEFORE = e2ebfbf3461cffa05ca3ddd442da995f133cfc69
    HEAD_AFTER = 748805f2f3e729b68792d678cb28159e978bb474
    ORIGIN_MAIN_SHA = 748805f2f3e729b68792d678cb28159e978bb474
    FILES_CHANGED = RHV3Lean.lean,
                    RHV3Lean/Objects/ZeroSourceReconstruction.lean (nouveau),
                    Certification/Challenge.lean, Solution.lean,
                    PrintAxioms.lean, comparator.json,
                    Certification/CHALLENGE_FROZEN_GIT_BLOB, ce manifeste.
    PUBLIC_REALISERS_ADDED = sSymmetricZeroWindow, finsetSymmetricZeroWindow,
                    cZeroContribution, cMemberContribution, cSymmetricZeroSum,
                    thm_symmetricZeroWindow_finite,
                    thm_symmetricZeroSum_eq_labelled_sum,
                    thm_memberContribution_determines_member,
                    thm_symmetricZeroWindow_mono,
                    fnWeightFromPsi, PPrimeFromPsi, fnCountingFromPsi,
                    fnPrimeAtRankFromPsi, fnGapAtRankFromPsi,
                    TReconstructedPrimeGrammar, fnReconstructGrammar,
                    rhv3CanonicalGrammar, thm_weightFromPsi_chebyshev,
                    thm_primeFromPsi_chebyshev_iff,
                    thm_primeFromPsi_chebyshev_eq,
                    thm_reconstructedPrimeAtRank_eq_canonicalPrimeAtRank,
                    thm_reconstructedCounting_eq_canonicalCounting,
                    thm_reconstructedSuccessor_eq_canonicalSuccessor,
                    thm_reconstructedGap_eq_canonicalGap,
                    thm_M9b_grammar_rigidity, thm_M9b_pointwise_components,
                    thm_reconstruction_is_not_a_definitional_alias
    PUBLIC_REALISERS_MODIFIED = aucun (additif seul)
    SEMANTIC_STEPS = L15 : la source complète des vrais zéros non triviaux,
                    tronquée symétriquement en hauteur, porte une somme finie
                    de contributions étiquetées PAR MEMBRE, disponibles avant
                    toute agrégation (maître §51-53).  L16 : un canal `psi`
                    quelconque donne, par différence première puis par le
                    critère exact de primalité, une grammaire première
                    complète et déterministe ; une fois ce canal identifié au
                    canal authentique de Chebyshev, elle coïncide
                    composante par composante avec l'histoire première
                    canonique déjà produite en O6/O10.
    MATHEMATICAL_STEPS = (L15) finitude de la fenêtre par compacité, même
                    technique que OFF.LOCAL_FINITENESS étendue à une fenêtre
                    entière (`isCompact_Icc.reProdIm isCompact_Icc` puis
                    `inter_riemannZetaZeros_finite`) ; provenance de la somme
                    par `Finset.sum_attach`.
                    (L16) `fnWeightFromPsi` par différence première ;
                    primalité recouvrée exactement via
                    `thm_prime_iff_vonMangoldt_eq_log` déjà produit dans
                    `VonMangoldtChebyshev.lean` (O10), réutilisé sans le
                    redéfinir ; rang/écart/comptage reconstruits transportés
                    par `congrArg`/`funext`, jamais par `rfl` sur un alias
                    (`thm_reconstruction_is_not_a_definitional_alias` l'atteste
                    par un contre-exemple explicite, canal nul).
    COMPARATOR_TARGETS = Certification/comparator.json (+4 :
                    cmp_L15_symmetricZeroWindow_finite,
                    cmp_L15_symmetricZeroSum_eq_labelled_sum,
                    cmp_L16_reconstructedPrimeAtRank_eq_canonicalPrimeAtRank,
                    cmp_L16_reconstructedGap_eq_canonicalGap)
    COMPARATOR_DELTA_RESULT = RHV3_COMPARATOR=PASS (60 targets, 0 missing,
                    LEAN_KERNEL_REPLAY=PASS, nanoda kernel accepts, Lean
                    default kernel accepts)
    COMPARATOR_CUMULATIVE_RESULT = RHV3_COMPARATOR=PASS (full run, same
                    verdict as DELTA)
    CONTRACT_AUDIT_RESULT = PASS (RHV3_CONTRACT_AUDIT=PASS,
                    registry/manifest NOT_REALISED count unchanged at 17)
    FIDELITY_AUDIT_RESULT = PASS (RHV3_FIDELITY_AUDIT=PASS,
                    MANIFEST_FIELDS_MISSING=0, no fidelity-verdict misuse)
    SAME_OBJECT_RESULTS = SAME_HISTORY PASS — `fnPrimeAtRankFromPsi
                    Chebyshev.psi = fnPrimeAtRank` et `fnGapAtRankFromPsi
                    Chebyshev.psi _ = nPrimeGap _` identifient la
                    reconstruction à l'UNIQUE histoire première de O6, jamais
                    à une seconde énumération.
    AXIOMS_RESULT = permitted only [propext, Classical.choice, Quot.sound] ;
                    aucun axiome nouveau
    BUILD_RESULT = PASS
    RH_EQUIVALENT_CONTRACTS =
    RESIDUAL_OBLIGATIONS_BEFORE = L15/L16 absents ; M9a (`psi_Z = psi`,
                    formule explicite) non amorcé.
    RESIDUAL_OBLIGATIONS_AFTER = L15 (source zéro tronquée, provenance) et L16
                    (identités ponctuelles rang/écart/comptage/primalité,
                    conditionnelles à `psiZ = Chebyshev.psi`) produits.  M9a
                    lui-même — la formule explicite reliant `cSymmetricZeroSum`
                    (ou sa limite) au canal `Chebyshev.psi` — reste
                    NOT_YET_CERTIFIED_LEAN : aucune analytique de ce type
                    n'est disponible dans Mathlib à ce jour, et ce tour ne la
                    suppose à aucun moment. `psiZ = Chebyshev.psi` n'apparaît
                    que comme HYPOTHÈSE explicite de `thm_M9b_grammar_rigidity`
                    / `thm_M9b_pointwise_components`, jamais comme fait acquis.
    NEXT_CONSUMER = le futur producteur T2/M9a devra construire un canal
                    `psiZ` à partir de `cSymmetricZeroSum` (ou sa limite en
                    cutoff), prouver `psiZ = Chebyshev.psi`, puis consommer
                    `thm_M9b_pointwise_components` pour hériter, sans nouvelle
                    preuve, de toutes les identités ponctuelles L16.
    PUSH_STATUS = pushed, HEAD == origin/main == 748805f2

## Recherche historique menée ce tour (maître Lean §21)

Mots-clés du mandat : `zero_reconstructed_complete_metapattern_eq`,
`zero_reconstructed_any_derived_object_eq`,
`zero_prime_transition_occurrence_set_eq`,
`zero_prime_finite_ordered_succession_eq`, `ZeroSource`,
`HistoryReconstruction`, `ExplicitFormula`, `VonMangoldt`, `Chebyshev`,
`PsiZeroChannel`, `RightContinuousRecovery`, `PrimeReconstruction`,
`CanonicalHistory`, cherchés dans `formalization/rhv2_fresh` et
`formalization/rh_gap_criterion`.

**Corps réellement porté : `RHV2Fresh/Prime/HistoryReconstruction.lean`
(M9b).** Hypothèses de son théorème principal
(`thm_M9b_grammar_rigidity`) : `psiZ = Chebyshev.psi` — reçue en hypothèse de
TRANSPORT, jamais utilisée comme fait acquis ; le corps lui-même ne reçoit ni
T1, ni C3, ni placeIndex, ni T2, ni RH, ni `M^Z=M` posé comme champ. Déjà
produit en RHV3 avant ce tour : non. Réutilisable : oui, intégralement — porté
sous les noms RHV3 (`fnReconstructGrammar`, `TReconstructedPrimeGrammar`,
`rhv3CanonicalGrammar`), avec réutilisation du théorème déjà produit
`thm_prime_iff_vonMangoldt_eq_log` de `VonMangoldtChebyshev.lean` (O10) plutôt
que sa re-preuve. Cible RHV3 : L16.

**Corps réellement porté : `RHV2Fresh/Prime/ExplicitFormula/ZeroSource.lean`,
§1 (fenêtre symétrique et finitude) et §2 (contributions étiquetées) SEULEMENT
— pas §3 et au-delà.** Hypothèses : aucune ; la finitude vient de la même
discrétion locale des zéros de zêta déjà utilisée par OFF.LOCAL_FINITENESS de
RHV3, étendue d'une fibre à une fenêtre. Déjà produit en RHV3 avant ce tour :
non — RHV3 n'avait qu'une finitude de fibre unique
(`thm_zeroHeightFiber_finite`), jamais de fenêtre. Réutilisable : oui, porté
sous les noms RHV3 (`sSymmetricZeroWindow`, `cMemberContribution`,
`cSymmetricZeroSum`), en réutilisant les objets O1 déjà produits
(`PIsNonTrivialZetaZero`, `TNonTrivialZetaZero`, `cZeroSupport`) plutôt que de
les redéfinir. Cible RHV3 : L15.

**Candidat inspecté, NON porté : `RiemannHypothesisProof/PrimeHistoryFromZeros.lean`
(rh_gap_criterion).** Étape : `EncZ = M` affirmé directement par
`ZerosReconstructWholePrimeGrammar` et consorts. Hypothèses : reçoit
`RhGap.zerosPrimePosition`, `RhGap.zerosWeightedCount`, etc. comme des
DÉFINITIONS déjà données par un module amont
(`RhGap.ScientificRebuild20260828.vonMangoldtReconstructedGrammar`) sans que
ce tour n'ait tracé leurs propres corps causaux jusqu'à la source des zéros ;
l'égalité `EncZ=M` y est un théorème SANS hypothèse de canal — ce qui est
exactement la forme interdite ici (M9a et M9b fusionnés sans démonstration
analytique explicite). Réutilisable : non, sans risque de faire passer M9a
pour acquis. Cible RHV3 : aucune — signalé pour mémoire seulement, jamais
porté.

Aucun nouveau corps causal inconditionnel de M9a (`psi_Z = psi`, formule
explicite) n'a été trouvé ce tour, conformément à l'attente du maître (M9a
n'est pas disponible sous Mathlib actuel). Ceci ne requalifie PAS T1 ni M9a en
mathématique ouverte : statuts inchangés,

    T1_CANONICAL_COUNT_EQ_ONE = NOT_YET_CERTIFIED_LEAN
    M9A_PSI_Z_EQ_PSI          = NOT_YET_CERTIFIED_LEAN

    LEAN_FINAL_RH_CERTIFIED = false
