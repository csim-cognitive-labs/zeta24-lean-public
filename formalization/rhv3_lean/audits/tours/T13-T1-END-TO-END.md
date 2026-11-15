# Manifeste — T13-T1-END-TO-END

    TOUR_ID = T13-T1-END-TO-END
    TIMESTAMP = 2026-09-11
    HEAD_BEFORE = a5328475bce31278bd96ea5979a23399cf1bf636
    HEAD_AFTER = 685bd0c7b6aa51e7ae87bfd67807ac6707674e0f
    ORIGIN_MAIN_SHA = 685bd0c7b6aa51e7ae87bfd67807ac6707674e0f
    FILES_CHANGED = RHV3Lean.lean,
                    RHV3Lean/Objects/ZeroSourceExplicitFormulaChannel.lean
                    (nouveau), audit_contracts.sh (marqueurs de maître
                    corrigés — script obsolète, cf. §1 ci-dessous),
                    Certification/Challenge.lean, Solution.lean,
                    PrintAxioms.lean, comparator.json,
                    Certification/CHALLENGE_FROZEN_GIT_BLOB, ce manifeste.
    PUBLIC_REALISERS_ADDED = rZeroChannelApprox, rPsiZeroMidpointChannel,
                    rPsiZeroChannel, PM9aMidpointIdentity,
                    PM9aChannelIdentityOnDomain, PM9aChannelIdentity,
                    thm_psiZeroChannel_of_le_one,
                    thm_chebyshevPsi_eq_zero_of_lt_two,
                    thm_M9a_total_of_domain, thm_M9a_M9b_composition,
                    thm_M9a_M9b_components,
                    thm_psiZeroChannel_not_definitionally_chebyshev
    PUBLIC_REALISERS_MODIFIED = aucun (additif seul)
    SEMANTIC_STEPS = Ce tour NE FERME PAS T1.  Conformément à l'ordre causal
                    du maître (§5bis, §26), la première obligation
                    identifiée par le mandat T13 est fermée en partie
                    seulement : le canal analytique `psi_Z` construit depuis
                    la source complète des zéros (L15) est maintenant NOMMÉ
                    dans RHV3, avec l'EXACTE proposition manquante
                    (`PM9aChannelIdentityOnDomain`) et le raccord logique
                    « l'identité sur le domaine x>1 suffit à l'identité
                    totale » ; cette proposition reste, comme avant ce tour,
                    NOT_YET_CERTIFIED_LEAN, jamais supposée comme fait.
    MATHEMATICAL_STEPS = `rZeroChannelApprox`/`rPsiZeroMidpointChannel`/
                    `rPsiZeroChannel` réutilisent tels quels
                    `cSymmetricZeroSum` de L15 (aucune redéfinition) ;
                    `thm_M9a_total_of_domain` est une pure réduction
                    logique (les deux canaux s'annulent sous 2 : l'un par
                    construction, l'autre parce que `Chebyshev.psi` compte
                    les puissances de premiers <= x et qu'il n'y en a
                    aucune sous 2) ; `thm_M9a_M9b_composition`/
                    `thm_M9a_M9b_components` réutilisent EXACTEMENT
                    `thm_M9b_grammar_rigidity`/
                    `thm_M9b_pointwise_components` de L16 (T12), sans
                    seconde preuve.
    COMPARATOR_TARGETS = Certification/comparator.json (+3 :
                    cmp_M9A_total_of_domain, cmp_M9A_M9B_composition,
                    cmp_M9A_psiZeroChannel_not_definitionally_chebyshev)
    COMPARATOR_DELTA_RESULT = RHV3_COMPARATOR=PASS (63 targets, 0 missing,
                    LEAN_KERNEL_REPLAY=PASS, nanoda kernel accepts, Lean
                    default kernel accepts)
    COMPARATOR_CUMULATIVE_RESULT = RHV3_COMPARATOR=PASS (full run, same
                    verdict as DELTA)
    CONTRACT_AUDIT_RESULT = PASS (RHV3_CONTRACT_AUDIT=PASS après correction
                    de audit_contracts.sh — les six marqueurs de
                    gouvernance cherchaient un préfixe markdown `# ` que la
                    version clarifiée du maître (2026-09-11,
                    docs/RH_STRATEGIE_LEAN.md) n'utilise plus dans ses
                    titres de section ; les six titres eux-mêmes sont
                    inchangés et présents. Règle automatisée corrigée pour
                    suivre le maître actif, conformément à §17/§18 du
                    maître : « une règle automatisée obsolète ... doit être
                    corrigée et ne peut bloquer la route normative » ;
                    correction purement syntaxique, aucun contenu de garde
                    affaibli.)
    FIDELITY_AUDIT_RESULT = PASS (RHV3_FIDELITY_AUDIT=PASS,
                    MANIFEST_FIELDS_MISSING=0, FIDELITY_VERDICTS_NOT_ALLOWED=0)
    SAME_OBJECT_RESULTS = SAME_HISTORY : `thm_M9a_M9b_composition`/
                    `thm_M9a_M9b_components` pointent sur l'UNIQUE
                    foncteur M9b déjà produit en L16 (T12), jamais une
                    seconde reconstruction. SAME_MEMBER/SAME_PASSAGE/
                    SAME_MIDDLE : sans objet à ce niveau — ce module ne
                    construit ni membre, ni passage, ni triple ; le
                    raccord membre-sensible (Phase E du maître) reste
                    TO_PRODUIRE.
    AXIOMS_RESULT = permitted only [propext, Classical.choice, Quot.sound] ;
                    aucun axiome nouveau (vérifié par lake build sur les
                    trois nouvelles cibles Comparator)
    BUILD_RESULT = PASS
    RESIDUAL_OBLIGATIONS_BEFORE = M9a (`psi_Z = Chebyshev.psi`) non nommé
                    dans RHV3 sous une forme distincte de M9b ; le premier
                    consumer manquant identifié par le mandat T13 §2
                    n'était pas encore matérialisé comme objet RHV3 propre.
    RESIDUAL_OBLIGATIONS_AFTER = M9a reste NOT_YET_CERTIFIED_LEAN.  La
                    recherche historique ciblée (mandat T13 §3, voir
                    section dédiée ci-dessous) établit que
                    `PM9aChannelIdentityOnDomain` (et sa forme médiane
                    `PM9aMidpointIdentity`) N'A JAMAIS ÉTÉ PROUVÉE nulle
                    part dans `formalization/rhv2_fresh` malgré ~20
                    fichiers et plusieurs milliers de lignes d'appareillage
                    Perron/contour réellement inconditionnel (finitude,
                    décroissance des bords latéraux, complétude des pôles,
                    résidus, formule médiane par tsum) : cet appareillage
                    réduit l'identité EXACTEMENT à un unique résidu encore
                    ouvert, nommé dans ce même corpus
                    `PSafeCentralHorizontalVanishes` (fichier
                    `RHV2Fresh/Prime/ExplicitFormula/
                    SafeRemainingBoundary.lean`), qui n'y est également
                    JAMAIS prouvé. Ce résidu n'a pas été porté ce tour (voir
                    §FIRST_REMAINING_CAUSAL_OBLIGATION du rapport). Phases
                    A et B du maître (§5bis) restent produites (Tour/
                    contacts/cellule membre-propre ; histoire première
                    canonique autonome). Phases C/D (reconstruction
                    zéro-source complète, identité M^Z=M) restent
                    NOT_YET_CERTIFIED_LEAN. Phases E/F/G/H (raccord
                    membre-sensible, T1, C3, rang, T2) ne sont PAS
                    amorcées ce tour, conformément à l'ordre causal
                    imposé : aucune ne peut être produite sans Phase C/D.
    NEXT_CONSUMER = soit un futur tour qui porte l'appareillage Perron/
                    contour complet de `rhv2_fresh` et referme
                    `PSafeCentralHorizontalVanishes` par une estimation
                    analytique réelle (zéro-densité / région sans zéro,
                    absente de Mathlib à ce jour) — un tour de portée
                    dédiée et non entamé ici faute de budget de tour ; soit
                    Phase E/F du maître si `PM9aChannelIdentityOnDomain`
                    devient un jour disponible par une autre voie.
    PUSH_STATUS = pushed, HEAD == origin/main == 685bd0c7

## 1. Correction du script d'audit (marqueurs de gouvernance)

`audit_contracts.sh` cherchait six chaînes préfixées `# ` (format markdown
`#`) dans `docs/RH_STRATEGIE_LEAN.md`. La version clarifiée du maître
(2026-09-11, commit `a5328475`) a reformaté ses titres de section SANS le
préfixe `#` (par ex. `2. Graphe global de la démonstration à transcrire` au
lieu de `# 2. Graphe global de la démonstration à transcrire`), sans changer
leur contenu ni leur ordre. Les six titres exacts (vérifiés par lecture
complète du maître avant ce tour) sont tous présents, identiques, à leur
place normative. Le script a été corrigé pour chercher les six titres SANS
le préfixe `#`, conformément à la règle du maître Lean §17/§18 : une règle
automatisée obsolète doit être corrigée, pas contournée, et ne peut bloquer
la route normative. Aucun contenu de garde n'a été affaibli : les six
mêmes titres, au même sens, sont toujours exigés.

## 2. Recherche historique ciblée de M9a (mandat T13 §3)

Mots-clés cherchés : `PrimeHistoryFromZeros`,
`PrimeDeterminedZeroCompleteGrammar`, `ZeroPrimeTerminalReconstruction`,
`VonMangoldtRigidGrammar`, `ZeroSource`, `HistoryReconstruction`,
`ExplicitFormula`, `PsiZeroChannel`, `RightContinuousRecovery`,
`PrimeReconstruction`, `CanonicalHistory`, `M9`, `M9a`, `M9b`, `Chebyshev`,
`VonMangoldt`, dans `formalization/rhv2_fresh` et
`formalization/rh_gap_criterion`.

### Corps inspectés (prose, un candidat par paragraphe)

**`RHV2Fresh/Prime/ExplicitFormula/PsiZeroChannel.lean`** —
`rPsiZeroChannel`, `PM9aMidpointIdentity`, `PM9aChannelIdentityOnDomain`,
`PM9aChannelIdentity`, `thm_M9a_total_of_domain`,
`thm_M9a_M9b_composition`. Corps existant : définitions et une réduction
logique réelle ; les trois `PM9a*` sont des `def : Prop` JAMAIS prouvées
dans ce fichier ni ailleurs dans le corpus (vérifié par grep exhaustif,
voir ci-dessous). Hypothèses : `thm_M9a_total_of_domain` ne reçoit qu'une
hypothèse de transport nommée (`hDomain`), jamais T1/C3/placeIndex/T2/
RH/M^Z=M. Réutilisable : OUI — porté ce tour sous les mêmes noms dans
RHV3.

**`RHV2Fresh/Prime/ExplicitFormula/ZeroSource.lean`**, §1-§2 — déjà
inspecté et porté en T12 (L15), reconfirmé sans changement ce tour.

**`RHV2Fresh/Prime/ExplicitFormula/SafeRemainingBoundary.lean`** —
`PSafeCentralHorizontalVanishes`,
`thm_safePerronRemainingBoundary_tendsto_zero`. Le théorème d'assemblage
existe et est inconditionnel UNE FOIS `PSafeCentralHorizontalVanishes`
reçue en hypothèse nommée ; mais cette proposition elle-même (le résidu
P4a, borne du segment horizontal central du contour de Perron) n'est
prouvée NULLE PART dans le corpus. Aucune prémisse interdite. Réutilisable
: pas porté ce tour, portée jugée trop large — voir §3 ci-dessous pour la
justification exacte de ce choix.

**`RHV2Fresh/Prime/ExplicitFormula/{ContourHeight, FreshRectangleResidue,
PerronBoundaryDecay, PerronSideIntegrals, PerronBoundaryAssembly,
RightVerticalMidpoint, PerronPrincipalParts, PerronConstantTerm,
PerronPoleOne, LogDerivativeResidues, TrivialZeroTerm, TruncatedPerron,
UnsmoothedPerronLocalResidue, SafePerronContour,
MellinInversionBridge}.lean`** — appareillage de contour de Perron (~15
fichiers, ~180 Ko). Tous les corps inconditionnels marqués
`No sorry/admit/axiom` compilent et s'assemblent jusqu'au même résidu
P4a. Aucune prémisse interdite trouvée par lecture des en-têtes et des
signatures publiques. Réutilisable : pas porté ce tour — voir §3.

**`RHV2Fresh/Prime/HistoryReconstruction.lean`** — M9b complet, déjà
inspecté et porté en T12 (L16), reconfirmé sans changement ce tour.

**`RiemannHypothesisProof/PrimeHistoryFromZeros.lean`** (rh_gap_criterion)
— `ZerosReconstructWholePrimeGrammar` et consorts. Corps existant, mais
`EncZ=M` y est un théorème SANS hypothèse de canal, important des
définitions amont (`RhGap.ScientificRebuild20260828.
vonMangoldtReconstructedGrammar`) dont ce tour n'a pas tracé le corps
causal jusqu'à la source des zéros — fusionne M9a et M9b sans
démonstration analytique explicite tracée, forme interdite. Réutilisable
: NON — déjà rejeté en T12, reconfirmé ce tour, non re-porté.

**`RhGapCriterion/{PrimeDeterminedZeroRecovery, ZeroReconstructedMetaPattern,
ZeroPrimeTerminalReconstructionContract, ZeroPrimeTerminalReconstructionAudit,
VonMangoldtRigidGrammar}.lean`** (rh_gap_criterion) — grammaires diverses,
inspectées par nom/en-tête seulement (portée du tour). Toutes dépendent,
directement ou par leur module parent `ScientificRebuild20260828`,
d'objets construits après une sélection de rang/premier cible dans ce
corpus historique — forme interdite par construction. Réutilisable : NON.

### Vérification exhaustive : `PM9aMidpointIdentity`/`PM9aChannelIdentityOnDomain` ne sont jamais prouvées

```
grep -rn "PM9aMidpointIdentity\|PM9aChannelIdentityOnDomain\|PM9aChannelIdentity\b" \
  --include=*.lean formalization/rhv2_fresh
```

donne des dizaines d'occurrences, TOUTES sous la forme d'une hypothèse
nommée (`(hMidpoint : PM9aMidpointIdentity)`, `(hChannel :
PM9aChannelIdentity)`, ou un champ `m9 : PM9aMidpointIdentity` d'une
structure de contrat) — aucune sous la forme `theorem ... :
PM9aMidpointIdentity := by ...` avec un corps de preuve réel. Ceci confirme,
par lecture directe et non par confiance dans un nom de fichier, que
l'ensemble du corpus historique de `rhv2_fresh` — malgré un effort
d'infrastructure Perron/contour réel et substantiel — n'a jamais fermé M9a,
et l'a réduit à l'unique résidu nommé `PSafeCentralHorizontalVanishes`.

## 3bis. Correctif macro-tour reçu en cours de tour — vérification supplémentaire

Un correctif de protocole (mode PRODUCTION_FAST / CERTIFICATION_MILESTONE,
§27 ajoutée au maître Lean, append-only) a demandé de retenter la
fermeture inconditionnelle de M9a plutôt que de s'arrêter à la première
identification du résidu ouvert. Avant de conclure à nouveau à
NOT_YET_CERTIFIED_LEAN, une vérification supplémentaire a été menée sur
`formalization/rh_gap_criterion`, qui contient une tentative *smoothed*
(lissée) de formule explicite plus aboutie que celle de `rhv2_fresh` :

`RhGapCriterion/ZetaP5Closure.lean` (`theorem P5_complete`) assemble
quatre faits, tous au sujet d'objets explicitement LISSÉS
(`smoothedVonMangoldtSum`, `smoothedZeroFormula`,
`smoothedPerronBoundaryRemainder`, `PiWeighted`) : (1) un comptage
premier PONDÉRÉ `PiMangoldtFromZeros x = PiWeighted x
⌊log x/log 2⌋₊` — une moyenne de Cesàro/Riesz à un ORDRE FINI fixé, pas
`Nat.primeCounting` exact ; (2) non-nullité des amplitudes de mode zéro ;
(3) une projection modale exacte, mais du canal PROJETÉ, pas de `psi_Z`
lui-même ; (4) une borne SUBEXPONENTIELLE (pas `o(1)`, pas nulle) sur le
reste. Aucune de ces quatre clauses n'établit `psiZ = Chebyshev.psi` ni
`PiMangoldtFromZeros = Nat.primeCounting` exactement : c'est exactement
la substitution interdite par le maître Lean §15, `smoothing ou
approximation terminale`, prise à son point le plus avancé du corpus
historique. Aucun corps inconditionnel et NON lissé n'a été trouvé.

Ceci confirme, par une seconde vérification indépendante et plus large
que celle du §2 ci-dessus, que Bloc A (§6 du correctif macro-tour) ne
peut être produit ce tour sans introduire une mathématique nouvelle et
non triviale (une estimation analytique réelle d'ordre PNT/région-sans-
zéro, absente de Mathlib) — ce qui est explicitement interdit par le
mandat («ne pas ouvrir une nouvelle recherche mathématique»). Le tour
s'arrête donc, conformément au §19 cas 2 du correctif macro-tour, au
premier producteur manquant : `PM9aChannelIdentityOnDomain` (ou son
résidu upstream `PSafeCentralHorizontalVanishes`), sans le contourner
et sans fabriquer une preuve conditionnelle déguisée en preuve
inconditionnelle (interdit par §27.6 du maître, ajouté ce tour).

## 3. Justification de la portée de ce tour (pourquoi l'appareillage Perron n'est pas porté)

Le mandat T13 §4 demande un producteur réel `ZEROS -> psi`, pas un
contournement par `Chebyshev.psi` canonique de Mathlib pris seul. Ce tour a
donc :

1. nommé exactement, dans RHV3, la même proposition manquante que le corpus
   historique (`PM9aChannelIdentityOnDomain`), au lieu de laisser M9a comme
   un bloc non différencié ;
2. prouvé la seule réduction logique disponible sans nouvelle mathématique
   (domaine `x>1` suffit à l'identité totale, car les deux canaux
   s'annulent sous `2`) ;
3. câblé cette proposition — jamais comme fait — sur le foncteur M9b déjà
   produit (T12), pour qu'un futur tour n'ait qu'à fournir UNE preuve de
   `PM9aChannelIdentityOnDomain` pour hériter de toutes les identités
   ponctuelles L16 sans nouvelle preuve.

Il n'a PAS porté les ~15 fichiers de l'appareillage Perron/contour, parce
que cet appareillage, même porté intégralement et sans erreur, RÉDUIRAIT
M9a au même résidu ouvert `PSafeCentralHorizontalVanishes` — il ne le
fermerait pas. Le porter ce tour aurait donc consommé un budget de tour
important pour déplacer la même flèche manquante d'un fichier à un autre,
sans avancer le statut `T1_LEAN_STATUS`. Ceci n'est PAS un jugement que
cette voie est stérile : c'est une décision de portée explicite, à
reconsidérer dans un tour dédié si le mandat le demande.

Conformément au mandat T13 §14, ce tour s'arrête donc au premier
producteur manquant dans l'ordre causal (Phase C du maître), sans le
contourner et sans le requalifier en mathématique ouverte.

    T1_CANONICAL_COUNT_EQ_ONE = NOT_YET_CERTIFIED_LEAN
    M9A_PSI_Z_EQ_PSI          = NOT_YET_CERTIFIED_LEAN
    C3_CANONICAL_MEMBERSHIP  = NOT_YET_CERTIFIED_LEAN
    CANONICAL_RANK           = NOT_YET_CERTIFIED_LEAN
    LEAN_FINAL_RH_CERTIFIED  = false

## 4. Correctif d'autorité reçu après ce tour — requalification du §2/§3/§3bis

Un correctif d'autorité a établi que `formalization/rhv2_fresh` et
`formalization/rh_gap_criterion` (comme tout document RHV2) sont
`HISTORICAL_REFERENCE_ONLY` : consultables pour retrouver un corps Lean à
porter, mais ne pouvant jamais gouverner un statut, une obligation, une
impossibilité ou une décision STOP/CONTINUE RHV3. Les §2, §3 et §3bis
ci-dessus contiennent des observations sur ce corpus historique
(`PSafeCentralHorizontalVanishes` non prouvé, `ZetaP5Closure.P5_complete`
lissé, absence d'une estimation zéro-densité dans Mathlib). Ces observations
restent utiles pour retrouver un corps à porter, mais sont ici requalifiées :

    HISTORICAL_OBSERVATIONS_NON_NORMATIVE = §2, §3, §3bis ci-dessus
    (candidats RHV2/rh_gap_criterion inspectés ; aucun n'est un fait ni une
    obligation ni une impossibilité RHV3 — seulement des candidats à
    éventuellement porter).

La conclusion correcte, formulée en RHV3 seul :

    FIRST_RHV3_UNPRODUCED_ARROW = PM9aChannelIdentityOnDomain
                    (défini dans
                    RHV3Lean/Objects/ZeroSourceExplicitFormulaChannel.lean ;
                    aucun corps RHV3 ne le produit actuellement).
    CAUSE_CLASSIFICATION       = NOT_YET_ANALYSED_INSIDE_RHV3_ONLY
    NEW_SCIENTIFIC_PREMISE     = NONE (aucune n'a été introduite ni requise
                    par ce tour)
    STOP_JUSTIFICATION_FROM_RHV2 = INVALID (retirée ; le §19 cas 2 du
                    correctif macro-tour reste la seule justification
                    valable, et doit être reformulée en termes RHV3 :
                    ACTIVE_RHV3_INPUTS, ACTIVE_RHV3_TARGET,
                    EXACT_TYPE_MISMATCH_OR_MISSING_LEMMA,
                    WHY_NO_CURRENT_RHV3_CONSTRUCTION_CAN_PROCEED — voir
                    tour suivant pour cet inventaire RHV3-only, non encore
                    fait à la date de cette correction)
    M9A_LEAN_STATUS            = NOT_YET_CERTIFIED_LEAN
    M9A_MATH_STATUS            = CLOSED (aucune mathématique nouvelle n'est
                    requise par le mandat ; seule la transcription Lean
                    manque)

## 5. Inventaire RHV3-only (mandat correctif §7) et STOP reformulé en RHV3 seul

Inventaire des modules RHV3 pertinents à la chaîne ZeroSource → M9a → M9b →
occurrence, sans référence à aucun statut RHV2 :

    ZeroSourceReconstruction.lean : fnReconstructGrammar, rhv3CanonicalGrammar,
        thm_M9b_grammar_rigidity, thm_M9b_pointwise_components — TOUS produits
        (T12), consomment `psiChannel = Chebyshev.psi` comme hypothèse
        nommée, jamais comme fait. DEPENDS_ON_M9A = oui (comme hypothèse de
        transport). USABLE_RHV3 = oui, déjà utilisé.
    ZeroSourceExplicitFormulaChannel.lean : rPsiZeroChannel,
        PM9aChannelIdentityOnDomain, thm_M9a_total_of_domain — produits ce
        tour. PM9aChannelIdentityOnDomain elle-même : AUCUN corps RHV3 ne la
        produit. DEPENDS_ON_T1 = non. DEPENDS_ON_C3 = non. USABLE_RHV3 =
        oui comme hypothèse ; NON comme fait acquis.
    ContactsAndCell.lean, PrimeOccurrence.lean, Triple.lean,
        VonMangoldtChebyshev.lean : géométrie locale (Tour/contacts/cellule/
        occurrence membre-propre), indépendants de M9a — déjà produits,
        n'ont besoin d'aucune preuve supplémentaire pour Phase A/B du
        maître. DEPENDS_ON_M9A = non.

Aucun objet RHV3 actif (produit ou non) ne fournit un corps, une
approximation, ou une réduction supplémentaire de
`PM9aChannelIdentityOnDomain` au-delà de la réduction domaine→total déjà
prouvée par `thm_M9a_total_of_domain`. Formulé strictement en RHV3, sans
aucune référence à RHV2 :

    ACTIVE_RHV3_INPUTS = cSymmetricZeroSum (L15), rPsiZeroChannel,
                    Chebyshev.psi (Mathlib), thm_M9a_total_of_domain
    ACTIVE_RHV3_TARGET = PM9aChannelIdentityOnDomain
                    (∀ x > 1, rPsiZeroChannel x = Chebyshev.psi x)
    EXACT_TYPE_MISMATCH_OR_MISSING_LEMMA = aucun lemme RHV3 actif ne relie
                    `limUnder (𝓝[>] x) rPsiZeroMidpointChannel` (limite
                    radiale du canal médian zéro-source) à `Chebyshev.psi x`
                    (fonction Mathlib définie par somme de von Mangoldt) ;
                    la chaîne manquante est analytique (formule explicite
                    exacte), pas une erreur de type Lean.
    WHY_NO_CURRENT_RHV3_CONSTRUCTION_CAN_PROCEED = aucun module RHV3 actif
                    ne contient ni ne peut assembler par `simp`/`rfl`/lemmes
                    Mathlib existants une preuve de cette identité ; ce n'est
                    pas une impossibilité déclarée, seulement l'absence
                    actuelle d'un producteur RHV3.
    LEAN_STATUS = NOT_YET_CERTIFIED_LEAN (jamais NEW_MATHEMATICAL_LOCK, ni
                    IMPOSSIBLE, ni NEW_SCIENTIFIC_PREMISE)

Ceci remplace, comme seule justification STOP valable pour ce point de la
chaîne, les formulations RHV2-dépendantes des §2/§3/§3bis (requalifiées
§4 ci-dessus).
