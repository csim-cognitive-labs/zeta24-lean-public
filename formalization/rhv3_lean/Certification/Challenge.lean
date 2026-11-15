/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import Certification.ChallengeDeps

/-!
# RHV3Lean — Challenge Comparator (ENONCES GELES)

    TRUSTED_CHALLENGE = true
    EDIT_POLICY       = FROZEN_AFTER_CREATION

Ce fichier est la référence d'ENONCES de la route RHV3.  Il est protégé par son
blob Git (`Certification/CHALLENGE_FROZEN_GIT_BLOB`) et par
`Certification/run_comparator.sh`.

Ce qu'il fait : il fixe, une fois pour toutes, le TYPE EXACT de chaque maillon
public déjà produit.  Comparator refusera ensuite toute Solution qui prouverait
un énoncé plus faible sous le même nom — c'est exactement la dérive que le
maître Lean § M.6 décrit et qu'un build vert ne détecte pas.

Ce qu'il ne fait pas : il ne contient AUCUN énoncé pour une obligation non
encore réalisée.  Les obligations manquantes sont inscrites, avec leur type fort
attendu, dans `Certification/comparator_manifest.json`, au statut
`NOT_REALISED`.  Le maître interdit d'affaiblir un Challenge pour faire passer
une Solution (§ Q.3) ; il n'interdit pas de ne pas encore avoir l'énoncé, tant
que l'absence est comptée.

Familles couvertes (maître § M.3) : C0, C1, C2, C3, C4.
Famille NON couverte : C5 (OFF et terminal), dont aucun maillon n'est produit.
-/

namespace RHV3Lean.Certification

open RHV3Lean

/-! ## Famille C0 — objets analytiques, miroir et ordre -/

/-- C0-01 — la provenance analytique du vrai zéro, et la bande ouverte. -/
theorem cmp_C0_trueZero_provenance (zZero : TNonTrivialZetaZero) :
    riemannZeta (cZeroSupport zZero) = 0 ∧
      0 < rZeroRadialPosition zZero ∧ rZeroRadialPosition zZero < 1 :=
  ⟨thm_zeroProvenance_zeta zZero, thm_zeroRadialPosition_positive zZero,
    thm_zeroRadialPosition_lt_one zZero⟩

/-- C0-02 — la multiplicité d'un vrai zéro n'est jamais nulle. -/
theorem cmp_C0_zeroMultiplicity_ne_zero (zZero : TNonTrivialZetaZero) :
    nZeroMultiplicity zZero ≠ 0 :=
  thm_zeroMultiplicity_ne_zero zZero

/-- C0-03 — les attributs du zéro sont fonctions de son seul support. -/
theorem cmp_C0_zeroAttributes_are_functions_of_support
    {zLeftZero zRightZero : TNonTrivialZetaZero}
    (hSameSupport : cZeroSupport zLeftZero = cZeroSupport zRightZero) :
    rZeroHeight zLeftZero = rZeroHeight zRightZero ∧
      rZeroRadialPosition zLeftZero = rZeroRadialPosition zRightZero ∧
        nZeroMultiplicity zLeftZero = nZeroMultiplicity zRightZero :=
  thm_zeroAttributes_are_functions_of_support hSameSupport

/-- C0-04 — l'ordre est MEMBRE-SENSIBLE : hauteur puis position radiale. -/
theorem cmp_C0_order_is_member_sensitive
    (zEarlier zLater : TNonTrivialZetaZero) :
    PZeroMemberPrecedes zEarlier zLater ↔
      rZeroHeight zEarlier < rZeroHeight zLater ∨
        (rZeroHeight zEarlier = rZeroHeight zLater ∧
          rZeroRadialPosition zEarlier < rZeroRadialPosition zLater) :=
  thm_zeroMemberPrecedes_iff_height_radial_lex zEarlier zLater

/-- C0-05 — la clé d'ordre sépare les membres, même à hauteur égale. -/
theorem cmp_C0_orderKey_injective : Function.Injective fnZeroOrderKey :=
  thm_zeroOrderKey_injective

/-- C0-06 — l'écart de hauteur d'un couple ordonné est NON NEGATIF.
La positivité stricte n'est jamais posée ici : c'est une conclusion. -/
theorem cmp_C0_zeroGap_nonnegative
    {zEarlier zLater : TNonTrivialZetaZero}
    (hPrecedes : PZeroMemberPrecedes zEarlier zLater) :
    0 ≤ rZeroPairHeightGap zEarlier zLater :=
  thm_zeroPairHeightGap_nonnegative hPrecedes

/-- C0-07 — l'écart est nul exactement dans la même fibre de hauteur. -/
theorem cmp_C0_zeroGap_null_iff_sameFiber
    (zEarlier zLater : TNonTrivialZetaZero) :
    rZeroPairHeightGap zEarlier zLater = 0 ↔
      rZeroHeight zEarlier = rZeroHeight zLater :=
  thm_zeroPairHeightGap_zero_iff_sameFiber zEarlier zLater

/-- C0-08 — le miroir fonctionnel est un vrai point d'annulation de zêta. -/
theorem cmp_C0_mirror_zetaVanishes (zZero : TNonTrivialZetaZero) :
    riemannZeta (cMirrorSupport zZero) = 0 :=
  thm_mirrorSupport_zetaVanishes zZero

/-- C0-09 — le miroir est à la MÊME hauteur, et à la position radiale
complémentaire. -/
theorem cmp_C0_mirror_sameHeight_complementaryRadial
    (zZero : TNonTrivialZetaZero) :
    rZeroHeight (zMirrorZero zZero) = rZeroHeight zZero ∧
      rZeroRadialPosition (zMirrorZero zZero) = 1 - rZeroRadialPosition zZero :=
  ⟨thm_mirror_sameHeight zZero, thm_mirror_radialPosition zZero⟩

/-- C0-10 — HORS LIGNE : deux membres DISTINCTS de la MÊME fibre, comparables,
d'écart de hauteur nul.  Première moitié du troisième paragraphe. -/
theorem cmp_C0_off_gives_two_distinct_sameFiber_members
    {zZero : TNonTrivialZetaZero} (hOff : PIsOffCriticalLine zZero) :
    zMirrorZero zZero ≠ zZero ∧
      rZeroHeight (zMirrorZero zZero) = rZeroHeight zZero ∧
        (PZeroMemberPrecedes (zMirrorZero zZero) zZero ∨
          PZeroMemberPrecedes zZero (zMirrorZero zZero)) ∧
        rZeroPairHeightGap (zMirrorZero zZero) zZero = 0 :=
  thm_offCriticalLineUpper_twoDistinctSameFiberMembers hOff

/-! ## Famille C1 — LEGACY_DIAGNOSTIC, hors surface scientifique active

La nouvelle route est la famille `TRUE_CONTACTS` plus bas. Ces déclarations
restent compilées seulement comme témoins historiques de régression.
-/

/-- C1-01 — l'équation de phase des incidences. -/
theorem cmp_C1_incidence_phaseEquation
    (zUpperZero : TUpperNonTrivialZetaZero) (kAddress : ℤ) :
    rTowerHeight zUpperZero * rTowerLogIncidence zUpperZero kAddress =
      rTowerPhase zUpperZero + (kAddress : ℝ) * Real.pi :=
  thm_rTowerLogIncidence_phaseEquation zUpperZero kAddress

/-- C1-02 — l'ordre des adresses est l'ordre des incidences. -/
theorem cmp_C1_incidence_strictOrder
    (zUpperZero : TUpperNonTrivialZetaZero)
    {kLeftAddress kRightAddress : ℤ} (hOrder : kLeftAddress < kRightAddress) :
    rTowerIncidence zUpperZero kLeftAddress <
      rTowerIncidence zUpperZero kRightAddress :=
  thm_rTowerIncidence_strictOrder zUpperZero hOrder

/-- C1-03 — les deux contacts sont strictement ordonnés. -/
theorem cmp_C1_contacts_strictOrder
    (zUpperZero : TUpperNonTrivialZetaZero) (tWindow : TTowerWindow) :
    rContactMinus zUpperZero tWindow < rContactPlus zUpperZero tWindow :=
  thm_contacts_strictOrder zUpperZero tWindow

/-- C1-04 — le diamètre logarithmique de la cellule, et sa positivité. -/
theorem cmp_C1_cellLogDiameter_formula
    (zUpperZero : TUpperNonTrivialZetaZero) (tWindow : TTowerWindow) :
    rCellLogDiameter zUpperZero tWindow =
        (tWindow.nSpan : ℝ) * Real.pi / rTowerHeight zUpperZero ∧
      0 < rCellLogDiameter zUpperZero tWindow :=
  ⟨thm_cellLogDiameter_formula zUpperZero tWindow,
    thm_cellLogDiameter_positive zUpperZero tWindow⟩

/-- C1-05 — INVERSION : la cellule rend la hauteur du membre. -/
theorem cmp_C1_inversion_recovers_height
    (zUpperZero : TUpperNonTrivialZetaZero) (tWindow : TTowerWindow) :
    rTowerHeight zUpperZero =
      (tWindow.nSpan : ℝ) * Real.pi / rCellLogDiameter zUpperZero tWindow :=
  thm_inversion_recovers_height zUpperZero tWindow

/-- C1-06 — INVERSION : la cellule rend la position radiale du membre. -/
theorem cmp_C1_inversion_recovers_radialPosition
    (zUpperZero : TUpperNonTrivialZetaZero) (tWindow : TTowerWindow) :
    rTowerRadialPosition zUpperZero =
      rTowerHeight zUpperZero /
        Real.tan (rTowerHeight zUpperZero *
          Real.log (rContactMinus zUpperZero tWindow)) :=
  thm_inversion_recovers_radialPosition zUpperZero tWindow

/-- C1-07 — même donnée complète de contacts, même membre. -/
theorem cmp_C1_sameContactData_sameMember
    {zLeftZero zRightZero : TUpperNonTrivialZetaZero}
    {tLeftWindow tRightWindow : TTowerWindow}
    (hSameSpan : tLeftWindow.nSpan = tRightWindow.nSpan)
    (hSameContactMinus :
      rContactMinus zLeftZero tLeftWindow = rContactMinus zRightZero tRightWindow)
    (hSameContactPlus :
      rContactPlus zLeftZero tLeftWindow = rContactPlus zRightZero tRightWindow) :
    zLeftZero = zRightZero :=
  thm_sameContactData_sameMember hSameSpan hSameContactMinus hSameContactPlus

/-- C1-08 — RELECTURE de κ.  Formule fermée du maître § S4 : l'adresse
d'entrée est LUE sur le contact d'entrée, jamais cherchée. -/
theorem cmp_C1_kappa_reading
    (zUpperZero : TUpperNonTrivialZetaZero) (tWindow : TTowerWindow) :
    ((tWindow.kEntryAddress : ℝ)) =
        (rTowerHeight zUpperZero *
            Real.log (rContactMinus zUpperZero tWindow) -
          rTowerPhase zUpperZero) / Real.pi ∧
      ∃ kAddress : ℤ,
        (rTowerHeight zUpperZero *
            Real.log (rContactMinus zUpperZero tWindow) -
          rTowerPhase zUpperZero) / Real.pi = (kAddress : ℝ) :=
  ⟨thm_kappa_eq_entry_quotient zUpperZero tWindow,
    thm_kappa_quotient_isInteger zUpperZero tWindow⟩

/-- C1-09 — RELECTURE de m.  Le nombre d'étages est la densité de la Tour
multipliée par le diamètre logarithmique de la cellule. -/
theorem cmp_C1_m_reading
    (zUpperZero : TUpperNonTrivialZetaZero) (tWindow : TTowerWindow) :
    ((tWindow.nSpan : ℝ)) =
      rTowerDensity zUpperZero * rCellLogDiameter zUpperZero tWindow :=
  thm_span_eq_density_mul_logDiameter zUpperZero tWindow

/-! ## Famille C2 — comptage, premier central, occurrence, R-ATT -/

/-- C2-01 — l'ensemble trouvé est exactement l'image de l'intervalle de rangs. -/
theorem cmp_C2_foundPrimes_eq_image_rankInterval (tInterval : TAlgebraicInterval) :
    sAlgebraicIntervalFoundPrimes tInterval =
      (Finset.Ico (nCellLeftEdgeRank tInterval)
        (nCellRightEdgeRank tInterval)).image fnPrimeAtRank :=
  thm_foundPrimes_eq_image_rankInterval tInterval

/-- C2-02 — VON MANGOLDT / CHEBYSHEV, portée exacte : le cardinal est la
DIFFERENCE des rangs aux deux bords. -/
theorem cmp_C2_foundCount_eq_edgeRankDifference (tInterval : TAlgebraicInterval) :
    nCellFoundCount tInterval =
      nCellRightEdgeRank tInterval - nCellLeftEdgeRank tInterval :=
  thm_cellFoundCount_eq_edgeRankDifference tInterval

/-- T1, forme exacte : cardinal un si et seulement si la cellule contient un
unique premier. Aucune non-vacuité ni occurrence n'est fournie en entrée. -/
theorem cmp_T1_count_one_iff_unique_prime (tInterval : TAlgebraicInterval) :
    nCellFoundCount tInterval = 1 ↔
      ∃! p : ℕ,
        Nat.Prime p ∧
          tInterval.rLeftEndpoint < (p : ℝ) ∧
          (p : ℝ) ≤ tInterval.rRightEndpoint :=
  thm_cellFoundCount_eq_one_iff_existsUniquePrime tInterval

/-- C2-03 — le rang central tombe entre les deux rangs aux bords. -/
theorem cmp_C2_centralRank_between_edges
    (tInterval : TAlgebraicInterval)
    (hFoundNonempty : 0 < nCellFoundCount tInterval) :
    nCellLeftEdgeRank tInterval ≤ nCellCentralRank tInterval - 1 ∧
      nCellCentralRank tInterval - 1 < nCellRightEdgeRank tInterval :=
  thm_cellCentralRank_between_edges tInterval hFoundNonempty

/-- C2-04 — CENTRALITE : le premier central est premier et il est DANS
l'intervalle algébrique.  C'est la loi retenue par les maîtres ; la lecture
retirée « une seule occurrence dans la cellule » n'apparaît nulle part. -/
theorem cmp_C2_centralPrime_isPrime_and_in_interval
    (tInterval : TAlgebraicInterval)
    (hFoundNonempty : 0 < nCellFoundCount tInterval) :
    Nat.Prime (nCellCentralPrime tInterval) ∧
      tInterval.rLeftEndpoint < (nCellCentralPrime tInterval : ℝ) ∧
        (nCellCentralPrime tInterval : ℝ) ≤ tInterval.rRightEndpoint :=
  ⟨thm_cellCentralPrime_isPrime tInterval,
    thm_cellCentralPrime_in_interval tInterval hFoundNonempty⟩

/-- C2-05 — GARDE-FOU : l'ensemble trouvé est en général PLURIEL.  Ce témoin
interdit définitivement le retour de la loi de comptage retirée. -/
theorem cmp_C2_foundPrimes_generallyPlural :
    2 ≤ (sAlgebraicIntervalFoundPrimes tWitnessInterval).card :=
  thm_foundPrimes_generallyPlural

/-- C2-06 — le comptage LIT, il ne déplace aucun contact. -/
theorem cmp_C2_countingReads_doesNotMoveContacts
    {tLeftInterval tRightInterval : TAlgebraicInterval}
    (hLeft : tLeftInterval.rLeftEndpoint = tRightInterval.rLeftEndpoint)
    (hRight : tLeftInterval.rRightEndpoint = tRightInterval.rRightEndpoint) :
    nCellLeftEdgeRank tLeftInterval = nCellLeftEdgeRank tRightInterval ∧
      nCellRightEdgeRank tLeftInterval = nCellRightEdgeRank tRightInterval ∧
        nCellFoundCount tLeftInterval = nCellFoundCount tRightInterval ∧
          nCellCentralPrime tLeftInterval = nCellCentralPrime tRightInterval :=
  thm_countingReads_doesNotMoveContacts hLeft hRight

/-- C2-07 — R-ATT : même provenance de lecture, même membre. -/
theorem cmp_C2_rATT_sameProvenance_sameMember
    {zLeftZero zRightZero : TUpperNonTrivialZetaZero}
    {tLeftState : TTrueHarmonicTowerState zLeftZero}
    {tRightState : TTrueHarmonicTowerState zRightZero}
    (hSameProvenance :
      tMemberProvenance zLeftZero tLeftState =
        tMemberProvenance zRightZero tRightState) :
    zLeftZero = zRightZero :=
  thm_rATT_sameProvenance_sameMember hSameProvenance

/-- C2-08 — LIMITE EXACTE de R-ATT : il ne sépare JAMAIS deux nombres premiers.
Toute étape qui aurait besoin de deux premiers distincts doit passer par la loi
locale du transport. -/
theorem cmp_C2_rATT_doesNotSeparatePrimes :
    ∃ tLeftOccurrence tRightOccurrence : TPrimeOccurrence,
      tLeftOccurrence ≠ tRightOccurrence ∧
        tLeftOccurrence.nPrime = tRightOccurrence.nPrime :=
  thm_rATT_doesNotSeparatePrimes

/-! ## Famille C3 — passage et transport membre-sensible -/

/-- C3-01 — l'écart d'un passage est non négatif ; il est strictement positif
exactement quand le passage est non nul. -/
theorem cmp_C3_passage_gap_nonneg_and_nonNull_iff_positive
    (tPassage : TZeroPassage) :
    0 ≤ rZeroPassageHeightGap tPassage ∧
      (PZeroPassageRelationNonNull tPassage ↔
        0 < rZeroPassageHeightGap tPassage) :=
  ⟨thm_zeroPassage_heightGap_nonnegative tPassage,
    thm_zeroPassage_nonNull_iff_gapPositive tPassage⟩

section RPass

variable {TImageMember TImageRelation : Type*}
variable {fnImageEarlierEndpoint fnImageLaterEndpoint : TImageRelation → TImageMember}
variable {fnMemberImage : TNonTrivialZetaZero → TImageMember}
variable {fnTransport : TZeroPassage → TImageRelation}

/-- C3-02 — R-PASS : les deux extrémités de l'image sont les images des deux
extrémités PROPRES du passage.  Aucune substitution de membre n'est exprimable. -/
theorem cmp_C3_rpass_endpoints_are_member_own
    (hTransport :
      PIsMemberSensitivePassageTransport fnImageEarlierEndpoint
        fnImageLaterEndpoint fnMemberImage fnTransport)
    (tPassage : TZeroPassage) :
    fnImageEarlierEndpoint (fnTransport tPassage) =
        fnMemberImage tPassage.zEarlierMember ∧
      fnImageLaterEndpoint (fnTransport tPassage) =
        fnMemberImage tPassage.zLaterMember :=
  thm_rpass_endpoints_are_member_own hTransport tPassage

end RPass

/-! ## Famille C4 — histoire première, place, loi locale, triple -/

/-- C4-01 — la grammaire des écarts premiers : aucune place n'est nulle. -/
theorem cmp_C4_primeGap_positive (nRank : ℕ) : 0 < nPrimeGap nRank :=
  thm_primeGap_positive nRank

/-- C4-02 — UNICITE de l'histoire première : toute énumération strictement
croissante dont l'image est exactement les premiers EST l'énumération
canonique. -/
theorem cmp_C4_primeHistory_unique
    (fnEnumeration : ℕ → ℕ)
    (hStrictMono : StrictMono fnEnumeration)
    (hRange : ∀ nValue : ℕ,
      Nat.Prime nValue ↔ ∃ nRank : ℕ, fnEnumeration nRank = nValue)
    (nRank : ℕ) :
    fnEnumeration nRank = fnPrimeAtRank nRank :=
  thm_primeHistory_unique fnEnumeration hStrictMono hRange nRank

/-- C4-03 — une place de l'histoire première n'est jamais nulle, et son écart
est strictement positif. -/
theorem cmp_C4_place_isNeverNull_and_gapPositive (tPlace : TPrimeHistoryPlace) :
    ¬ PPlaceRelationNull tPlace ∧
      nPlaceEarlierEndpoint tPlace < nPlaceLaterEndpoint tPlace :=
  ⟨thm_place_isNeverNull tPlace, thm_place_gap_positive tPlace⟩

section LocalLaw

variable {fnMemberCentralPrime : TNonTrivialZetaZero → ℕ}
variable {fnPassagePlace : TZeroPassage → TPrimeHistoryPlace}

/-- C4-04 — SEPARATION DES EXTREMITES, DERIVEE de la loi locale.  Ce n'est pas
une obligation ouverte : c'est une conséquence. -/
theorem cmp_C4_localLaw_endpointsDistinct
    (hLocalLaw :
      PLocalLawTransportsPassageOntoPlace fnMemberCentralPrime fnPassagePlace)
    (tPassage : TZeroPassage) :
    fnMemberCentralPrime tPassage.zEarlierMember ≠
      fnMemberCentralPrime tPassage.zLaterMember :=
  thm_endpointsDistinct_of_localLaw hLocalLaw tPassage

end LocalLaw

/-- C4-07 — SAME-MIDDLE : le membre médian est littéralement le même objet dans
les deux passages du triple. -/
theorem cmp_C4_triple_sameMiddleMember (tThree : TThreeConsecutiveZeros) :
    (tEarlierPassage tThree).zLaterMember =
        (tLaterPassage tThree).zEarlierMember ∧
      (tEarlierPassage tThree).zLaterMember = tThree.zMiddleZero :=
  thm_triple_sameMiddleMember tThree

/-! ## Famille C5 — OFF : fibre finie, couple consécutif, passage de gap nul -/

/-- C5-01 — OFF.LOCAL_FINITENESS : la fibre de hauteur est FINIE.  Elle est
déduite de la discrétion locale des zéros de zêta, jamais posée. -/
theorem cmp_C5_zeroHeightFiber_finite (rHeight : ℝ) :
    (sZeroHeightFiber rHeight).Finite :=
  thm_zeroHeightFiber_finite rHeight

/-- C5-02 — rien d'étranger à la fibre ne peut s'interposer entre deux membres
de même hauteur : un voisinage constaté dans la fibre est GLOBAL. -/
theorem cmp_C5_sameFiberInterposition
    {zEarlier zLater zBetween : TNonTrivialZetaZero}
    (hSameHeight : rZeroHeight zEarlier = rZeroHeight zLater)
    (hAfter : PZeroMemberPrecedes zEarlier zBetween)
    (hBefore : PZeroMemberPrecedes zBetween zLater) :
    rZeroHeight zBetween = rZeroHeight zEarlier :=
  thm_sameFiberInterposition hSameHeight hAfter hBefore

/-- C5-03 — extraction d'un couple VERITABLEMENT consécutif dans la fibre. -/
theorem cmp_C5_existsConsecutiveInFiber
    {zLeftZero zRightZero : TNonTrivialZetaZero}
    (hDistinct : zLeftZero ≠ zRightZero)
    (hSameHeight : rZeroHeight zLeftZero = rZeroHeight zRightZero) :
    ∃ zEarlier zLater : TNonTrivialZetaZero,
      rZeroHeight zEarlier = rZeroHeight zLeftZero ∧
        rZeroHeight zLater = rZeroHeight zLeftZero ∧
          PZeroMembersConsecutive zEarlier zLater :=
  thm_existsConsecutiveInFiber hDistinct hSameHeight

/-- C5-04 — OFF.REAL_PASSAGE + OFF.ZERO_GAP : un vrai zéro hors ligne produit
un VRAI passage, consécutif, dont l'écart de hauteur est NUL. -/
theorem cmp_C5_offCriticalLine_existsNullPassage
    {zZero : TNonTrivialZetaZero} (hOff : PIsOffCriticalLine zZero) :
    ∃ tPassage : TZeroPassage,
      rZeroPassageHeightGap tPassage = 0 ∧
        rZeroHeight tPassage.zEarlierMember = rZeroHeight zZero :=
  thm_offCriticalLine_existsNullPassage hOff

/-- C5-05 — la même conclusion en NULLITE DE LA RELATION, forme que la
contradiction terminale opposera sur le MÊME passage. -/
theorem cmp_C5_offCriticalLine_existsNullRelationPassage
    {zZero : TNonTrivialZetaZero} (hOff : PIsOffCriticalLine zZero) :
    ∃ tPassage : TZeroPassage, PZeroPassageRelationNull tPassage :=
  thm_offCriticalLine_existsNullRelationPassage hOff

/-- C5-06 — LE BRIDGE : les deux extrémités d'un passage sont lisibles en
branche supérieure dès que l'extrémité d'entrée est de hauteur positive, et le
bridge ne change ni l'un ni l'autre membre.  La positivité de l'extrémité de
sortie n'est PAS supposée : elle est déduite de la non-négativité de l'écart. -/
theorem cmp_ROUTE_passageEndpoints_upperBranch
    (tPassage : TZeroPassage)
    (hEarlierPositive : 0 < rZeroHeight tPassage.zEarlierMember) :
    (tPassageUpperEndpoints tPassage hEarlierPositive).1.1 =
        tPassage.zEarlierMember ∧
      (tPassageUpperEndpoints tPassage hEarlierPositive).2.1 =
        tPassage.zLaterMember :=
  thm_passageEndpoints_upperBranch tPassage hEarlierPositive

/-! ## Famille C6 — LEGACY_DIAGNOSTIC, hors surface scientifique active

Ces déclarations historiques restent compilées pour contrôler la régression.
Elles ne figurent plus dans `comparator.json` et ne réalisent aucune cible S4.
-/

/-- C6-01 — S4.INHABITANT : le porteur canonique produit est un TERME, son
adresse d'entrée est à l'origine de l'orbite et son nombre d'étages est
strictement positif pour tout membre. -/
theorem cmp_C6_canonicalOperator_inhabited :
    ∀ zUpperZero : TUpperNonTrivialZetaZero,
      (tRatioFourOperator.fnWindow zUpperZero).kEntryAddress = 0 ∧
        0 < tRatioFourOperator.nOperatorSpan zUpperZero :=
  fun zUpperZero => ⟨rfl, tRatioFourOperator.nOperatorSpan_positive zUpperZero⟩

/-- C6-02 — la cellule du porteur part d'au moins un et son rapport
multiplicatif atteint quatre. -/
theorem cmp_C6_canonicalOperator_contacts_ratioFour :
    ∀ zUpperZero : TUpperNonTrivialZetaZero,
      (1 : ℝ) ≤ tRatioFourOperator.rOperatorContactMinus zUpperZero ∧
        4 * tRatioFourOperator.rOperatorContactMinus zUpperZero ≤
          tRatioFourOperator.rOperatorContactPlus zUpperZero :=
  fun zUpperZero =>
    ⟨thm_ratioFourOperator_one_le_contactMinus zUpperZero,
      thm_ratioFourOperator_ratio_four zUpperZero⟩

/-- C6-03 — un intervalle algébrique de rapport quatre contient DEUX premiers
distincts : la pluralité est produite, jamais la lecture retirée. -/
theorem cmp_C6_ratioFourInterval_containsTwoPrimes
    {rLeft rRight : ℝ} (hOneLe : 1 ≤ rLeft) (hRatio : 4 * rLeft ≤ rRight) :
    ∃ nSmallPrime nLargePrime : ℕ,
      Nat.Prime nSmallPrime ∧ Nat.Prime nLargePrime ∧ nSmallPrime < nLargePrime ∧
        rLeft < (nSmallPrime : ℝ) ∧ (nLargePrime : ℝ) ≤ rRight :=
  thm_ratioFourInterval_containsTwoPrimes hOneLe hRatio

/-- C6-04 — S4/O10.CANONICAL_CELL_NONEMPTY : la cellule canonique est REELLEMENT
non vide, et C3 y est REELLEMENT. -/
theorem cmp_C6_canonicalCell_nonempty_and_centralPrime_inside :
    ∀ zUpperZero : TUpperNonTrivialZetaZero,
      0 < nCellFoundCount (tRatioFourOperator.tOperatorCell zUpperZero) ∧
        Nat.Prime (tRatioFourOperator.nOperatorCentralPrime zUpperZero) ∧
          (tRatioFourOperator.tOperatorCell zUpperZero).rLeftEndpoint <
              (tRatioFourOperator.nOperatorCentralPrime zUpperZero : ℝ) ∧
            (tRatioFourOperator.nOperatorCentralPrime zUpperZero : ℝ) ≤
              (tRatioFourOperator.tOperatorCell zUpperZero).rRightEndpoint :=
  fun zUpperZero =>
    ⟨thm_ratioFourOperator_cellFoundCount_positive zUpperZero,
      tRatioFourOperator.thm_operatorCentralPrime_isPrime zUpperZero,
      (thm_ratioFourOperator_centralPrime_in_cell zUpperZero).1,
      (thm_ratioFourOperator_centralPrime_in_cell zUpperZero).2⟩

/-- C6-05 — LL.SAME_OPERATOR : la lecture centrale d'un membre quelconque est
portée par le porteur, elle est un vrai premier, et elle est fonction du seul
membre. -/
theorem cmp_C6_memberCentralPrime_carriedByOperator
    (tOperator : TCanonicalTowerOperator) (zZero : TNonTrivialZetaZero) :
    fnOperatorMemberCentralPrime tOperator zZero =
        tOperator.nOperatorCentralPrime (zUpperRepresentative zZero) ∧
      Nat.Prime (fnOperatorMemberCentralPrime tOperator zZero) :=
  ⟨rfl, thm_operatorMemberCentralPrime_isPrime tOperator zZero⟩

/-- C6-06 — O8.RPASS_REAL_TRANSPORT, DECOMPOSE : R-PASS sur le porteur équivaut
EXACTEMENT à la loi locale sur ce même porteur conjuguée à l'absence de passage
nul.  Aucune force n'est dissimulée dans le prédicat. -/
theorem cmp_C6_rpass_iff_localLaw
    {tOperator : TCanonicalTowerOperator}
    {fnPassagePlace : TZeroPassage → TPrimeHistoryPlace} :
    PRPassOnOperator tOperator fnPassagePlace ↔
      PLocalLawOnOperator tOperator fnPassagePlace :=
  thm_rpass_iff_localLaw

/-- C6-07 — les clauses libres du transport : extrémités, ordre strict,
séparation dérivée et corridor vide, toutes obtenues de la seule loi locale. -/
theorem cmp_C6_rpassClauses_free
    {tOperator : TCanonicalTowerOperator}
    {fnPassagePlace : TZeroPassage → TPrimeHistoryPlace}
    (hLocalLaw : PLocalLawOnOperator tOperator fnPassagePlace)
    (tPassage : TZeroPassage) :
    fnOperatorMemberCentralPrime tOperator tPassage.zEarlierMember =
        nPlaceEarlierEndpoint (fnPassagePlace tPassage) ∧
      fnOperatorMemberCentralPrime tOperator tPassage.zLaterMember =
          nPlaceLaterEndpoint (fnPassagePlace tPassage) ∧
        fnOperatorMemberCentralPrime tOperator tPassage.zEarlierMember <
            fnOperatorMemberCentralPrime tOperator tPassage.zLaterMember ∧
          fnOperatorMemberCentralPrime tOperator tPassage.zEarlierMember ≠
            fnOperatorMemberCentralPrime tOperator tPassage.zLaterMember :=
  ⟨(thm_rpassClause_endpoints hLocalLaw tPassage).1,
    (thm_rpassClause_endpoints hLocalLaw tPassage).2,
    thm_rpassClause_order hLocalLaw tPassage,
    thm_rpassClause_endpointsDistinct hLocalLaw tPassage⟩

/-- C6-08 — le corridor de l'image est vide : aucun premier ne se glisse
strictement entre les deux premiers centraux du passage. -/
theorem cmp_C6_rpassClause_corridorEmpty
    {tOperator : TCanonicalTowerOperator}
    {fnPassagePlace : TZeroPassage → TPrimeHistoryPlace}
    (hLocalLaw : PLocalLawOnOperator tOperator fnPassagePlace)
    (tPassage : TZeroPassage) {nCandidate : ℕ} (hPrime : Nat.Prime nCandidate)
    (hLeft : fnOperatorMemberCentralPrime tOperator tPassage.zEarlierMember < nCandidate)
    (hRight : nCandidate < fnOperatorMemberCentralPrime tOperator tPassage.zLaterMember) :
    False :=
  thm_rpassClause_corridorEmpty hLocalLaw tPassage hPrime hLeft hRight

/-! ## Famille C7 — universalisation vers l'énoncé public -/

/-- C7-01 — aucun vrai zéro n'est réel : la hauteur d'un vrai zéro n'est jamais
nulle, donc la branche supérieure ne perd aucun membre. -/
theorem cmp_C7_zeroHeight_ne_zero (zZero : TNonTrivialZetaZero) :
    rZeroHeight zZero ≠ 0 :=
  thm_zeroHeight_ne_zero zZero

/-- C7-02 — le représentant supérieur porte exactement la même position
radiale. -/
theorem cmp_C7_upperRepresentative_radialPosition (zZero : TNonTrivialZetaZero) :
    rZeroRadialPosition (zUpperRepresentative zZero).1 = rZeroRadialPosition zZero :=
  thm_upperRepresentative_radialPosition zZero

/-- C7-03 — les hypothèses publiques confinent le point dans la bande ouverte,
et le vrai zéro attaché a pour support ce point même. -/
theorem cmp_C7_inOpenStrip_of_mathlibHypotheses
    (cPoint : ℂ) (hZero : riemannZeta cPoint = 0)
    (hNotTrivial : ¬ ∃ nIndex : ℕ, cPoint = -2 * (nIndex + 1)) :
    0 < cPoint.re ∧ cPoint.re < 1 ∧
      cZeroSupport (zNonTrivialZeroOfMathlib cPoint hZero hNotTrivial) = cPoint :=
  ⟨(thm_inOpenStrip_of_mathlibHypotheses hZero hNotTrivial).1,
    (thm_inOpenStrip_of_mathlibHypotheses hZero hNotTrivial).2, rfl⟩

/-- C7-04 — la centralité de la branche supérieure donne l'énoncé public, sans
aucune hypothèse de Tour, de premier ou de transport. -/
theorem cmp_C7_riemannHypothesis_of_allUpperOnCriticalLine
    (hUpper : ∀ zUpperZero : TUpperNonTrivialZetaZero,
      rZeroRadialPosition zUpperZero.1 = 1 / 2) :
    RiemannHypothesis :=
  thm_riemannHypothesis_of_allUpperOnCriticalLine hUpper

/-! ## Famille TRUE_CONTACTS — API forte contacts-only -/

theorem cmp_TRUE_CONTACTS_consecutive_width
    {z : TUpperNonTrivialZetaZero} (S : TTrueHarmonicTowerState z) :
    Real.log S.contactPlus - Real.log S.contactMinus = Real.pi / rZeroHeight z.1 :=
  S.consecutive_width

theorem cmp_TRUE_CONTACTS_tangent_law
    {z : TUpperNonTrivialZetaZero} (S : TTrueHarmonicTowerState z) :
    rZeroRadialPosition z.1 * Real.tan (rZeroHeight z.1 * Real.log S.contactMinus) =
      rZeroHeight z.1 :=
  S.tangent_law

theorem cmp_TRUE_CONTACTS_decode_height
    {z : TUpperNonTrivialZetaZero} (S : TTrueHarmonicTowerState z) :
    S.rDecodedHeight = rZeroHeight z.1 :=
  S.thm_decodedHeight_eq_zeroHeight

theorem cmp_TRUE_CONTACTS_decode_radial
    {z : TUpperNonTrivialZetaZero} (S : TTrueHarmonicTowerState z) :
    S.rDecodedRadialPosition = rZeroRadialPosition z.1 :=
  S.thm_decodedRadialPosition_eq_zeroRadialPosition

theorem cmp_TRUE_CONTACTS_decode_member
    {z : TUpperNonTrivialZetaZero} (S : TTrueHarmonicTowerState z) :
    Complex.mk S.rDecodedRadialPosition S.rDecodedHeight = cZeroSupport z.1 :=
  S.thm_contacts_decode_same_member

/-- La cellule propre est produite directement par les deux contacts du même
état, sans adresse ni fenêtre intermédiaire. -/
theorem cmp_TRUE_CONTACTS_direct_cell
    {z : TUpperNonTrivialZetaZero} (S : TTrueHarmonicTowerState z) :
    S.terminalCell.rLeftEndpoint = S.contactMinus ∧
      S.terminalCell.rRightEndpoint = S.contactPlus ∧
        Complex.mk S.rDecodedRadialPosition S.rDecodedHeight = cZeroSupport z.1 :=
  ⟨S.terminalCell_endpoints.1, S.terminalCell_endpoints.2,
    S.terminalCell_decodes_source⟩

theorem cmp_TRUE_CONTACTS_same_contacts_same_member
    {zLeft zRight : TUpperNonTrivialZetaZero}
    (SLeft : TTrueHarmonicTowerState zLeft)
    (SRight : TTrueHarmonicTowerState zRight)
    (hMinus : SLeft.contactMinus = SRight.contactMinus)
    (hPlus : SLeft.contactPlus = SRight.contactPlus) : zLeft = zRight :=
  TTrueHarmonicTowerState.thm_same_true_contacts_same_member SLeft SRight hMinus hPlus

theorem cmp_CONTROL_principal_branch_carrier (z : TUpperNonTrivialZetaZero) :
    tPrincipalBranchCarrier.fnState z = tPrincipalBranchTowerState z :=
  thm_principalBranchCarrier_state z

theorem cmp_SAME_CELL_contacts_only
    (K : TTrueTowerCarrier) (z : TUpperNonTrivialZetaZero) :
    (K.tCarrierCell z).rLeftEndpoint = (K.fnState z).contactMinus ∧
      (K.tCarrierCell z).rRightEndpoint = (K.fnState z).contactPlus :=
  K.thm_carrierCell_contactsOnly z

theorem cmp_OCCURRENCE_contacts_only
    (K : TTrueTowerCarrier) (z : TUpperNonTrivialZetaZero) :
    (K.tCarrierPrimeOccurrence z).tProvenance.contactMinus =
        (K.fnState z).contactMinus ∧
      (K.tCarrierPrimeOccurrence z).tProvenance.contactPlus =
        (K.fnState z).contactPlus ∧
      (K.tCarrierPrimeOccurrence z).nPrime =
        fnPrimeAtRank (nCellCentralRank (K.tCarrierCell z) - 1) :=
  ⟨rfl, rfl, rfl⟩

theorem cmp_VON_MANGOLDT_CHEBYSHEV_same_cell
    (K : TTrueTowerCarrier) (z : TUpperNonTrivialZetaZero) :
    nCellFoundCount (K.tCarrierCell z) =
        nPrimeCountingFromJ rChebyshevJNat
            ⌊(K.tCarrierCell z).rRightEndpoint⌋₊ -
          nPrimeCountingFromJ rChebyshevJNat
            ⌊(K.tCarrierCell z).rLeftEndpoint⌋₊ ∧
      K.nCarrierCentralPrime z =
        fnPrimeAtRank (nCellCentralRank (K.tCarrierCell z) - 1) :=
  K.thm_carrierVonMangoldtChebyshev_sameCell z

theorem cmp_PASSAGE_PLACE_earlier_occurrence
    (K : TTrueTowerCarrier) (E : TZeroPassage) :
    K.fnCarrierMemberCentralPrime E.zEarlierMember =
      nPlaceEarlierEndpoint (K.fnCarrierPassagePlace E) :=
  K.thm_carrierPassagePlace_earlierEndpoint E

/-- C8-07 — la décomposition exacte du transport, relue sur le porteur d'ETATS
PROPRES.  La force résiduelle reste la seule clause nommée. -/
theorem cmp_C8_carrier_rpass_iff_localLaw
    {tCarrier : TTrueTowerCarrier}
    {fnPassagePlace : TZeroPassage → TPrimeHistoryPlace} :
    tCarrier.PRPassOnCarrier fnPassagePlace ↔
      tCarrier.PLocalLawOnCarrier fnPassagePlace :=
  thm_carrier_rpass_iff_localLaw

/-! ## Famille Y — vrai couple miroir et consumers de collision -/

theorem cmp_Y_offMirror_exact_objects (zOff : TOffCriticalLineUpperZero) :
    offOriginalUpperMember zOff = zOff.1 ∧
      offMirrorUpperMember zOff = zUpperMirrorZero zOff.1 :=
  ⟨rfl, rfl⟩

theorem cmp_Y_offMirror_sameHeight_distinct (zOff : TOffCriticalLineUpperZero) :
    rZeroHeight (offMirrorUpperMember zOff).1 =
        rZeroHeight (offOriginalUpperMember zOff).1 ∧
      offOriginalUpperMember zOff ≠ offMirrorUpperMember zOff :=
  ⟨thm_offMirror_sameHeight zOff, thm_offMirror_distinct zOff⟩

theorem cmp_Y_off_impossible_consumer
    (K : TTrueTowerCarrier)
    (hInjective : Function.Injective K.nCarrierCentralPrime)
    (zOff : TOffCriticalLineUpperZero)
    (hPrimeEq : K.nCarrierCentralPrime (offOriginalUpperMember zOff) =
      K.nCarrierCentralPrime (offMirrorUpperMember zOff)) : False :=
  thm_off_impossible_by_samePrimeCollision K hInjective zOff hPrimeEq

theorem cmp_Y_riemannHypothesis_consumer
    (K : TTrueTowerCarrier)
    (hInjective : Function.Injective K.nCarrierCentralPrime)
    (hMirrorCollision : ∀ zOff : TOffCriticalLineUpperZero,
      K.nCarrierCentralPrime (offOriginalUpperMember zOff) =
        K.nCarrierCentralPrime (offMirrorUpperMember zOff)) :
    RiemannHypothesis :=
  riemannHypothesis_of_samePrimeCollision K hInjective hMirrorCollision

/-! ## Famille S4-CANONICAL — le producteur causal des contacts propres -/

theorem cmp_S4_canonical_contactMinus_ge_two (z : TUpperNonTrivialZetaZero) :
    2 ≤ (canonicalTrueTowerState z).contactMinus :=
  thm_canonicalContactMinus_ge_two z

theorem cmp_S4_canonical_same_contacts_same_member
    {zLeft zRight : TUpperNonTrivialZetaZero}
    (hMinus :
      (canonicalTrueTowerState zLeft).contactMinus =
        (canonicalTrueTowerState zRight).contactMinus)
    (hPlus :
      (canonicalTrueTowerState zLeft).contactPlus =
        (canonicalTrueTowerState zRight).contactPlus) :
    zLeft = zRight :=
  thm_canonicalTrueTowerState_injective hMinus hPlus

theorem cmp_S4_canonical_carrier_state (z : TUpperNonTrivialZetaZero) :
    tCanonicalTrueTowerCarrier.fnState z = canonicalTrueTowerState z :=
  thm_canonicalTrueTowerCarrier_state z

/-! ## Famille O8-RPASS-FULL — la conservation de nullité du même passage -/

theorem cmp_O8_fullRpass_null_of_sourceNull
    {TImageMember TImageRelation : Type*}
    {fnImageEarlierEndpoint fnImageLaterEndpoint : TImageRelation → TImageMember}
    {fnMemberImage : TNonTrivialZetaZero → TImageMember}
    {fnTransport : TZeroPassage → TImageRelation}
    {PImageRelationNull : TImageRelation → Prop}
    (hFull :
      PIsFullMemberSensitivePassageTransport (fnImageEarlierEndpoint := fnImageEarlierEndpoint)
        (fnImageLaterEndpoint := fnImageLaterEndpoint) (fnMemberImage := fnMemberImage)
        (fnTransport := fnTransport) PImageRelationNull)
    {tPassage : TZeroPassage} (hNullZ : PZeroPassageRelationNull tPassage) :
    PImageRelationNull (fnTransport tPassage) :=
  thm_fullRpass_null_of_sourceNull hFull hNullZ

theorem cmp_O8_fullRpass_nonNull_of_sourceNonNull
    {TImageMember TImageRelation : Type*}
    {fnImageEarlierEndpoint fnImageLaterEndpoint : TImageRelation → TImageMember}
    {fnMemberImage : TNonTrivialZetaZero → TImageMember}
    {fnTransport : TZeroPassage → TImageRelation}
    {PImageRelationNull : TImageRelation → Prop}
    (hFull :
      PIsFullMemberSensitivePassageTransport (fnImageEarlierEndpoint := fnImageEarlierEndpoint)
        (fnImageLaterEndpoint := fnImageLaterEndpoint) (fnMemberImage := fnMemberImage)
        (fnTransport := fnTransport) PImageRelationNull)
    {tPassage : TZeroPassage} (hNonNullZ : PZeroPassageRelationNonNull tPassage) :
    ¬ PImageRelationNull (fnTransport tPassage) :=
  thm_fullRpass_nonNull_of_sourceNonNull hFull hNonNullZ

/-! ## Famille L15/L16 — reconstruction depuis la source complète des zéros -/

theorem cmp_L15_symmetricZeroWindow_finite (rCutoff : ℝ) :
    (sSymmetricZeroWindow rCutoff).Finite :=
  thm_symmetricZeroWindow_finite rCutoff

theorem cmp_L15_symmetricZeroSum_eq_labelled_sum (rArgument rCutoff : ℝ) :
    cSymmetricZeroSum rArgument rCutoff =
      ∑ cPoint ∈ (finsetSymmetricZeroWindow rCutoff).attach,
        cMemberContribution rArgument
          ⟨cPoint.1, (thm_mem_finsetSymmetricZeroWindow.mp cPoint.2).1⟩ :=
  thm_symmetricZeroSum_eq_labelled_sum rArgument rCutoff

theorem cmp_L16_reconstructedPrimeAtRank_eq_canonicalPrimeAtRank :
    fnPrimeAtRankFromPsi Chebyshev.psi = fnPrimeAtRank :=
  thm_reconstructedPrimeAtRank_eq_canonicalPrimeAtRank

theorem cmp_L16_reconstructedGap_eq_canonicalGap (nRank : ℕ) :
    fnGapAtRankFromPsi Chebyshev.psi nRank = nPrimeGap nRank :=
  thm_reconstructedGap_eq_canonicalGap nRank

theorem cmp_M9A_total_of_domain
    (hDomain : PM9aChannelIdentityOnDomain) :
    PM9aChannelIdentity :=
  thm_M9a_total_of_domain hDomain

theorem cmp_M9A_M9B_composition
    (hChannel : PM9aChannelIdentity) :
    fnReconstructGrammar rPsiZeroChannel = rhv3CanonicalGrammar :=
  thm_M9a_M9b_composition hChannel

theorem cmp_M9A_psiZeroChannel_not_definitionally_chebyshev :
    rPsiZeroChannel 1 = 0 ∧ Chebyshev.psi 1 = 0 :=
  thm_psiZeroChannel_not_definitionally_chebyshev

end RHV3Lean.Certification
