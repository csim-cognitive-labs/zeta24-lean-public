/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.OffFibreAndPassage
import RHV3Lean.Objects.PlaceAndLocalLaw
import RHV3Lean.Objects.TrueTowerCarrier
import RHV3Lean.Objects.Universalization

/-!
# RHV3Lean — force exacte du cœur passage / place

    TRACE_ID              : RHV3-TERMINAL-CORE-STRENGTH
    SEMANTIC_OBJECT       : conservation du gap source, distincte de sa
                            conversion en diagonalité première.
    SEMANTIC_STATEMENT    : un contrat de transport n'est pas son producteur ;
                            l'existence de la conversion en diagonalité est
                            équivalente à l'absence de tout passage zéro nul et
                            implique donc RH.
    MATHEMATICAL_STATEMENT: (exists Phi, forall E, Null_Z(E) -> Null_P(Phi E))
                            iff (forall E, not Null_Z(E)); le membre gauche
                            implique RiemannHypothesis via le passage OFF.
    MATHEMATICAL_PARENT   : O7/O8, OFF fibre, O6 non-nullité des places,
                            universalisation.
    PROOF_STRATEGY        : appliquer la non-nullité de toute place dans un
                            sens ; dans l'autre, éliminer la fausse nullité ;
                            sous OFF consommer le passage nul déjà produit.
    REQUIRED_LEMMAS       : thm_offCriticalLine_existsNullRelationPassage,
                            thm_place_isNeverNull,
                            thm_riemannHypothesis_of_allUpperOnCriticalLine.
    WHY_EACH_LEMMA_EXISTS : OFF produit le même passage nul ; O6 exclut toute
                            place nulle ; l'universalisation est analytique.
    LEAN_DEFINITION       : TSourceTaggedPrimePlace,
                            PTaggedSourceHeightDegenerate,
                            PZeroNullityForcesPrimeDiagonal.
    LEAN_THEOREM          : thm_sourceHeightNullity_is_preserved_as_provenance,
                            thm_existsZeroNullityToPrimeDiagonal_iff_noNullPassage,
                            thm_zeroNullityToPrimeDiagonal_implies_riemannHypothesis.
    SAME_MEMBER_CHECK     : le zéro OFF est celui fourni au producteur OFF.
    SAME_PASSAGE_CHECK    : le même terme E est donné à hDiagonal.
    SAME_MIDDLE_CHECK     : non applicable à la réduction passage-wise.
    SAME_HISTORY_CHECK    : le codomaine TPrimeHistoryPlace est l'histoire
                            canonique unique.
    FORBIDDEN_PREMISES    : ce module ne prétend pas produire hDiagonal ; ses
                            théorèmes mesurent explicitement sa force.
    NEXT_CONSUMER         : audit de non-circularité du futur producteur T2.
    AXIOMS                : propext, Classical.choice, Quot.sound au plus.
    LEAN_STATUS           : CERTIFIED_STRENGTH_AUDIT

Ce module ne contient aucun theorem RH sans argument : il prouve pourquoi le
seul argument affiché par ses consumers est précisément le cœur scientifique
qui reste à démontrer.
-/

namespace RHV3Lean

/-- Une place première étiquetée par le passage source exact. Cette structure
conserve l'observable de hauteur comme provenance sans l'identifier à une
égalité de premiers. -/
structure TSourceTaggedPrimePlace where
  sourcePassage : TZeroPassage
  primePlace : TPrimeHistoryPlace

/-- Attachement d'un passage source à une place candidate. -/
def tSourceTaggedPrimePlace
    (place : TZeroPassage → TPrimeHistoryPlace) (E : TZeroPassage) :
    TSourceTaggedPrimePlace :=
  ⟨E, place E⟩

/-- Le passage source complet est conservé définitionnellement : membres,
ordre, consécutivité et toutes ses projections restent disponibles. -/
@[simp] theorem thm_sourcePassage_preserved
    (place : TZeroPassage → TPrimeHistoryPlace)
    (E : TZeroPassage) :
    (tSourceTaggedPrimePlace place E).sourcePassage = E :=
  rfl

/-- L'observable conservé est la nullité de l'écart du passage source, pas la
diagonalité des deux premiers. -/
def PTaggedSourceHeightDegenerate (tagged : TSourceTaggedPrimePlace) : Prop :=
  PZeroPassageRelationNull tagged.sourcePassage

/-- L'écart entre les deux zéros du passage source reste une projection exacte
de l'occurrence enrichie. Il ne s'agit pas d'une hauteur nulle. -/
def TSourceTaggedPrimePlace.sourceHeightGap
    (tagged : TSourceTaggedPrimePlace) : ℝ :=
  rZeroPassageHeightGap tagged.sourcePassage

/-- Conservation exacte de l'écart source à travers l'attachement. -/
@[simp] theorem thm_sourceHeightGap_preserved
    (place : TZeroPassage → TPrimeHistoryPlace)
    (E : TZeroPassage) :
    (tSourceTaggedPrimePlace place E).sourceHeightGap =
      rZeroPassageHeightGap E :=
  rfl

/-- La nullité de l'écart de hauteur est conservée intégralement comme provenance. Cette
preuve ne conclut rien sur les extrémités premières. -/
theorem thm_sourceHeightNullity_is_preserved_as_provenance
    (place : TZeroPassage → TPrimeHistoryPlace)
    (E : TZeroPassage) :
    PTaggedSourceHeightDegenerate (tSourceTaggedPrimePlace place E) ↔
      PZeroPassageRelationNull E :=
  Iff.rfl

/-! ## Conservation effective par les Tours propres

La structure étiquetée ci-dessus conserve le passage. Les deux théorèmes
suivants enregistrent aussi le fait analytique plus précis demandé au niveau
des Tours : sur la branche supérieure, chaque Tour redécode la hauteur de son
propre membre, donc leur différence redécode exactement le gap du passage.
-/

/-- Différence des deux hauteurs redécodées par les Tours propres des deux
extrémités du même passage. -/
noncomputable def rTowerDecodedPassageHeightGap
    (carrier : TTrueTowerCarrier) (E : TZeroPassage) : ℝ :=
  (carrier.fnState (zUpperRepresentative E.zLaterMember)).rDecodedHeight -
    (carrier.fnState (zUpperRepresentative E.zEarlierMember)).rDecodedHeight

/-- Sur la branche supérieure, la Tour conserve exactement l'écart
`T(B)-T(A)` du passage source; aucune hauteur individuelle n'est supposée
nulle. -/
theorem thm_towerDecodedPassageHeightGap_eq_sourceHeightGap
    (carrier : TTrueTowerCarrier) (E : TZeroPassage)
    (hEarlier : 0 < rZeroHeight E.zEarlierMember)
    (hLater : 0 < rZeroHeight E.zLaterMember) :
    rTowerDecodedPassageHeightGap carrier E = rZeroPassageHeightGap E := by
  unfold rTowerDecodedPassageHeightGap rZeroPassageHeightGap rZeroPairHeightGap
  rw [(carrier.fnState (zUpperRepresentative E.zLaterMember)).thm_decodedHeight_eq_zeroHeight,
    (carrier.fnState (zUpperRepresentative E.zEarlierMember)).thm_decodedHeight_eq_zeroHeight]
  simp only [zUpperRepresentative]
  rw [thm_upperRepresentativeMember_of_positiveHeight hLater,
    thm_upperRepresentativeMember_of_positiveHeight hEarlier]

/-- En particulier, la nullité de l'écart entre les deux zéros n'est pas
perdue dans les Tours harmoniques propres. -/
theorem thm_tower_preserves_sourceHeightGap_nullity
    (carrier : TTrueTowerCarrier) (E : TZeroPassage)
    (hEarlier : 0 < rZeroHeight E.zEarlierMember)
    (hLater : 0 < rZeroHeight E.zLaterMember)
    (hGapZero : rZeroPassageHeightGap E = 0) :
    rTowerDecodedPassageHeightGap carrier E = 0 := by
  rw [thm_towerDecodedPassageHeightGap_eq_sourceHeightGap carrier E hEarlier hLater]
  exact hGapZero

/-- Application fermée au vrai passage miroir OFF sur la branche supérieure :
le producteur de fibre fournit le passage et sa positivité; aucune hypothèse de
conservation n'est ajoutée. Le gap entre les deux zéros reste nul après
décodage par leurs deux Tours propres. -/
theorem thm_upperOff_tower_preserves_mirrorPassageGap
    (carrier : TTrueTowerCarrier)
    {zUpper : TUpperNonTrivialZetaZero}
    (hOff : PIsOffCriticalLine zUpper.1) :
    ∃ E : TZeroPassage,
      rZeroPassageHeightGap E = 0 ∧
        rTowerDecodedPassageHeightGap carrier E = 0 := by
  obtain ⟨E, hGapZero, hEarlierHeight⟩ :=
    thm_offCriticalLine_existsNullPassage hOff
  have hEarlierPositive : 0 < rZeroHeight E.zEarlierMember := by
    rw [hEarlierHeight]
    exact zUpper.2
  have hLaterPositive : 0 < rZeroHeight E.zLaterMember := by
    have hGapNonnegative := thm_zeroPassage_heightGap_nonnegative E
    unfold rZeroPassageHeightGap rZeroPairHeightGap at hGapNonnegative
    linarith
  exact ⟨E, hGapZero,
    thm_tower_preserves_sourceHeightGap_nullity carrier E
      hEarlierPositive hLaterPositive hGapZero⟩

/-- Le cas OFF fidèle : le même objet enrichi conserve un gap source nul et
porte simultanément une vraie place première non nulle. Il n'y a aucune perte
de l'effet miroir et aucune contradiction entre ces deux observables distincts. -/
theorem thm_off_zeroSourceGap_and_strictPrimePlace_coexist
    (place : TZeroPassage → TPrimeHistoryPlace)
    {zZero : TNonTrivialZetaZero}
    (hOff : PIsOffCriticalLine zZero) :
    ∃ tagged : TSourceTaggedPrimePlace,
      tagged.sourceHeightGap = 0 ∧
        ¬ PPlaceRelationNull tagged.primePlace := by
  obtain ⟨E, hGapZero, _⟩ := thm_offCriticalLine_existsNullPassage hOff
  refine ⟨tSourceTaggedPrimePlace place E, ?_, ?_⟩
  · exact hGapZero
  · exact thm_place_isNeverNull (place E)

/-- Implication plus forte utilisée par le piège proposé : la nullité de
l'écart entre les deux hauteurs forcerait la diagonalité de la place première.
Ce n'est pas le théorème de conservation par la Tour ci-dessus. -/
def PZeroNullityForcesPrimeDiagonal
    (place : TZeroPassage → TPrimeHistoryPlace) : Prop :=
  ∀ E : TZeroPassage,
    PZeroPassageRelationNull E → PPlaceRelationNull (place E)

/-- Produire la conversion vers la diagonalité des places canoniques est exactement
produire l'absence universelle de passage zéro nul.

La réciproque utilise une place constante uniquement pour mesurer la force
logique du contrat : sous absence de passage nul, sa prémisse est impossible. -/
theorem thm_existsZeroNullityToPrimeDiagonal_iff_noNullPassage :
    (∃ place : TZeroPassage → TPrimeHistoryPlace,
        PZeroNullityForcesPrimeDiagonal place) ↔
      (∀ E : TZeroPassage, ¬ PZeroPassageRelationNull E) := by
  constructor
  · rintro ⟨place, hTransport⟩ E hNull
    exact thm_place_isNeverNull (place E) (hTransport E hNull)
  · intro hNoNull
    refine ⟨fun _ => ⟨0⟩, ?_⟩
    intro E hNull
    exact (hNoNull E hNull).elim

/-- Sur le vrai passage OFF produit dans la fibre, la conversion en diagonalité
entre immédiatement en contradiction avec la non-nullité de sa place. -/
theorem thm_zeroNullityToPrimeDiagonal_implies_offImpossible
    (place : TZeroPassage → TPrimeHistoryPlace)
    (hDiagonal : PZeroNullityForcesPrimeDiagonal place)
    {zZero : TNonTrivialZetaZero}
    (hOff : PIsOffCriticalLine zZero) : False := by
  obtain ⟨E, hNull⟩ := thm_offCriticalLine_existsNullRelationPassage hOff
  exact thm_place_isNeverNull (place E) (hDiagonal E hNull)

/-- Centralité de tout vrai zéro supérieur, conditionnelle exactement à la
conversion en diagonalité dont la force est auditée ci-dessus. -/
theorem thm_zeroNullityToPrimeDiagonal_implies_allUpperCentral
    (place : TZeroPassage → TPrimeHistoryPlace)
    (hDiagonal : PZeroNullityForcesPrimeDiagonal place)
    (zUpper : TUpperNonTrivialZetaZero) :
    rZeroRadialPosition zUpper.1 = 1 / 2 := by
  by_contra hOff
  exact thm_zeroNullityToPrimeDiagonal_implies_offImpossible
    place hDiagonal hOff

/-- Audit terminal : la conversion demandée implique déjà RH. Ce theorem n'est
pas un theorem terminal, car `hDiagonal` est précisément le producteur absent. -/
theorem thm_zeroNullityToPrimeDiagonal_implies_riemannHypothesis
    (place : TZeroPassage → TPrimeHistoryPlace)
    (hDiagonal : PZeroNullityForcesPrimeDiagonal place) :
    RiemannHypothesis := by
  exact thm_riemannHypothesis_of_allUpperOnCriticalLine
    (thm_zeroNullityToPrimeDiagonal_implies_allUpperCentral place hDiagonal)

end RHV3Lean

#print axioms RHV3Lean.thm_sourceHeightNullity_is_preserved_as_provenance
#print axioms RHV3Lean.thm_towerDecodedPassageHeightGap_eq_sourceHeightGap
#print axioms RHV3Lean.thm_tower_preserves_sourceHeightGap_nullity
#print axioms RHV3Lean.thm_upperOff_tower_preserves_mirrorPassageGap
#print axioms RHV3Lean.thm_off_zeroSourceGap_and_strictPrimePlace_coexist
#print axioms RHV3Lean.thm_existsZeroNullityToPrimeDiagonal_iff_noNullPassage
#print axioms RHV3Lean.thm_zeroNullityToPrimeDiagonal_implies_riemannHypothesis
