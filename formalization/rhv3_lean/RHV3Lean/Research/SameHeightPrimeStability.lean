/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Objects.ZeroGapGrammar
import RHV3Lean.Objects.CanonicalOccurrenceTransport
import RHV3Lean.Objects.SamePrimeCollision

/-!
# RHV3 — same-height prime stability research surface

This module materializes the exact incidence interface between the member-sensitive
canonical occurrence and the member's geometric cell.  It deliberately does not
identify the reconstructed occurrence with the cell's central prime.

No synthetic OFF point, nullity transport, RH assumption, or prime-selected
geometry is introduced here.
-/

namespace RHV3Lean

/-- A same-height ordered pair has zero height-gap.  This is unconditional and
already follows from O7; it is restated here as the zero-side input to the new
route. -/
theorem thm_sameHeight_zeroPairHeightGap_eq_zero
    (zLeft zRight : TNonTrivialZetaZero)
    (hSameHeight : rZeroHeight zLeft = rZeroHeight zRight) :
    rZeroPairHeightGap zLeft zRight = 0 :=
  (thm_zeroPairHeightGap_zero_iff_sameFiber zLeft zRight).2 hSameHeight

/-! ## Exact incidence interface -/

/-- Incidence is membership, not equality with the central prime selected from
the cell.  This theorem removes that possible type confusion exactly. -/
theorem thm_memberCanonicalOccurrence_incident_ownEvent_iff
    (tCarrier : TTrueTowerCarrier)
    (z : TUpperNonTrivialZetaZero) :
    PMemberAnchorLandsInOwnCell tCarrier z ↔
      nMemberCanonicalAnchor z ∈
        sAlgebraicIntervalFoundPrimes (tCarrier.tCarrierCell z) := by
  rw [thm_mem_foundPrimes_iff]
  exact ⟨fun h => ⟨thm_memberCanonicalAnchor_isPrime z, h⟩, fun h => h.2⟩

/-- Landing of the member anchor in its own cell is exactly the pair of rank
inequalities identified by the dependency audit.  This theorem does not assume
or prove either inequality; it removes all remaining definitional noise around
Q1. -/
theorem thm_memberCanonicalAnchor_mem_ownCell_iff_sourceIndex_rankWindow
    (tCarrier : TTrueTowerCarrier)
    (z : TUpperNonTrivialZetaZero) :
    PMemberAnchorLandsInOwnCell tCarrier z ↔
      nCellLeftEdgeRank (tCarrier.tCarrierCell z) ≤ nZeroSourceIndex z.1 ∧
        nZeroSourceIndex z.1 < nCellRightEdgeRank (tCarrier.tCarrierCell z) := by
  unfold PMemberAnchorLandsInOwnCell nMemberCanonicalAnchor
  rw [← thm_foundPrime_iff_rank_between, thm_mem_foundPrimes_iff]
  exact ⟨fun h => ⟨thm_primeAtRank_isPrime _, h⟩, fun h => h.2⟩

/-! ## What equal height actually gives on the geometric side -/

/-- Equal height fixes the logarithmic width of the two proper cells.  It does
not fix either contact and therefore does not identify the cells. -/
theorem thm_sameHeight_sameOwnCellLogWidth
    (tCarrier : TTrueTowerCarrier)
    {zLeft zRight : TUpperNonTrivialZetaZero}
    (hSameHeight : rZeroHeight zLeft.1 = rZeroHeight zRight.1) :
    Real.log (tCarrier.tCarrierCell zLeft).rRightEndpoint -
        Real.log (tCarrier.tCarrierCell zLeft).rLeftEndpoint =
      Real.log (tCarrier.tCarrierCell zRight).rRightEndpoint -
        Real.log (tCarrier.tCarrierCell zRight).rLeftEndpoint := by
  change Real.log (tCarrier.fnState zLeft).contactPlus -
      Real.log (tCarrier.fnState zLeft).contactMinus =
    Real.log (tCarrier.fnState zRight).contactPlus -
      Real.log (tCarrier.fnState zRight).contactMinus
  rw [(tCarrier.fnState zLeft).consecutive_width,
    (tCarrier.fnState zRight).consecutive_width, hSameHeight]

/-- In fact the cell map of any true-state carrier is injective: both contacts
decode the complete member `(beta,T)`.  Hence distinct equal-height members do
not have the same geometric cell in the present model. -/
theorem thm_distinctMembers_distinctOwnCells
    (tCarrier : TTrueTowerCarrier)
    {zLeft zRight : TUpperNonTrivialZetaZero}
    (hDistinct : zLeft ≠ zRight) :
    tCarrier.tCarrierCell zLeft ≠ tCarrier.tCarrierCell zRight := by
  intro hCell
  apply hDistinct
  apply TTrueHarmonicTowerState.thm_same_true_contacts_same_member
    (tCarrier.fnState zLeft) (tCarrier.fnState zRight)
  · exact congrArg TAlgebraicInterval.rLeftEndpoint hCell
  · exact congrArg TAlgebraicInterval.rRightEndpoint hCell

/-- Applied to the authentic functional-equation mirror, the proposed
same-cell version of "same event" goes in the opposite direction: an OFF pair
has equal height but necessarily distinct proper cells. -/
theorem thm_trueOff_mirrorOwnCells_distinct
    (tCarrier : TTrueTowerCarrier)
    (zOff : TOffCriticalLineUpperZero) :
    tCarrier.tCarrierCell (offOriginalUpperMember zOff) ≠
      tCarrier.tCarrierCell (offMirrorUpperMember zOff) :=
  thm_distinctMembers_distinctOwnCells tCarrier (thm_offMirror_distinct zOff)

/-! ## Post-M9 consequence on an authentic OFF mirror pair -/

/-- The post-M9 member-sensitive canonical anchor is injective on the authentic
upper zero source.  Hence a genuine OFF member and its functional mirror have
distinct canonical prime anchors even though they have the same height.  This
is an unconditional consequence of the already-produced zero-source index and
prime enumeration; it prevents any future proof from silently identifying the
two canonical occurrences. -/
theorem thm_offMirror_canonicalAnchors_distinct
    (zOff : TOffCriticalLineUpperZero) :
    nMemberCanonicalAnchor (offOriginalUpperMember zOff) ≠
      nMemberCanonicalAnchor (offMirrorUpperMember zOff) := by
  intro hEq
  apply thm_offMirror_distinct zOff
  apply thm_zeroSourceIndex_injective
  apply thm_primeAtRank_injective
  simpa [nMemberCanonicalAnchor] using hEq

/-- The same separation holds for the member occurrences reconstructed in
`M^Z`, because M9a has already been proved and transports each occurrence to
its canonical anchor without any T1/T2 premise. -/
theorem thm_offMirror_memberMZOccurrences_distinct
    (zOff : TOffCriticalLineUpperZero) :
    nMemberMZOccurrence (offOriginalUpperMember zOff) ≠
      nMemberMZOccurrence (offMirrorUpperMember zOff) := by
  intro hEq
  apply thm_offMirror_canonicalAnchors_distinct zOff
  calc
    nMemberCanonicalAnchor (offOriginalUpperMember zOff) =
        nMemberMZOccurrence (offOriginalUpperMember zOff) :=
      (thm_memberMZOccurrence_eq_canonicalAnchor_unconditional
        (offOriginalUpperMember zOff)).symm
    _ = nMemberMZOccurrence (offMirrorUpperMember zOff) := hEq
    _ = nMemberCanonicalAnchor (offMirrorUpperMember zOff) :=
      thm_memberMZOccurrence_eq_canonicalAnchor_unconditional
        (offMirrorUpperMember zOff)

/-! ## Q4 — unconditional prime succession on a genuine upper passage -/

/-- Consecutive upper members have strictly increasing canonical prime
anchors.  The only inputs are genuine member-sensitive consecutivity and the
upper-half-plane witnesses already carried by the endpoint types. -/
theorem thm_consecutive_canonicalPrimes_strict
    {zEarlier zLater : TUpperNonTrivialZetaZero}
    (hConsecutive : PZeroMembersConsecutive zEarlier.1 zLater.1) :
    nMemberCanonicalAnchor zEarlier < nMemberCanonicalAnchor zLater := by
  unfold nMemberCanonicalAnchor
  exact thm_primeAtRank_strictMono
    (thm_zeroSourceIndex_strictMono zEarlier.2 hConsecutive.1)

theorem thm_consecutive_canonicalPrimes_distinct
    {zEarlier zLater : TUpperNonTrivialZetaZero}
    (hConsecutive : PZeroMembersConsecutive zEarlier.1 zLater.1) :
    nMemberCanonicalAnchor zEarlier ≠ nMemberCanonicalAnchor zLater :=
  ne_of_lt (thm_consecutive_canonicalPrimes_strict hConsecutive)

/-- The complete already-produced `z_n ↔ p_n`, `z_(n+1) ↔ p_(n+1)`
package.  Besides the two member-sensitive occurrence equalities and strict
prime succession, the conclusion retains the proved M9A channel and the
prime/counting components of `M^Z = M`; thus the analytic reconstruction is a
proof dependency, not a comment-only citation. -/
theorem thm_consecutive_memberOccurrences_eq_successiveCanonicalPrimes
    {zEarlier zLater : TUpperNonTrivialZetaZero}
    (hConsecutive : PZeroMembersConsecutive zEarlier.1 zLater.1) :
    nMemberMZOccurrence zEarlier = nMemberCanonicalAnchor zEarlier ∧
      nMemberMZOccurrence zLater = nMemberCanonicalAnchor zLater ∧
      nMemberCanonicalAnchor zEarlier =
        fnPrimeAtRank (nZeroSourceIndex zEarlier.1) ∧
      nMemberCanonicalAnchor zLater =
        fnPrimeSuccessor (nZeroSourceIndex zEarlier.1) ∧
      nMemberCanonicalAnchor zEarlier < nMemberCanonicalAnchor zLater ∧
      PM9aChannelIdentityOnNaturals ∧
      (fnReconstructGrammar rPsiZeroChannel).primeAt = fnPrimeAtRank ∧
      (fnReconstructGrammar rPsiZeroChannel).counting = Nat.primeCounting := by
  let tPassage : TZeroPassage := ⟨zEarlier.1, zLater.1, hConsecutive⟩
  have hM9 := thm_M9a_M9b_components_unconditional
  refine ⟨thm_memberMZOccurrence_eq_canonicalAnchor_unconditional zEarlier,
    thm_memberMZOccurrence_eq_canonicalAnchor_unconditional zLater, rfl, ?_,
    thm_consecutive_canonicalPrimes_strict hConsecutive,
    thm_M9aChannelIdentityOnNaturals_proved, hM9.2.1, hM9.2.2.1⟩
  exact thm_memberCanonicalAnchor_succ_of_passage
    tPassage zEarlier.2 zLater.2

#print axioms thm_memberCanonicalOccurrence_incident_ownEvent_iff
#print axioms thm_memberCanonicalAnchor_mem_ownCell_iff_sourceIndex_rankWindow
#print axioms thm_sameHeight_sameOwnCellLogWidth
#print axioms thm_distinctMembers_distinctOwnCells
#print axioms thm_trueOff_mirrorOwnCells_distinct
#print axioms thm_offMirror_canonicalAnchors_distinct
#print axioms thm_offMirror_memberMZOccurrences_distinct
#print axioms thm_consecutive_canonicalPrimes_strict
#print axioms thm_consecutive_canonicalPrimes_distinct
#print axioms thm_consecutive_memberOccurrences_eq_successiveCanonicalPrimes

end RHV3Lean
