/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV3Lean.Research.SameHeightPrimeStability

/-!
# RHV3Lean — terminal same-prime route

The terminal active route contains no nullity transport.

The middle of the construction remains the already-produced post-M9/M9A chain:

* each upper zero has a member-sensitive source index;
* `nMemberMZOccurrence` is the prime occurrence reconstructed by `M^Z`;
* M9a identifies that occurrence unconditionally with `nMemberCanonicalAnchor`;
* authentic consecutive zero members are transported to successive canonical
  primes by `thm_memberCanonicalAnchor_succ_of_passage` and
  `thm_memberMZOccurrence_succ_of_passage_unconditional`;
* `thm_consecutive_memberOccurrences_eq_successiveCanonicalPrimes` packages
  those facts together with the proved M9A channel and the prime/counting
  components of `M^Z = M`.

The terminal contradiction is therefore only the same-prime argument on the
authentic functional-equation mirror pair.  No `PNullPassageForcesNullPlace`,
`PZeroNullityForcesPrimeDiagonal`, zero-gap transport, contact equality, cell
equality, T1 premise or T2 premise occurs in this module.

The sole remaining named scientific premise is the collision statement saying
that an authentic OFF mirror pair is assigned the same reconstructed prime.
The contradiction then uses the already-produced injective member-sensitive
reconstruction: `thm_offMirror_memberMZOccurrences_distinct`.
-/

namespace RHV3Lean

/-- Terminal collision statement, expressed directly on the prime occurrences
reconstructed by the already-produced `M^Z = M` member-sensitive channel. -/
def POffMirrorSameReconstructedPrime : Prop :=
  ∀ zOff : TOffCriticalLineUpperZero,
    nMemberMZOccurrence (offOriginalUpperMember zOff) =
      nMemberMZOccurrence (offMirrorUpperMember zOff)

/-- The authentic OFF mirror pair cannot satisfy the same-prime collision,
because post-M9/M9A reconstruction gives distinct member-sensitive prime
occurrences to distinct upper members. -/
theorem thm_offMirror_sameReconstructedPrime_contradiction
    (hSamePrime : POffMirrorSameReconstructedPrime)
    (zOff : TOffCriticalLineUpperZero) : False := by
  exact thm_offMirror_memberMZOccurrences_distinct zOff (hSamePrime zOff)

/-- Every authentic upper nontrivial zero is central under the sole terminal
same-prime collision statement.  T1/T2 are not terminal parameters: their real
post-M9 content is already compiled into the member-sensitive reconstruction. -/
theorem thm_allUpperOnCriticalLine_of_sameReconstructedPrime
    (hSamePrime : POffMirrorSameReconstructedPrime) :
    ∀ z : TUpperNonTrivialZetaZero, rZeroRadialPosition z.1 = 1 / 2 := by
  intro z
  by_contra hOff
  exact thm_offMirror_sameReconstructedPrime_contradiction hSamePrime ⟨z, hOff⟩

/-- Terminal RH theorem on the corrected same-prime route.

Exactly one scientific premise remains in the theorem type.  There is no
nullity premise and no T1/T2 premise. -/
theorem thm_riemannHypothesis
    (hSamePrime : POffMirrorSameReconstructedPrime) :
    RiemannHypothesis :=
  thm_riemannHypothesis_of_allUpperOnCriticalLine
    (thm_allUpperOnCriticalLine_of_sameReconstructedPrime hSamePrime)

/-- Explicit one-premise terminal alias used by audits. -/
theorem thm_riemannHypothesis_of_sameReconstructedPrime_alone
    (hSamePrime : POffMirrorSameReconstructedPrime) :
    RiemannHypothesis :=
  thm_riemannHypothesis hSamePrime

#check POffMirrorSameReconstructedPrime
#check thm_offMirror_sameReconstructedPrime_contradiction
#check thm_allUpperOnCriticalLine_of_sameReconstructedPrime
#check thm_riemannHypothesis
#check thm_riemannHypothesis_of_sameReconstructedPrime_alone

#print axioms thm_offMirror_sameReconstructedPrime_contradiction
#print axioms thm_riemannHypothesis

end RHV3Lean
