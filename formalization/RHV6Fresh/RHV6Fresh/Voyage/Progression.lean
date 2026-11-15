/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Grammar.ExpectedMinimum

/-!
# RHV6Fresh — Voyage, step 1: obligatory progression from the zeros alone

First chain of the demonstration:

    passage précédent a → b
      → ordre des premiers (M^Z = M, Seam)
      → premier minimal attendu q(a)

Only the zero order and the Seam `M^Z = M` enter.  No Tower, no contact, no
prime reading, and no OFF case is considered here: the progression is the
same law for every consecutive passage.
-/

namespace RHV6Fresh

open RHV3Lean

/-- The passage carried by two consecutive upper members. -/
def passageOf {a b : TrueZero} (hab : PZeroMembersConsecutive a.1 b.1) : TZeroPassage :=
  ⟨a.1, b.1, hab⟩

/-- **Progression obligatoire.** On every consecutive passage the occurrence
of the later member is exactly the expected minimum of the earlier one. -/
theorem progression_occurrence {a b : TrueZero}
    (hab : PZeroMembersConsecutive a.1 b.1) :
    occurrence b = expectedMinimumPrime a :=
  (expectedMinimumPrime_eq_laterOccurrence (passageOf hab) a.2 b.2).symm

/-- The occurrence strictly advances on every consecutive passage. -/
theorem progression_strict {a b : TrueZero}
    (hab : PZeroMembersConsecutive a.1 b.1) :
    occurrence a < occurrence b :=
  occurrence_strict_of_passage (passageOf hab) a.2 b.2

/-- The expected minimum is the prime successor of the member's own
occurrence: `q(a) = p_{n(a)+1}`. -/
theorem expectedMinimum_eq_succ_occurrence (a : TrueZero) :
    expectedMinimumPrime a = fnPrimeSuccessor (nZeroSourceIndex a.1) := rfl

theorem occurrence_eq_primeAtRank (z : TrueZero) :
    occurrence z = fnPrimeAtRank (nZeroSourceIndex z.1) := by
  rw [occurrence_eq_canonicalAnchor]
  rfl

end RHV6Fresh
