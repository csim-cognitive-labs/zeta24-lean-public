/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.IndependentContactComparison
import RHV6Fresh.Voyage.Progression

/-!
# RHV6Fresh — Voyage, step 2: Von Mangoldt reading of a Tower cell

Second chain of the demonstration, for one Tower state `S` of a member:

    contacts propres (C⁻, C⁺)
      → lecture Von Mangoldt / Chebyshev des contacts
      → premier produit `producedPrime S`

The produced prime is an **output** of the counting at the supplied contacts.
It is monotone in the upper contact: a cell that ends earlier on the axis
produces a prime that is at most the one produced by a cell ending later.
-/

namespace RHV6Fresh

open RHV3Lean

/-- The prime effectively produced by the Von Mangoldt/Chebyshev reading of
the upper contact of a Tower state (last prime `≤ C⁺`). -/
noncomputable def producedPrime {z : TrueZero} (S : TTrueHarmonicTowerState z) : ℕ :=
  lastPrimeAtStateUpper S

theorem producedPrime_eq_vonMangoldt {z : TrueZero} (S : TTrueHarmonicTowerState z) :
    producedPrime S =
      fnPrimeAtRank (nPrimeCountingFromJ rChebyshevJNat ⌊S.contactPlus⌋₊ - 1) := by
  unfold producedPrime lastPrimeAtStateUpper
  rw [primeCountAtStateUpper_eq_vonMangoldt]

theorem producedPrime_prime {z : TrueZero} (S : TTrueHarmonicTowerState z)
    (hPositive : 0 < primeCountAtStateUpper S) : Nat.Prime (producedPrime S) :=
  lastPrimeAtStateUpper_prime S hPositive

/-- The count at the upper contact is monotone in that contact. -/
theorem primeCountAtStateUpper_mono {z w : TrueZero}
    (S : TTrueHarmonicTowerState z) (S' : TTrueHarmonicTowerState w)
    (h : S.contactPlus ≤ S'.contactPlus) :
    primeCountAtStateUpper S ≤ primeCountAtStateUpper S' := by
  unfold primeCountAtStateUpper nEdgePrimeRank
  apply Nat.count_monotone
  have := Nat.floor_le_floor h
  omega

/-- **The produced prime is monotone in the upper contact.** -/
theorem producedPrime_mono {z w : TrueZero}
    (S : TTrueHarmonicTowerState z) (S' : TTrueHarmonicTowerState w)
    (h : S.contactPlus ≤ S'.contactPlus) :
    producedPrime S ≤ producedPrime S' := by
  unfold producedPrime lastPrimeAtStateUpper
  exact thm_primeAtRank_strictMono.monotone
    (Nat.sub_le_sub_right (primeCountAtStateUpper_mono S S' h) 1)

/-- A cell whose upper contact reaches `2` counts at least one prime. -/
theorem primeCountAtStateUpper_pos_of_two_le {b : TrueZero}
    (S : TTrueHarmonicTowerState b) (h : (2 : ℝ) ≤ S.contactPlus) :
    0 < primeCountAtStateUpper S := by
  unfold primeCountAtStateUpper
  by_contra hNot
  have hLe : nEdgePrimeRank S.contactPlus ≤ 0 := by omega
  have hLt := (thm_edgeRank_le_iff_lt_primeAtRank (le_of_lt S.contactPlus_pos) 0).mp hLe
  rw [thm_primeAtRank_zero_eq_two] at hLt
  push_cast at hLt
  linarith

theorem three_le_expectedMinimumPrime (a : TrueZero) :
    3 ≤ expectedMinimumPrime a := by
  unfold expectedMinimumPrime fnPrimeSuccessor fnPrimeAtRank
  have := Nat.add_two_le_nth_prime (nZeroSourceIndex a.1 + 1)
  omega

/-- Reaching an expected minimum forces a positive count (the zero-count
convention reads `2`, below every expected minimum). -/
theorem count_pos_of_reaches {a b : TrueZero} (S : TTrueHarmonicTowerState b)
    (h : expectedMinimumPrime a ≤ producedPrime S) :
    0 < primeCountAtStateUpper S := by
  by_contra hNot
  have hZero : primeCountAtStateUpper S = 0 := by omega
  have hLast : producedPrime S = 2 := by
    unfold producedPrime lastPrimeAtStateUpper
    rw [hZero]
    exact thm_primeAtRank_zero_eq_two
  have := three_le_expectedMinimumPrime a
  omega

/-- Comparison with the expected minimum, on the same produced prime: the
produced prime reaches `q(a)` exactly when the upper contact does. -/
theorem expectedMinimum_le_produced_iff (a : TrueZero) {b : TrueZero}
    (S : TTrueHarmonicTowerState b) (hCount : 0 < primeCountAtStateUpper S) :
    expectedMinimumPrime a ≤ producedPrime S ↔
      (expectedMinimumPrime a : ℝ) ≤ S.contactPlus :=
  expectedMinimum_le_stateReadout_iff a S hCount

theorem produced_lt_expectedMinimum_iff (a : TrueZero) {b : TrueZero}
    (S : TTrueHarmonicTowerState b) (hCount : 0 < primeCountAtStateUpper S) :
    producedPrime S < expectedMinimumPrime a ↔
      S.contactPlus < (expectedMinimumPrime a : ℝ) :=
  stateReadout_lt_expectedMinimum_iff a S hCount

end RHV6Fresh
