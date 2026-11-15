/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ExpectedObserved
import RHV6Fresh.Grammar.ExpectedMinimum

/-!
Exact comparison for any supplied tower state. No state is selected here.
These equivalences do not assert either terminal inequality: they identify
the real contact bound needed to prove each inequality on the same readout.
The positive-count premise prevents the zero-count convention from being
mistaken for an observed prime.
-/

namespace RHV6Fresh

open RHV3Lean

theorem expectedMinimum_le_stateReadout_iff
    (a : TrueZero) {b : TrueZero} (S : TTrueHarmonicTowerState b)
    (hCount : 0 < primeCountAtStateUpper S) :
    expectedMinimumPrime a ≤ lastPrimeAtStateUpper S ↔
      (expectedMinimumPrime a : ℝ) ≤ S.contactPlus := by
  have hRank :
      expectedMinimumPrime a ≤ lastPrimeAtStateUpper S ↔
        nZeroSourceIndex a.1 + 1 < primeCountAtStateUpper S := by
    unfold expectedMinimumPrime fnPrimeSuccessor lastPrimeAtStateUpper
    rw [thm_primeAtRank_strictMono.le_iff_le]
    omega
  rw [hRank]
  have hBound := thm_edgeRank_le_iff_lt_primeAtRank
    (le_of_lt S.contactPlus_pos) (nZeroSourceIndex a.1 + 1)
  change primeCountAtStateUpper S ≤ nZeroSourceIndex a.1 + 1 ↔
    S.contactPlus < (expectedMinimumPrime a : ℝ) at hBound
  exact ⟨fun h => le_of_not_gt (fun hlt => (not_le_of_gt h) (hBound.mpr hlt)),
    fun h => Nat.lt_of_not_ge (fun hle => (not_lt_of_ge h) (hBound.mp hle))⟩

theorem stateReadout_lt_expectedMinimum_iff
    (a : TrueZero) {b : TrueZero} (S : TTrueHarmonicTowerState b)
    (hCount : 0 < primeCountAtStateUpper S) :
    lastPrimeAtStateUpper S < expectedMinimumPrime a ↔
      S.contactPlus < (expectedMinimumPrime a : ℝ) := by
  simpa only [not_le] using
    not_congr (expectedMinimum_le_stateReadout_iff a S hCount)

end RHV6Fresh
