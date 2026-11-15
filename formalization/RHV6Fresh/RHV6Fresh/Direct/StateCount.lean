/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Direct.MirrorCount
import RHV6Fresh.Tower.ProperTower

/-!
# RHV6Fresh — L2 : comptage sur l'état porté (maître mathématique §6, maître Lean §6)

Pour toute paire à deux lois `S : AnalyticContactPair z` (donc pour l'unique
état porté `(firstTowerOf z).properState`, `Direct/PairTowers.lean`) :

    countedRank S  = π(C⁺(S))            (canal Von Mangoldt/Chebyshev, `nEdgePrimeRank`)
    countedPrime S = p_(countedRank S − 1)   (dernier premier compté jusqu'au dernier rayon)

L2 lit directement `S.lastRayContact`.  Le raccord avec la forme indexée
`countedPrimeAt z k` (contact `C_{k+1}`) est **exact au dernier rayon**
`C⁺ = C_{k+m}` (`countedPrime_eq_countedPrimeAt_lastRay`) ; il ne vaut à la
coordonnée d'entrée que pour un étage (`countedPrime_of_one_stage`) et n'est
jamais affirmé génériquement par `rfl` (maître Lean §22-B).  Aucun choix
d'état, aucune sélection de branche, aucun premier en entrée.
-/

namespace RHV6Fresh

open RHV3Lean

variable {z : TrueZero}

/-- `N = π(C⁺)` : rang compté au dernier rayon. -/
noncomputable def countedRank (S : AnalyticContactPair z) : ℕ :=
  nEdgePrimeRank S.lastRayContact

/-- `p_constaté = p_{N−1}` : dernier premier compté jusqu'au dernier rayon. -/
noncomputable def countedPrime (S : AnalyticContactPair z) : ℕ :=
  fnPrimeAtRank (countedRank S - 1)

theorem countedRank_eq_vonMangoldt (S : AnalyticContactPair z) :
    countedRank S = nPrimeCountingFromJ rChebyshevJNat ⌊S.lastRayContact⌋₊ := by
  unfold countedRank
  rw [thm_edgePrimeRank_eq_primeCountingFromJ]

theorem countedPrime_eq_vonMangoldt (S : AnalyticContactPair z) :
    countedPrime S =
      fnPrimeAtRank (nPrimeCountingFromJ rChebyshevJNat ⌊S.lastRayContact⌋₊ - 1) := by
  unfold countedPrime
  rw [countedRank_eq_vonMangoldt]

theorem countedPrime_prime (S : AnalyticContactPair z) :
    Nat.Prime (countedPrime S) :=
  thm_primeAtRank_isPrime _

/-- Le dernier rayon est le contact supérieur indexé à la coordonnée `k + m − 1`. -/
theorem lastRayContact_eq_contactPlusAt (S : AnalyticContactPair z) :
    S.lastRayContact = contactPlusAt z (S.entryCoordinate + S.stageCount - 1) := by
  rw [S.lastRayContact_eq_incidence]
  unfold contactPlusAt
  rw [show S.entryCoordinate + (S.stageCount : ℤ) - 1 + 1 =
      S.entryCoordinate + S.stageCount by ring]
  rfl

/-- **Raccord exact au dernier rayon** `C_{k+m}` avec la forme indexée. -/
theorem countedPrime_eq_countedPrimeAt_lastRay (S : AnalyticContactPair z) :
    countedPrime S = countedPrimeAt z (S.entryCoordinate + S.stageCount - 1) := by
  unfold countedPrime countedRank
  rw [lastRayContact_eq_contactPlusAt]
  rfl

theorem countedRank_eq_countedRankAt_lastRay (S : AnalyticContactPair z) :
    countedRank S = countedRankAt z (S.entryCoordinate + S.stageCount - 1) := by
  unfold countedRank
  rw [lastRayContact_eq_contactPlusAt]
  rfl

/-- Raccord à la coordonnée d'entrée, valable pour un seul étage seulement. -/
theorem countedPrime_of_one_stage (S : AnalyticContactPair z) (h : S.stageCount = 1) :
    countedPrime S = countedPrimeAt z S.entryCoordinate := by
  rw [countedPrime_eq_countedPrimeAt_lastRay, h]
  congr 1
  push_cast
  ring

/-- Contrôle : la paire consécutive `(C_k, C_{k+1})` compte au contact indexé. -/
theorem countedPrime_analyticPairAt (z : TrueZero) (k : ℤ) :
    countedPrime (analyticPairAt z k) = countedPrimeAt z k := rfl

/-- Lemme de conversion (maître Lean §6) : dernier rayon sous `p_min` ⇒ premier
constaté sous `p_min`. -/
theorem countedPrime_lt_expected_of_lastRay (a : TrueZero) {w : TrueZero}
    (S : AnalyticContactPair w)
    (h : S.lastRayContact < (expectedMinimumPrime a : ℝ)) :
    countedPrime S < expectedMinimumPrime a := by
  rw [countedPrime_eq_countedPrimeAt_lastRay]
  apply countedPrimeAt_lt_expected_of_contact
  rw [← lastRayContact_eq_contactPlusAt]
  exact h

/-- Le premier constaté est au plus le dernier rayon (comptage inclusif, N > 0). -/
theorem countedPrime_le_lastRay (S : AnalyticContactPair z) (hPos : 0 < countedRank S) :
    (countedPrime S : ℝ) ≤ S.lastRayContact := by
  have := lastPrimeAtStateUpper_le_contact
    (towerStateAt z (S.entryCoordinate + S.stageCount - 1))
    (by rw [countedRank_eq_countedRankAt_lastRay] at hPos; exact hPos)
    (le_of_lt (contactPlusAt_positive _ _))
  rw [countedPrime_eq_countedPrimeAt_lastRay, lastRayContact_eq_contactPlusAt]
  exact this

end RHV6Fresh
