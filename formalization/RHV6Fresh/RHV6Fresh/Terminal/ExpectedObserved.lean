/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Tower.Incidences

namespace RHV6Fresh

open RHV3Lean

/-! API générique de comptage (maître mathématique §6) sur un état à deux
contacts consécutifs `TTrueHarmonicTowerState` (forme indexée).  Aucun état
n'est choisi ici ; l'instanciation sélectionnée par l'occurrence a été
supprimée le 2026-09-22 (maître Lean §22-C, §11 « Supprimés »).  L2 sur l'état
porté est `Direct/StateCount.lean` ; il lit `S.lastRayContact` et ne consomme ce
module que par `lastPrimeAtStateUpper_le_contact` (`countedPrime_le_lastRay`). -/

noncomputable def primeCountAtStateUpper
    {z : TrueZero} (S : TTrueHarmonicTowerState z) : ℕ :=
  nEdgePrimeRank S.contactPlus

theorem primeCountAtStateUpper_eq_vonMangoldt
    {z : TrueZero} (S : TTrueHarmonicTowerState z) :
    primeCountAtStateUpper S =
      nPrimeCountingFromJ rChebyshevJNat ⌊S.contactPlus⌋₊ := by
  unfold primeCountAtStateUpper
  rw [thm_edgePrimeRank_eq_primeCountingFromJ]

noncomputable def lastPrimeAtStateUpper
    {z : TrueZero} (S : TTrueHarmonicTowerState z) : ℕ :=
  fnPrimeAtRank (primeCountAtStateUpper S - 1)

theorem lastPrimeAtStateUpper_prime
    {z : TrueZero} (S : TTrueHarmonicTowerState z)
    (hPositive : 0 < primeCountAtStateUpper S) :
    Nat.Prime (lastPrimeAtStateUpper S) := by
  unfold lastPrimeAtStateUpper
  exact thm_primeAtRank_isPrime _

theorem lastPrimeAtStateUpper_le_contact
    {z : TrueZero} (S : TTrueHarmonicTowerState z)
    (hPositive : 0 < primeCountAtStateUpper S)
    (hContact : 0 ≤ S.contactPlus) :
    (lastPrimeAtStateUpper S : ℝ) ≤ S.contactPlus := by
  unfold lastPrimeAtStateUpper primeCountAtStateUpper nEdgePrimeRank
  change 0 < Nat.count Nat.Prime (⌊S.contactPlus⌋₊ + 1) at hPositive
  have hcount : Nat.count Nat.Prime (⌊S.contactPlus⌋₊ + 1) > 0 := by
    exact hPositive
  have hlast :
      Nat.nth Nat.Prime (Nat.count Nat.Prime (⌊S.contactPlus⌋₊ + 1) - 1) <
        ⌊S.contactPlus⌋₊ + 1 := by
    apply (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).mp
    exact Nat.sub_lt hcount (by omega)
  have hrank : fnPrimeAtRank (Nat.count Nat.Prime (⌊S.contactPlus⌋₊ + 1) - 1) ≤
      ⌊S.contactPlus⌋₊ := by
    unfold fnPrimeAtRank
    omega
  have hfloor : (⌊S.contactPlus⌋₊ : ℝ) ≤ S.contactPlus :=
    Nat.floor_le hContact
  exact le_trans (by exact_mod_cast hrank) hfloor

end RHV6Fresh
