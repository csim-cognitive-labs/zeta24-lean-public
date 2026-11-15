/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Tower.InvertedTower
import RHV6Fresh.Direct.PivotCell

/-!
# RHV6Fresh — lecture « atteint » et comptage dans la seconde orientation (Tour du zéro réfléchi `1 − ρ`)

Niveau LECTURE ARITHMÉTIQUE.  Le comptage de Von Mangoldt/Chebyshev se fait **au dernier rayon** ;
dans la seconde orientation le dernier rayon est le rayon du bas.  Un premier `p` est atteint par un
état inversé `S` lorsque `p ≤ C⁺(S)`, avec `C⁺(S)` le rayon du bas : même formule de comptage, même
dualité rang/contact que `Direct/Reached.lean`, appliquées au dernier rayon de cette orientation.

La règle du pivot dans la seconde orientation (`invertedPivotPair z q`) : même événement d'arrêt, même
anneau `(C_k, C_{k+1}]` avec `k = ⌈(T log q − φ)/π⌉ − 1` (`pivotCoordinate`), contacts inversés par
théorème (`Tower/ReflectedMotion.lean`, `invertedPairAt_eq_reflected`) :
entrée `C_{k+1}` (au-dessus du pivot), dernier rayon `C_k` (strictement sous le pivot).  Le pivot est
donc dans la cellule et n'est jamais compté au dernier rayon (`invertedPivotPair_not_reaches`).

Aucun zéro hors ligne calculé ; aucune hypothèse ; aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

namespace InvertedContactPair

variable {z : TrueZero} (S : InvertedContactPair z)

/-- La cellule de l'état inversé : l'unique intervalle `[C⁺, C⁻]` de ses deux contacts. -/
def cell : Set ℝ := Set.Icc S.lastRayContact S.entryContact

/-- `p` est atteint par `S` : compté jusqu'au dernier rayon (le rayon du bas). -/
def reaches (p : ℕ) : Prop := (p : ℝ) ≤ S.lastRayContact

theorem not_reaches_iff (p : ℕ) : ¬ S.reaches p ↔ S.lastRayContact < (p : ℝ) := by
  unfold reaches
  exact not_le

theorem reaches_of_le {p q : ℕ} (hpq : p ≤ q) (hq : S.reaches q) : S.reaches p :=
  le_trans (by exact_mod_cast hpq) hq

theorem not_reaches_of_lastRay_lt {p : ℕ} (h : S.lastRayContact < (p : ℝ)) : ¬ S.reaches p :=
  (S.not_reaches_iff p).mpr h

/-- `N = π(C⁺)` : rang compté au dernier rayon. -/
noncomputable def countedRank : ℕ := nEdgePrimeRank S.lastRayContact

/-- `p_constaté = p_{N−1}` : dernier premier compté jusqu'au dernier rayon. -/
noncomputable def countedPrime : ℕ := fnPrimeAtRank (S.countedRank - 1)

theorem countedPrime_prime : Nat.Prime S.countedPrime := thm_primeAtRank_isPrime _

theorem countedRank_eq_vonMangoldt :
    S.countedRank = nPrimeCountingFromJ rChebyshevJNat ⌊S.lastRayContact⌋₊ := by
  unfold countedRank
  rw [thm_edgePrimeRank_eq_primeCountingFromJ]

/-- **Dualité rang/contact** (RHV3Lean) au dernier rayon de la seconde orientation. -/
theorem reaches_primeAtRank_iff (r : ℕ) : S.reaches (fnPrimeAtRank r) ↔ r < S.countedRank := by
  unfold reaches countedRank
  have hpos : 0 ≤ S.lastRayContact := le_of_lt S.lastRayContact_pos
  constructor
  · intro h
    by_contra hnot
    exact absurd ((thm_edgeRank_le_iff_lt_primeAtRank hpos r).mp (not_lt.mp hnot)) (not_lt.mpr h)
  · intro h
    by_contra hnot
    exact absurd ((thm_edgeRank_le_iff_lt_primeAtRank hpos r).mpr (not_le.mp hnot)) (not_le.mpr h)

/-- Un premier est atteint exactement quand il ne dépasse pas le premier constaté (compte positif). -/
theorem reaches_iff_le_countedPrime {p : ℕ} (hp : Nat.Prime p) (hPos : 0 < S.countedRank) :
    S.reaches p ↔ p ≤ S.countedPrime := by
  have hr := S.reaches_primeAtRank_iff (Nat.count Nat.Prime p)
  rw [thm_primeAtRank_surjective_onPrimes hp] at hr
  rw [hr]
  unfold countedPrime
  constructor
  · intro hlt
    have h1 : fnPrimeAtRank (Nat.count Nat.Prime p) ≤ fnPrimeAtRank (S.countedRank - 1) :=
      thm_primeAtRank_strictMono.monotone (by omega)
    rwa [thm_primeAtRank_surjective_onPrimes hp] at h1
  · intro hle
    have h1 : fnPrimeAtRank (Nat.count Nat.Prime p) ≤ fnPrimeAtRank (S.countedRank - 1) := by
      simpa only [thm_primeAtRank_surjective_onPrimes hp] using hle
    have h2 : Nat.count Nat.Prime p ≤ S.countedRank - 1 :=
      thm_primeAtRank_strictMono.le_iff_le.mp h1
    omega

/-- Le premier constaté est strictement sous tout premier de rang au moins un qui n'est pas atteint. -/
theorem countedPrime_lt_of_not_reaches_succ {n : ℕ} (h : ¬ S.reaches (fnPrimeAtRank (n + 1))) :
    S.countedPrime < fnPrimeAtRank (n + 1) := by
  rw [reaches_primeAtRank_iff] at h
  unfold countedPrime
  apply thm_primeAtRank_strictMono
  omega

/-- L'occurrence est atteinte exactement quand le rang compté dépasse l'index zéro-source. -/
theorem reaches_occurrence_iff {w : TrueZero} (S : InvertedContactPair w) :
    S.reaches (occurrence w) ↔ nZeroSourceIndex w.1 < S.countedRank := by
  rw [occurrence_eq_primeAtRank]
  exact S.reaches_primeAtRank_iff _

/-- Compte positif dès que l'occurrence est atteinte. -/
theorem countedRank_pos_of_reaches_occurrence {w : TrueZero} (S : InvertedContactPair w)
    (hRead : S.reaches (occurrence w)) : 0 < S.countedRank := by
  have h := S.reaches_occurrence_iff.mp hRead
  omega

end InvertedContactPair

/-! ## La règle du pivot dans la seconde orientation -/

/-- La paire de rayons `(C_{k+1}, C_k)` à `k = pivotCoordinate z q`, contacts inversés : le même
anneau que `pivotPair z q`, entrée en haut, dernier rayon en bas. -/
noncomputable def invertedPivotPair (z : TrueZero) (q : ℝ) : InvertedContactPair z :=
  invertedPairAt z (pivotCoordinate z q)

theorem invertedPivotPair_entryContact (z : TrueZero) (q : ℝ) :
    (invertedPivotPair z q).entryContact = (pivotPair z q).lastRayContact := rfl

theorem invertedPivotPair_lastRayContact (z : TrueZero) (q : ℝ) :
    (invertedPivotPair z q).lastRayContact = (pivotPair z q).entryContact := rfl

theorem invertedPivotPair_upright (z : TrueZero) (q : ℝ) :
    (invertedPivotPair z q).upright = pivotPair z q := rfl

/-- Le pivot est dans la cellule : le dernier rayon (bas) est strictement sous lui, l'entrée (haut)
est au moins lui. -/
theorem invertedPivotPair_cell_contains (z : TrueZero) {q : ℝ} (hq : 0 < q) :
    (invertedPivotPair z q).lastRayContact < q ∧ q ≤ (invertedPivotPair z q).entryContact :=
  ⟨entry_lt_pivot z hq, pivot_le_lastRay z hq⟩

theorem invertedPivotPair_lastRay_lt_pivot (z : TrueZero) {q : ℝ} (hq : 0 < q) :
    (invertedPivotPair z q).lastRayContact < q :=
  entry_lt_pivot z hq

/-- Dans la seconde orientation, le pivot n'est **jamais** compté au dernier rayon : le dernier rayon
est le rayon du bas de son anneau. -/
theorem invertedPivotPair_not_reaches (z : TrueZero) {p : ℕ} (hp : 0 < p) :
    ¬ (invertedPivotPair z p).reaches p :=
  (invertedPivotPair z p).not_reaches_of_lastRay_lt
    (invertedPivotPair_lastRay_lt_pivot z (by exact_mod_cast hp))

/-- Aucun premier au moins égal au pivot n'est atteint. -/
theorem invertedPivotPair_not_reaches_of_le (z : TrueZero) {p q : ℕ} (hqp : q ≤ p) (hq : 0 < q) :
    ¬ (invertedPivotPair z q).reaches p :=
  fun h => invertedPivotPair_not_reaches z hq ((invertedPivotPair z q).reaches_of_le hqp h)

/-- Les lectures : la coordonnée d'entrée est celle du rayon du haut, `k + 1` ; `m = 1`. -/
theorem invertedPivotPair_entryCoordinate (z : TrueZero) (q : ℝ) :
    (invertedPivotPair z q).entryCoordinate = pivotCoordinate z q + 1 := by
  unfold InvertedContactPair.entryCoordinate
  rw [invertedPivotPair_upright, pivotPair_entryCoordinate, pivotPair_stageCount]
  simp

theorem invertedPivotPair_stageCount (z : TrueZero) (q : ℝ) :
    (invertedPivotPair z q).stageCount = 1 := by
  unfold InvertedContactPair.stageCount
  rw [invertedPivotPair_upright, pivotPair_stageCount]

end RHV6Fresh
