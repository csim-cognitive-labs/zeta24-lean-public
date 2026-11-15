/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Direct.StateCount
import RHV6Fresh.Voyage.Progression

/-!
# RHV6Fresh — cellule de l'état et lecture « atteint » (2026-09-22, sixième correction)

Transcription du maître mathématique §6 et §9 corrigés (maître Lean §9, §26) :

* la **cellule** d'un état `S` est l'unique intervalle algébrique `[C⁻, C⁺]`
  délimité par ses deux contacts ; elle contient un ou plusieurs premiers ;
* un premier `p` est **atteint** par `S` lorsqu'il est compté jusqu'au dernier
  rayon : `p ≤ C⁺` ; il est **non atteint** sinon (`C⁺ < p`).

Le test (maîtres finaux §9) est le même exercice pour chaque Tour : contacts par la règle du pivot,
comptage jusqu'au dernier rayon, confrontation à la même référence `p_min(z)` ; ses constats sont R₁
et C_lecture (théorèmes sur la première Tour, `Direct/PairTowers.lean`) et, sur la seconde Tour,
V (théorème de la seconde orientation, `Direct/InvertedCount.lean`) et C_lecture (lecture) ; la comparaison finale des deux Tours est compilée dans
Terminal/TwoTowersComparison.lean et Terminal/PairContradiction.lean.  Ici : la définition, ses équivalences arithmétiques
(dualité rang/contact de RHV3Lean) et le raccord de fermeture par la
progression compilée.  Aucun recul n'entre nulle part.  Aucun `sorry`, aucun
`admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

variable {z : TrueZero}

/-- La cellule de l'état : l'unique intervalle `[C⁻, C⁺]` de ses deux contacts. -/
def AnalyticContactPair.cell (S : AnalyticContactPair z) : Set ℝ :=
  Set.Icc S.entryContact S.lastRayContact

theorem AnalyticContactPair.cell_nonempty (S : AnalyticContactPair z) : S.cell.Nonempty :=
  Set.nonempty_Icc.mpr (le_of_lt S.ordered)

/-- `p` est atteint par `S` : compté jusqu'au dernier rayon. -/
def reaches (S : AnalyticContactPair z) (p : ℕ) : Prop := (p : ℝ) ≤ S.lastRayContact

theorem not_reaches_iff (S : AnalyticContactPair z) (p : ℕ) :
    ¬ reaches S p ↔ S.lastRayContact < (p : ℝ) := by
  unfold reaches
  exact not_le

theorem reaches_of_le (S : AnalyticContactPair z) {p q : ℕ} (hpq : p ≤ q)
    (hq : reaches S q) : reaches S p :=
  le_trans (by exact_mod_cast hpq) hq

theorem reaches_of_mem_cell (S : AnalyticContactPair z) {p : ℕ} (h : (p : ℝ) ∈ S.cell) :
    reaches S p := h.2

/-- **Dualité rang/contact** (RHV3Lean) : le premier de rang `r` est atteint
exactement quand `r` est strictement sous le rang compté au dernier rayon. -/
theorem reaches_primeAtRank_iff (S : AnalyticContactPair z) (r : ℕ) :
    reaches S (fnPrimeAtRank r) ↔ r < countedRank S := by
  unfold reaches countedRank
  have hpos : 0 ≤ S.lastRayContact := le_of_lt S.lastRayContact_pos
  constructor
  · intro h
    by_contra hnot
    exact absurd ((thm_edgeRank_le_iff_lt_primeAtRank hpos r).mp (not_lt.mp hnot)) (not_lt.mpr h)
  · intro h
    by_contra hnot
    exact absurd ((thm_edgeRank_le_iff_lt_primeAtRank hpos r).mpr (not_le.mp hnot)) (not_le.mpr h)

/-- Un premier est atteint exactement quand il ne dépasse pas le premier constaté
(compte positif). -/
theorem reaches_iff_le_countedPrime (S : AnalyticContactPair z) {p : ℕ}
    (hp : Nat.Prime p) (hPos : 0 < countedRank S) :
    reaches S p ↔ p ≤ countedPrime S := by
  have hr := reaches_primeAtRank_iff S (Nat.count Nat.Prime p)
  rw [thm_primeAtRank_surjective_onPrimes hp] at hr
  rw [hr]
  unfold countedPrime
  constructor
  · intro hlt
    have h1 : fnPrimeAtRank (Nat.count Nat.Prime p) ≤ fnPrimeAtRank (countedRank S - 1) :=
      thm_primeAtRank_strictMono.monotone (by omega)
    rwa [thm_primeAtRank_surjective_onPrimes hp] at h1
  · intro hle
    have h1 : fnPrimeAtRank (Nat.count Nat.Prime p) ≤ fnPrimeAtRank (countedRank S - 1) := by
      simpa only [thm_primeAtRank_surjective_onPrimes hp] using hle
    have h2 : Nat.count Nat.Prime p ≤ countedRank S - 1 :=
      thm_primeAtRank_strictMono.le_iff_le.mp h1
    omega

/-- L'occurrence est atteinte exactement quand le rang compté dépasse l'index
zéro-source : `n(w) < π(C⁺)`. -/
theorem reaches_occurrence_iff {w : TrueZero} (S : AnalyticContactPair w) :
    reaches S (occurrence w) ↔ nZeroSourceIndex w.1 < countedRank S := by
  rw [occurrence_eq_primeAtRank]
  exact reaches_primeAtRank_iff S _

/-- Le minimum attendu est atteint exactement quand `n(w) + 1 < π(C⁺)`. -/
theorem reaches_expected_iff {w : TrueZero} (S : AnalyticContactPair w) :
    reaches S (expectedMinimumPrime w) ↔ nZeroSourceIndex w.1 + 1 < countedRank S := by
  unfold expectedMinimumPrime fnPrimeSuccessor
  exact reaches_primeAtRank_iff S _

/-- **Raccord de fermeture** : sur un passage consécutif `z → z'`, atteindre
l'occurrence de `z'` c'est atteindre le minimum attendu de `z` (progression
compilée, aucune Tour). -/
theorem reaches_expected_of_reaches_occurrence {z z' : TrueZero}
    (hab : PZeroMembersConsecutive z.1 z'.1) (S' : AnalyticContactPair z')
    (h : reaches S' (occurrence z')) : reaches S' (expectedMinimumPrime z) := by
  rw [← progression_occurrence hab]
  exact h

/-- Forme positive générique : `p ≤ C⁺` est la lecture « atteint ». -/
theorem reaches_of_le_lastRay {w : TrueZero} (S : AnalyticContactPair w) {p : ℕ}
    (h : (p : ℝ) ≤ S.lastRayContact) : reaches S p := h

/-- Forme négative générique (neuvième correction, MATH §22) : l'inégalité `C⁺ < p` est le fait à
démontrer ; « non atteint » en est le corollaire trivial.  Pour V : `p = p_min(z)` sur l'état de `z*`. -/
theorem not_reaches_of_lastRay_lt {w : TrueZero} (S : AnalyticContactPair w) {p : ℕ}
    (h : S.lastRayContact < (p : ℝ)) : ¬ reaches S p :=
  (not_reaches_iff S _).mpr h

/-- Forme exacte de R₁ sur un état porté (maître MATH §22) : `p_min(w) ≤ C⁺` est la lecture positive. -/
theorem reaches_expected_of_le_lastRay {w : TrueZero} (S : AnalyticContactPair w)
    (h : ((expectedMinimumPrime w : ℕ) : ℝ) ≤ S.lastRayContact) :
    reaches S (expectedMinimumPrime w) := h

/-- Corollaire, même zéro : `C⁺ < p_min(w)` ⇒ `p_min(w)` non atteint. -/
theorem not_reaches_expected_of_lastRay_lt {w : TrueZero} (S : AnalyticContactPair w)
    (h : S.lastRayContact < ((expectedMinimumPrime w : ℕ) : ℝ)) :
    ¬ reaches S (expectedMinimumPrime w) :=
  (not_reaches_iff S _).mpr h

/-- Atteint et non atteint sur le même état : contradiction (forme littérale de
la fermeture, maître Lean §10). -/
theorem reaches_and_not_reaches_false {w : TrueZero} (S : AnalyticContactPair w) {p : ℕ}
    (h1 : reaches S p) (h2 : ¬ reaches S p) : False := h2 h1

/-- Contrôle de formule : à la coordonnée `k`, « atteint » est `p ≤ C_{k+1}`. -/
theorem reaches_analyticPairAt_iff (z : TrueZero) (k : ℤ) (p : ℕ) :
    reaches (analyticPairAt z k) p ↔ (p : ℝ) ≤ contactPlusAt z k := Iff.rfl

end RHV6Fresh
