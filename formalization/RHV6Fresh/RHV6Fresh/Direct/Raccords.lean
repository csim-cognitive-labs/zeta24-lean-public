/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Voyage.FiberSuccessor
import RHV6Fresh.Direct.Reached
import RHV6Fresh.Tower.TrueTowerStructure

/-!
# RHV6Fresh — raccords du zéro suivant et lecture « atteint » aux coordonnées lues

Module `RHV6Fresh/Direct/Raccords.lean` (tour 2 de la boucle production /
critique, 2026-09-22 ; dérivations sans hypothèse retenues du tour 1).

## 1. Le zéro suivant (maître mathématique §2, §9 ; maître Lean §8, §9.2)

Pour un membre de côté `β < 1/2` et son successeur consécutif `z'`
(`exists_fiberSuccessor`, `Voyage/FiberSuccessor.lean`), le maître mathématique §9
écrit : `z' := min_≺ S(z)`, `z ▷ z'`, `T(z') = T`, `β < β(z') ≤ 1 − β`, et
`z' = z*` si aucun zéro de même ordonnée ne s'interpose.  Le maître Lean §9.2 précise
que `T(z') = T(z)` « se déduit de `hβ`, `hab` par `mirror_precedes` et le verrou de
la fibre » : c'est ce qui rend la signature de `next_not_reaches_expected` (sans
hypothèse d'ordonnée) suffisante.  Ce module transcrit ces quatre faits :

* `fiberSuccessor_ordinate_eq`        : `T(z') = T(z)` depuis `hβ`, `hab` seuls ;
* `consecutive_successor_unique`      : le successeur consécutif est unique
  (totalité de l'ordre, maître mathématique §2) ;
* `fiberSuccessor_eq_mirror_or_precedes`, `fiberSuccessor_eq_mirror_of_noInterposition` :
  `z' = z*`, ou bien `z'` s'interpose entre `z` et `z*` (maître sémantique §9) ;
* `radial_gt_of_consecutive_lowerSide`, `radial_le_mirror_of_consecutive_lowerSide` :
  `β(z) < β(z') ≤ 1 − β(z)` depuis `hβ`, `hab` seuls.

Aucun zéro n'est construit, calculé ni approché ; le miroir n'entre que par
`mirror_precedes` (ordre) ; aucun recul n'est considéré (maître Lean §26).

## 2. Lecture « atteint » aux coordonnées lues (maître mathématique §5.c, §6)

`A(w, p) :⇔ p ≤ C⁺` (§6) et `C⁺ = C_{k+m} = exp((φ + (k+m)π)/T)` avec `k`, `m` lus
(§5.c, `lastRayContact_eq_incidence`).  D'où, pour toute paire à deux lois (lemme
générique de L2, jamais un énoncé L5, maître Lean §6, §12) :

    reaches S p  ↔  T·log p ≤ φ + (k + m)·π        (p > 0).

Les lectures `k`, `m` ne sont ni posées ni cherchées : elles sont lues sur `S`.

## 3. Un étage (maître mathématique §5.c ; maître Lean §5.2, §22-B)

Lorsque le nombre d'étages lu vaut `1`, la paire portée est, comme valeur, la
valeur des formules à sa coordonnée lue (`contacts_of_one_stage` + extensionnalité
par contacts) : `S = analyticPairAt z S.entryCoordinate`.  C'est le raccord d'un
étage, sous hypothèse explicite `stageCount = 1`, jamais un raccord générique.
Il ne fait d'aucune valeur de formule un contact de la Tour : il dit que les deux
contacts d'un état à un étage sont `C_k` et `C_{k+1}` à la coordonnée lue.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau ; aucun habitant du type porteur
`TrueTower z`, aucun énoncé de multiplicité, aucune formule de `k`.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Le zéro suivant : raccords sans hypothèse -/

/-- `T(z') = T(z)` se déduit de `hβ` et `hab` (maître Lean §9.2) : le miroir suit
`z` (`mirror_precedes`) ; ou bien `z'` est le miroir, ou bien `z'` s'interpose entre
`z` et son miroir et le verrou de la fibre (`thm_sameFiberInterposition`) fixe son
ordonnée, ou bien le miroir s'interposerait entre `z` et `z'`, ce que la
consécutivité interdit. -/
theorem fiberSuccessor_ordinate_eq {z z' : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (hab : PZeroMembersConsecutive z.1 z'.1) :
    rZeroHeight z'.1 = rZeroHeight z.1 := by
  have hMirror := mirror_precedes hβ
  by_cases hEq : z'.1 = (mirrorMember z).1
  · rw [hEq]
    exact mirrorMember_ordinate z
  · rcases thm_distinctZeroMembers_comparable hEq with hBefore | hAfter
    · exact thm_sameFiberInterposition (mirrorMember_ordinate z).symm hab.1 hBefore
    · exact absurd ⟨(mirrorMember z).1, hMirror, hAfter⟩ hab.2

/-- Le successeur consécutif est unique (totalité de l'ordre, maître mathématique §2 :
`z' = min_≺ S(z)`). -/
theorem consecutive_successor_unique {z z₁ z₂ : TrueZero}
    (h₁ : PZeroMembersConsecutive z.1 z₁.1)
    (h₂ : PZeroMembersConsecutive z.1 z₂.1) :
    z₁ = z₂ := by
  by_contra hNe
  have hNe' : z₁.1 ≠ z₂.1 := fun h => hNe (Subtype.ext h)
  rcases thm_distinctZeroMembers_comparable hNe' with h | h
  · exact h₂.2 ⟨z₁.1, h₁.1, h⟩
  · exact h₁.2 ⟨z₂.1, h₂.1, h⟩

/-- Dichotomie du maître sémantique §9 : le zéro suivant est le miroir lui-même, ou
un zéro de même ordonnée qui s'interpose entre `z` et son miroir. -/
theorem fiberSuccessor_eq_mirror_or_precedes {z z' : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (hab : PZeroMembersConsecutive z.1 z'.1) :
    z' = mirrorMember z ∨ PZeroMemberPrecedes z'.1 (mirrorMember z).1 := by
  by_cases hEq : z'.1 = (mirrorMember z).1
  · exact Or.inl (Subtype.ext hEq)
  · rcases thm_distinctZeroMembers_comparable hEq with hBefore | hAfter
    · exact Or.inr hBefore
    · exact absurd ⟨(mirrorMember z).1, mirror_precedes hβ, hAfter⟩ hab.2

/-- Sans interposition (`S(z) = {z*}`, maître mathématique §9), le zéro suivant est le
miroir. -/
theorem fiberSuccessor_eq_mirror_of_noInterposition {z z' : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (hab : PZeroMembersConsecutive z.1 z'.1)
    (hNo : ¬ ∃ v : TNonTrivialZetaZero,
      PZeroMemberPrecedes z.1 v ∧ PZeroMemberPrecedes v (mirrorMember z).1) :
    z' = mirrorMember z :=
  consecutive_successor_unique hab ⟨mirror_precedes hβ, hNo⟩

/-- `β(z) < β(z')` depuis `hβ`, `hab` seuls (maître mathématique §9). -/
theorem radial_gt_of_consecutive_lowerSide {z z' : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (hab : PZeroMembersConsecutive z.1 z'.1) :
    rZeroRadialPosition z.1 < rZeroRadialPosition z'.1 :=
  fiberSuccessor_radial_gt (fiberSuccessor_ordinate_eq hβ hab) hab

/-- `β(z') ≤ 1 − β(z)` depuis `hβ`, `hab` seuls (maître mathématique §9). -/
theorem radial_le_mirror_of_consecutive_lowerSide {z z' : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (hab : PZeroMembersConsecutive z.1 z'.1) :
    rZeroRadialPosition z'.1 ≤ 1 - rZeroRadialPosition z.1 :=
  fiberSuccessor_radial_le_mirror hβ (fiberSuccessor_ordinate_eq hβ hab) hab

/-! ## 2. Lecture « atteint » aux coordonnées lues -/

/-- L'occurrence d'un zéro est un nombre premier (`Occ(z) = p_{n(z)}`, maître
mathématique §6). -/
theorem occurrence_prime (w : TrueZero) : Nat.Prime (occurrence w) := by
  rw [occurrence_eq_primeAtRank]
  exact thm_primeAtRank_isPrime _

theorem occurrence_pos (w : TrueZero) : 0 < occurrence w :=
  (occurrence_prime w).pos

/-- Arithmétique : `p ≤ exp(a/T) ↔ T·log p ≤ a` pour `T > 0`, `p > 0`. -/
theorem nat_le_exp_div_iff {T a : ℝ} (hT : 0 < T) {p : ℕ} (hp : 0 < p) :
    (p : ℝ) ≤ Real.exp (a / T) ↔ T * Real.log p ≤ a := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [← Real.log_le_iff_le_exp hpR, le_div_iff₀ hT, mul_comm]

/-- **Lecture « atteint » aux coordonnées lues** (maître mathématique §5.c, §6) : pour
toute paire à deux lois, `p ≤ C⁺ = C_{k+m}` équivaut à `T·log p ≤ φ + (k + m)·π`,
avec `k = entryCoordinate` et `m = stageCount` lus sur la paire. -/
theorem reaches_iff_readCoordinates {z : TrueZero} (S : AnalyticContactPair z)
    {p : ℕ} (hp : 0 < p) :
    reaches S p ↔
      rZeroHeight z.1 * Real.log p ≤
        rTowerPhase z + ((S.entryCoordinate + S.stageCount : ℤ) : ℝ) * Real.pi := by
  unfold reaches
  rw [S.lastRayContact_eq_incidence]
  unfold rTowerIncidence rTowerLogIncidence rTowerHeight
  exact nat_le_exp_div_iff z.2 hp

/-- Forme « non atteint » : `C⁺ < p ↔ φ + (k + m)·π < T·log p`. -/
theorem not_reaches_iff_readCoordinates {z : TrueZero} (S : AnalyticContactPair z)
    {p : ℕ} (hp : 0 < p) :
    ¬ reaches S p ↔
      rTowerPhase z + ((S.entryCoordinate + S.stageCount : ℤ) : ℝ) * Real.pi <
        rZeroHeight z.1 * Real.log p := by
  rw [reaches_iff_readCoordinates S hp]
  exact not_le

/-- Spécialisation à l'occurrence (`Occ(w) > 0`). -/
theorem reaches_occurrence_iff_readCoordinates {w : TrueZero} (S : AnalyticContactPair w) :
    reaches S (occurrence w) ↔
      rZeroHeight w.1 * Real.log (occurrence w) ≤
        rTowerPhase w + ((S.entryCoordinate + S.stageCount : ℤ) : ℝ) * Real.pi :=
  reaches_iff_readCoordinates S (occurrence_pos w)

/-! ## 3. Un étage -/

/-- Raccord d'un étage (maître Lean §5.2, §22-B) : sous `stageCount = 1`, la paire est
la valeur des formules à sa coordonnée lue. -/
theorem AnalyticContactPair.eq_analyticPairAt_of_one_stage {z : TrueZero}
    (S : AnalyticContactPair z) (hOne : S.stageCount = 1) :
    S = analyticPairAt z S.entryCoordinate := by
  obtain ⟨hE, hL⟩ := S.contacts_of_one_stage hOne
  exact AnalyticContactPair.ext_contacts hE hL

end RHV6Fresh
