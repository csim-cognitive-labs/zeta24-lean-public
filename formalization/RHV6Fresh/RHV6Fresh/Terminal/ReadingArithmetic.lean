/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Direct.PairTowers
import RHV6Fresh.Terminal.Universalization

/-!
# RHV6Fresh — contenu arithmétique exact de la lecture de la seconde Tour (destruction de V, 2026-09-26)

Code d'abord (auteur, 2026-09-25) : ce fichier ne pose rien, il déplie ce que le code compilé dit
déjà.  La règle du pivot est `pivotCoordinate z q = ⌈(T log q − φ)/π⌉ − 1` ; la différence de deux
positions est `T·log(q₂/q₁)/π` (`towerPosition_sub`).  La lecture C_lecture de la seconde Tour
(`secondTower_reads_occurrence_iff_coordinate_lt`) est donc une inégalité entre `π/T` et un écart
logarithmique de premiers consécutifs de la grammaire première : elle est acquise dès que
`π ≤ T·log(p_min(z*)/Occ(z*))` (`secondTower_reads_of_gap_ge_pi`).

Les anneaux du miroir sont ceux du membre décalés de moins d'un demi-anneau
(`mirror_phase_lt`, `pivotCoordinate_mirror_mem`) : la géométrie du miroir ne déplace une référence
que d'au plus une coordonnée, elle n'impose aucune position.

**Destruction (auteur, 2026-09-26)** : la notion « V » et tout ce qui la confrontait à une référence
d'un autre zéro (`secondTower_verification_imp_gap_lt_pi`, `pair_collision_is_sameRing_and_not_of_consecutive`,
`secondTower_readings_iff_noLowerSide`, `riemannHypothesis_iff_secondTower_readings`, qui dépendaient
tous de `pair_constats_exclusive`/`pair_towers_false`, supprimés) sont retirés. La cible de fermeture
reste `riemannHypothesis_iff_noLowerSide` (§4) : aucun zéro de côté `β < 1/2` ⟺ RH, sans passer par
une notion de « V ».
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. La position dans la Tour est linéaire en logarithme -/

theorem towerPosition_sub (z : TrueZero) {q₁ q₂ : ℝ} (h₁ : 0 < q₁) (h₂ : 0 < q₂) :
    towerPosition z q₂ - towerPosition z q₁ =
      rZeroHeight z.1 * Real.log (q₂ / q₁) / Real.pi := by
  unfold towerPosition
  rw [Real.log_div (ne_of_gt h₂) (ne_of_gt h₁)]
  ring

/-- Deux références dans le même anneau : leur écart logarithmique est sous le pas `π/T`. -/
theorem sameRing_imp_gap_lt_pi (z : TrueZero) {q₁ q₂ : ℝ} (h₁ : 0 < q₁) (h₂ : q₁ ≤ q₂)
    (hk : pivotCoordinate z q₁ = pivotCoordinate z q₂) :
    rZeroHeight z.1 * Real.log (q₂ / q₁) < Real.pi := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have h₂' : 0 < q₂ := lt_of_lt_of_le h₁ h₂
  unfold pivotCoordinate at hk
  have hc : ⌈towerPosition z q₁⌉ = ⌈towerPosition z q₂⌉ := by omega
  have hx : towerPosition z q₂ - towerPosition z q₁ < 1 := by
    have a := Int.le_ceil (towerPosition z q₂)
    have b := Int.ceil_lt_add_one (towerPosition z q₁)
    rw [← hc] at a
    linarith
  rw [towerPosition_sub z h₁ h₂', div_lt_one hπ] at hx
  exact hx

/-- Un pas `π/T` entier entre deux références : la première est dans un anneau strictement
inférieur. -/
theorem coordinate_lt_of_gap_ge_pi (z : TrueZero) {q₁ q₂ : ℝ} (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hgap : Real.pi ≤ rZeroHeight z.1 * Real.log (q₂ / q₁)) :
    pivotCoordinate z q₁ < pivotCoordinate z q₂ := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hx : 1 ≤ towerPosition z q₂ - towerPosition z q₁ := by
    rw [towerPosition_sub z h₁ h₂]
    exact (le_div_iff₀ hπ).mpr (by linarith)
  have hc : ⌈towerPosition z q₁⌉ + 1 ≤ ⌈towerPosition z q₂⌉ := by
    have := Int.ceil_mono (show towerPosition z q₁ + 1 ≤ towerPosition z q₂ by linarith)
    rwa [Int.ceil_add_one] at this
  unfold pivotCoordinate
  omega

/-! ## 2. Les deux lectures de la seconde Tour, en écarts de premiers -/

/-- Un pas entier `π/T` de la Tour du miroir entre `Occ(z*)` et `p_min(z*)` suffit à L. -/
theorem secondTower_reads_of_gap_ge_pi (z : TrueZero)
    (hgap : Real.pi ≤ rZeroHeight z.1 *
      Real.log ((expectedMinimumPrime (mirrorMember z) : ℝ) /
        (occurrence (mirrorMember z) : ℝ))) :
    (secondTowerOf z).properState.reaches (occurrence (mirrorMember z)) := by
  rw [secondTower_reads_occurrence_iff_coordinate_lt]
  have h₁ : (0 : ℝ) < (occurrence (mirrorMember z) : ℝ) := by
    exact_mod_cast (occurrence_prime (mirrorMember z)).pos
  have h₂ : (0 : ℝ) < (expectedMinimumPrime (mirrorMember z) : ℝ) := by
    exact_mod_cast expectedMinimumPrime_pos (mirrorMember z)
  rw [← mirrorMember_ordinate z] at hgap
  exact coordinate_lt_of_gap_ge_pi (mirrorMember z) h₁ h₂ hgap

/-! ## 3. Les anneaux du miroir : ceux du membre, décalés de moins d'un demi-anneau -/

theorem mirror_phase_lt {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2) :
    (towerMotionOf (mirrorMember z)).phase < (towerMotionOf z).phase := by
  have hβ0 : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hT : 0 < rZeroHeight z.1 := z.2
  change rTowerPhase (mirrorMember z) < rTowerPhase z
  unfold rTowerPhase rTowerHeight rTowerRadialPosition
  rw [mirrorMember_ordinate, mirrorMember_radial]
  apply Real.arctan_strictMono
  exact div_lt_div_of_pos_left hT hβ0 (by linarith)

theorem towerPosition_mirror_sub (z : TrueZero) (q : ℝ) :
    towerPosition (mirrorMember z) q - towerPosition z q =
      ((towerMotionOf z).phase - (towerMotionOf (mirrorMember z)).phase) / Real.pi := by
  unfold towerPosition
  rw [mirrorMember_ordinate]
  ring

/-- Pour toute référence `q`, la coordonnée du miroir est celle du membre ou la suivante : le
recul du miroir ne déplace une référence que d'au plus un anneau et n'impose aucune position. -/
theorem pivotCoordinate_mirror_mem {z : TrueZero} (hβ : rZeroRadialPosition z.1 < 1 / 2)
    (q : ℝ) :
    pivotCoordinate (mirrorMember z) q = pivotCoordinate z q ∨
      pivotCoordinate (mirrorMember z) q = pivotCoordinate z q + 1 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hlt := mirror_phase_lt hβ
  have hz := towerMotion_phase_lt_pi_div_two z
  have hw := towerMotion_phase_pos (mirrorMember z)
  have hδ0 : 0 < towerPosition (mirrorMember z) q - towerPosition z q := by
    rw [towerPosition_mirror_sub]
    exact div_pos (by linarith) hπ
  have hδ1 : towerPosition (mirrorMember z) q - towerPosition z q < 1 := by
    rw [towerPosition_mirror_sub, div_lt_one hπ]
    linarith
  have a : ⌈towerPosition z q⌉ ≤ ⌈towerPosition (mirrorMember z) q⌉ :=
    Int.ceil_mono (by linarith)
  have b : ⌈towerPosition (mirrorMember z) q⌉ ≤ ⌈towerPosition z q⌉ + 1 := by
    have := Int.ceil_mono
      (show towerPosition (mirrorMember z) q ≤ towerPosition z q + 1 by linarith)
    rwa [Int.ceil_add_one] at this
  unfold pivotCoordinate
  omega

/-! ## 4. La prémisse de la cible de fermeture est l'hypothèse de Riemann -/

theorem riemannHypothesis_iff_noLowerSide :
    RiemannHypothesis ↔ ∀ z : TrueZero, ¬ rZeroRadialPosition z.1 < 1 / 2 :=
  ⟨fun hRH z hβ =>
      absurd (thm_zeroRadialPosition_half_of_riemannHypothesis hRH z.1) (ne_of_lt hβ),
    riemannHypothesis_of_noLowerSide⟩

end RHV6Fresh
