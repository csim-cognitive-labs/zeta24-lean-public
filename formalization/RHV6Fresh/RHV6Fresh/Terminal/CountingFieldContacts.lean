/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.BackgroundModulation
import RHV6Fresh.Terminal.DiagonalPassage

/-!
# Contacts du champ de comptage autour de `li` : restitution de `T`, de `β` et du facteur radial (auteur, 2026-10-12)

Représentation corrigée (E204) : la contribution de comptage d'un zéro, `b_ρ(x) = −2 Re Ei(ρ log x)` (branche de `Ei` le long de `ρ log x`,
jamais `li` de la puissance principale `x^ρ` ; correction du 2026-10-18), oscille autour du fond `F` (E332 : `F = li − log 2 + ∫_x^∞`,
courbe, non axe) ; ses extrema sont les points `D_k = exp((π/2 + kπ)/T)` (`modulationExtremum`, `backgroundRelativeModulation_extremum`),
les contacts de Tour sont `C_k = exp((arctan(T/β) + kπ)/T)`, et `C_k < D_k < C_{k+1}`.

Contenu (DÉMONTRÉ, axiomes standard ; toute position radiale) :
* les extrema du champ de comptage ne lisent que la hauteur : pas logarithmique `π/T`, `T` restitué par deux extrema
  consécutifs, deux zéros de même hauteur ont les mêmes extrema (aveugles à `β`) ;
* le décalage `δ_k = log D_k − log C_k` est indépendant de `k` et restitue `β = T·tan(T·δ_k)` ;
* le facteur radial est lu sur ce décalage : `log λ = δ_ligne − δ_k`, `δ_ligne = arctan(1/(2T))/T` ; `λ = 1 ⟺ δ_k = δ_ligne`
  (CARACTÉRISATION : lire le décalage ne le fixe pas) ; sous la ligne le décalage est strictement plus petit.

Non formalisé : la formule explicite de `J` (Riemann, `Σ_ρ Ei(ρ log x)` ; nommée sans preuve, `CountingExplicitFormula`,
`Terminal/CountingFieldArchitecture.lean`) et `Ei` (absente de Mathlib) ; les contacts de `F + b_ρ`
avec l'axe `li` (racines de `b_ρ`) ne sont lus que numériquement (E204).
-/

namespace RHV6Fresh

open RHV3Lean

/-- Pas logarithmique des extrema du champ de comptage : `log D_{k+1} − log D_k = π/T`. -/
theorem modulationExtremum_log_step (z : TrueZero) (k : ℤ) :
    Real.log (modulationExtremum z (k + 1)) - Real.log (modulationExtremum z k) =
      Real.pi / rZeroHeight z.1 := by
  have hT : rZeroHeight z.1 ≠ 0 := z.2.ne'
  unfold modulationExtremum
  rw [Real.log_exp, Real.log_exp]
  push_cast
  field_simp
  ring

/-- **`T` restitué par deux extrema consécutifs** (aucune lecture de `β`). -/
theorem height_of_consecutive_extrema (z : TrueZero) (k : ℤ) :
    rZeroHeight z.1 =
      Real.pi / (Real.log (modulationExtremum z (k + 1)) - Real.log (modulationExtremum z k)) := by
  rw [modulationExtremum_log_step]
  have hT : rZeroHeight z.1 ≠ 0 := z.2.ne'
  field_simp

/-- **Extrema aveugles à la position radiale** : deux zéros de même hauteur ont les mêmes extrema. -/
theorem modulationExtremum_eq_of_height {z w : TrueZero} (h : rZeroHeight z.1 = rZeroHeight w.1) (k : ℤ) :
    modulationExtremum z k = modulationExtremum w k := by
  unfold modulationExtremum; rw [h]

/-- **`β` restitué par le décalage extremum–contact** : `β = T·tan(T·(log D_k − log C_k))`, à tout étage `k`. -/
theorem radial_of_extremum_offset (z : TrueZero) (k : ℤ) :
    rZeroRadialPosition z.1 =
      rZeroHeight z.1 *
        Real.tan (rZeroHeight z.1 * (Real.log (modulationExtremum z k) - Real.log (contactMinusAt z k))) := by
  have hT : 0 < rZeroHeight z.1 := z.2
  rw [extremum_contact_offset, mul_div_cancel₀ _ hT.ne', Real.tan_arctan]
  field_simp

/-- Décalage de la Tour de ligne à la hauteur `T` : `arctan(1/(2T))/T`. -/
noncomputable def lineExtremumOffset (T : ℝ) : ℝ := Real.arctan (1 / (2 * T)) / T

/-- **Le facteur radial lu sur le champ de comptage** : `log λ = δ_ligne − (log D_k − log C_k)`, à tout étage. -/
theorem log_radialFactor_eq_offset (z : TrueZero) (k : ℤ) :
    Real.log (radialFactor z) =
      lineExtremumOffset (rZeroHeight z.1) -
        (Real.log (modulationExtremum z k) - Real.log (contactMinusAt z k)) := by
  have hT : 0 < rZeroHeight z.1 := z.2
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  rw [extremum_contact_offset]
  unfold radialFactor lineExtremumOffset linePhase
  rw [Real.log_exp, towerMotion_phase]
  have h1 : Real.arctan (rZeroHeight z.1 / rZeroRadialPosition z.1) =
      Real.pi / 2 - Real.arctan (rZeroRadialPosition z.1 / rZeroHeight z.1) := by
    rw [← Real.arctan_inv_of_pos (div_pos hβ hT), inv_div]
  have h2 : Real.arctan (rZeroHeight z.1 / (1 / 2)) = Real.pi / 2 - Real.arctan (1 / (2 * rZeroHeight z.1)) := by
    have hpos : 0 < 1 / (2 * rZeroHeight z.1) := by positivity
    rw [← Real.arctan_inv_of_pos hpos]
    congr 1; field_simp
  rw [h1, h2]
  field_simp
  ring

/-- **Caractérisation** : `λ = 1 ⟺` le décalage du champ de comptage est celui de la ligne (lire ne fixe pas). -/
theorem radialFactor_eq_one_iff_offset (z : TrueZero) (k : ℤ) :
    radialFactor z = 1 ↔
      Real.log (modulationExtremum z k) - Real.log (contactMinusAt z k) = lineExtremumOffset (rZeroHeight z.1) := by
  constructor
  · intro h
    have := log_radialFactor_eq_offset z k
    rw [h, Real.log_one] at this; linarith
  · intro h
    have := log_radialFactor_eq_offset z k
    rw [h, sub_self] at this
    have hpos := radialFactor_pos z
    calc radialFactor z = Real.exp (Real.log (radialFactor z)) := (Real.exp_log hpos).symm
      _ = 1 := by rw [this, Real.exp_zero]

/-- Sous la ligne, le décalage est strictement plus petit que celui de la ligne. -/
theorem offset_lt_line_of_low (z : TrueZero) (hlow : rZeroRadialPosition z.1 < 1 / 2) (k : ℤ) :
    Real.log (modulationExtremum z k) - Real.log (contactMinusAt z k) < lineExtremumOffset (rZeroHeight z.1) := by
  have h := log_radialFactor_eq_offset z k
  have hpos : 0 < Real.log (radialFactor z) := Real.log_pos ((radialFactor_gt_one_iff z).mpr hlow)
  linarith

/-- **Lecture du champ de comptage à l'arrivée d'un passage** : extrema = ceux de toute Tour de même hauteur (aveugles),
hauteur restituée, `β` restitué, `log λ` lu sur le décalage, `λ = 1 ⟺` décalage de ligne. Toute position radiale. -/
theorem counting_field_reading (z : TrueZero) (k : ℤ) :
    rZeroHeight z.1 =
        Real.pi / (Real.log (modulationExtremum z (k + 1)) - Real.log (modulationExtremum z k)) ∧
      rZeroRadialPosition z.1 =
        rZeroHeight z.1 *
          Real.tan (rZeroHeight z.1 * (Real.log (modulationExtremum z k) - Real.log (contactMinusAt z k))) ∧
      Real.log (radialFactor z) =
        lineExtremumOffset (rZeroHeight z.1) -
          (Real.log (modulationExtremum z k) - Real.log (contactMinusAt z k)) ∧
      (radialFactor z = 1 ↔
        Real.log (modulationExtremum z k) - Real.log (contactMinusAt z k) = lineExtremumOffset (rZeroHeight z.1)) :=
  ⟨height_of_consecutive_extrema z k, radial_of_extremum_offset z k, log_radialFactor_eq_offset z k,
    radialFactor_eq_one_iff_offset z k⟩

#print axioms counting_field_reading
#print axioms offset_lt_line_of_low

end RHV6Fresh
