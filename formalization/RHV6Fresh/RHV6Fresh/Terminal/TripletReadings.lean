/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.HorizontalExclusion
import RHV6Fresh.Terminal.GeneratedFrequency

/-!
# Trois lectures, deux inconnues (module isolé, non importé par la chaîne)

Lecture de l'amplitude d'un terme conjoint sur deux positions, et réduction vers la ligne critique
avec prémisse nommée. Aucun axiome, aucun `sorry`.
-/

namespace RHV6Fresh

open Complex RHV3Lean

/-- Le module du terme conjoint : `|m| · |x^β / N|`. -/
theorem jointTerm_norm (m β T θ N x : ℝ) :
    ‖jointTerm m β T θ N x‖ = |m| * |x ^ β / N| := by
  unfold jointTerm
  simp only [norm_neg, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs,
    mul_one]

/-- **Lecture de l'amplitude sur deux positions** : rapport des modules `= (x₂/x₁)^β`. -/
theorem jointTerm_norm_ratio {m β T θ N x₁ x₂ : ℝ} (hm : m ≠ 0) (hN : N ≠ 0)
    (h₁ : 0 < x₁) (h₂ : 0 < x₂) :
    ‖jointTerm m β T θ N x₂‖ / ‖jointTerm m β T θ N x₁‖ = (x₂ / x₁) ^ β := by
  rw [jointTerm_norm, jointTerm_norm, Real.div_rpow h₂.le h₁.le]
  have a1 : 0 < x₁ ^ β := Real.rpow_pos_of_pos h₁ β
  have a2 : 0 < x₂ ^ β := Real.rpow_pos_of_pos h₂ β
  have hm' : 0 < |m| := abs_pos.mpr hm
  have hN' : 0 < |N| := abs_pos.mpr hN
  rw [abs_div, abs_div, abs_of_pos a1, abs_of_pos a2]
  field_simp

/-- **L'exposant d'amplitude se lit sur le rapport** : deux exposants donnant le même rapport
sur deux positions distinctes (`x₂ > x₁ > 0`) sont égaux. -/
theorem amplitude_exponent_determined {β β' x₁ x₂ : ℝ} (h₁ : 0 < x₁) (h : x₁ < x₂)
    (heq : (x₂ / x₁) ^ β = (x₂ / x₁) ^ β') : β = β' := by
  have hq : 1 < x₂ / x₁ := (one_lt_div h₁).mpr h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact absurd heq (ne_of_lt ((Real.rpow_lt_rpow_left_iff hq).mpr hlt))
  · exact absurd heq (ne_of_gt ((Real.rpow_lt_rpow_left_iff hq).mpr hgt))

/-- Prémisse nommée (seconde obligation) : l'amplitude imposée par les écarts à un vrai zéro est celle
de son symétrique, au rapport `q`. -/
def AmplitudeImposedByGaps (z : TrueZero) (q : ℝ) : Prop :=
  q ^ rZeroRadialPosition z.1 = q ^ (1 - rZeroRadialPosition z.1)

/-- **Réduction** : amplitude imposée par les écarts (prémisse nommée, de force RH) ⟺ ligne critique. -/
theorem amplitudeImposed_iff_onLine {z : TrueZero} {q : ℝ} (hq : 1 < q) :
    AmplitudeImposedByGaps z q ↔ rZeroRadialPosition z.1 = 1 / 2 :=
  amplitude_exponents_eq_iff_onLine hq

/-- Hors ligne, l'amplitude imposée par les écarts est incompatible avec celle du terme (conditionnel). -/
theorem off_triplet_incompatible {z : TrueZero} {q : ℝ} (hq : 1 < q)
    (hOff : rZeroRadialPosition z.1 ≠ 1 / 2) : ¬ AmplitudeImposedByGaps z q :=
  fun h => hOff ((amplitudeImposed_iff_onLine hq).mp h)

end RHV6Fresh

#print axioms RHV6Fresh.off_triplet_incompatible
#print axioms RHV6Fresh.jointTerm_norm_ratio
