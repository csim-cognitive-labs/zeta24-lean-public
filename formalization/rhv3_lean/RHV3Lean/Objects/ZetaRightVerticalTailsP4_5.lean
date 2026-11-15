/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaPerronFiniteRectangle

/-!
# P4.5 right vertical tails
-/

open Complex Set Filter MeasureTheory
open scoped Topology Interval

noncomputable section

namespace RHV3Lean

theorem right_vertical_lower_tail_tendsto_zero
    {x σR : ℝ}
    (hx : 1 < x)
    (hσR : 1 < σR) :
    Tendsto
      (fun T : ℝ =>
        rightVerticalLowerTail'
          (zetaPerronIntegrand x)
          σR
          T)
      atTop
      (𝓝 0) := by
  let f : ℝ → ℂ := fun t => zetaPerronIntegrand x (σR + t * I)
  have hf_int : Integrable f :=
    integrable_zetaPerronIntegrand_vertical (x := x) (σR := σR) hx hσR
  have hf_left : IntegrableOn f (Iic (0 : ℝ)) := hf_int.integrableOn
  have hneg : Tendsto (fun T : ℝ => -T) atTop atBot :=
    tendsto_neg_atTop_atBot
  have htail :
      Tendsto
        (fun T : ℝ => ∫ t in Iic (-T), f t)
        atTop
        (𝓝 0) :=
    MeasureTheory.tendsto_integral_Iic_zero (f := f) (μ := volume) hneg
  have _ : ∃ b : ℝ, IntegrableOn f (Iic b) := ⟨0, hf_left⟩
  simpa [rightVerticalLowerTail', f] using
    (htail.const_smul I).const_smul (1 / (2 * Real.pi * I) : ℂ)

theorem right_vertical_upper_tail_tendsto_zero
    {x σR : ℝ}
    (hx : 1 < x)
    (hσR : 1 < σR) :
    Tendsto
      (fun T : ℝ =>
        rightVerticalUpperTail'
          (zetaPerronIntegrand x)
          σR
          T)
      atTop
      (𝓝 0) := by
  let f : ℝ → ℂ := fun t => zetaPerronIntegrand x (σR + t * I)
  have hf_int : Integrable f :=
    integrable_zetaPerronIntegrand_vertical (x := x) (σR := σR) hx hσR
  have hf_right : IntegrableOn f (Ici (0 : ℝ)) := hf_int.integrableOn
  have htail :
      Tendsto
        (fun T : ℝ => ∫ t in Ici T, f t)
        atTop
        (𝓝 0) :=
    MeasureTheory.tendsto_integral_Ici_zero (f := f) (μ := volume) tendsto_id
  have _ : ∃ b : ℝ, IntegrableOn f (Ici b) := ⟨0, hf_right⟩
  simpa [rightVerticalUpperTail', f] using
    (htail.const_smul I).const_smul (1 / (2 * Real.pi * I) : ℂ)

theorem right_vertical_split_zetaPerron
    {x σR T : ℝ}
    (hx : 1 < x)
    (hσR : 1 < σR) :
    VerticalIntegral' (zetaPerronIntegrand x) σR =
      rightVerticalLowerTail' (zetaPerronIntegrand x) σR T +
        VIntegral' (zetaPerronIntegrand x) σR (-T) T +
        rightVerticalUpperTail' (zetaPerronIntegrand x) σR T :=
  verticalIntegral'_split_right_line
    (zetaPerronIntegrand x)
    σR
    T
    (integrable_zetaPerronIntegrand_vertical (x := x) (σR := σR) hx hσR)

theorem right_vertical_tails_tendsto_zero
    {x σR : ℝ}
    (hx : 1 < x)
    (hσR : 1 < σR) :
    Tendsto
      (fun T : ℝ =>
        rightVerticalLowerTail'
          (zetaPerronIntegrand x)
          σR
          T)
      atTop
      (𝓝 0) ∧
    Tendsto
      (fun T : ℝ =>
        rightVerticalUpperTail'
          (zetaPerronIntegrand x)
          σR
          T)
      atTop
      (𝓝 0) :=
  ⟨right_vertical_lower_tail_tendsto_zero hx hσR,
    right_vertical_upper_tail_tendsto_zero hx hσR⟩

end RHV3Lean
