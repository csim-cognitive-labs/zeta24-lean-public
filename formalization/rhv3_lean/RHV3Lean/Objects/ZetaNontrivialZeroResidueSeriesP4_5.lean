/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaTrivialZeroResidueSeriesP4_5
import RHV3Lean.Objects.ZetaZeroHeightPerronBridge

/-!
# P4.5 non-trivial zero residue series
-/

open Complex Set Filter Finset BigOperators
open scoped Topology

noncomputable section

namespace RHV3Lean

noncomputable def nontrivialZeroResidueTerm
    (x : ℝ)
    (ρ : {ρ : ℂ // IsNontrivialZetaZero ρ}) :
    ℂ :=
  -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
    Perron.f x (ρ : ℂ)

private theorem finite_small_nontrivial_zeros :
    ({ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} |
      |(ρ : ℂ).im| < 1} : Set {ρ : ℂ // IsNontrivialZetaZero ρ}).Finite := by
  have hfin : (nontrivialZetaZerosByHeight 1).Finite :=
    nontrivialZetaZerosByHeight_finite 1
  refine Set.Finite.of_finite_image ?_ (Set.injOn_of_injective Subtype.coe_injective)
  refine hfin.subset ?_
  intro z hz
  rcases hz with ⟨ρ, hρ, rfl⟩
  exact ⟨ρ.property, hρ⟩

private theorem norm_perron_f_nontrivial_le_imag_square
    {x : ℝ}
    (hx : 1 < x)
    (ρ : {ρ : ℂ // IsNontrivialZetaZero ρ})
    (hlarge : 1 ≤ |(ρ : ℂ).im|) :
    ‖Perron.f x (ρ : ℂ)‖ ≤
      x * |(ρ : ℂ).im|⁻¹ ^ (2 : ℕ) := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hstrip := isNontrivialZetaZero_re_mem_Ioo ρ.property
  have hpow_le : x ^ (ρ : ℂ).re ≤ x := by
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    have hre_le : (ρ : ℂ).re ≤ 1 := le_of_lt hstrip.2
    simpa [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx1 hre_le
  have him_pos : 0 < |(ρ : ℂ).im| := lt_of_lt_of_le zero_lt_one hlarge
  have hρ_inv :
      ‖(ρ : ℂ)‖⁻¹ ≤ |(ρ : ℂ).im|⁻¹ :=
    inv_anti₀ him_pos (Complex.abs_im_le_norm (ρ : ℂ))
  have hρ1_inv :
      ‖(ρ : ℂ) + 1‖⁻¹ ≤ |(ρ : ℂ).im|⁻¹ := by
    have him_le : |(ρ : ℂ).im| ≤ ‖(ρ : ℂ) + 1‖ := by
      simpa [Complex.add_im] using Complex.abs_im_le_norm ((ρ : ℂ) + 1)
    exact inv_anti₀ him_pos him_le
  have hden_inv :
      (‖(ρ : ℂ)‖ * ‖(ρ : ℂ) + 1‖)⁻¹ ≤
        |(ρ : ℂ).im|⁻¹ ^ (2 : ℕ) := by
    rw [mul_inv_rev, pow_two]
    exact mul_le_mul hρ1_inv hρ_inv
      (inv_nonneg.mpr (norm_nonneg _)) (inv_nonneg.mpr (abs_nonneg _))
  rw [Perron.f, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  calc
    x ^ (ρ : ℂ).re / (‖(ρ : ℂ)‖ * ‖(ρ : ℂ) + 1‖)
        = x ^ (ρ : ℂ).re * (‖(ρ : ℂ)‖ * ‖(ρ : ℂ) + 1‖)⁻¹ := by
          rw [div_eq_mul_inv]
    _ ≤ x * |(ρ : ℂ).im|⁻¹ ^ (2 : ℕ) :=
      mul_le_mul hpow_le hden_inv
        (inv_nonneg.mpr (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
        (le_of_lt hxpos)

private theorem norm_nontrivialZeroResidueTerm_le_weighted
    {x : ℝ}
    (hx : 1 < x)
    (ρ : {ρ : ℂ // IsNontrivialZetaZero ρ})
    (hlarge : 1 ≤ |(ρ : ℂ).im|) :
    ‖nontrivialZeroResidueTerm x ρ‖ ≤
      x *
        ((zetaZeroMultiplicity (ρ : ℂ) : ℝ) *
          |(ρ : ℂ).im|⁻¹ ^ (2 : ℕ)) := by
  have hm_nonneg : 0 ≤ (zetaZeroMultiplicity (ρ : ℂ) : ℝ) := by positivity
  change ‖(-(zetaZeroMultiplicity (ρ : ℂ) : ℂ)) * Perron.f x (ρ : ℂ)‖ ≤
    x *
      ((zetaZeroMultiplicity (ρ : ℂ) : ℝ) *
        |(ρ : ℂ).im|⁻¹ ^ (2 : ℕ))
  rw [norm_mul, norm_neg, Complex.norm_natCast]
  have hperron := norm_perron_f_nontrivial_le_imag_square hx ρ hlarge
  calc
    (zetaZeroMultiplicity (ρ : ℂ) : ℝ) * ‖Perron.f x (ρ : ℂ)‖
        ≤ (zetaZeroMultiplicity (ρ : ℂ) : ℝ) *
            (x * |(ρ : ℂ).im|⁻¹ ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hperron hm_nonneg
    _ = x *
        ((zetaZeroMultiplicity (ρ : ℂ) : ℝ) *
          |(ρ : ℂ).im|⁻¹ ^ (2 : ℕ)) := by ring

theorem nontrivial_zero_residue_series_summable
    {x : ℝ}
    (hx : 1 < x) :
    Summable
      (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
        nontrivialZeroResidueTerm x ρ) := by
  have hweighted :=
    (weighted_zetaZeroMultiplicity_imagSquare_summable).mul_left x
  refine Summable.of_norm_bounded_eventually hweighted ?_
  rw [Filter.eventually_cofinite]
  refine finite_small_nontrivial_zeros.subset ?_
  intro ρ hbad
  rw [Set.mem_setOf_eq] at hbad ⊢
  by_contra hsmall
  have hlarge : 1 ≤ |(ρ : ℂ).im| := le_of_not_gt hsmall
  have hle := norm_nontrivialZeroResidueTerm_le_weighted hx ρ hlarge
  have htarget_nonneg :
      0 ≤ x *
        ((zetaZeroMultiplicity (ρ : ℂ) : ℝ) *
          |(ρ : ℂ).im|⁻¹ ^ (2 : ℕ)) := by positivity
  exact hbad (by
    simpa [Real.norm_eq_abs, abs_of_nonneg htarget_nonneg] using hle)

theorem nontrivial_zero_height_finset_bridge
    {x σR T : ℝ}
    {N : ℕ}
    (h : PerronRectangleAdmissible x σR N T) :
    sumResiduesIn (zetaPerronIntegrand x)
        (zetaPerronNontrivialZeroSet σR N T) =
      ∑ ρ ∈ nontrivialZetaZerosByHeightFinset T,
        -(zetaZeroMultiplicity ρ : ℂ) * Perron.f x ρ :=
  zetaPerron_nontrivial_zero_residue_sum_eq_byHeight h

/-- Alias canonique, indexé par le sous-type des zéros non triviaux, du finset des zéros de
hauteur `< T`. Point d'entrée canonique pour tout objet indexé par le sous-type. -/
noncomputable def nontrivialZetaZerosByHeightSubtypeFinset
    (T : ℝ) :
    Finset {ρ : ℂ // IsNontrivialZetaZero ρ} :=
  Finset.map
    ⟨fun ρ : {ρ : ℂ // ρ ∈ nontrivialZetaZerosByHeightFinset T} =>
      ⟨(ρ : ℂ),
        ((mem_nontrivialZetaZerosByHeightFinset (T := T) (ρ := (ρ : ℂ))).1
          ρ.property).1⟩,
      by
        intro a b hab
        have hval :
            (a : ℂ) = (b : ℂ) :=
          congrArg (fun z : {ρ : ℂ // IsNontrivialZetaZero ρ} => (z : ℂ)) hab
        exact Subtype.ext hval⟩
    (nontrivialZetaZerosByHeightFinset T).attach

/-- Caractérisation d'appartenance de l'alias canonique indexé par le sous-type : identique à
`mem_nontrivialZetaZerosByHeightFinset`, ne retenant que la condition de hauteur. -/
theorem mem_nontrivialZetaZerosByHeightSubtypeFinset
    {T : ℝ}
    {ρ : {ρ : ℂ // IsNontrivialZetaZero ρ}} :
    ρ ∈ nontrivialZetaZerosByHeightSubtypeFinset T ↔
      |(ρ : ℂ).im| < T := by
  classical
  constructor
  · intro hρ
    rw [nontrivialZetaZerosByHeightSubtypeFinset, Finset.mem_map] at hρ
    rcases hρ with ⟨z, hz, hzeq⟩
    have hval : (z : ℂ) = (ρ : ℂ) :=
      congrArg (fun w : {ρ : ℂ // IsNontrivialZetaZero ρ} => (w : ℂ)) hzeq
    have hzmem :=
      (mem_nontrivialZetaZerosByHeightFinset (T := T) (ρ := (z : ℂ))).1 z.property
    simpa [← hval] using hzmem.2
  · intro hρ
    rw [nontrivialZetaZerosByHeightSubtypeFinset, Finset.mem_map]
    refine ⟨⟨(ρ : ℂ), ?_⟩, ?_, ?_⟩
    · rw [mem_nontrivialZetaZerosByHeightFinset]
      exact ⟨ρ.property, hρ⟩
    · simp
    · ext
      rfl

/-- L'alias canonique indexé par le sous-type diverge vers `atTop` avec la hauteur `T`. -/
theorem tendsto_nontrivial_height_subtype_finset_atTop :
    Tendsto nontrivialZetaZerosByHeightSubtypeFinset atTop atTop := by
  rw [tendsto_atTop]
  intro S
  let B : ℝ := ∑ ρ ∈ S, (|(ρ : ℂ).im| + 1)
  filter_upwards [eventually_gt_atTop B] with T hT
  intro ρ hρS
  rw [mem_nontrivialZetaZerosByHeightSubtypeFinset]
  have hterm_le : |(ρ : ℂ).im| + 1 ≤ B := by
    simpa [B] using Finset.single_le_sum
      (s := S)
      (f := fun η : {ρ : ℂ // IsNontrivialZetaZero ρ} => |(η : ℂ).im| + 1)
      (fun η _ ↦ by positivity)
      hρS
  linarith

/-- La somme complexe canonique sur `nontrivialZetaZerosByHeightFinset` coïncide exactement
avec la somme du terme individuel sur l'alias indexé par le sous-type. -/
theorem nontrivial_height_complex_sum_eq_subtype_sum
    (x T : ℝ) :
    (∑ ρ ∈ nontrivialZetaZerosByHeightFinset T,
      -(zetaZeroMultiplicity ρ : ℂ) * Perron.f x ρ)
      =
    ∑ ρ ∈ nontrivialZetaZerosByHeightSubtypeFinset T,
      nontrivialZeroResidueTerm x ρ := by
  classical
  rw [nontrivialZetaZerosByHeightSubtypeFinset, Finset.sum_map]
  unfold nontrivialZeroResidueTerm
  exact (Finset.sum_attach
      (s := nontrivialZetaZerosByHeightFinset T)
      (f := fun ρ : ℂ =>
        -(zetaZeroMultiplicity ρ : ℂ) * Perron.f x ρ)).symm

theorem nontrivial_zero_residue_series_symmetric_convergent
    {x : ℝ}
    (hx : 1 < x) :
    Tendsto
      (fun T : ℝ =>
        ∑ ρ ∈ nontrivialZetaZerosByHeightFinset T,
          -(zetaZeroMultiplicity ρ : ℂ) *
            Perron.f x ρ)
      atTop
      (𝓝
        (∑' ρ : {ρ : ℂ // IsNontrivialZetaZero ρ},
          nontrivialZeroResidueTerm x ρ)) := by
  have hsum := nontrivial_zero_residue_series_summable hx
  have hnet :
      Tendsto
        (fun S : Finset {ρ : ℂ // IsNontrivialZetaZero ρ} =>
          ∑ ρ ∈ S, nontrivialZeroResidueTerm x ρ)
        atTop
        (𝓝
          (∑' ρ : {ρ : ℂ // IsNontrivialZetaZero ρ},
            nontrivialZeroResidueTerm x ρ)) :=
    hsum.hasSum
  have hsub := hnet.comp tendsto_nontrivial_height_subtype_finset_atTop
  refine hsub.congr' ?_
  filter_upwards with T
  exact (nontrivial_height_complex_sum_eq_subtype_sum x T).symm

end RHV3Lean
