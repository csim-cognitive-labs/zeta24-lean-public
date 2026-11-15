/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaZeroHeightSummability

/-!
# P4.2: bridge between P3c3 finite Perron zeros and canonical height truncation
-/

open Set Filter Finset BigOperators Complex
open scoped Topology ComplexConjugate

namespace RHV3Lean

private theorem zetaPerronIntegrand_pole_at_nontrivial_zero
    {x : ℝ} (xpos : 0 < x) {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) :
    meromorphicOrderAt (zetaPerronIntegrand x) ρ < 0 := by
  have hL := meromorphicAt_neg_logDeriv_riemannZeta ρ
  have hK := meromorphicAt_perronKernel (x := x) xpos ρ
  have hprod : meromorphicOrderAt (zetaPerronIntegrand x) ρ =
      meromorphicOrderAt (fun s ↦ -logDeriv riemannZeta s) ρ +
        meromorphicOrderAt (Perron.f x) ρ := by
    have h := meromorphicOrderAt_mul (f := fun s ↦ -logDeriv riemannZeta s)
      (g := Perron.f x) hL hK
    have hfun : ((fun s ↦ -logDeriv riemannZeta s) * Perron.f x)
        = zetaPerronIntegrand x := rfl
    rw [← hfun]
    exact h
  have hK_ana : AnalyticAt ℂ (Perron.f x) ρ :=
    analyticAt_perronKernel xpos (isNontrivialZetaZero_ne_zero hρ)
      (isNontrivialZetaZero_ne_negOne hρ)
  have hK_ord : meromorphicOrderAt (Perron.f x) ρ = (0 : WithTop ℤ) := by
    rw [hK_ana.meromorphicOrderAt_eq,
      hK_ana.analyticOrderAt_eq_zero.mpr
        (perronKernel_ne_zero xpos (isNontrivialZetaZero_ne_zero hρ)
          (isNontrivialZetaZero_ne_negOne hρ))]
    simp
  rw [hprod, meromorphicOrderAt_neg_logDeriv_riemannZeta_zero hρ.1, hK_ord]
  exact_mod_cast (by norm_num : (-1 : ℤ) < 0)

private lemma zetaPerron_border_of_rect_abs_im_eq
    {x σR T : ℝ} {N : ℕ} (h : PerronRectangleAdmissible x σR N T)
    {ρ : ℂ}
    (hrect : ρ ∈ Rectangle (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T))
    (him : |ρ.im| = T) :
    ρ ∈ RectangleBorder (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) := by
  have hTnonneg : 0 ≤ T := le_of_lt h.T_pos
  have him_cases : ρ.im = T ∨ ρ.im = -T := by
    by_cases hnonneg : 0 ≤ ρ.im
    · left
      simpa [abs_of_nonneg hnonneg] using him
    · right
      have hneg : ρ.im < 0 := lt_of_not_ge hnonneg
      have hneg_eq : -ρ.im = T := by
        simpa [abs_of_neg hneg] using him
      linarith
  simp [Rectangle, perronRectangleLowerLeft, perronRectangleUpperRight,
    perronRectangleSigmaL] at hrect
  rcases hrect with ⟨hre, himrect⟩
  rw [RectangleBorder]
  rcases him_cases with himtop | himbot
  · left; right
    exact ⟨by
      simpa [perronRectangleLowerLeft, perronRectangleUpperRight, perronRectangleSigmaL]
        using hre, by simp [perronRectangleUpperRight, himtop]⟩
  · left; left; left
    exact ⟨by
      simpa [perronRectangleLowerLeft, perronRectangleUpperRight, perronRectangleSigmaL]
        using hre, by simp [perronRectangleLowerLeft, himbot]⟩

private lemma abs_im_lt_of_zetaPerron_nontrivial_mem
    {x σR T : ℝ} {N : ℕ}
    (h : PerronRectangleAdmissible x σR N T)
    {ρ : ℂ}
    (hρ : ρ ∈ zetaPerronNontrivialZeroSet σR N T) :
    |ρ.im| < T := by
  have hrect := hρ.1
  have hnon := hρ.2
  simp [Rectangle, perronRectangleLowerLeft, perronRectangleUpperRight] at hrect
  have him_le : |ρ.im| ≤ T := by
    rcases hrect with ⟨_, himrect⟩
    rw [Set.uIcc_of_le (by linarith [h.T_pos])] at himrect
    exact abs_le.mpr himrect
  rcases lt_or_eq_of_le him_le with hlt | heq
  · exact hlt
  · have hborder := zetaPerron_border_of_rect_abs_im_eq h hρ.1 heq
    have hpole : ρ ∈ {s | meromorphicOrderAt (zetaPerronIntegrand x) s < 0} :=
      zetaPerronIntegrand_pole_at_nontrivial_zero (lt_trans zero_lt_one h.x_gt) hnon
    have hdis := Set.disjoint_left.mp h.no_poles_on_boundary hborder hpole
    exact False.elim hdis

theorem zetaPerronNontrivialZeroSet_eq_byHeight
    {x σR T : ℝ} {N : ℕ}
    (h : RHV3Lean.PerronRectangleAdmissible x σR N T) :
    RHV3Lean.zetaPerronNontrivialZeroSet σR N T =
      nontrivialZetaZerosByHeight T := by
  ext ρ
  constructor
  · intro hρ
    exact ⟨hρ.2, abs_im_lt_of_zetaPerron_nontrivial_mem h hρ⟩
  · intro hρ
    refine ⟨?_, hρ.1⟩
    rw [nontrivialZetaZerosByHeight] at hρ
    change IsNontrivialZetaZero ρ ∧ |ρ.im| < T at hρ
    have hstrip := isNontrivialZetaZero_re_mem_Ioo hρ.1
    rw [Rectangle]
    simp [perronRectangleLowerLeft, perronRectangleUpperRight, perronRectangleSigmaL]
    constructor
    · apply Set.mem_uIcc_of_le
      · have hN : (1 : ℝ) ≤ N := by exact_mod_cast h.N_ge_one
        nlinarith [hstrip.1, hN]
      · exact le_of_lt (lt_trans hstrip.2 h.sigmaR_gt)
    · have himabs : |ρ.im| < T := hρ.2
      rw [abs_lt] at himabs
      apply Set.mem_uIcc_of_le
      · exact le_of_lt himabs.1
      · exact le_of_lt himabs.2

theorem zetaPerronNontrivialZeroFinset_eq_byHeight
    {x σR T : ℝ} {N : ℕ}
    (h : RHV3Lean.PerronRectangleAdmissible x σR N T) :
    RHV3Lean.zetaPerronNontrivialZeroFinset σR N T =
      nontrivialZetaZerosByHeightFinset T := by
  classical
  ext ρ
  simp [zetaPerronNontrivialZeroFinset, nontrivialZetaZerosByHeightFinset,
    zetaPerronNontrivialZeroSet_eq_byHeight h]

theorem zetaPerron_nontrivial_zero_residue_sum_eq_byHeight
    {x σR T : ℝ} {N : ℕ}
    (h : RHV3Lean.PerronRectangleAdmissible x σR N T) :
    sumResiduesIn (RHV3Lean.zetaPerronIntegrand x)
        (RHV3Lean.zetaPerronNontrivialZeroSet σR N T) =
      ∑ ρ ∈ nontrivialZetaZerosByHeightFinset T,
        -(RHV3Lean.zetaZeroMultiplicity ρ : ℂ) * Perron.f x ρ := by
  classical
  rw [zetaPerron_nontrivial_zero_residue_sum h.x_gt]
  have hfin : (zetaPerronNontrivialZeroSet σR N T).Finite :=
    zetaPerron_nontrivial_zero_set_finite σR N T
  haveI : Fintype (zetaPerronNontrivialZeroSet σR N T) := hfin.fintype
  rw [tsum_fintype]
  rw [← zetaPerronNontrivialZeroFinset_eq_byHeight h]
  simp only [zetaPerronNontrivialZeroFinset]
  exact (Finset.sum_subtype (s := hfin.toFinset)
    (p := fun ρ ↦ ρ ∈ zetaPerronNontrivialZeroSet σR N T)
    (f := fun ρ ↦ -(zetaZeroMultiplicity ρ : ℂ) * Perron.f x ρ)
    (by simp)).symm

end RHV3Lean
