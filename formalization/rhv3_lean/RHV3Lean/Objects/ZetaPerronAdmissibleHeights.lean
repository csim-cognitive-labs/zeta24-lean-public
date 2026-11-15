/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import Mathlib.Order.Interval.Set.Infinite
import RHV3Lean.Objects.ZetaZeroHeightPerronBridge

/-!
# Tour 23-B - P4.3: arbitrarily large admissible Perron heights

This module proves the geometric existence of admissible Perron rectangle heights.
It does not prove quantitative good heights or any horizontal boundary estimate.
-/

open Set Filter Finset BigOperators Complex
open scoped Topology ComplexConjugate

namespace RHV3Lean

/-! ## Forbidden non-trivial-zero heights -/

/-- Finset of non-trivial-zero ordinates forbidden below a finite upper height. -/
noncomputable def nontrivialZetaForbiddenHeightsBelow (U : ℝ) : Finset ℝ :=
  (nontrivialZetaZerosByHeightFinset U).image fun ρ : ℂ => |ρ.im|

@[simp] theorem mem_nontrivialZetaForbiddenHeightsBelow
    {U T : ℝ} :
    T ∈ nontrivialZetaForbiddenHeightsBelow U ↔
      ∃ ρ ∈ nontrivialZetaZerosByHeightFinset U,
        |ρ.im| = T := by
  classical
  simp [nontrivialZetaForbiddenHeightsBelow]

theorem abs_im_mem_forbiddenHeightsBelow
    {U : ℝ} {ρ : ℂ}
    (hρ : IsNontrivialZetaZero ρ)
    (hU : |ρ.im| < U) :
    |ρ.im| ∈ nontrivialZetaForbiddenHeightsBelow U := by
  classical
  rw [mem_nontrivialZetaForbiddenHeightsBelow]
  exact ⟨ρ, by simpa using And.intro hρ hU, rfl⟩

/-! ## Zero-free heights in every unit interval -/

theorem exists_nontrivial_zero_free_height_between
    (H : ℝ) :
    ∃ T : ℝ,
      T ∈ Set.Ioo (max H 0) (max H 0 + 1) ∧
      ∀ ρ : ℂ,
        IsNontrivialZetaZero ρ →
        |ρ.im| ≠ T := by
  classical
  let B : ℝ := max H 0
  let U : ℝ := B + 1
  have hBU : B < U := by dsimp [U]; linarith
  have hinf : (Set.Ioo B U).Infinite := Set.Ioo_infinite hBU
  obtain ⟨T, hTmem, hTnot⟩ :=
    hinf.exists_notMem_finset (nontrivialZetaForbiddenHeightsBelow U)
  refine ⟨T, by simpa [B, U] using hTmem, ?_⟩
  intro ρ hρ hρT
  have hltU : |ρ.im| < U := by
    rw [hρT]
    exact hTmem.2
  have hforbidden : |ρ.im| ∈ nontrivialZetaForbiddenHeightsBelow U :=
    abs_im_mem_forbiddenHeightsBelow hρ hltU
  exact hTnot (by simpa [hρT] using hforbidden)

theorem exists_nontrivial_zero_free_height_gt
    (H : ℝ) :
    ∃ T : ℝ,
      H < T ∧
      0 < T ∧
      ∀ ρ : ℂ,
        IsNontrivialZetaZero ρ →
        |ρ.im| ≠ T := by
  obtain ⟨T, hTmem, hfree⟩ := exists_nontrivial_zero_free_height_between H
  exact ⟨T, by linarith [le_max_left H 0, hTmem.1],
    by linarith [le_max_right H 0, hTmem.1], hfree⟩

/-! ## Global pole classification, independent of admissible rectangles -/

theorem zetaPerronIntegrand_pole_classified_global
    {x : ℝ}
    (hx : 1 < x)
    {s : ℂ}
    (hs : meromorphicOrderAt (zetaPerronIntegrand x) s < 0) :
    s = 1 ∨
    s = 0 ∨
    s = -1 ∨
    IsTrivialZetaZero s ∨
    IsNontrivialZetaZero s := by
  by_cases hs_one : s = 1
  · exact Or.inl hs_one
  by_cases hs_zero : s = 0
  · exact Or.inr (Or.inl hs_zero)
  by_cases hs_neg_one : s = -1
  · exact Or.inr (Or.inr (Or.inl hs_neg_one))
  by_cases hzeta : riemannZeta s = 0
  · rcases zetaZero_trivial_or_nontrivial hzeta with htriv | hnon
    · exact Or.inr (Or.inr (Or.inr (Or.inl htriv)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hnon)))
  · have xpos : 0 < x := lt_trans zero_lt_one hx
    have hL : AnalyticAt ℂ (fun z ↦ -logDeriv riemannZeta z) s :=
      (analyticAt_logDeriv_riemannZeta hs_one hzeta).neg
    have hK : AnalyticAt ℂ (Perron.f x) s :=
      analyticAt_perronKernel xpos hs_zero hs_neg_one
    have hprod : AnalyticAt ℂ (zetaPerronIntegrand x) s := by
      rw [show zetaPerronIntegrand x =
          (fun z ↦ -logDeriv riemannZeta z * Perron.f x z) by rfl]
      exact hL.mul hK
    exact False.elim ((not_le_of_gt hs) hprod.meromorphicOrderAt_nonneg)

/-! ## Boundary geometry -/

theorem isTrivialZetaZero_im_eq_zero
    {ρ : ℂ}
    (hρ : IsTrivialZetaZero ρ) :
    ρ.im = 0 := by
  rcases hρ with ⟨n, rfl⟩
  simp

theorem isTrivialZetaZero_re_lt_one
    {ρ : ℂ}
    (hρ : IsTrivialZetaZero ρ) :
    ρ.re < 1 := by
  rcases hρ with ⟨n, rfl⟩
  have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  simp
  nlinarith

theorem isTrivialZetaZero_re_ne_perronRectangleSigmaL
    {ρ : ℂ}
    (hρ : IsTrivialZetaZero ρ)
    {N : ℕ}
    (_hN : 1 ≤ N) :
    ρ.re ≠ perronRectangleSigmaL N := by
  intro h
  rcases hρ with ⟨n, rfl⟩
  have hreal :
      ((2 * (n + 1) : ℕ) : ℝ) = ((2 * N + 1 : ℕ) : ℝ) := by
    have h' : (-2 * (((n : ℕ) : ℝ) + 1) : ℝ) =
        -((2 * (N : ℝ)) + 1) := by
      simpa [perronRectangleSigmaL, mul_assoc] using h
    norm_num at h' ⊢
    nlinarith
  have hnat : 2 * (n + 1) = 2 * N + 1 := by
    exact_mod_cast hreal
  omega

private lemma mem_perronRectangleBorder_cases
    {σR T : ℝ} {N : ℕ} {s : ℂ}
    (hs : s ∈
      RectangleBorder (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T)) :
  s.im = -T ∨ s.im = T ∨ s.re = perronRectangleSigmaL N ∨ s.re = σR := by
  simp [RectangleBorder, perronRectangleLowerLeft, perronRectangleUpperRight] at hs
  rcases hs with ((hbot | hleft) | htop) | hright
  · left
    exact hbot.2
  · right; right; left
    simpa [perronRectangleSigmaL] using hleft.1
  · right; left
    exact htop.2
  · right; right; right
    exact hright.1

private lemma one_not_mem_perronRectangleBorder
    {σR T : ℝ} {N : ℕ}
    (hσR : 1 < σR) (hN : 1 ≤ N) (hT : 0 < T) :
    (1 : ℂ) ∉
      RectangleBorder (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) := by
  intro hborder
  have hcases := mem_perronRectangleBorder_cases (σR := σR) (T := T) (N := N) hborder
  rcases hcases with himbot | himtop | hleft | hright
  · have h' : (0 : ℝ) = -T := by simpa using himbot
    linarith
  · have h' : (0 : ℝ) = T := by simpa using himtop
    linarith
  · have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h' : (1 : ℝ) = -((2 * (N : ℝ)) + 1) := by
      simpa [perronRectangleSigmaL] using hleft
    nlinarith
  · have h' : (1 : ℝ) = σR := by simpa using hright
    linarith

private lemma zero_not_mem_perronRectangleBorder
    {σR T : ℝ} {N : ℕ}
    (hσR : 1 < σR) (hN : 1 ≤ N) (hT : 0 < T) :
    (0 : ℂ) ∉
      RectangleBorder (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) := by
  intro hborder
  have hcases := mem_perronRectangleBorder_cases (σR := σR) (T := T) (N := N) hborder
  rcases hcases with himbot | himtop | hleft | hright
  · have h' : (0 : ℝ) = -T := by simpa using himbot
    linarith
  · have h' : (0 : ℝ) = T := by simpa using himtop
    linarith
  · have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h' : (0 : ℝ) = -((2 * (N : ℝ)) + 1) := by
      simpa [perronRectangleSigmaL] using hleft
    nlinarith
  · have h' : (0 : ℝ) = σR := by simpa using hright
    linarith

private lemma neg_one_not_mem_perronRectangleBorder
    {σR T : ℝ} {N : ℕ}
    (hσR : 1 < σR) (hN : 1 ≤ N) (hT : 0 < T) :
    (-1 : ℂ) ∉
      RectangleBorder (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) := by
  intro hborder
  have hcases := mem_perronRectangleBorder_cases (σR := σR) (T := T) (N := N) hborder
  rcases hcases with himbot | himtop | hleft | hright
  · have h' : (0 : ℝ) = -T := by simpa using himbot
    linarith
  · have h' : (0 : ℝ) = T := by simpa using himtop
    linarith
  · have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h' : (-1 : ℝ) = -((2 * (N : ℝ)) + 1) := by
      simpa [perronRectangleSigmaL] using hleft
    nlinarith
  · have h' : (-1 : ℝ) = σR := by simpa using hright
    linarith

private lemma trivialZero_not_mem_perronRectangleBorder
    {σR T : ℝ} {N : ℕ} {ρ : ℂ}
    (hρ : IsTrivialZetaZero ρ)
    (hσR : 1 < σR) (hN : 1 ≤ N) (hT : 0 < T) :
    ρ ∉
      RectangleBorder (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) := by
  intro hborder
  have hcases := mem_perronRectangleBorder_cases (σR := σR) (T := T) (N := N) hborder
  have himzero := isTrivialZetaZero_im_eq_zero hρ
  rcases hcases with himbot | himtop | hleft | hright
  · linarith
  · linarith
  · exact isTrivialZetaZero_re_ne_perronRectangleSigmaL hρ hN hleft
  · have hrelt := isTrivialZetaZero_re_lt_one hρ
    linarith

private lemma nontrivialZero_not_mem_perronRectangleBorder_of_height
    {σR T : ℝ} {N : ℕ} {ρ : ℂ}
    (hρ : IsNontrivialZetaZero ρ)
    (hσR : 1 < σR) (hN : 1 ≤ N) (hT : 0 < T)
    (hfree :
      ∀ ρ : ℂ,
        IsNontrivialZetaZero ρ →
        |ρ.im| ≠ T) :
    ρ ∉
      RectangleBorder (perronRectangleLowerLeft N T) (perronRectangleUpperRight σR T) := by
  intro hborder
  have hcases := mem_perronRectangleBorder_cases (σR := σR) (T := T) (N := N) hborder
  have hstrip := isNontrivialZetaZero_re_mem_Ioo hρ
  rcases hcases with himbot | himtop | hleft | hright
  · have himabs : |ρ.im| = T := by
      rw [himbot]
      simp [abs_of_pos hT]
    exact hfree ρ hρ himabs
  · have himabs : |ρ.im| = T := by
      rw [himtop]
      exact abs_of_pos hT
    exact hfree ρ hρ himabs
  · have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hleft' : ρ.re = -((2 * (N : ℝ)) + 1) := by
      simpa [perronRectangleSigmaL] using hleft
    nlinarith [hstrip.1]
  · nlinarith [hstrip.2]

theorem perronRectangle_no_boundary_poles_of_zero_free_height
    {x σR T : ℝ}
    {N : ℕ}
    (hx : 1 < x)
    (hσR : 1 < σR)
    (hN : 1 ≤ N)
    (hT : 0 < T)
    (hfree :
      ∀ ρ : ℂ,
        IsNontrivialZetaZero ρ →
        |ρ.im| ≠ T) :
    Disjoint
      (RectangleBorder
        (perronRectangleLowerLeft N T)
        (perronRectangleUpperRight σR T))
      {s | meromorphicOrderAt (zetaPerronIntegrand x) s < 0} := by
  refine Set.disjoint_left.mpr ?_
  intro s hsborder hspole
  rcases zetaPerronIntegrand_pole_classified_global hx hspole with
    hs1 | hs0 | hsn1 | htriv | hnon
  · subst s
    exact one_not_mem_perronRectangleBorder hσR hN hT hsborder
  · subst s
    exact zero_not_mem_perronRectangleBorder hσR hN hT hsborder
  · subst s
    exact neg_one_not_mem_perronRectangleBorder hσR hN hT hsborder
  · exact trivialZero_not_mem_perronRectangleBorder htriv hσR hN hT hsborder
  · exact nontrivialZero_not_mem_perronRectangleBorder_of_height hnon hσR hN hT hfree hsborder

/-! ## Admissibility and arbitrarily large heights -/

theorem perronRectangleAdmissible_of_zero_free_height
    {x σR T : ℝ}
    {N : ℕ}
    (hx : 1 < x)
    (hσR : 1 < σR)
    (hN : 1 ≤ N)
    (hT : 0 < T)
    (hfree :
      ∀ ρ : ℂ,
        IsNontrivialZetaZero ρ →
        |ρ.im| ≠ T) :
    PerronRectangleAdmissible x σR N T where
  x_gt := hx
  sigmaR_gt := hσR
  N_ge_one := hN
  T_pos := hT
  no_poles_on_boundary :=
    perronRectangle_no_boundary_poles_of_zero_free_height hx hσR hN hT hfree

theorem exists_perronRectangleAdmissible_height_between
    {x σR : ℝ}
    {N : ℕ}
    (hx : 1 < x)
    (hσR : 1 < σR)
    (hN : 1 ≤ N)
    (H : ℝ) :
    ∃ T : ℝ,
      max H 0 < T ∧
      T < max H 0 + 1 ∧
      PerronRectangleAdmissible x σR N T := by
  obtain ⟨T, hTmem, hfree⟩ := exists_nontrivial_zero_free_height_between H
  have hTpos : 0 < T := by linarith [le_max_right H 0, hTmem.1]
  exact ⟨T, hTmem.1, hTmem.2,
    perronRectangleAdmissible_of_zero_free_height hx hσR hN hTpos hfree⟩

theorem exists_perronRectangleAdmissible_height_gt
    {x σR : ℝ}
    {N : ℕ}
    (hx : 1 < x)
    (hσR : 1 < σR)
    (hN : 1 ≤ N)
    (H : ℝ) :
    ∃ T : ℝ,
      H < T ∧
      PerronRectangleAdmissible x σR N T := by
  obtain ⟨T, hB, _hU, hAdm⟩ :=
    exists_perronRectangleAdmissible_height_between hx hσR hN H
  exact ⟨T, by linarith [le_max_left H 0, hB], hAdm⟩

end RHV3Lean
