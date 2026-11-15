/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaReflectionMultiplicity
import RHV3Lean.Objects.P4Port.NumberTheory.LSeries.ZetaFiniteOrder

/-!
# P4.5 trivial zeta zero simplicity
-/

open Complex Set Filter Finset BigOperators
open scoped Topology

noncomputable section

namespace RHV3Lean

def trivialZetaZeroAt (n : ℕ) : ℂ :=
  -2 * ((n + 1 : ℕ) : ℂ)

theorem riemannZeta_trivialZetaZeroAt
    (n : ℕ) :
    riemannZeta (trivialZetaZeroAt n) = 0 := by
  simpa [trivialZetaZeroAt] using riemannZeta_neg_two_mul_nat_add_one n

theorem trivialZetaZeroAt_ne_zero
    (n : ℕ) :
    trivialZetaZeroAt n ≠ 0 := by
  unfold trivialZetaZeroAt
  norm_num
  exact_mod_cast Nat.succ_ne_zero n

theorem trivialZetaZeroAt_ne_one
    (n : ℕ) :
    trivialZetaZeroAt n ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp [trivialZetaZeroAt] at hre
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem inv_Gammaℝ_eq_shift_two
    (s : ℂ) :
    s.Gammaℝ⁻¹ =
      (s / (2 * Real.pi)) *
        (s + 2).Gammaℝ⁻¹ := by
  by_cases hs : s = 0
  · subst s
    simp [Complex.Gammaℝ_eq_zero_iff]
  · have hΓ := Complex.Gammaℝ_add_two (s := s) hs
    have hπ : ((2 : ℂ) * (Real.pi : ℂ)) ≠ 0 := by
      norm_num [Real.pi_ne_zero]
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    rw [hΓ]
    field_simp [hs, hπ, h2, Real.pi_ne_zero]

theorem inv_Gammaℝ_eq_finite_shift_product
    (m : ℕ)
    (s : ℂ) :
    s.Gammaℝ⁻¹ =
      (∏ k ∈ Finset.range m,
        (s + 2 * (k : ℂ)) /
          (2 * Real.pi)) *
      (s + 2 * (m : ℂ)).Gammaℝ⁻¹ := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [ih]
      have hshift :=
        inv_Gammaℝ_eq_shift_two (s := s + 2 * (m : ℂ))
      rw [hshift]
      simp [Finset.prod_range_succ, Nat.cast_add, Nat.cast_one]
      ring_nf

noncomputable def trivialGammaRRegularFactor
    (n : ℕ)
    (s : ℂ) :
    ℂ :=
  (1 / (2 * Real.pi : ℂ)) *
    (∏ k ∈ (Finset.range (n + 2)).erase (n + 1),
      (s + 2 * (k : ℂ)) / (2 * Real.pi)) *
    (s + 2 * ((n + 2 : ℕ) : ℂ)).Gammaℝ⁻¹

theorem inv_Gammaℝ_trivial_factorization
    (n : ℕ) :
    (fun s : ℂ => s.Gammaℝ⁻¹)
      =ᶠ[𝓝 (trivialZetaZeroAt n)]
    (fun s =>
      (s - trivialZetaZeroAt n) *
        trivialGammaRRegularFactor n s) := by
  apply Filter.Eventually.of_forall
  intro s
  have hprod := inv_Gammaℝ_eq_finite_shift_product (m := n + 2) (s := s)
  change s.Gammaℝ⁻¹ =
    (s - trivialZetaZeroAt n) * trivialGammaRRegularFactor n s
  rw [hprod]
  unfold trivialGammaRRegularFactor trivialZetaZeroAt
  have hmem : n + 1 ∈ Finset.range (n + 2) := by simp
  rw [← Finset.mul_prod_erase
    (s := Finset.range (n + 2))
    (f := fun k => (s + 2 * (k : ℂ)) / (2 * Real.pi))
    hmem]
  ring_nf

theorem analyticAt_trivialGammaRRegularFactor
    (n : ℕ) :
    AnalyticAt ℂ
      (trivialGammaRRegularFactor n)
      (trivialZetaZeroAt n) := by
  unfold trivialGammaRRegularFactor
  have hconst :
      AnalyticAt ℂ (fun _ : ℂ => (1 / (2 * Real.pi : ℂ))) (trivialZetaZeroAt n) := by
    fun_prop
  have hprod :
      AnalyticAt ℂ
        (fun s : ℂ =>
          ∏ k ∈ (Finset.range (n + 2)).erase (n + 1),
            (s + 2 * (k : ℂ)) / (2 * Real.pi))
        (trivialZetaZeroAt n) := by
    apply Finset.analyticAt_fun_prod
    intro k hk
    fun_prop
  have hshift_arg :
      AnalyticAt ℂ
        (fun s : ℂ => s + 2 * ((n + 2 : ℕ) : ℂ))
        (trivialZetaZeroAt n) := by
    fun_prop
  have hgamma :
      AnalyticAt ℂ
        (fun s : ℂ => (s + 2 * ((n + 2 : ℕ) : ℂ)).Gammaℝ⁻¹)
        (trivialZetaZeroAt n) := by
    simpa [Function.comp_def] using
      (AnalyticAt.comp
        (g := fun z : ℂ => z.Gammaℝ⁻¹)
        (f := fun s : ℂ => s + 2 * ((n + 2 : ℕ) : ℂ))
        (x := trivialZetaZeroAt n)
        (Complex.differentiable_Gammaℝ_inv.analyticAt
          (trivialZetaZeroAt n + 2 * ((n + 2 : ℕ) : ℂ)))
        hshift_arg)
  exact (hconst.mul hprod).mul hgamma

theorem trivialGammaRRegularFactor_ne_zero
    (n : ℕ) :
    trivialGammaRRegularFactor n
      (trivialZetaZeroAt n) ≠ 0 := by
  have hconst :
      (1 / (2 * Real.pi : ℂ)) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  have hprod :
      (∏ k ∈ (Finset.range (n + 2)).erase (n + 1),
        (trivialZetaZeroAt n + 2 * (k : ℂ)) / (2 * Real.pi)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    have hk_ne : k ≠ n + 1 := by
      exact (Finset.mem_erase.mp hk).1
    have hnum : trivialZetaZeroAt n + 2 * (k : ℂ) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      have hcast : (k : ℝ) = (n + 1 : ℝ) := by
        simp [trivialZetaZeroAt] at hre
        linarith
      exact hk_ne (Nat.cast_injective (R := ℝ) (by
        simpa [Nat.cast_add, Nat.cast_one] using hcast))
    have hden : ((2 : ℂ) * (Real.pi : ℂ)) ≠ 0 := by
      norm_num [Real.pi_ne_zero]
    exact div_ne_zero hnum hden
  have hshift :
      trivialZetaZeroAt n + 2 * (((n + 2 : ℕ) : ℂ)) = 2 := by
    unfold trivialZetaZeroAt
    norm_num [Nat.cast_add, Nat.cast_one]
    ring_nf
  have hgamma :
      (trivialZetaZeroAt n + 2 * (((n + 2 : ℕ) : ℂ))).Gammaℝ⁻¹ ≠ 0 := by
    rw [hshift]
    exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (s := (2 : ℂ)) (by norm_num))
  unfold trivialGammaRRegularFactor
  exact mul_ne_zero (mul_ne_zero hconst hprod) hgamma

theorem analyticOrderAt_inv_Gammaℝ_trivial_eq_one
    (n : ℕ) :
    analyticOrderAt
      (fun s : ℂ => s.Gammaℝ⁻¹)
      (trivialZetaZeroAt n)
      = 1 := by
  have hana : AnalyticAt ℂ (fun s : ℂ => s.Gammaℝ⁻¹) (trivialZetaZeroAt n) :=
    Complex.differentiable_Gammaℝ_inv.analyticAt _
  refine (hana.analyticOrderAt_eq_natCast (n := 1)).mpr ?_
  refine ⟨trivialGammaRRegularFactor n, ?_, ?_, ?_⟩
  · exact analyticAt_trivialGammaRRegularFactor n
  · exact trivialGammaRRegularFactor_ne_zero n
  · filter_upwards [inv_Gammaℝ_trivial_factorization n] with z hz
    rw [hz]
    simp [pow_one]

theorem analyticOrderNatAt_inv_Gammaℝ_trivial_eq_one
    (n : ℕ) :
    analyticOrderNatAt
      (fun s : ℂ => s.Gammaℝ⁻¹)
      (trivialZetaZeroAt n)
      = 1 := by
  have htop :
      analyticOrderAt
        (fun s : ℂ => s.Gammaℝ⁻¹)
        (trivialZetaZeroAt n) ≠ ⊤ := by
    rw [analyticOrderAt_inv_Gammaℝ_trivial_eq_one n]
    simp
  have hcast := Nat.cast_analyticOrderNatAt
    (f := fun s : ℂ => s.Gammaℝ⁻¹)
    (z₀ := trivialZetaZeroAt n)
    htop
  apply Nat.cast_injective (R := ℕ∞)
  simpa using hcast.trans (analyticOrderAt_inv_Gammaℝ_trivial_eq_one n)

theorem completedRiemannZeta_trivialZetaZeroAt_ne_zero
    (n : ℕ) :
    completedRiemannZeta
      (trivialZetaZeroAt n) ≠ 0 := by
  let s₀ := trivialZetaZeroAt n
  let u : ℂ := 1 - s₀
  have hu_re : 1 < u.re := by
    simp [u, s₀, trivialZetaZeroAt]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hnon_u : completedRiemannZeta u ≠ 0 :=
    Complex.completedRiemannZeta_ne_zero_of_one_lt_re hu_re
  have hsym : completedRiemannZeta s₀ = completedRiemannZeta u := by
    simpa [u, s₀, sub_eq_add_neg] using
      (completedRiemannZeta_one_sub s₀).symm
  simpa [s₀] using hsym.symm ▸ hnon_u

theorem analyticAt_completedRiemannZeta_trivialZetaZeroAt
    (n : ℕ) :
    AnalyticAt ℂ
      completedRiemannZeta
      (trivialZetaZeroAt n) := by
  have hbase : AnalyticAt ℂ completedRiemannZeta₀ (trivialZetaZeroAt n) :=
    differentiable_completedZeta₀.analyticAt _
  have hid : AnalyticAt ℂ (fun z : ℂ ↦ z) (trivialZetaZeroAt n) := analyticAt_id
  have hone : AnalyticAt ℂ (fun _ : ℂ ↦ (1 : ℂ)) (trivialZetaZeroAt n) := analyticAt_const
  have hinv_z : AnalyticAt ℂ (fun z : ℂ ↦ z⁻¹) (trivialZetaZeroAt n) :=
    hid.inv (trivialZetaZeroAt_ne_zero n)
  have hsub :
      AnalyticAt ℂ ((fun _ : ℂ ↦ (1 : ℂ)) - fun z : ℂ ↦ z) (trivialZetaZeroAt n) :=
    hone.sub hid
  have hsub_ne :
      (((fun _ : ℂ ↦ (1 : ℂ)) - fun z : ℂ ↦ z) (trivialZetaZeroAt n)) ≠ 0 := by
    simpa only [Pi.sub_apply] using
      (sub_ne_zero.mpr (Ne.symm (trivialZetaZeroAt_ne_one n)) :
        (1 - trivialZetaZeroAt n : ℂ) ≠ 0)
  have hinv_sub :
      AnalyticAt ℂ (((fun _ : ℂ ↦ (1 : ℂ)) - fun z : ℂ ↦ z)⁻¹)
        (trivialZetaZeroAt n) :=
    hsub.inv hsub_ne
  have hformula :
      AnalyticAt ℂ
        ((completedRiemannZeta₀ - fun z : ℂ ↦ z⁻¹) -
          (((fun _ : ℂ ↦ (1 : ℂ)) - fun z : ℂ ↦ z)⁻¹))
        (trivialZetaZeroAt n) :=
    (hbase.sub hinv_z).sub hinv_sub
  apply AnalyticAt.congr hformula
  apply Filter.Eventually.of_forall
  intro z
  simp only [Pi.sub_apply, Pi.inv_apply]
  simpa only [div_eq_mul_inv, one_mul] using
    (completedRiemannZeta_eq z).symm

theorem analyticOrderAt_completedRiemannZeta_trivial_eq_zero
    (n : ℕ) :
    analyticOrderAt
      completedRiemannZeta
      (trivialZetaZeroAt n)
      = 0 := by
  exact (analyticAt_completedRiemannZeta_trivialZetaZeroAt n).analyticOrderAt_eq_zero.mpr
    (completedRiemannZeta_trivialZetaZeroAt_ne_zero n)

theorem riemannZeta_eventuallyEq_completed_mul_invGammaR
    (n : ℕ) :
    riemannZeta
      =ᶠ[𝓝 (trivialZetaZeroAt n)]
    (fun s =>
      completedRiemannZeta s *
        s.Gammaℝ⁻¹) := by
  have hne : trivialZetaZeroAt n ≠ 0 := trivialZetaZeroAt_ne_zero n
  filter_upwards [isOpen_ne.mem_nhds hne] with z hz
  rw [riemannZeta_def_of_ne_zero hz, div_eq_mul_inv]

theorem analyticOrderAt_riemannZeta_trivial_eq_one
    (n : ℕ) :
    analyticOrderAt
      riemannZeta
      (trivialZetaZeroAt n)
      = 1 := by
  have hcomp := analyticAt_completedRiemannZeta_trivialZetaZeroAt n
  have hinv : AnalyticAt ℂ (fun s : ℂ => s.Gammaℝ⁻¹) (trivialZetaZeroAt n) :=
    Complex.differentiable_Gammaℝ_inv.analyticAt _
  rw [analyticOrderAt_congr (riemannZeta_eventuallyEq_completed_mul_invGammaR n)]
  change analyticOrderAt
      (completedRiemannZeta * fun s : ℂ => s.Gammaℝ⁻¹)
      (trivialZetaZeroAt n) = _
  rw [analyticOrderAt_mul hcomp hinv,
    analyticOrderAt_completedRiemannZeta_trivial_eq_zero n,
    analyticOrderAt_inv_Gammaℝ_trivial_eq_one n]
  norm_num

theorem zetaZeroMultiplicity_trivialZetaZeroAt
    (n : ℕ) :
    zetaZeroMultiplicity
      (trivialZetaZeroAt n)
      = 1 := by
  unfold zetaZeroMultiplicity
  have htop :
      analyticOrderAt
        riemannZeta
        (trivialZetaZeroAt n) ≠ ⊤ := by
    rw [analyticOrderAt_riemannZeta_trivial_eq_one n]
    simp
  have hcast := Nat.cast_analyticOrderNatAt
    (f := riemannZeta)
    (z₀ := trivialZetaZeroAt n)
    htop
  apply Nat.cast_injective (R := ℕ∞)
  simpa using hcast.trans (analyticOrderAt_riemannZeta_trivial_eq_one n)

end RHV3Lean
