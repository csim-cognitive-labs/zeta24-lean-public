/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

/-
Copyright (c) 2026 csim-cognitive-labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: csim-cognitive-labs, OpenAI
-/
import RHV3Lean.Objects.ZetaPerronResidueInterface

/-!
# Tour 23-B — itération P3c1 : identité exacte sur la droite σ > 1

Cette étape prouve l'ÉGALITÉ EXACTE, pour `1 < σ`, `1 < x` :

\[
\frac{1}{2\pi i}\int_{(\sigma)} -\frac{\zeta'}{\zeta}(s)\,\frac{x^s}{s(s+1)}\,ds
= \sum_{n<x}\Lambda(n)\Big(1-\frac nx\Big),
\]

par échange série–intégrale rigoureux (convergence absolue/dominée,
`integral_tsum_of_summable_integral_norm`) puis formule de Perron P2 terme à terme.

Périmètre STRICT (mandat corrigé, PR #55) : aucun déplacement de contour, aucun rectangle,
aucune somme sur les zéros, aucun passage à la limite `T→∞`/`N→∞`, aucune identification à
`R ρ U`, aucune porte modifiée. Les rectangles zéro-free de P3b ne sont pas utilisés ici.

Dossier mathématique préalable :
`validation/p4_autoresearch_prime/rh_resolution_progression/`
`stage42_round23b_iterationP3c1_math_dossier.md`.
-/

open Set Filter Complex ArithmeticFunction LSeries.notation MeasureTheory Real
open scoped Topology

namespace RHV3Lean

/-! ## 1. La somme de von Mangoldt lissée, objet de première classe -/

/-- La somme de von Mangoldt lissée `∑_{n<x} Λ(n)·(1 − n/x)`. La troncature stricte `n < x`
est capturée exactement par `Finset.range ⌈x⌉₊` (`Nat.lt_ceil`). -/
noncomputable def smoothedVonMangoldtSum (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range ⌈x⌉₊, (Λ n : ℂ) * (1 - (n : ℂ) / (x : ℂ))

/-! ## 2. Rescaling exact terme de Dirichlet × noyau -/

/-- `term(Λ,s,n)·K_x(s) = Λ(n)·K_{x/n}(s)` : le terme général de la série de von Mangoldt
absorbe le noyau de Perron en un noyau rescalé (réutilise `Perron.f_mul_eq_f`, P2). -/
theorem vonMangoldt_term_mul_perronKernel {x : ℝ} (xpos : 0 < x) (s : ℂ) (n : ℕ) :
    LSeries.term ↗Λ s n * Perron.f x s = (Λ n : ℂ) * Perron.f (x / n) s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · have hn' : (n : ℕ) ≠ 0 := hn.ne'
    have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hcast : ((n : ℝ) : ℂ) = (n : ℂ) := by push_cast; ring
    rw [LSeries.term_of_ne_zero hn', div_eq_mul_inv, ← Complex.cpow_neg, mul_assoc]
    congr 1
    rw [mul_comm, ← hcast]
    exact Perron.f_mul_eq_f (x := (n : ℝ)) xpos hnpos s
  -- note : pour n = 0, les deux membres sont nuls (`term _ _ 0 = 0` et `Λ 0 = 0`)

/-! ## 3. Développement ponctuel sur la droite -/

/-- Sur la droite `Re s = σ > 1`, l'intégrande se développe en série absolument convergente
de noyaux rescalés (P1 + distribution du produit dans la `tsum`). -/
theorem neg_logDeriv_mul_perronKernel_eq_tsum {x : ℝ} (xpos : 0 < x) {σ : ℝ}
    (hσ : 1 < σ) (t : ℝ) :
    -logDeriv riemannZeta (σ + t * I) * Perron.f x (σ + t * I)
      = ∑' n : ℕ, (Λ n : ℂ) * Perron.f (x / n) (σ + t * I) := by
  have hre : 1 < ((σ : ℂ) + t * I).re := by simp [hσ]
  rw [negLogDeriv_riemannZeta_eq_LSeries_vonMangoldt hre, LSeries, ← tsum_mul_right]
  exact tsum_congr fun n ↦ vonMangoldt_term_mul_perronKernel xpos _ n

/-! ## 4. Convergence absolue : intégrabilité et sommabilité des normes -/

/-- Chaque terme est verticalement intégrable pour `σ > 1` (réutilise
`Perron.isIntegrable`, P2 ; le terme `n = 0` est identiquement nul). -/
theorem integrable_vonMangoldt_perron_term {x : ℝ} (xpos : 0 < x) {σ : ℝ}
    (hσ : 1 < σ) (n : ℕ) :
    Integrable (fun t : ℝ ↦ (Λ n : ℂ) * Perron.f (x / n) (σ + t * I)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_mul]
    exact integrable_zero _ _ _
  · have hxn : 0 < x / n := div_pos xpos (Nat.cast_pos.mpr hn)
    exact (Perron.isIntegrable hxn (by linarith) (by linarith)).const_mul _

/-- Factorisation exacte des normes du noyau pour base réelle positive :
`‖K_y(s)‖ = y^{Re s}·‖K_1(s)‖`. -/
theorem norm_perron_f_eq_rpow_mul {y : ℝ} (ypos : 0 < y) (s : ℂ) :
    ‖Perron.f y s‖ = y ^ s.re * ‖Perron.f 1 s‖ := by
  show ‖(y : ℂ) ^ s / (s * (s + 1))‖ = y ^ s.re * ‖((1 : ℝ) : ℂ) ^ s / (s * (s + 1))‖
  rw [norm_div, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ypos]
  simp only [Complex.ofReal_one, Complex.one_cpow, norm_one]
  ring

/-- Sommabilité des intégrales de normes : la suite `n ↦ ∫‖Λ(n)·K_{x/n}(σ+ti)‖dt` vaut
exactement `(x^σ·C_σ)·‖term(Λ,σ,n)‖` avec `C_σ = ∫‖K_1(σ+ti)‖dt`, et la série de von
Mangoldt est absolument sommable en `σ > 1` (Mathlib + dimension finie). -/
theorem summable_integral_norm_vonMangoldt_perron {x : ℝ} (xpos : 0 < x) {σ : ℝ}
    (hσ : 1 < σ) :
    Summable fun n : ℕ ↦ ∫ t : ℝ, ‖(Λ n : ℂ) * Perron.f (x / n) (σ + t * I)‖ := by
  set C : ℝ := ∫ t : ℝ, ‖Perron.f 1 ((σ : ℂ) + t * I)‖ with hC
  have hre : ∀ t : ℝ, ((σ : ℂ) + t * I).re = σ := fun t ↦ by simp
  -- sommabilité en norme de la série de von Mangoldt au point réel σ
  have hsummable : Summable fun n : ℕ ↦ ‖LSeries.term ↗Λ (σ : ℂ) n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simp [hσ])).norm
  -- égalité exacte terme à terme avec le majorant sommable
  have hfun : (fun n : ℕ ↦ ∫ t : ℝ, ‖(Λ n : ℂ) * Perron.f (x / n) (σ + t * I)‖)
      = fun n : ℕ ↦ (x ^ σ * C) * ‖LSeries.term ↗Λ (σ : ℂ) n‖ := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      have hxn : 0 < x / n := div_pos xpos hnpos
      have hnorm_t : ∀ t : ℝ, ‖(Λ n : ℂ) * Perron.f (x / n) (σ + t * I)‖
          = (Λ n * (x / n) ^ σ) * ‖Perron.f 1 ((σ : ℂ) + t * I)‖ := by
        intro t
        rw [norm_mul, norm_perron_f_eq_rpow_mul hxn, hre t]
        have : ‖(Λ n : ℂ)‖ = Λ n := by
          rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
        rw [this]
        ring
      calc ∫ t : ℝ, ‖(Λ n : ℂ) * Perron.f (x / n) (σ + t * I)‖
          = ∫ t : ℝ, (Λ n * (x / n) ^ σ) * ‖Perron.f 1 ((σ : ℂ) + t * I)‖ := by
            exact integral_congr_ae (Eventually.of_forall hnorm_t)
        _ = (Λ n * (x / n) ^ σ) * C := by rw [integral_const_mul, hC]
        _ = (x ^ σ * C) * ‖LSeries.term ↗Λ (σ : ℂ) n‖ := by
            rw [LSeries.term_of_ne_zero hn.ne']
            have hterm_norm : ‖(Λ n : ℂ) / (n : ℂ) ^ (σ : ℂ)‖ = Λ n / (n : ℝ) ^ σ := by
              rw [norm_div]
              have h1 : ‖(Λ n : ℂ)‖ = Λ n := by
                rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
              have h2 : ‖(n : ℂ) ^ (σ : ℂ)‖ = (n : ℝ) ^ σ := by
                have h := Complex.norm_cpow_eq_rpow_re_of_pos hnpos (σ : ℂ)
                rw [show (((n : ℝ) : ℂ)) = (n : ℂ) by push_cast; ring] at h
                simpa using h
              rw [h1, h2]
            rw [hterm_norm, Real.div_rpow xpos.le hnpos.le]
            field_simp
  rw [hfun]
  exact hsummable.mul_left _

/-! ## 5. Perron terme à terme (P2) -/

/-- Primitive algébrique tronquée pour le cas frontière `K₁(s)=1/(s(s+1))`. -/
private lemma perron_f_one_truncated_integral {σ : ℝ} (σpos : 0 < σ) (T : ℝ) :
    ∫ t in (-T)..T, Perron.f 1 (σ + t * I)
      = 2 * (Real.arctan (T / σ) - Real.arctan (T / (σ + 1))) := by
  have hσ_ne : σ ≠ 0 := ne_of_gt σpos
  have hσ1_ne : σ + 1 ≠ 0 := by linarith
  have hInt₀ : IntervalIntegrable (fun t : ℝ ↦ (1 : ℂ) / (σ + t * I)) volume (-T) T := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) ?_
    intro t
    exact fun h ↦ hσ_ne (by simpa using congrArg Complex.re h)
  have hInt₁ : IntervalIntegrable (fun t : ℝ ↦ (1 : ℂ) / ((σ + 1 : ℝ) + t * I)) volume (-T) T := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) ?_
    intro t
    exact fun h ↦ hσ1_ne (by simpa using congrArg Complex.re h)
  have hpf : ∀ t : ℝ,
      Perron.f 1 (σ + t * I) = (1 : ℂ) / (σ + t * I) - 1 / ((σ + 1 : ℝ) + t * I) := by
    intro t
    have hs0 : (σ : ℂ) + t * I ≠ 0 := fun h ↦ hσ_ne (by simpa using congrArg Complex.re h)
    have hs1 : (σ : ℂ) + t * I ≠ -1 := by
      intro h
      have hre : σ = -1 := by simpa using congrArg Complex.re h
      exact hσ1_ne (by linarith)
    simpa [Perron.f, add_assoc, add_comm, add_left_comm] using
      Perron.keyIdentity (x := 1) (s := (σ : ℂ) + t * I) hs0 hs1
  calc
    ∫ t in (-T)..T, Perron.f 1 (σ + t * I)
        = ∫ t in (-T)..T, ((1 : ℂ) / (σ + t * I) - 1 / ((σ + 1 : ℝ) + t * I)) := by
          exact intervalIntegral.integral_congr fun t _ ↦ hpf t
    _ = (∫ t in (-T)..T, (1 : ℂ) / (σ + t * I))
        - ∫ t in (-T)..T, (1 : ℂ) / ((σ + 1 : ℝ) + t * I) := by
          rw [intervalIntegral.integral_sub hInt₀ hInt₁]
    _ = 2 * (Real.arctan (T / σ) - Real.arctan (T / (σ + 1))) := by
          rw [integral_const_div_re_add_self (A := (1 : ℂ)) (x := σ) (y₁ := -T) (y₂ := T) hσ_ne,
            integral_const_div_re_add_self (A := (1 : ℂ)) (x := σ + 1) (y₁ := -T) (y₂ := T) hσ1_ne]
          have hσneg₁ : T / -σ = -(T / σ) := by
            field_simp [hσ_ne]
          have hσneg₂ : -T / -σ = T / σ := by
            field_simp [hσ_ne]
          have hσ1neg₁ : T / -(σ + 1) = -(T / (σ + 1)) := by
            field_simp [hσ1_ne]
          have hσ1neg₂ : -T / -(σ + 1) = T / (σ + 1) := by
            field_simp [hσ1_ne]
          rw [hσneg₁, hσneg₂, hσ1neg₁, hσ1neg₂]
          simp only [neg_sq, sub_self, mul_zero, Real.arctan_neg, Complex.ofReal_neg]
          field_simp [Complex.I_ne_zero]
          ring

/-- Cas frontière exact du noyau de Perron lissé :
`K₁(s)=1/(s(s+1))` a une intégrale verticale normalisée nulle sur toute droite `σ>0`. -/
theorem verticalIntegral'_perron_f_one
    {σ : ℝ} (σpos : 0 < σ) :
    VerticalIntegral' (Perron.f 1) σ = 0 := by
  have hInt : Integrable (fun t : ℝ ↦ Perron.f 1 (σ + t * I)) :=
    Perron.isIntegrable (by norm_num) (ne_of_gt σpos) (by linarith)
  have h_tendsto_integral :
      Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T, Perron.f 1 (σ + t * I)) atTop
        (𝓝 (∫ t : ℝ, Perron.f 1 (σ + t * I))) :=
    intervalIntegral_tendsto_integral hInt tendsto_neg_atTop_atBot tendsto_id
  have h_tendsto_zero :
      Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T, Perron.f 1 (σ + t * I)) atTop
        (𝓝 0) := by
    have hσ1pos : 0 < σ + 1 := by linarith
    have h_arctan_real :
        Tendsto (fun T : ℝ ↦
            2 * (Real.arctan (T / σ) - Real.arctan (T / (σ + 1)))) atTop
          (𝓝 0) := by
      have h0 : Tendsto (fun T : ℝ ↦ Real.arctan (T / σ)) atTop (𝓝 (π / 2)) := by
        convert (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp
          (tendsto_id.const_mul_atTop (inv_pos.mpr σpos)) using 1
        ext T
        simp [div_eq_mul_inv, mul_comm]
      have h1 : Tendsto (fun T : ℝ ↦ Real.arctan (T / (σ + 1))) atTop (𝓝 (π / 2)) := by
        convert (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp
          (tendsto_id.const_mul_atTop (inv_pos.mpr hσ1pos)) using 1
        ext T
        simp [div_eq_mul_inv, mul_comm]
      simpa using (h0.sub h1).const_mul 2
    have h_arctan_complex :
        Tendsto (fun T : ℝ ↦
            ((2 * (Real.arctan (T / σ) - Real.arctan (T / (σ + 1))) : ℝ) : ℂ)) atTop
          (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp h_arctan_real
    have h_arctan_zero : Tendsto (fun T : ℝ ↦
            (2 : ℂ) * (Real.arctan (T / σ) - Real.arctan (T / (σ + 1)))) atTop
          (𝓝 0) := by
      simpa using h_arctan_complex
    exact h_arctan_zero.congr' (Eventually.of_forall fun T ↦ (perron_f_one_truncated_integral σpos T).symm)
  have hintegral_zero : (∫ t : ℝ, Perron.f 1 (σ + t * I)) = 0 :=
    tendsto_nhds_unique h_tendsto_integral h_tendsto_zero
  simp [VerticalIntegral', VerticalIntegral, hintegral_zero]

/-- Valeur exacte de l'intégrale verticale du noyau rescalé : `1 − 1/y` si `y > 1`,
`0` si `y = 1`, et `0` si `0 < y < 1`. -/
theorem verticalIntegral'_perron_f_eval {y : ℝ} (ypos : 0 < y)
    {σ : ℝ} (σpos : 0 < σ) :
    VerticalIntegral' (Perron.f y) σ = if 1 < y then 1 - 1 / (y : ℂ) else 0 := by
  rcases lt_trichotomy y 1 with hlt | heq | hgt
  · rw [if_neg (by linarith)]
    have h0 := Perron.formulaLtOne ypos hlt σpos
    show (1 / (2 * ↑π * I)) • VerticalIntegral (Perron.f y) σ = 0
    rw [h0, smul_zero]
  · subst heq
    rw [if_neg (by norm_num)]
    exact verticalIntegral'_perron_f_one σpos
  · rw [if_pos hgt]
    exact Perron.formulaGtOne hgt σpos

/-! ## 6. Théorème central : identité exacte de la droite σ > 1 -/

/-- **Identité exacte P3c1.** Pour `1 < σ`, `1 < x` :
la moyenne de Perron lissée de `−ζ'/ζ` sur la droite `σ` vaut EXACTEMENT la somme finie
`∑_{n<x} Λ(n)(1−n/x)`. Aucun contour déplacé, aucun zéro invoqué, aucun passage à la
limite. -/
theorem verticalIntegral'_eq_smoothedVonMangoldtSum {x : ℝ} (x_gt : 1 < x)
    {σ : ℝ} (hσ : 1 < σ) :
    VerticalIntegral' (fun s ↦ -logDeriv riemannZeta s * Perron.f x s) σ
      = smoothedVonMangoldtSum x := by
  have xpos : 0 < x := lt_trans one_pos x_gt
  -- (b) échange série–intégrale : HasSum des intégrales vers l'intégrale totale
  have hHasSum := hasSum_integral_of_summable_integral_norm
    (μ := (volume : Measure ℝ))
    (F := fun (n : ℕ) (t : ℝ) ↦ (Λ n : ℂ) * Perron.f (x / n) (σ + t * I))
    (fun n ↦ integrable_vonMangoldt_perron_term xpos hσ n)
    (summable_integral_norm_vonMangoldt_perron xpos hσ)
  -- (a) l'intégrale totale est celle de l'intégrande
  have hcongr : (∫ t : ℝ, ∑' n : ℕ, (Λ n : ℂ) * Perron.f (x / n) (σ + t * I))
      = ∫ t : ℝ, -logDeriv riemannZeta (σ + t * I) * Perron.f x (σ + t * I) :=
    integral_congr_ae (Eventually.of_forall fun t ↦
      (neg_logDeriv_mul_perronKernel_eq_tsum xpos hσ t).symm)
  rw [hcongr] at hHasSum
  -- (c) multiplication scalaire : passage à VerticalIntegral'
  have hV : HasSum
      (fun n : ℕ ↦ (1 / (2 * (π : ℂ) * I)) •
        I • ∫ t : ℝ, (Λ n : ℂ) * Perron.f (x / n) (σ + t * I))
      (VerticalIntegral' (fun s ↦ -logDeriv riemannZeta s * Perron.f x s) σ) := by
    have h1 := hHasSum.const_smul (I : ℂ)
    have h2 := h1.const_smul ((1 : ℂ) / (2 * (π : ℂ) * I))
    exact h2
  -- chaque sommande = Λ(n)·V'(K_{x/n})(σ)
  have hterm : (fun n : ℕ ↦ (1 / (2 * (π : ℂ) * I)) •
        I • ∫ t : ℝ, (Λ n : ℂ) * Perron.f (x / n) (σ + t * I))
      = fun n : ℕ ↦ (Λ n : ℂ) * VerticalIntegral' (Perron.f (x / n)) σ := by
    funext n
    show (1 / (2 * (π : ℂ) * I)) • I • ∫ t : ℝ, (Λ n : ℂ) * Perron.f (x / n) (σ + t * I)
      = (Λ n : ℂ) * ((1 / (2 * (π : ℂ) * I)) • (I • ∫ t : ℝ, Perron.f (x / n) (σ + t * I)))
    rw [integral_const_mul]
    simp only [smul_eq_mul]
    ring
  rw [hterm] at hV
  -- (c') évaluation de chaque terme
  have heval : (fun n : ℕ ↦ (Λ n : ℂ) * VerticalIntegral' (Perron.f (x / n)) σ)
      = fun n : ℕ ↦ if n ∈ Finset.range ⌈x⌉₊ then (Λ n : ℂ) * (1 - (n : ℂ) / (x : ℂ))
        else 0 := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · by_cases h0 : (0 : ℕ) ∈ Finset.range ⌈x⌉₊ <;> simp [h0]
    · have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      have hypos : 0 < x / n := div_pos xpos hnpos
      rw [verticalIntegral'_perron_f_eval hypos (by linarith)]
      by_cases hmem : n ∈ Finset.range ⌈x⌉₊
      · have hnx : (n : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hmem)
        have hgt : 1 < x / n := (one_lt_div hnpos).mpr hnx
        rw [if_pos hgt, if_pos hmem]
        congr 1
        have hcast : ((x / n : ℝ) : ℂ) = (x : ℂ) / (n : ℂ) := by push_cast; ring
        rw [hcast, one_div_div]
      · have hnx : ¬ ((n : ℝ) < x) := fun h ↦ hmem (Finset.mem_range.mpr (Nat.lt_ceil.mpr h))
        have hlt : ¬ (1 < x / n) := by
          rw [not_lt]
          exact (div_le_one hnpos).mpr (not_lt.mp hnx)
        rw [if_neg hlt, if_neg hmem, mul_zero]
  rw [heval] at hV
  -- (d) la tsum est la somme finie lissée
  have htsum := hV.tsum_eq
  rw [← htsum]
  rw [tsum_eq_sum (s := Finset.range ⌈x⌉₊) (fun n hn ↦ if_neg hn)]
  unfold smoothedVonMangoldtSum
  exact Finset.sum_congr rfl fun n hn ↦ if_pos hn

example {x : ℝ} (x_gt : 1 < x)
    {σ : ℝ} (hσ : 1 < σ) :
    VerticalIntegral'
        (fun s ↦ -logDeriv riemannZeta s * Perron.f x s) σ
      = smoothedVonMangoldtSum x :=
  verticalIntegral'_eq_smoothedVonMangoldtSum x_gt hσ

example {σ : ℝ} (hσ : 1 < σ) :
    VerticalIntegral'
        (fun s ↦ -logDeriv riemannZeta s * Perron.f 2 s) σ
      = smoothedVonMangoldtSum 2 :=
  verticalIntegral'_eq_smoothedVonMangoldtSum (by norm_num) hσ

example {σ : ℝ} (hσ : 0 < σ) :
    VerticalIntegral' (Perron.f 1) σ = 0 :=
  verticalIntegral'_perron_f_one hσ

end RHV3Lean

/-! ## Audit d'axiomes — Tour 23-B, itération P3c1 -/

#print axioms RHV3Lean.smoothedVonMangoldtSum
#print axioms RHV3Lean.vonMangoldt_term_mul_perronKernel
#print axioms RHV3Lean.neg_logDeriv_mul_perronKernel_eq_tsum
#print axioms RHV3Lean.integrable_vonMangoldt_perron_term
#print axioms RHV3Lean.norm_perron_f_eq_rpow_mul
#print axioms RHV3Lean.summable_integral_norm_vonMangoldt_perron
#print axioms RHV3Lean.verticalIntegral'_perron_f_one
#print axioms RHV3Lean.verticalIntegral'_perron_f_eval
#print axioms RHV3Lean.verticalIntegral'_eq_smoothedVonMangoldtSum
