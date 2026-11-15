/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ArgumentPrinciple

/-!
# Comptage sur un rectangle au-dessus de l'axe réel : élimination du facteur Γ

Sur un rectangle `[z, w]` contenu dans `Im > 0`, le facteur `s(1 − s)Γℝ(s)` de `ξ₁ = ζ·s(1 − s)Γℝ(s)` est holomorphe et
ne s'annule pas : son intégrale de bord logarithmique est nulle (Cauchy). L'intégrale de bord de `ξ₁′/ξ₁` est donc celle
de `ζ′/ζ` : le comptage des zéros dans le rectangle ne lit que `ζ`, aucune valeur de `Γ`.
-/

namespace RHV6Fresh

open Complex Set Filter
open scoped Interval

/-- Le demi-plan supérieur ouvert. -/
theorem isOpen_upperHalf : IsOpen {s : ℂ | 0 < s.im} := isOpen_lt continuous_const continuous_im

/-- Facteur `s(1 − s)Γℝ(s)`, différentiable au-dessus de l'axe réel. -/
theorem gammaFactor_differentiableAt {s : ℂ} (hs : 0 < s.im) :
    DifferentiableAt ℂ (fun u : ℂ => u * (1 - u) * Gammaℝ u) s :=
  ((differentiableAt_id.mul ((differentiableAt_const _).sub differentiableAt_id)).mul
    (analyticAt_Gammaℝ_of_im_ne_zero hs.ne').differentiableAt)

theorem gammaFactor_differentiableOn :
    DifferentiableOn ℂ (fun s : ℂ => s * (1 - s) * Gammaℝ s) {s : ℂ | 0 < s.im} :=
  fun _ hs => (gammaFactor_differentiableAt hs).differentiableWithinAt

theorem zeta_differentiableOn_upper : DifferentiableOn ℂ riemannZeta {s : ℂ | 0 < s.im} := fun s hs =>
  (differentiableAt_riemannZeta (fun h => by rw [h] at hs; simp at hs)).differentiableWithinAt

theorem rect_subset_upper {z w : ℂ} (him : z.im ≤ w.im) (hpos : 0 < z.im) :
    [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ {s : ℂ | 0 < s.im} := by
  intro s hs
  rw [mem_reProdIm, uIcc_of_le him] at hs
  exact lt_of_lt_of_le hpos hs.2.1

theorem rectBoundary_subset_upper {z w : ℂ} (him : z.im ≤ w.im) (hpos : 0 < z.im) :
    rectBoundary z w ⊆ {s : ℂ | 0 < s.im} := by
  intro s hs
  rcases hs with ⟨h1, -⟩ | ⟨-, h2⟩
  · show 0 < s.im
    rcases h1 with h | h <;> rw [h] <;> linarith
  · exact lt_of_lt_of_le hpos h2.1

/-- **Élimination de Γ** : sur un rectangle au-dessus de l'axe réel, sans zéro de `ζ` sur le bord, l'intégrale de bord de
`ξ₁′/ξ₁` est celle de `ζ′/ζ`. -/
theorem rectBoundaryIntegral_completedEntire_eq_zeta {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im)
    (hpos : 0 < z.im) (hB : ∀ s ∈ rectBoundary z w, riemannZeta s ≠ 0) :
    rectBoundaryIntegral (logDeriv completedEntire) z w = rectBoundaryIntegral (logDeriv riemannZeta) z w := by
  set h : ℂ → ℂ := fun s => s * (1 - s) * Gammaℝ s with hh
  set U : Set ℂ := {s : ℂ | 0 < s.im} with hU
  have hUo : IsOpen U := isOpen_upperHalf
  have hdh : DifferentiableOn ℂ h U := gammaFactor_differentiableOn
  have hdz : DifferentiableOn ℂ riemannZeta U := zeta_differentiableOn_upper
  have hh0 : ∀ s ∈ U, h s ≠ 0 := fun s hs => gammaFactor_ne_zero (ne_of_gt hs)
  have hBU := rectBoundary_subset_upper him.le hpos
  -- sur le bord : logDeriv ξ₁ = logDeriv ζ + logDeriv h
  have hEq : EqOn (logDeriv completedEntire) (fun s => logDeriv riemannZeta s + logDeriv h s)
      (rectBoundary z w) := by
    intro s hs
    have hsU : s ∈ U := hBU hs
    have hev : completedEntire =ᶠ[nhds s] fun t => riemannZeta t * h t := by
      filter_upwards [hUo.mem_nhds hsU] with t ht
      exact completedEntire_eq_zeta_mul (ne_of_gt ht)
    have hld : logDeriv completedEntire s = logDeriv (fun t => riemannZeta t * h t) s := by
      simp only [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    rw [hld, logDeriv_mul s (hB s hs) (hh0 s hsU) (hdz.differentiableAt (hUo.mem_nhds hsU))
      (hdh.differentiableAt (hUo.mem_nhds hsU))]
  -- continuité des deux dérivées logarithmiques sur le bord
  have hcont : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → (∀ s ∈ rectBoundary z w, f s ≠ 0) →
      ContinuousOn (logDeriv f) (rectBoundary z w) := by
    intro f hf hf0
    have : logDeriv f = fun s => deriv f s / f s := rfl
    rw [this]
    exact ((hf.deriv hUo).continuousOn.mono hBU).div (hf.continuousOn.mono hBU) hf0
  have hIz := rectSidesIntegrable_of_continuousOn hre.le him.le (hcont _ hdz hB)
  have hIh := rectSidesIntegrable_of_continuousOn hre.le him.le (hcont _ hdh (fun s hs => hh0 s (hBU hs)))
  rw [rectBoundaryIntegral_congr hre.le him.le hEq, rectBoundaryIntegral_add hIz hIh]
  -- Cauchy pour logDeriv h sur le rectangle fermé
  have hCauchy : rectBoundaryIntegral (logDeriv h) z w = 0 := by
    have hd : DifferentiableOn ℂ (logDeriv h) ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
      have : logDeriv h = fun s => deriv h s / h s := rfl
      rw [this]
      exact (((hdh.deriv hUo).div hdh hh0).mono (rect_subset_upper him.le hpos))
    have hc := integral_boundary_rect_eq_zero_of_differentiableOn (logDeriv h) z w hd
    simpa only [rectBoundaryIntegral, smul_eq_mul] using hc
  rw [hCauchy, add_zero]

#print axioms rectBoundaryIntegral_completedEntire_eq_zeta

/-! ## Côté d'un rectangle : intégrale logarithmique = accroissement d'un logarithme -/

/-- **Côté horizontal** : si `f` est holomorphe sur un ouvert `U` contenant le segment `[a, b] + ci` et si `u·f` y reste
dans le plan fendu, `∫_a^b f′/f(x + ci) dx = log(u f(b + ci)) − log(u f(a + ci))`. -/
theorem integral_logDeriv_horizontal {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {a b c : ℝ} (hab : a ≤ b) (u : ℂ) (hseg : ∀ x ∈ Icc a b, (x : ℂ) + c * I ∈ U)
    (hslit : ∀ x ∈ Icc a b, u * f ((x : ℂ) + c * I) ∈ slitPlane) :
    ∫ x in a..b, logDeriv f ((x : ℂ) + c * I) =
      log (u * f ((b : ℂ) + c * I)) - log (u * f ((a : ℂ) + c * I)) := by
  have hu : u ≠ 0 := by
    intro h; have := hslit a ⟨le_rfl, hab⟩; rw [h, zero_mul] at this; exact slitPlane_ne_zero this rfl
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt (fun x : ℝ => log (u * f ((x : ℂ) + c * I)))
      (logDeriv f ((x : ℂ) + c * I)) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hxU := hseg x hx
    have hfx : HasDerivAt f (deriv f ((x : ℂ) + c * I)) ((x : ℂ) + c * I) :=
      (hf.differentiableAt (hU.mem_nhds hxU)).hasDerivAt
    have hg : HasDerivAt (fun w : ℂ => u * f (w + c * I)) (u * deriv f ((x : ℂ) + c * I)) (x : ℂ) := by
      have := hfx.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const (c * I))
      simpa using this.const_mul u
    have hfne : f ((x : ℂ) + c * I) ≠ 0 := by
      intro h0; have := hslit x hx; rw [h0, mul_zero] at this; exact slitPlane_ne_zero this rfl
    have := (hg.comp_ofReal (z := x)).clog_real (hslit x hx)
    convert this using 1
    rw [logDeriv_apply]; field_simp
  have hcont : ContinuousOn (fun x : ℝ => logDeriv f ((x : ℂ) + c * I)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    have hfne : ∀ x ∈ Icc a b, f ((x : ℂ) + c * I) ≠ 0 := fun x hx h0 => by
      have := hslit x hx; rw [h0, mul_zero] at this; exact slitPlane_ne_zero this rfl
    have hpath : ContinuousOn (fun x : ℝ => (x : ℂ) + c * I) (Icc a b) :=
      (continuous_ofReal.add continuous_const).continuousOn
    have : (fun x : ℝ => logDeriv f ((x : ℂ) + c * I)) =
        fun x : ℝ => deriv f ((x : ℂ) + c * I) / f ((x : ℂ) + c * I) := rfl
    rw [this]
    exact ((hf.deriv hU).continuousOn.comp hpath hseg).div (hf.continuousOn.comp hpath hseg) hfne
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)

/-- **Côté vertical** : `i·∫_a^b f′/f(c + yi) dy = log(u f(c + bi)) − log(u f(c + ai))` sous les mêmes conditions. -/
theorem integral_logDeriv_vertical {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {a b c : ℝ} (hab : a ≤ b) (u : ℂ) (hseg : ∀ y ∈ Icc a b, (c : ℂ) + y * I ∈ U)
    (hslit : ∀ y ∈ Icc a b, u * f ((c : ℂ) + y * I) ∈ slitPlane) :
    I * ∫ y in a..b, logDeriv f ((c : ℂ) + y * I) =
      log (u * f ((c : ℂ) + b * I)) - log (u * f ((c : ℂ) + a * I)) := by
  have hderiv : ∀ y ∈ uIcc a b, HasDerivAt (fun y : ℝ => log (u * f ((c : ℂ) + y * I)))
      (I * logDeriv f ((c : ℂ) + y * I)) y := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    have hyU := hseg y hy
    have hfy : HasDerivAt f (deriv f ((c : ℂ) + y * I)) ((c : ℂ) + y * I) :=
      (hf.differentiableAt (hU.mem_nhds hyU)).hasDerivAt
    have hg : HasDerivAt (fun w : ℂ => u * f (c + w * I)) (u * (deriv f ((c : ℂ) + y * I) * I)) (y : ℂ) := by
      have hlin : HasDerivAt (fun w : ℂ => (c : ℂ) + w * I) I (y : ℂ) := by
        simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (c : ℂ)
      exact (hfy.comp (y : ℂ) hlin).const_mul u
    have hfne : f ((c : ℂ) + y * I) ≠ 0 := by
      intro h0; have := hslit y hy; rw [h0, mul_zero] at this; exact slitPlane_ne_zero this rfl
    have hu : u ≠ 0 := by
      intro h0; have := hslit y hy; rw [h0, zero_mul] at this; exact slitPlane_ne_zero this rfl
    have := (hg.comp_ofReal (z := y)).clog_real (hslit y hy)
    convert this using 1
    rw [logDeriv_apply]; field_simp
  have hcont : ContinuousOn (fun y : ℝ => I * logDeriv f ((c : ℂ) + y * I)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    have hfne : ∀ y ∈ Icc a b, f ((c : ℂ) + y * I) ≠ 0 := fun y hy h0 => by
      have := hslit y hy; rw [h0, mul_zero] at this; exact slitPlane_ne_zero this rfl
    have hpath : ContinuousOn (fun y : ℝ => (c : ℂ) + y * I) (Icc a b) :=
      (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
    have : (fun y : ℝ => I * logDeriv f ((c : ℂ) + y * I)) =
        fun y : ℝ => I * (deriv f ((c : ℂ) + y * I) / f ((c : ℂ) + y * I)) := rfl
    rw [this]
    exact continuousOn_const.mul
      (((hf.deriv hU).continuousOn.comp hpath hseg).div (hf.continuousOn.comp hpath hseg) hfne)
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)

#print axioms integral_logDeriv_horizontal
#print axioms integral_logDeriv_vertical

/-! ## Rectangles du demi-plan `Re > 0` traversant l'axe réel : facteur `sΓℝ(s)` -/

theorem isOpen_rightHalf : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re

theorem Gammaℝ_differentiableAt_of_re_pos {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have h : DifferentiableAt ℂ (fun w => ((Gammaℝ w)⁻¹)⁻¹) s :=
    (differentiable_Gammaℝ_inv s).inv (inv_ne_zero hG)
  simpa only [inv_inv] using h

theorem sGammaFactor_differentiableOn :
    DifferentiableOn ℂ (fun u : ℂ => u * Gammaℝ u) {s : ℂ | 0 < s.re} := fun _ hs =>
  (differentiableAt_id.mul (Gammaℝ_differentiableAt_of_re_pos hs)).differentiableWithinAt

theorem rect_subset_right {z w : ℂ} (hre : z.re ≤ w.re) (hpos : 0 < z.re) :
    [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ {s : ℂ | 0 < s.re} := by
  intro s hs
  rw [mem_reProdIm, uIcc_of_le hre] at hs
  exact lt_of_lt_of_le hpos hs.1.1

/-- **Élimination de Γ, rectangle de `Re > 0`** (il peut traverser l'axe réel et contenir `s = 1`) : sans zéro de `ζ` sur
le bord et `1` hors du bord, l'intégrale de bord de `ξ₁′/ξ₁` est celle de `((1 − s)ζ)′/((1 − s)ζ)`. -/
theorem rectBoundaryIntegral_completedEntire_eq_zetaFactor {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im)
    (hpos : 0 < z.re) (h1 : (1 : ℂ) ∉ rectBoundary z w) (hB : ∀ s ∈ rectBoundary z w, riemannZeta s ≠ 0) :
    rectBoundaryIntegral (logDeriv completedEntire) z w =
      rectBoundaryIntegral (logDeriv (fun s => (1 - s) * riemannZeta s)) z w := by
  set h : ℂ → ℂ := fun s => s * Gammaℝ s with hh
  set k : ℂ → ℂ := fun s => (1 - s) * riemannZeta s with hk
  set V : Set ℂ := {s : ℂ | 0 < s.re} with hV
  set U : Set ℂ := {s : ℂ | 0 < s.re} ∩ {s : ℂ | s ≠ 1} with hU
  have hVo : IsOpen V := isOpen_rightHalf
  have hUo : IsOpen U := isOpen_rightHalf.inter isOpen_ne
  have hdh : DifferentiableOn ℂ h V := sGammaFactor_differentiableOn
  have hdk : DifferentiableOn ℂ k U := fun s hs =>
    (((differentiableAt_const _).sub differentiableAt_id).mul
      (differentiableAt_riemannZeta hs.2)).differentiableWithinAt
  have hh0 : ∀ s ∈ V, h s ≠ 0 := by
    intro s hs
    have hs' : 0 < s.re := hs
    refine mul_ne_zero (fun h0 => ?_) (Gammaℝ_ne_zero_of_re_pos hs')
    rw [h0, zero_re] at hs'; exact lt_irrefl 0 hs'
  have hBV : rectBoundary z w ⊆ V := fun s hs =>
    rect_subset_right hre.le hpos (by
      rw [mem_reProdIm, uIcc_of_le hre.le, uIcc_of_le him.le]
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨h2, ?_⟩; rcases h1 with h1 | h1 <;> rw [h1] <;> simp [him.le]
      · refine ⟨?_, h2⟩; rcases h1 with h1 | h1 <;> rw [h1] <;> simp [hre.le])
  have hBU : rectBoundary z w ⊆ U := fun s hs => ⟨hBV hs, fun h' => h1 (h' ▸ hs)⟩
  have hk0 : ∀ s ∈ rectBoundary z w, k s ≠ 0 := fun s hs =>
    mul_ne_zero (sub_ne_zero.mpr (fun h' => h1 (h' ▸ hs))) (hB s hs)
  have hEq : EqOn (logDeriv completedEntire) (fun s => logDeriv k s + logDeriv h s) (rectBoundary z w) := by
    intro s hs
    have hsU : s ∈ U := hBU hs
    have hev : completedEntire =ᶠ[nhds s] fun t => k t * h t := by
      filter_upwards [hUo.mem_nhds hsU] with t ht
      have ht0 : t ≠ 0 := fun h0 => by
        have h' : 0 < t.re := ht.1
        rw [h0, zero_re] at h'; exact lt_irrefl 0 h'
      rw [completedEntire_eq_zeta_mul' ht0 ht.2 (Gammaℝ_ne_zero_of_re_pos ht.1)]
      simp only [hk, hh]; ring
    have hld : logDeriv completedEntire s = logDeriv (fun t => k t * h t) s := by
      simp only [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    rw [hld, logDeriv_mul s (hk0 s hs) (hh0 s (hBV hs)) (hdk.differentiableAt (hUo.mem_nhds hsU))
      (hdh.differentiableAt (hVo.mem_nhds (hBV hs)))]
  have hcont : ∀ (f : ℂ → ℂ) (W : Set ℂ), IsOpen W → DifferentiableOn ℂ f W → rectBoundary z w ⊆ W →
      (∀ s ∈ rectBoundary z w, f s ≠ 0) → ContinuousOn (logDeriv f) (rectBoundary z w) := by
    intro f W hWo hf hsub hf0
    have : logDeriv f = fun s => deriv f s / f s := rfl
    rw [this]
    exact ((hf.deriv hWo).continuousOn.mono hsub).div (hf.continuousOn.mono hsub) hf0
  have hIk := rectSidesIntegrable_of_continuousOn hre.le him.le (hcont k U hUo hdk hBU hk0)
  have hIh := rectSidesIntegrable_of_continuousOn hre.le him.le
    (hcont h V hVo hdh hBV (fun s hs => hh0 s (hBV hs)))
  rw [rectBoundaryIntegral_congr hre.le him.le hEq, rectBoundaryIntegral_add hIk hIh]
  have hCauchy : rectBoundaryIntegral (logDeriv h) z w = 0 := by
    have hd : DifferentiableOn ℂ (logDeriv h) ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
      have : logDeriv h = fun s => deriv h s / h s := rfl
      rw [this]
      exact (((hdh.deriv hVo).div hdh hh0).mono (rect_subset_right hre.le hpos))
    have hc := integral_boundary_rect_eq_zero_of_differentiableOn (logDeriv h) z w hd
    simpa only [rectBoundaryIntegral, smul_eq_mul] using hc
  rw [hCauchy, add_zero]

#print axioms rectBoundaryIntegral_completedEntire_eq_zetaFactor

end RHV6Fresh
