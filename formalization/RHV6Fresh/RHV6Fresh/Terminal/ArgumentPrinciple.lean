/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ZetaRealSegment

/-!
# Principe de l'argument sur un rectangle, pour une fonction entière (lemme (2) de la certification)

Mathlib ne contient que les théorèmes de Cauchy sur rectangle et la formule de Cauchy sur disque. On démontre ici,
sans hypothèse ni axiome nouveau :

1. l'intégrale de bord de `1/(z − a)` sur un rectangle contenant `a` dans son intérieur vaut `2πi`
   (`rectBoundaryIntegral_inv_sub`), par les primitives `log(z − a)` et `log(−(z − a))` sur les côtés ;
2. la linéarité de l'intégrale de bord pour des fonctions continues sur le bord ;
3. la factorisation globale `f = Π (z − ρ)^{m_ρ} · g` d'une fonction entière par ses zéros d'ordre fini sur un
   ensemble fini, avec `g` entière et non nulle en chaque `ρ` (`exists_entire_factorization`) ;
4. le **principe de l'argument** : si `f` est entière, sans zéro sur le bord, et si `Z` est l'ensemble de ses zéros dans
   le rectangle ouvert, `∮ f'/f = 2πi Σ_{ρ ∈ Z} ord_ρ f` (`argument_principle_rect`) ;
5. l'instance pour `ξ₁` sur `[−1, 2] × [0, T]` (`completedEntire_argument_principle`) : le membre de droite est le
   comptage de la fenêtre supérieure ouverte avec multiplicités.
-/

namespace RHV6Fresh

open RHV3Lean Complex Set Filter Topology intervalIntegral
open scoped Interval

/-! ## 1. Intégrale de bord de `1/(z − a)` -/

theorem hasDerivAt_affine_re (a : ℂ) (y x : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) + y * I - a) 1 x := by
  have := (((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * I)).sub_const a
  simpa using this

theorem hasDerivAt_affine_im (a : ℂ) (x y : ℝ) :
    HasDerivAt (fun y : ℝ => (x : ℂ) + y * I - a) I y := by
  have := ((((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (x : ℂ)).sub_const a
  simpa using this

theorem continuousOn_inv_affine_re (a : ℂ) (y : ℝ) (hy : y ≠ a.im) (x₀ x₁ : ℝ) :
    IntervalIntegrable (fun x : ℝ => (1 : ℂ) / ((x : ℂ) + y * I - a)) MeasureTheory.volume x₀ x₁ := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
  · exact ((continuous_ofReal.add continuous_const).sub continuous_const).continuousOn
  · intro x _ h
    apply hy
    have := congrArg Complex.im h
    exact sub_eq_zero.mp (by simpa using this)

theorem continuousOn_inv_affine_im (a : ℂ) (x : ℝ) (hx : x ≠ a.re) (y₀ y₁ : ℝ) :
    IntervalIntegrable (fun y : ℝ => (1 : ℂ) / ((x : ℂ) + y * I - a)) MeasureTheory.volume y₀ y₁ := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
  · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).sub continuous_const
      |>.continuousOn
  · intro y _ h
    apply hx
    have := congrArg Complex.re h
    exact sub_eq_zero.mp (by simpa using this)

/-- Côté horizontal (`y ≠ Im a`) : primitive `log(z − a)`. -/
theorem integral_inv_sub_horizontal (a : ℂ) (x₀ x₁ y : ℝ) (hy : y ≠ a.im) :
    ∫ x : ℝ in x₀..x₁, (1 : ℂ) / ((x : ℂ) + y * I - a) =
      log ((x₁ : ℂ) + y * I - a) - log ((x₀ : ℂ) + y * I - a) := by
  apply integral_eq_sub_of_hasDerivAt
  · intro x _
    have hs : (x : ℂ) + y * I - a ∈ slitPlane := by
      rw [mem_slitPlane_iff]; right
      simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      exact sub_ne_zero.mpr hy
    simpa using (hasDerivAt_affine_re a y x).clog_real hs
  · exact continuousOn_inv_affine_re a y hy x₀ x₁

/-- Côté vertical à droite de `a` (`Re a < x`) : primitive `log(z − a)`. -/
theorem integral_inv_sub_vertical_right (a : ℂ) (x y₀ y₁ : ℝ) (hx : a.re < x) :
    I * ∫ y : ℝ in y₀..y₁, (1 : ℂ) / ((x : ℂ) + y * I - a) =
      log ((x : ℂ) + y₁ * I - a) - log ((x : ℂ) + y₀ * I - a) := by
  rw [← integral_const_mul]
  apply integral_eq_sub_of_hasDerivAt
  · intro y _
    have hs : (x : ℂ) + y * I - a ∈ slitPlane := by
      rw [mem_slitPlane_iff]; left
      simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_zero,
        add_zero]
      linarith
    have := (hasDerivAt_affine_im a x y).clog_real hs
    simpa [div_eq_mul_inv, mul_comm] using this
  · exact (continuousOn_inv_affine_im a x hx.ne' y₀ y₁).const_mul I

/-- Côté vertical à gauche de `a` (`x < Re a`) : primitive `log(−(z − a))`. -/
theorem integral_inv_sub_vertical_left (a : ℂ) (x y₀ y₁ : ℝ) (hx : x < a.re) :
    I * ∫ y : ℝ in y₀..y₁, (1 : ℂ) / ((x : ℂ) + y * I - a) =
      log (-((x : ℂ) + y₁ * I - a)) - log (-((x : ℂ) + y₀ * I - a)) := by
  rw [← integral_const_mul]
  apply integral_eq_sub_of_hasDerivAt
  · intro y _
    have hs : -((x : ℂ) + y * I - a) ∈ slitPlane := by
      rw [mem_slitPlane_iff]; left
      simp only [neg_re, sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one,
        sub_zero, add_zero]
      linarith
    have hne : (x : ℂ) + y * I - a ≠ 0 := by
      intro h; apply hx.ne; have := congrArg Complex.re h
      exact sub_eq_zero.mp (by simpa using this)
    have hd : HasDerivAt (fun y : ℝ => -((x : ℂ) + y * I - a)) (-I) y := (hasDerivAt_affine_im a x y).neg
    exact (hd.clog_real hs).congr_deriv (by rw [neg_div_neg_eq, div_eq_mul_one_div])
  · exact (continuousOn_inv_affine_im a x hx.ne y₀ y₁).const_mul I

theorem log_sub_log_neg_of_im_pos {v : ℂ} (hv : 0 < v.im) : log v - log (-v) = (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [log_re]
  · simp only [sub_im, log_im, arg_neg_eq_arg_sub_pi_of_im_pos hv, mul_im, ofReal_re, I_im, mul_one,
      ofReal_im, I_re, mul_zero, add_zero]
    ring

theorem log_neg_sub_log_of_im_neg {u : ℂ} (hu : u.im < 0) : log (-u) - log u = (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [log_re]
  · simp only [sub_im, log_im, arg_neg_eq_arg_add_pi_of_im_neg hu, mul_im, ofReal_re, I_im, mul_one,
      ofReal_im, I_re, mul_zero, add_zero]
    ring

/-- **Formule de Cauchy pour `1/(z − a)` sur le rectangle** : `a` dans le rectangle ouvert ⟹ `∮ dz/(z − a) = 2πi`. -/
theorem rectBoundaryIntegral_inv_sub {z w a : ℂ} (h₁ : z.re < a.re) (h₂ : a.re < w.re) (h₃ : z.im < a.im)
    (h₄ : a.im < w.im) :
    rectBoundaryIntegral (fun s => 1 / (s - a)) z w = 2 * (Real.pi : ℂ) * I := by
  unfold rectBoundaryIntegral
  rw [integral_inv_sub_horizontal a z.re w.re z.im h₃.ne, integral_inv_sub_horizontal a z.re w.re w.im h₄.ne',
    integral_inv_sub_vertical_right a w.re z.im w.im h₂, integral_inv_sub_vertical_left a z.re z.im w.im h₁]
  have hu : ((z.re : ℂ) + z.im * I - a).im < 0 := by
    simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add]
    linarith
  have hv : 0 < ((z.re : ℂ) + w.im * I - a).im := by
    simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add]
    linarith
  have e₁ := log_sub_log_neg_of_im_pos hv
  have e₂ := log_neg_sub_log_of_im_neg hu
  linear_combination e₁ + e₂

/-! ## 2. Linéarité de l'intégrale de bord -/

theorem mem_rectBoundary_bottom {z w : ℂ} (hre : z.re ≤ w.re) {x : ℝ} (hx : x ∈ uIcc z.re w.re) :
    (x : ℂ) + z.im * I ∈ rectBoundary z w := by
  left; rw [uIcc_of_le hre] at hx
  refine ⟨Or.inl ?_, ?_⟩ <;> simpa

theorem mem_rectBoundary_top {z w : ℂ} (hre : z.re ≤ w.re) {x : ℝ} (hx : x ∈ uIcc z.re w.re) :
    (x : ℂ) + w.im * I ∈ rectBoundary z w := by
  left; rw [uIcc_of_le hre] at hx
  refine ⟨Or.inr ?_, ?_⟩ <;> simpa

theorem mem_rectBoundary_right {z w : ℂ} (him : z.im ≤ w.im) {y : ℝ} (hy : y ∈ uIcc z.im w.im) :
    (w.re : ℂ) + y * I ∈ rectBoundary z w := by
  right; rw [uIcc_of_le him] at hy
  refine ⟨Or.inr ?_, ?_⟩ <;> simpa

theorem mem_rectBoundary_left {z w : ℂ} (him : z.im ≤ w.im) {y : ℝ} (hy : y ∈ uIcc z.im w.im) :
    (z.re : ℂ) + y * I ∈ rectBoundary z w := by
  right; rw [uIcc_of_le him] at hy
  refine ⟨Or.inl ?_, ?_⟩ <;> simpa

/-- Les quatre intégrales de côté d'une fonction continue sur le bord existent. -/
structure RectSidesIntegrable (f : ℂ → ℂ) (z w : ℂ) : Prop where
  bottom : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + z.im * I)) MeasureTheory.volume z.re w.re
  top : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + w.im * I)) MeasureTheory.volume z.re w.re
  right : IntervalIntegrable (fun y : ℝ => f ((w.re : ℂ) + y * I)) MeasureTheory.volume z.im w.im
  left : IntervalIntegrable (fun y : ℝ => f ((z.re : ℂ) + y * I)) MeasureTheory.volume z.im w.im

theorem rectSidesIntegrable_of_continuousOn {f : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : ContinuousOn f (rectBoundary z w)) : RectSidesIntegrable f z w where
  bottom := ContinuousOn.intervalIntegrable <| hf.comp
    ((continuous_ofReal.add continuous_const).continuousOn) fun x hx => mem_rectBoundary_bottom hre hx
  top := ContinuousOn.intervalIntegrable <| hf.comp
    ((continuous_ofReal.add continuous_const).continuousOn) fun x hx => mem_rectBoundary_top hre hx
  right := ContinuousOn.intervalIntegrable <| hf.comp
    ((continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn)
    fun y hy => mem_rectBoundary_right him hy
  left := ContinuousOn.intervalIntegrable <| hf.comp
    ((continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn)
    fun y hy => mem_rectBoundary_left him hy

theorem rectBoundaryIntegral_add {f g : ℂ → ℂ} {z w : ℂ} (hf : RectSidesIntegrable f z w)
    (hg : RectSidesIntegrable g z w) :
    rectBoundaryIntegral (fun s => f s + g s) z w = rectBoundaryIntegral f z w + rectBoundaryIntegral g z w := by
  unfold rectBoundaryIntegral
  rw [integral_add hf.bottom hg.bottom, integral_add hf.top hg.top, integral_add hf.right hg.right,
    integral_add hf.left hg.left]
  ring

theorem rectBoundaryIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectBoundaryIntegral (fun s => c * f s) z w = c * rectBoundaryIntegral f z w := by
  unfold rectBoundaryIntegral
  simp only [integral_const_mul]
  ring

theorem rectBoundaryIntegral_congr {f g : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (h : EqOn f g (rectBoundary z w)) : rectBoundaryIntegral f z w = rectBoundaryIntegral g z w := by
  unfold rectBoundaryIntegral
  rw [integral_congr (fun x hx => h (mem_rectBoundary_bottom hre hx)),
    integral_congr (fun x hx => h (mem_rectBoundary_top hre hx)),
    integral_congr (fun y hy => h (mem_rectBoundary_right him hy)),
    integral_congr (fun y hy => h (mem_rectBoundary_left him hy))]

theorem rectBoundaryIntegral_sum {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ) {z w : ℂ}
    (hF : ∀ i ∈ S, RectSidesIntegrable (F i) z w) :
    rectBoundaryIntegral (fun s => ∑ i ∈ S, F i s) z w = ∑ i ∈ S, rectBoundaryIntegral (F i) z w := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [rectBoundaryIntegral]
  | insert a S ha ih =>
    rw [Finset.forall_mem_insert] at hF
    have hsum : RectSidesIntegrable (fun s => ∑ i ∈ S, F i s) z w := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · have h := IntervalIntegrable.sum S fun i hi => (hF.2 i hi).bottom
        rwa [Finset.sum_fn] at h
      · have h := IntervalIntegrable.sum S fun i hi => (hF.2 i hi).top
        rwa [Finset.sum_fn] at h
      · have h := IntervalIntegrable.sum S fun i hi => (hF.2 i hi).right
        rwa [Finset.sum_fn] at h
      · have h := IntervalIntegrable.sum S fun i hi => (hF.2 i hi).left
        rwa [Finset.sum_fn] at h
    simp only [Finset.sum_insert ha]
    rw [rectBoundaryIntegral_add hF.1 hsum, ih hF.2]

/-! ## 3. Factorisation d'une fonction entière par ses zéros d'ordre fini -/

/-- Division par `(z − ρ)^m` : si `f` est entière d'ordre fini `m` en `ρ`, alors `f = (z − ρ)^m · g` avec `g` entière
et `g ρ ≠ 0`. -/
theorem exists_entire_div_pow {f : ℂ → ℂ} (hf : Differentiable ℂ f) {ρ : ℂ} (hne : analyticOrderAt f ρ ≠ ⊤) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ z, f z = (z - ρ) ^ analyticOrderNatAt f ρ * g z) ∧ g ρ ≠ 0 := by
  obtain ⟨h, hh, hh0, hev⟩ := ((hf.analyticAt ρ).analyticOrderNatAt_eq_iff hne).mp rfl
  set m := analyticOrderNatAt f ρ
  classical
  let g : ℂ → ℂ := Function.update (fun z => f z / (z - ρ) ^ m) ρ (h ρ)
  have hg_eq : ∀ z, z ≠ ρ → g z = f z / (z - ρ) ^ m := fun z hz => Function.update_of_ne hz _ _
  have hgρ : g ρ = h ρ := Function.update_self _ _ _
  -- g coïncide avec h au voisinage de ρ
  have hgh : g =ᶠ[𝓝 ρ] h := by
    filter_upwards [hev] with z hz
    by_cases hzρ : z = ρ
    · rw [hzρ, hgρ]
    · rw [hg_eq z hzρ, hz, smul_eq_mul, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.mpr hzρ))]
  refine ⟨g, ?_, ?_, by rw [hgρ]; exact hh0⟩
  · intro z
    by_cases hzρ : z = ρ
    · rw [hzρ]
      exact hh.differentiableAt.congr_of_eventuallyEq hgh
    · have hopen : {s : ℂ | s ≠ ρ} ∈ 𝓝 z := isOpen_ne.mem_nhds hzρ
      have hd : DifferentiableAt ℂ (fun s => f s / (s - ρ) ^ m) z :=
        (hf z).div ((differentiableAt_id.sub_const ρ).pow m) (pow_ne_zero _ (sub_ne_zero.mpr hzρ))
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [hopen] with s hs
      exact hg_eq s hs
  · intro z
    by_cases hzρ : z = ρ
    · rw [hzρ, hgρ]
      have := hev.self_of_nhds
      rw [this, smul_eq_mul]
    · rw [hg_eq z hzρ, mul_div_cancel₀ _ (pow_ne_zero _ (sub_ne_zero.mpr hzρ))]

/-- Transfert de l'ordre : si `f = (z − ρ₀)^m · f₁` partout et `ρ ≠ ρ₀`, les ordres de `f` et `f₁` en `ρ` coïncident. -/
theorem analyticOrderAt_eq_of_pow_mul {f f₁ : ℂ → ℂ} (hf₁ : Differentiable ℂ f₁) {ρ₀ : ℂ} {m : ℕ}
    (hfac : ∀ z, f z = (z - ρ₀) ^ m * f₁ z) {ρ : ℂ} (hρ : ρ ≠ ρ₀) :
    analyticOrderAt f ρ = analyticOrderAt f₁ ρ := by
  have hpow : AnalyticAt ℂ (fun z : ℂ => (z - ρ₀) ^ m) ρ := (analyticAt_id.sub analyticAt_const).pow m
  have h0 : analyticOrderAt (fun z : ℂ => (z - ρ₀) ^ m) ρ = 0 :=
    hpow.analyticOrderAt_eq_zero.mpr (pow_ne_zero _ (sub_ne_zero.mpr hρ))
  have hfun : f = (fun z => (z - ρ₀) ^ m) * f₁ := funext hfac
  rw [hfun, analyticOrderAt_mul hpow (hf₁.analyticAt ρ), h0, zero_add]

/-- **Factorisation globale** : `f` entière, `Z` fini, ordres finis sur `Z` ⟹ `f = Π_{ρ ∈ Z} (z − ρ)^{ord_ρ f} · g` avec
`g` entière et `g ρ ≠ 0` pour tout `ρ ∈ Z`. -/
theorem exists_entire_factorization (Z : Finset ℂ) :
    ∀ f : ℂ → ℂ, Differentiable ℂ f → (∀ ρ ∈ Z, analyticOrderAt f ρ ≠ ⊤) →
      ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
        (∀ z, f z = (∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ) * g z) ∧ ∀ ρ ∈ Z, g ρ ≠ 0 := by
  classical
  induction Z using Finset.induction_on with
  | empty => intro f hf _; exact ⟨f, hf, fun z => by simp, fun ρ h => absurd h (Finset.notMem_empty ρ)⟩
  | insert ρ₀ Z hρ₀ ih =>
    intro f hf hne
    rw [Finset.forall_mem_insert] at hne
    obtain ⟨f₁, hf₁, hfac, hf₁ρ₀⟩ := exists_entire_div_pow hf hne.1
    have hord : ∀ ρ ∈ Z, analyticOrderAt f ρ = analyticOrderAt f₁ ρ := fun ρ hρ =>
      analyticOrderAt_eq_of_pow_mul hf₁ hfac (fun h => hρ₀ (h ▸ hρ))
    obtain ⟨g, hg, hgfac, hg0⟩ := ih f₁ hf₁ (fun ρ hρ => (hord ρ hρ) ▸ hne.2 ρ hρ)
    refine ⟨g, hg, fun z => ?_, ?_⟩
    · rw [Finset.prod_insert hρ₀, mul_assoc, hfac z, hgfac z]
      congr 2
      apply Finset.prod_congr rfl
      intro ρ hρ
      unfold analyticOrderNatAt
      rw [hord ρ hρ]
    · intro ρ hρ
      rw [Finset.mem_insert] at hρ
      rcases hρ with rfl | hρ
      · intro h
        apply hf₁ρ₀
        rw [hgfac ρ, h, mul_zero]
      · exact hg0 ρ hρ

/-! ## 4. Le principe de l'argument -/

theorem logDeriv_sub_const (ρ s : ℂ) : logDeriv (fun z : ℂ => z - ρ) s = 1 / (s - ρ) := by
  rw [logDeriv_apply]
  have : deriv (fun z : ℂ => z - ρ) s = 1 := by
    rw [deriv_sub_const]; exact deriv_id s
  rw [this]

/-- Décomposition de la dérivée logarithmique sur la factorisation, en tout point où `f ≠ 0`. -/
theorem logDeriv_factorization {f g : ℂ → ℂ} (hg : Differentiable ℂ g) (Z : Finset ℂ) (m : ℂ → ℕ)
    (hfac : ∀ z, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * g z) {s : ℂ} (hs : f s ≠ 0) :
    logDeriv f s = (∑ ρ ∈ Z, (m ρ : ℂ) * (1 / (s - ρ))) + logDeriv g s := by
  have hfun : f = fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * g z := funext hfac
  have hs' := hs
  rw [hfac s] at hs'
  have hP : (∏ ρ ∈ Z, (s - ρ) ^ m ρ) ≠ 0 := left_ne_zero_of_mul hs'
  have hgs : g s ≠ 0 := right_ne_zero_of_mul hs'
  have hPd : DifferentiableAt ℂ (fun z => ∏ ρ ∈ Z, (z - ρ) ^ m ρ) s := by
    have e : (fun z => ∏ ρ ∈ Z, (z - ρ) ^ m ρ) = ∏ ρ ∈ Z, (fun z : ℂ => (z - ρ) ^ m ρ) := by
      ext z; simp [Finset.prod_apply]
    rw [e]
    exact DifferentiableAt.finset_prod fun ρ _ => (differentiableAt_id.sub_const ρ).pow _
  rw [hfun, logDeriv_mul s hP hgs hPd (hg s)]
  congr 1
  rw [Finset.prod_ne_zero_iff] at hP
  rw [logDeriv_prod hP (fun ρ _ => (differentiableAt_id.sub_const ρ).pow _)]
  apply Finset.sum_congr rfl
  intro ρ _
  have hd : DifferentiableAt ℂ (fun z : ℂ => z - ρ) s := differentiableAt_id.sub_const ρ
  rw [logDeriv_fun_pow hd, logDeriv_sub_const]

/-- Rectangle fermé = rectangle ouvert ∪ bord. -/
theorem mem_openRect_or_rectBoundary {z w s : ℂ} (hs : s ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]])
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) :
    (s.re ∈ Ioo z.re w.re ∧ s.im ∈ Ioo z.im w.im) ∨ s ∈ rectBoundary z w := by
  rw [mem_reProdIm, uIcc_of_le hre, uIcc_of_le him] at hs
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hs
  by_cases hr : s.re ∈ Ioo z.re w.re
  · by_cases hi : s.im ∈ Ioo z.im w.im
    · exact Or.inl ⟨hr, hi⟩
    · right; left
      refine ⟨?_, ⟨h1, h2⟩⟩
      rw [mem_Ioo, not_and_or, not_lt, not_lt] at hi
      rcases hi with hi | hi
      · exact Or.inl (le_antisymm hi h3)
      · exact Or.inr (le_antisymm h4 hi)
  · right; right
    refine ⟨?_, ⟨h3, h4⟩⟩
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hr
    rcases hr with hr | hr
    · exact Or.inl (le_antisymm hr h1)
    · exact Or.inr (le_antisymm h2 hr)

/-- **Principe de l'argument sur un rectangle** (fonction entière, sans zéro sur le bord, `Z` = ses zéros dans le
rectangle ouvert, tous d'ordre fini) : `∮ f'/f = 2πi · Σ_{ρ ∈ Z} ord_ρ f`. -/
theorem argument_principle_rect (f : ℂ → ℂ) (hf : Differentiable ℂ f) {z w : ℂ} (hre : z.re < w.re)
    (him : z.im < w.im) (Z : Finset ℂ)
    (hZ : ∀ s, s ∈ Z ↔ (f s = 0 ∧ s.re ∈ Ioo z.re w.re ∧ s.im ∈ Ioo z.im w.im))
    (hne : ∀ ρ ∈ Z, analyticOrderAt f ρ ≠ ⊤) (hB : ∀ s ∈ rectBoundary z w, f s ≠ 0) :
    rectBoundaryIntegral (logDeriv f) z w = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) := by
  obtain ⟨g, hg, hfac, hg0⟩ := exists_entire_factorization Z f hf hne
  set m : ℂ → ℕ := fun ρ => analyticOrderNatAt f ρ with hm
  -- g ne s'annule pas sur le rectangle fermé
  have hg_ne : ∀ s ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], g s ≠ 0 := by
    intro s hs
    rcases mem_openRect_or_rectBoundary hs hre.le him.le with h | h
    · by_cases hsZ : s ∈ Z
      · exact hg0 s hsZ
      · have hfs : f s ≠ 0 := fun h0 => hsZ ((hZ s).mpr ⟨h0, h.1, h.2⟩)
        intro h0; apply hfs; rw [hfac s, h0, mul_zero]
    · have hfs := hB s h
      intro h0; apply hfs; rw [hfac s, h0, mul_zero]
  -- ∮ g'/g = 0 (Cauchy)
  have hCauchy : rectBoundaryIntegral (logDeriv g) z w = 0 := by
    have hd : DifferentiableOn ℂ (logDeriv g) ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
      have : logDeriv g = fun s => deriv g s / g s := rfl
      rw [this]
      exact (hg.deriv.differentiableOn).div hg.differentiableOn hg_ne
    have h := integral_boundary_rect_eq_zero_of_differentiableOn (logDeriv g) z w hd
    simpa only [rectBoundaryIntegral, smul_eq_mul] using h
  -- continuité sur le bord
  have hgB : ContinuousOn (logDeriv g) (rectBoundary z w) := by
    have : logDeriv g = fun s => deriv g s / g s := rfl
    rw [this]
    refine ContinuousOn.div hg.deriv.continuous.continuousOn hg.continuous.continuousOn ?_
    intro s hs
    apply hg_ne
    rw [mem_reProdIm, uIcc_of_le hre.le, uIcc_of_le him.le]
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨h2, ?_⟩
      rcases h1 with h1 | h1 <;> rw [h1] <;> simp [him.le]
    · refine ⟨?_, h2⟩
      rcases h1 with h1 | h1 <;> rw [h1] <;> simp [hre.le]
  have hterm : ∀ ρ ∈ Z, ContinuousOn (fun s : ℂ => (m ρ : ℂ) * (1 / (s - ρ))) (rectBoundary z w) := by
    intro ρ hρ
    obtain ⟨-, hr, hi⟩ := (hZ ρ).mp hρ
    refine continuousOn_const.mul (continuousOn_const.div (continuous_id.sub continuous_const).continuousOn ?_)
    intro s hs h0
    have hsρ : s = ρ := sub_eq_zero.mp h0
    rw [hsρ] at hs
    rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩
    · rcases h1 with h1 | h1
      · exact hi.1.ne' h1
      · exact hi.2.ne h1
    · rcases h1 with h1 | h1
      · exact hr.1.ne' h1
      · exact hr.2.ne h1
  -- sur le bord, logDeriv f = Σ m_ρ/(s − ρ) + logDeriv g
  have hEq : EqOn (logDeriv f) (fun s => (∑ ρ ∈ Z, (m ρ : ℂ) * (1 / (s - ρ))) + logDeriv g s)
      (rectBoundary z w) := fun s hs => logDeriv_factorization hg Z m hfac (hB s hs)
  rw [rectBoundaryIntegral_congr hre.le him.le hEq]
  rw [rectBoundaryIntegral_add
    (rectSidesIntegrable_of_continuousOn hre.le him.le (continuousOn_finset_sum Z fun ρ hρ => hterm ρ hρ))
    (rectSidesIntegrable_of_continuousOn hre.le him.le hgB), hCauchy, add_zero]
  rw [rectBoundaryIntegral_sum Z (fun ρ s => (m ρ : ℂ) * (1 / (s - ρ)))
    (fun ρ hρ => rectSidesIntegrable_of_continuousOn hre.le him.le (hterm ρ hρ))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  obtain ⟨-, hr, hi⟩ := (hZ ρ).mp hρ
  rw [rectBoundaryIntegral_const_mul, rectBoundaryIntegral_inv_sub hr.1 hr.2 hi.1 hi.2]
  ring

/-! ## 5. Instance pour `ξ₁` sur `[−1, 2] × [0, T]` -/

/-- `ξ₁` est d'ordre fini en tout point (elle n'est pas identiquement nulle : `ξ₁(0) = −1`). -/
theorem completedEntire_analyticOrderAt_ne_top (ρ : ℂ) : analyticOrderAt completedEntire ρ ≠ ⊤ := by
  have h0 : analyticOrderAt completedEntire 0 ≠ ⊤ := by
    rw [(differentiable_completedEntire.analyticAt 0).analyticOrderAt_eq_zero.mpr
      (by rw [completedEntire_zero]; norm_num)]
    exact WithTop.zero_ne_top
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (U := univ)
    (fun s _ => differentiable_completedEntire.analyticAt s) isPreconnected_univ (mem_univ 0) (mem_univ ρ) h0

/-- **Lemme (2) de la certification** : principe de l'argument pour `ξ₁` sur `[−1, 2] × [0, T]`, sans zéro sur le
bord : `(2πi)⁻¹ ∮ ξ₁'/ξ₁ = Σ_{ρ ∈ fenêtre supérieure ouverte} m_ρ` (multiplicités de `ζ`). -/
theorem completedEntire_argument_principle (T : ℝ) (hT : 0 < T)
    (hB : ∀ s ∈ rectBoundary (-1 : ℂ) (2 + T * I), completedEntire s ≠ 0) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * rectBoundaryIntegral (logDeriv completedEntire) (-1) (2 + T * I) =
      ((∑ ρ ∈ upperWindowOpen T, zetaZeroMultiplicity ρ : ℕ) : ℂ) := by
  have hre : (-1 : ℂ).re < (2 + T * I).re := by simp; norm_num
  have him : (-1 : ℂ).im < (2 + T * I).im := by simpa using hT
  have hZ : ∀ s, s ∈ upperWindowOpen T ↔
      (completedEntire s = 0 ∧ s.re ∈ Ioo (-1 : ℂ).re (2 + T * I).re ∧
        s.im ∈ Ioo (-1 : ℂ).im (2 + T * I).im) := by
    intro s
    rw [← completedEntire_zero_openRect_iff]
    simp only [neg_re, one_re, add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_zero, add_zero, neg_im, one_im, neg_zero, add_im, im_ofNat, mul_im, zero_add, mem_Ioo]
    tauto
  have h := argument_principle_rect completedEntire differentiable_completedEntire hre him (upperWindowOpen T)
    hZ (fun ρ _ => completedEntire_analyticOrderAt_ne_top ρ) hB
  rw [h]
  have h2π : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ h2π, one_mul]
  push_cast
  apply Finset.sum_congr rfl
  intro ρ hρ
  obtain ⟨hnt, him, -⟩ := mem_upperWindowOpen.mp hρ
  rw [completedEntire_multiplicity hnt.1 him.ne']

#print axioms rectBoundaryIntegral_inv_sub
#print axioms exists_entire_factorization
#print axioms argument_principle_rect
#print axioms completedEntire_argument_principle

end RHV6Fresh
