/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Direct.PairTowers
import RHV3Lean.Objects.ZetaSmoothedUnsmoothingP5

/-!
# RHV6Fresh — la Tour est le terme du zéro dans la formule explicite compilée (destruction de V, 2026-09-26)

Ce module établit,
par théorème, que cet anneau n'est pas une géométrie posée à côté de zêta : c'est la géométrie du
terme `q^ρ / ρ` que le zéro `ρ = β + iT` porte dans la formule explicite de Riemann, compilée dans
la base (`smoothed_riemann_explicit_formula`, `psiRecoveredFromZeros_eq_psi`).

1. La position de Tour est l'argument du terme : `π · towerPosition z q = T log q − φ`, et la partie
   imaginaire du terme vaut `q^β · β · sin(π · towerPosition z q) / (‖ρ‖² cos φ)`
   (`zeroTerm_im_eq_sin_towerPosition`).  Les rayons `C_k` de la Tour sont exactement les points où
   le terme est réel (`zeroTerm_real_iff_ray`, `ray_zeroTerm_real`).
2. L'inversion est la conjugaison du terme : le terme du conjugué est le conjugué du terme, sa partie
   imaginaire est l'opposée (`conjugate_term_eq_conj`, `conjugate_term_im`) ; la somme des deux est
   réelle (`pair_term_real`).  C'est le nombre imaginaire, source de l'inversion, compilé.
3. Là où `β` entre : l'amplitude.  `‖q^ρ/ρ‖ = q^β / ‖ρ‖` (`zeroTerm_norm`) ; pour le miroir,
   `q^(1−β) / ‖ρ*‖` (`mirror_zeroTerm_norm`) ; hors ligne, l'exposant du miroir domine
   (`mirror_amplitude_exponent_dominates`).  Sur la droite les deux exposants sont égaux.
4. La liaison des deux grammaires en forme analytique, compilée dans la base : `ψ(x)` est
   reconstruite depuis les zéros (`liaison_analytic`), et le terme de la Tour est la dérivée du
   terme du zéro dans cette formule (`zeroTerm_is_derivative_of_explicit_term`).

Ce que ces théorèmes établissent : la lecture C_lecture de la seconde Tour est une condition
d'anneau sur le terme du miroir aux deux premiers `p_min(z*)` et `Occ(z*)`, ENTIÈREMENT interne à
`z*`.  La formule explicite compilée ne contraint que la somme de tous les termes, jamais un terme
isolé.  Ce qui reste pour fermer RH est donc précisément : isoler le terme de la paire hors ligne
dans cette somme, c'est-à-dire un énoncé sur `ψ(x) − x` que ni la base ni Mathlib ne contiennent.
-/

namespace RHV6Fresh

open RHV3Lean Complex

/-! ## 0. Le point complexe du zéro et son terme -/

/-- Le support complexe du zéro : `ρ = β + iT`. -/
abbrev zeroPoint (z : TrueZero) : ℂ := z.1.1

theorem zeroPoint_re (z : TrueZero) : (zeroPoint z).re = rZeroRadialPosition z.1 := rfl

theorem zeroPoint_im (z : TrueZero) : (zeroPoint z).im = rZeroHeight z.1 := rfl

theorem zeroPoint_re_pos (z : TrueZero) : 0 < (zeroPoint z).re :=
  thm_zeroRadialPosition_positive z.1

theorem zeroPoint_ne_zero (z : TrueZero) : zeroPoint z ≠ 0 := by
  intro h
  have := zeroPoint_re_pos z
  rw [h] at this
  simp at this

theorem zeroPoint_add_one_ne_zero (z : TrueZero) : zeroPoint z + 1 ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h'
  linarith [zeroPoint_re_pos z]

theorem zeroPoint_ne_neg_one (z : TrueZero) : zeroPoint z ≠ -1 := by
  intro h
  apply zeroPoint_add_one_ne_zero z
  rw [h]; ring

/-- Le terme du zéro dans la formule explicite : `q^ρ / ρ`. -/
noncomputable def zeroTerm (z : TrueZero) (q : ℝ) : ℂ :=
  (q : ℂ) ^ zeroPoint z / zeroPoint z

/-! ## 1. La position de Tour est l'argument du terme -/

theorem pi_mul_towerPosition (z : TrueZero) (q : ℝ) :
    Real.pi * towerPosition z q = rZeroHeight z.1 * Real.log q - (towerMotionOf z).phase := by
  unfold towerPosition
  field_simp [Real.pi_pos.ne']

theorem cpow_zeroPoint_re {z : TrueZero} {q : ℝ} (hq : 0 < q) :
    ((q : ℂ) ^ zeroPoint z).re =
      Real.exp (rZeroRadialPosition z.1 * Real.log q) *
        Real.cos (rZeroHeight z.1 * Real.log q) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'),
    ← Complex.ofReal_log hq.le, Complex.exp_re, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    zeroPoint_re, zeroPoint_im, mul_comm (Real.log q), mul_comm (Real.log q)]

theorem cpow_zeroPoint_im {z : TrueZero} {q : ℝ} (hq : 0 < q) :
    ((q : ℂ) ^ zeroPoint z).im =
      Real.exp (rZeroRadialPosition z.1 * Real.log q) *
        Real.sin (rZeroHeight z.1 * Real.log q) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'),
    ← Complex.ofReal_log hq.le, Complex.exp_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    zeroPoint_re, zeroPoint_im, mul_comm (Real.log q), mul_comm (Real.log q)]

/-- Partie imaginaire du terme : `q^β (β sin θ − T cos θ) / ‖ρ‖²`, `θ = T log q`. -/
theorem zeroTerm_im {z : TrueZero} {q : ℝ} (hq : 0 < q) :
    (zeroTerm z q).im =
      Real.exp (rZeroRadialPosition z.1 * Real.log q) *
        (rZeroRadialPosition z.1 * Real.sin (rZeroHeight z.1 * Real.log q) -
          rZeroHeight z.1 * Real.cos (rZeroHeight z.1 * Real.log q)) /
        Complex.normSq (zeroPoint z) := by
  unfold zeroTerm
  rw [Complex.div_im, cpow_zeroPoint_re hq, cpow_zeroPoint_im hq, zeroPoint_re, zeroPoint_im]
  ring

/-- L'identité de phase : `β sin θ − T cos θ = (β / cos φ) · sin (θ − φ)`, `φ = arctan (T/β)`. -/
theorem phase_identity (z : TrueZero) (θ : ℝ) :
    rZeroRadialPosition z.1 * Real.sin θ - rZeroHeight z.1 * Real.cos θ =
      rZeroRadialPosition z.1 / Real.cos (towerMotionOf z).phase *
        Real.sin (θ - (towerMotionOf z).phase) := by
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  have hcos : 0 < Real.cos (towerMotionOf z).phase := by
    rw [towerMotion_phase]; exact Real.cos_arctan_pos _
  have hsin : Real.sin (towerMotionOf z).phase =
      rZeroHeight z.1 / rZeroRadialPosition z.1 * Real.cos (towerMotionOf z).phase := by
    have ht : Real.tan (towerMotionOf z).phase = rZeroHeight z.1 / rZeroRadialPosition z.1 := by
      rw [towerMotion_phase, Real.tan_arctan]
    rw [Real.tan_eq_sin_div_cos] at ht
    field_simp at ht
    rw [div_mul_eq_mul_div, eq_div_iff hβ.ne']
    linear_combination ht
  rw [Real.sin_sub, hsin]
  field_simp

/-- **La Tour est l'argument du terme** : la partie imaginaire du terme du zéro vaut
`q^β · β · sin(π · towerPosition z q) / (‖ρ‖² cos φ)`. -/
theorem zeroTerm_im_eq_sin_towerPosition {z : TrueZero} {q : ℝ} (hq : 0 < q) :
    (zeroTerm z q).im =
      Real.exp (rZeroRadialPosition z.1 * Real.log q) * rZeroRadialPosition z.1 *
        Real.sin (Real.pi * towerPosition z q) /
        (Complex.normSq (zeroPoint z) * Real.cos (towerMotionOf z).phase) := by
  rw [zeroTerm_im hq, phase_identity z, pi_mul_towerPosition]
  have hcos : 0 < Real.cos (towerMotionOf z).phase := by
    rw [towerMotion_phase]; exact Real.cos_arctan_pos _
  have hN : 0 < Complex.normSq (zeroPoint z) := Complex.normSq_pos.mpr (zeroPoint_ne_zero z)
  field_simp

/-- Le terme est réel exactement quand la position de Tour est entière (sinus nul). -/
theorem zeroTerm_real_iff_sin {z : TrueZero} {q : ℝ} (hq : 0 < q) :
    (zeroTerm z q).im = 0 ↔ Real.sin (Real.pi * towerPosition z q) = 0 := by
  rw [zeroTerm_im_eq_sin_towerPosition hq]
  have hcos : 0 < Real.cos (towerMotionOf z).phase := by
    rw [towerMotion_phase]; exact Real.cos_arctan_pos _
  have hN : 0 < Complex.normSq (zeroPoint z) := Complex.normSq_pos.mpr (zeroPoint_ne_zero z)
  have he : 0 < Real.exp (rZeroRadialPosition z.1 * Real.log q) := Real.exp_pos _
  have hβ : 0 < rZeroRadialPosition z.1 := thm_zeroRadialPosition_positive z.1
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 (mul_pos he hβ).ne'
      · exact h2
    · exact absurd h1 (mul_pos hN hcos).ne'
  · intro h
    rw [h]; simp

/-- La position de Tour du rayon `C_k` est `k`. -/
theorem towerPosition_contactMinusAt (z : TrueZero) (k : ℤ) :
    towerPosition z (contactMinusAt z k) = k := by
  have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
  unfold towerPosition contactMinusAt
  rw [towerMotion_incidence, Real.log_exp]
  field_simp
  ring

/-- **Les rayons de la Tour sont les points réels du terme.** -/
theorem ray_zeroTerm_real (z : TrueZero) (k : ℤ) :
    (zeroTerm z (contactMinusAt z k)).im = 0 := by
  rw [zeroTerm_real_iff_sin (contactMinusAt_positive z k), towerPosition_contactMinusAt,
    mul_comm]
  exact Real.sin_int_mul_pi k

/-- Réciproque : un réel `q > 0` où le terme est réel est un rayon de la Tour. -/
theorem zeroTerm_real_iff_ray {z : TrueZero} {q : ℝ} (hq : 0 < q) :
    (zeroTerm z q).im = 0 ↔ ∃ k : ℤ, q = contactMinusAt z k := by
  constructor
  · intro h
    rw [zeroTerm_real_iff_sin hq, Real.sin_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n, ?_⟩
    have hT : rZeroHeight z.1 ≠ 0 := ne_of_gt z.2
    have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hpos : towerPosition z q = n := by
      apply mul_left_cancel₀ hπ
      linear_combination -hn
    have hlog : Real.log q =
        ((towerMotionOf z).phase + (n : ℝ) * Real.pi) / rZeroHeight z.1 := by
      unfold towerPosition at hpos
      rw [div_eq_iff hπ] at hpos
      rw [eq_div_iff hT]
      linear_combination hpos
    unfold contactMinusAt
    rw [towerMotion_incidence, ← hlog, Real.exp_log hq]
  · rintro ⟨k, rfl⟩
    exact ray_zeroTerm_real z k

/-! ## 2. L'inversion est la conjugaison du terme -/

/-- Le terme du zéro conjugué `ρ̄` est le conjugué du terme de `ρ`. -/
theorem conjugate_term_eq_conj {z : TrueZero} {q : ℝ} (hq : 0 < q) :
    (q : ℂ) ^ (starRingEnd ℂ (zeroPoint z)) / starRingEnd ℂ (zeroPoint z) =
      starRingEnd ℂ (zeroTerm z q) := by
  unfold zeroTerm
  rw [map_div₀, Complex.cpow_conj _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hq.le]; exact Real.pi_pos.ne),
    Complex.conj_ofReal]

/-- L'inversion : la partie imaginaire du terme conjugué est l'opposée. -/
theorem conjugate_term_im {z : TrueZero} {q : ℝ} (hq : 0 < q) :
    ((q : ℂ) ^ (starRingEnd ℂ (zeroPoint z)) / starRingEnd ℂ (zeroPoint z)).im =
      -(zeroTerm z q).im := by
  rw [conjugate_term_eq_conj hq, Complex.conj_im]

/-- La somme des termes du zéro et de son conjugué est réelle : `2 · Re (q^ρ/ρ)`. -/
theorem pair_term_real {z : TrueZero} {q : ℝ} (hq : 0 < q) :
    zeroTerm z q + (q : ℂ) ^ (starRingEnd ℂ (zeroPoint z)) / starRingEnd ℂ (zeroPoint z) =
      ((2 * (zeroTerm z q).re : ℝ) : ℂ) := by
  rw [conjugate_term_eq_conj hq, Complex.add_conj]

/-! ## 3. Là où `β` entre : l'amplitude -/

theorem zeroTerm_norm {z : TrueZero} {q : ℝ} (hq : 0 < q) :
    ‖zeroTerm z q‖ = q ^ rZeroRadialPosition z.1 / ‖zeroPoint z‖ := by
  unfold zeroTerm
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hq, zeroPoint_re]

theorem mirror_zeroTerm_norm {z : TrueZero} {q : ℝ} (hq : 0 < q) :
    ‖zeroTerm (mirrorMember z) q‖ =
      q ^ (1 - rZeroRadialPosition z.1) / ‖zeroPoint (mirrorMember z)‖ := by
  rw [zeroTerm_norm hq, mirrorMember_radial]

/-- Hors ligne, l'exposant d'amplitude du miroir domine celui du zéro original. -/
theorem mirror_amplitude_exponent_dominates {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 < 1 / 2) {q : ℝ} (hq : 1 ≤ q) :
    q ^ rZeroRadialPosition z.1 ≤ q ^ (1 - rZeroRadialPosition z.1) :=
  Real.rpow_le_rpow_of_exponent_le hq (by linarith)

/-- Sur la droite, les deux exposants sont égaux. -/
theorem onLine_amplitude_exponents_equal {z : TrueZero}
    (hβ : rZeroRadialPosition z.1 = 1 / 2) :
    rZeroRadialPosition z.1 = 1 - rZeroRadialPosition z.1 := by
  rw [hβ]; norm_num

/-! ## 4. La liaison analytique compilée dans la base -/

/-- Tout membre est un zéro non trivial au sens de la formule explicite compilée. -/
theorem zeroPoint_isNontrivial (z : TrueZero) : IsNontrivialZetaZero (zeroPoint z) := by
  refine ⟨z.1.2.1, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have h := zeroPoint_re_pos z
    rw [hn] at h
    simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.natCast_re,
      Complex.one_re, Complex.neg_im, Complex.add_im, Complex.natCast_im, Complex.one_im] at h
    norm_num at h
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · intro h
    have h' : (zeroPoint z).re < 1 := thm_zeroRadialPosition_lt_one z.1
    rw [h] at h'
    simp at h'

/-- Le terme du membre dans le canal des zéros de la formule explicite compilée. -/
theorem explicit_term_of_member (z : TrueZero) (x : ℝ) :
    nontrivialZeroResidueTerm x ⟨zeroPoint z, zeroPoint_isNontrivial z⟩ =
      -(zetaZeroMultiplicity (zeroPoint z) : ℂ) * Perron.f x (zeroPoint z) := rfl

/-- **La liaison des deux grammaires, forme analytique compilée** : `ψ` est reconstruite depuis
les zéros (base, `psiRecoveredFromZeros_eq_psi`). -/
theorem liaison_analytic {x : ℝ} (hx : 2 ≤ x) :
    psiRecoveredFromZeros x = (Chebyshev.psi x : ℂ) :=
  psiRecoveredFromZeros_eq_psi hx

/-- Le terme de la Tour est la dérivée en `x` de `x · Perron.f x ρ = x^{ρ+1}/(ρ(ρ+1))`, le terme
lissé du zéro dans la formule explicite compilée. -/
theorem zeroTerm_is_derivative_of_explicit_term (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * Perron.f y (zeroPoint z)) (zeroTerm z x) x := by
  have hd := (hasDerivAt_ofReal_cpow_const' hx.ne' (zeroPoint_ne_neg_one z)).div_const
    (zeroPoint z)
  have hfun : (fun y : ℝ => (y : ℂ) * Perron.f y (zeroPoint z)) =
      fun y : ℝ => (y : ℂ) ^ (zeroPoint z + 1) / (zeroPoint z + 1) / zeroPoint z := by
    funext y
    simp only [Perron.f]
    by_cases hy : (y : ℂ) = 0
    · rw [hy, Complex.zero_cpow (zeroPoint_ne_zero z),
        Complex.zero_cpow (zeroPoint_add_one_ne_zero z)]
      simp
    · rw [Complex.cpow_add _ _ hy, Complex.cpow_one]
      field_simp
  rw [hfun]
  exact hd

/-- La dérivée du terme du membre dans le canal compilé est `−m(ρ) · (terme de la Tour)`. -/
theorem explicit_term_derivative (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ => (y : ℂ) * nontrivialZeroResidueTerm y ⟨zeroPoint z, zeroPoint_isNontrivial z⟩)
      (-(zetaZeroMultiplicity (zeroPoint z) : ℂ) * zeroTerm z x) x := by
  have h := (zeroTerm_is_derivative_of_explicit_term z hx).const_mul
    (-(zetaZeroMultiplicity (zeroPoint z) : ℂ))
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp only [explicit_term_of_member]
  ring

end RHV6Fresh
