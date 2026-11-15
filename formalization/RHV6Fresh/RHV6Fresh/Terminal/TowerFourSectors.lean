/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.LocalFourSectors
import RHV6Fresh.Terminal.RadialSlope

/-!
# RHV6Fresh — table de symétrie d'une Tour entière (auteur, 2026-10-03, contre-vérification de `LocalFourSectors`)

`LocalFourSectors` ne classait qu'un déplacement recentré d'une paire de membres ; il ne portait ni sur les contacts,
ni sur les rayons, ni sur l'ordre d'une Tour. Ce fichier calcule la symétrie de la Tour elle-même.

Tour d'un membre `ρ = 1/2 + d + iT`, en coordonnée arithmétique `u = log x` : le terme `x^ρ/ρ` ramené à l'échelle
critique `√x` est la courbe `u ↦ a·e^{d u}·e^{i(T u − φ)}`, `a = 1/‖ρ‖`, `φ = arg ρ` (`rescaledTower_eq`). Contacts
(courbe réelle) en `u_k = (φ + kπ)/T`. Les deux axes passent par le centre (l'origine) : axe arithmétique (le réel,
porteur des contacts) et axe critique (l'imaginaire).

* **Les trois transformations, exactement** (§1) : opposition centrale = avance d'un demi-tour, à un facteur
  `e^{dπ/T}` près (`towerCurve_central`) ; réflexion par l'axe arithmétique = lecture à rebours `u ↦ 2φ/T − u`, à un
  facteur `e^{d(2u − 2φ/T)}` près (`towerCurve_arith_reflect`) ; réflexion par l'axe critique = lecture à rebours
  `u ↦ (2φ+π)/T − u`, même forme (`towerCurve_crit_reflect`). Indices des contacts : `k ↦ k + 1`, `k ↦ −k`,
  `k ↦ 1 − k` (`contact_index_rules`).
* **Symétrie à quatre secteurs de la Tour entière ⟺ en ligne** (§2) : la Tour, comme ensemble, est invariante par
  l'opposition centrale, par la réflexion arithmétique, par la réflexion critique, chacune ⟺ `d = 0`
  (`tower_central_invariant_iff`, `tower_arith_invariant_iff`, `tower_crit_invariant_iff`). Hors ligne : aucune des
  trois. Dans le plan brut (sans l'échelle `√x`), le même énoncé porte sur `β > 0` : aucune Tour n'y a ces symétries
  (`raw_tower_not_centrally_invariant`).
* **Ordre et orientation** (§3) : seules l'opposition centrale et les rotations conservent le sens de lecture
  arithmétique ; les deux réflexions renversent l'ordre (`reflection_reverses_order`) ; lue dans le sens arithmétique,
  l'image réfléchie est la Tour du membre conjugué, de hauteur `−T` (`reflection_forward_is_conjugate`) ; hors ligne,
  la réflexion arithmétique échange la Tour avec une Tour de profondeur opposée, lue à rebours
  (`arith_reflect_exchanges_depth`).

Borne : symétrie géométrique de la Tour en ligne, orientation arithmétique privilégiée (une seule symétrie,
l'opposition centrale, conserve l'ordre des premiers). La symétrie à quatre secteurs est un certificat de la position
radiale du membre donné, du même ordre que l'amplitude plate à l'échelle `√x` (`rescaled_amplitude_flat_iff`) ; vraie
pour les membres de zêta en ligne, fausse pour ceux du monde décalé ; elle ne fixe pas la Tour suivante. Aucun
`sorry`, aucun axiome, aucune prémisse.
-/

namespace RHV6Fresh

open Complex RHV3Lean

/-- **Tour en coordonnée arithmétique** `u = log x` : `a·e^{d u}·e^{i(T u − φ)}`. -/
noncomputable def towerCurve (d T φ a u : ℝ) : ℂ :=
  ((a * Real.exp (d * u) : ℝ) : ℂ) * Complex.exp (((T * u - φ : ℝ) : ℂ) * I)

theorem towerCurve_norm (d T φ a u : ℝ) (ha : 0 < a) : ‖towerCurve d T φ a u‖ = a * Real.exp (d * u) := by
  unfold towerCurve
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

/-- Forme polaire : `x^{−1/2}·x^ρ/ρ` en `x = e^u`, pour tout point `ρ ≠ 0`. -/
theorem curve_of_point (ρ : ℂ) (hρ0 : ρ ≠ 0) (u : ℝ) :
    ((Real.exp (-(u / 2)) : ℝ) : ℂ) * (Complex.exp (u * ρ) / ρ) =
      towerCurve (ρ.re - 1 / 2) ρ.im (Complex.arg ρ) (1 / ‖ρ‖) u := by
  have hr : (‖ρ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hρ0)
  have he : Complex.exp ((Complex.arg ρ : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  have hpol : (‖ρ‖ : ℂ) * Complex.exp ((Complex.arg ρ : ℂ) * I) = ρ := Complex.norm_mul_exp_arg_mul_I ρ
  have key : ((Real.exp (-(u / 2)) : ℝ) : ℂ) * Complex.exp (u * ρ) =
      ((Real.exp ((ρ.re - 1 / 2) * u) : ℝ) : ℂ) * Complex.exp (((ρ.im * u : ℝ) : ℂ) * I) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    conv_lhs => rw [← Complex.re_add_im ρ]
    push_cast; ring
  have hrot : Complex.exp (((ρ.im * u : ℝ) : ℂ) * I) =
      Complex.exp (((ρ.im * u - Complex.arg ρ : ℝ) : ℂ) * I) * Complex.exp ((Complex.arg ρ : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  unfold towerCurve
  calc ((Real.exp (-(u / 2)) : ℝ) : ℂ) * (Complex.exp (u * ρ) / ρ)
      = (((Real.exp (-(u / 2)) : ℝ) : ℂ) * Complex.exp (u * ρ)) / ρ := by ring
    _ = (((Real.exp ((ρ.re - 1 / 2) * u) : ℝ) : ℂ) *
          Complex.exp (((ρ.im * u - Complex.arg ρ : ℝ) : ℂ) * I) * Complex.exp ((Complex.arg ρ : ℂ) * I)) /
          ((‖ρ‖ : ℂ) * Complex.exp ((Complex.arg ρ : ℂ) * I)) := by rw [hpol, key, hrot, mul_assoc]
    _ = _ := by push_cast; field_simp

/-- **Lien au terme du membre** : `x^{−1/2}·x^ρ/ρ` en `x = e^u` est la courbe de profondeur `β − 1/2`. -/
theorem rescaledTower_eq (z : TrueZero) (u : ℝ) :
    ((Real.exp (-(u / 2)) : ℝ) : ℂ) * zeroTerm z (Real.exp u) =
      towerCurve (rZeroRadialPosition z.1 - 1 / 2) (rZeroHeight z.1) (Complex.arg (zeroPoint z))
        (1 / ‖zeroPoint z‖) u := by
  unfold zeroTerm
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
  exact curve_of_point (zeroPoint z) (zeroPoint_ne_zero z) u

/-! ## 1. Les trois transformations, exactement -/

/-- **Opposition centrale = avance d'un demi-tour**, au facteur `e^{dπ/T}` près. -/
theorem towerCurve_central (d T φ a u : ℝ) (hT : T ≠ 0) :
    towerCurve d T φ a (u + Real.pi / T) =
      -(((Real.exp (d * Real.pi / T)) : ℝ) : ℂ) * towerCurve d T φ a u := by
  unfold towerCurve
  have h1 : a * Real.exp (d * (u + Real.pi / T)) = Real.exp (d * Real.pi / T) * (a * Real.exp (d * u)) := by
    rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hθ : T * (u + Real.pi / T) - φ = (T * u - φ) + Real.pi := by field_simp; ring
  rw [h1, hθ, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I, Complex.ofReal_mul]
  ring

/-- **Réflexion par l'axe arithmétique = lecture à rebours** `u ↦ 2φ/T − u`, au facteur `e^{d(2u − 2φ/T)}` près. -/
theorem towerCurve_arith_reflect (d T φ a u : ℝ) (hT : T ≠ 0) :
    (starRingEnd ℂ) (towerCurve d T φ a u) =
      ((Real.exp (d * (2 * u - 2 * φ / T)) : ℝ) : ℂ) * towerCurve d T φ a (2 * φ / T - u) := by
  unfold towerCurve
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hθ : T * (2 * φ / T - u) - φ = -(T * u - φ) := by field_simp; ring
  have hamp : Real.exp (d * (2 * u - 2 * φ / T)) * (a * Real.exp (d * (2 * φ / T - u))) = a * Real.exp (d * u) := by
    rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  rw [hθ, ← mul_assoc, ← Complex.ofReal_mul, hamp]
  congr 2; push_cast; ring

/-- **Réflexion par l'axe critique = lecture à rebours** `u ↦ (2φ + π)/T − u`, même forme. -/
theorem towerCurve_crit_reflect (d T φ a u : ℝ) (hT : T ≠ 0) :
    -(starRingEnd ℂ) (towerCurve d T φ a u) =
      ((Real.exp (d * (2 * u - (2 * φ + Real.pi) / T)) : ℝ) : ℂ) *
        towerCurve d T φ a ((2 * φ + Real.pi) / T - u) := by
  have hc : (2 * φ + Real.pi) / T - u = (2 * φ / T - u) + Real.pi / T := by field_simp; ring
  rw [hc, towerCurve_central d T φ a _ hT, towerCurve_arith_reflect d T φ a u hT]
  have : Real.exp (d * (2 * u - (2 * φ + Real.pi) / T)) * Real.exp (d * Real.pi / T) =
      Real.exp (d * (2 * u - 2 * φ / T)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [← this]; push_cast; ring

/-- **Règles d'indice des contacts** `u_k = (φ + kπ)/T` : centrale `k ↦ k + 1`, arithmétique `k ↦ −k`, critique
`k ↦ 1 − k`. -/
theorem contact_index_rules (T φ : ℝ) (k : ℤ) (hT : T ≠ 0) :
    (φ + k * Real.pi) / T + Real.pi / T = (φ + ((k + 1 : ℤ) : ℝ) * Real.pi) / T ∧
      2 * φ / T - (φ + k * Real.pi) / T = (φ + ((-k : ℤ) : ℝ) * Real.pi) / T ∧
      (2 * φ + Real.pi) / T - (φ + k * Real.pi) / T = (φ + ((1 - k : ℤ) : ℝ) * Real.pi) / T := by
  refine ⟨?_, ?_, ?_⟩ <;> push_cast <;> field_simp <;> ring

/-- Les contacts sont sur l'axe arithmétique : `(−1)^k a e^{d u_k}`. -/
theorem towerCurve_contact (d T φ a : ℝ) (k : ℤ) (hT : T ≠ 0) :
    towerCurve d T φ a ((φ + k * Real.pi) / T) =
      ((a * Real.exp (d * ((φ + k * Real.pi) / T)) : ℝ) : ℂ) * (-1) ^ k := by
  unfold towerCurve
  congr 1
  have hθ : T * ((φ + k * Real.pi) / T) - φ = k * Real.pi := by field_simp; ring
  rw [hθ, Complex.ofReal_mul, Complex.ofReal_intCast, mul_assoc, Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-! ## 2. Symétrie à quatre secteurs de la Tour entière ⟺ en ligne -/

private theorem towerCurve_ne_zero (d T φ a u : ℝ) (ha : 0 < a) : towerCurve d T φ a u ≠ 0 := by
  intro h
  have := towerCurve_norm d T φ a u ha
  rw [h, norm_zero] at this
  exact (by positivity : (0:ℝ) < a * Real.exp (d * u)).ne this

/-- Égalité des modules hors ligne ⟹ même point de lecture. -/
private theorem same_norm_same_u {d T φ a u u' : ℝ} (ha : 0 < a) (hd : d ≠ 0)
    (h : ‖towerCurve d T φ a u'‖ = ‖towerCurve d T φ a u‖) : u' = u := by
  rw [towerCurve_norm _ _ _ _ _ ha, towerCurve_norm _ _ _ _ _ ha] at h
  have := mul_left_cancel₀ ha.ne' h
  have := Real.exp_injective this
  exact mul_left_cancel₀ hd this

/-- **Opposition centrale** : la Tour est invariante ⟺ `d = 0`. -/
theorem tower_central_invariant_iff (d T φ a : ℝ) (ha : 0 < a) (hT : T ≠ 0) :
    (∀ u, ∃ u', towerCurve d T φ a u' = -towerCurve d T φ a u) ↔ d = 0 := by
  constructor
  · intro h
    by_contra hd
    obtain ⟨u', hu'⟩ := h 0
    have e := same_norm_same_u (u' := u') (u := 0) ha hd (by rw [hu', norm_neg])
    rw [e] at hu'
    have h2 : (2 : ℂ) * towerCurve d T φ a 0 = 0 := by linear_combination hu'
    exact towerCurve_ne_zero d T φ a 0 ha ((mul_eq_zero.1 h2).resolve_left two_ne_zero)
  · rintro rfl u
    exact ⟨u + Real.pi / T, by rw [towerCurve_central _ _ _ _ _ hT]; simp⟩

/-- **Réflexion arithmétique** : la Tour est invariante ⟺ `d = 0`. -/
theorem tower_arith_invariant_iff (d T φ a : ℝ) (ha : 0 < a) (hT : T ≠ 0) :
    (∀ u, ∃ u', towerCurve d T φ a u' = (starRingEnd ℂ) (towerCurve d T φ a u)) ↔ d = 0 := by
  constructor
  · intro h
    by_contra hd
    obtain ⟨u', hu'⟩ := h ((φ + Real.pi / 2) / T)
    have e := same_norm_same_u (u' := u') (u := (φ + Real.pi / 2) / T) ha hd (by rw [hu', Complex.norm_conj])
    rw [e] at hu'
    have hi : (towerCurve d T φ a ((φ + Real.pi / 2) / T)).im = 0 := by
      have := congrArg Complex.im hu'; rw [Complex.conj_im] at this; linarith
    have hv : towerCurve d T φ a ((φ + Real.pi / 2) / T) =
        ((a * Real.exp (d * ((φ + Real.pi / 2) / T))) : ℝ) * I := by
      unfold towerCurve
      have hθ : T * ((φ + Real.pi / 2) / T) - φ = Real.pi / 2 := by field_simp; ring
      rw [hθ]; push_cast; rw [Complex.exp_pi_div_two_mul_I]
    rw [hv, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at hi
    have : (0:ℝ) < a * Real.exp (d * ((φ + Real.pi / 2) / T)) := by positivity
    nlinarith
  · rintro rfl u
    exact ⟨2 * φ / T - u, by rw [towerCurve_arith_reflect _ _ _ _ _ hT]; simp⟩

/-- **Réflexion critique** : la Tour est invariante ⟺ `d = 0`. -/
theorem tower_crit_invariant_iff (d T φ a : ℝ) (ha : 0 < a) (hT : T ≠ 0) :
    (∀ u, ∃ u', towerCurve d T φ a u' = -(starRingEnd ℂ) (towerCurve d T φ a u)) ↔ d = 0 := by
  constructor
  · intro h
    by_contra hd
    obtain ⟨u', hu'⟩ := h (φ / T)
    have e := same_norm_same_u (u' := u') (u := φ / T) ha hd (by rw [hu', norm_neg, Complex.norm_conj])
    rw [e] at hu'
    have hr : (towerCurve d T φ a (φ / T)).re = 0 := by
      have := congrArg Complex.re hu'; rw [Complex.neg_re, Complex.conj_re] at this; linarith
    have hv : towerCurve d T φ a (φ / T) = ((a * Real.exp (d * (φ / T))) : ℝ) := by
      unfold towerCurve
      have hθ : T * (φ / T) - φ = 0 := by field_simp; ring
      rw [hθ, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [hv, Complex.ofReal_re] at hr
    exact (by positivity : (0:ℝ) < a * Real.exp (d * (φ / T))).ne' hr
  · rintro rfl u
    exact ⟨(2 * φ + Real.pi) / T - u, by rw [towerCurve_crit_reflect _ _ _ _ _ hT]; simp⟩

/-- **Plan brut** : le terme `x^ρ/ρ` d'un membre (profondeur `β > 0`) n'est jamais invariant par l'opposition
centrale ; la symétrie n'apparaît qu'à l'échelle critique `√x`. -/
theorem raw_tower_not_centrally_invariant (β T φ a : ℝ) (hβ : 0 < β) (ha : 0 < a) (hT : T ≠ 0) :
    ¬ ∀ u, ∃ u', towerCurve β T φ a u' = -towerCurve β T φ a u := by
  rw [tower_central_invariant_iff β T φ a ha hT]; exact hβ.ne'

/-! ## 3. Ordre et orientation -/

/-- **Les réflexions renversent l'ordre arithmétique, l'opposition centrale le conserve.** -/
theorem reflection_reverses_order (c s : ℝ) {u v : ℝ} (h : u < v) : c - v < c - u ∧ u + s < v + s :=
  ⟨by linarith, by linarith⟩

/-- **Lue dans le sens arithmétique, l'image réfléchie est la Tour du membre conjugué** (hauteur `−T`). -/
theorem reflection_forward_is_conjugate (d T φ a u : ℝ) :
    (starRingEnd ℂ) (towerCurve d T φ a u) = towerCurve d (-T) (-φ) a u := by
  unfold towerCurve
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 2; push_cast; ring

/-- **Hors ligne, la réflexion arithmétique échange la profondeur** : l'image est la Tour de profondeur `−d`, même
hauteur, lue à rebours. -/
theorem arith_reflect_exchanges_depth (d T φ a u : ℝ) (hT : T ≠ 0) :
    (starRingEnd ℂ) (towerCurve d T φ a u) =
      towerCurve (-d) T φ (a * Real.exp (2 * d * φ / T)) (2 * φ / T - u) := by
  rw [towerCurve_arith_reflect _ _ _ _ _ hT]
  unfold towerCurve
  rw [← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  rw [mul_left_comm, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2; field_simp; ring

#print axioms curve_of_point
#print axioms rescaledTower_eq
#print axioms towerCurve_central
#print axioms towerCurve_arith_reflect
#print axioms towerCurve_crit_reflect
#print axioms contact_index_rules
#print axioms towerCurve_contact
#print axioms tower_central_invariant_iff
#print axioms tower_arith_invariant_iff
#print axioms tower_crit_invariant_iff
#print axioms raw_tower_not_centrally_invariant
#print axioms reflection_forward_is_conjugate
#print axioms arith_reflect_exchanges_depth

end RHV6Fresh
