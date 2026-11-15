/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.HarmonicCrossCurrent
import RHV6Fresh.Terminal.JointParameterReading

/-!
# RHV6Fresh — architecture du signal exact `x^ρ/ρ` (audit radial total, 2026-10-13)

Trois représentations d'un membre `ρ = β + iT`, de TYPES DISTINCTS (`t = log x`, `d = β − 1/2`) :

* `ExactZeroSignal`      : `E_ρ(t) = e^{ρt}/ρ` (le terme `x^ρ/ρ` de la formule explicite, `zeroTerm_eq_exactSignal`) ;
* `RescaledZeroSignal`   : `R_ρ(t) = e^{−t/2} E_ρ(t) = e^{(d + iT)t}/ρ` ;
* `UnitCoefficientMode`  : `U_ρ(t) = e^{(d + iT)t}` (le `complexMode` d'E224–E241, `unitMode_eval_eq_complexMode`).

Conversions démontrées : `E = (e^{t/2}/ρ)·U`, `R = U/ρ`, `U = ρ·R`. Aucune égalité entre modes unitaires n'est une égalité de
contributions exactes sans l'un de ces théorèmes.

Résultats (axiomes standard), pour `β > 0`, `‖ρ‖ = √(β² + T²)`, `θ = arctan(T/β)` :

1. **Forme polaire** `E_ρ(t) = (e^{βt}/‖ρ‖)·e^{i(Tt − θ)}` (`exactSignal_polar`) ; module, parties réelle et imaginaire
   (`exactSignal_norm`, `exactSignal_re`, `exactSignal_im`).
2. **Courant exact** `J = Im(Ē E') = T e^{2βt}/(β² + T²)` (`exactCurrent_eq`), multiple RÉEL POSITIF du courant unitaire
   (`exactCurrent_eq_scaled_reduced`) : le test à deux abscisses est inchangé (`exactCurrentRatio_two_points_iff`, ⟺ même `β`).
3. **Interférence exacte** `‖E₁ + E₂‖² = e^{2β₁t}/‖ρ₁‖² + e^{2β₂t}/‖ρ₂‖² + 2e^{(β₁+β₂)t}/(‖ρ₁‖‖ρ₂‖)·cos ΔΦ`,
   `ΔΦ = (T₂ − T₁)t + θ₁ − θ₂` (`exact_interference_normSq`).
4. **Courant croisé exact** `W₁₂ = Im(Ē₁ E₂') = e^{(β₁+β₂)t}/(‖ρ₁‖‖ρ₂‖)·[T₂ cos ΔΦ + β₂ sin ΔΦ]` (`exactCross_eq`), partie
   symétrique (`exactCross_symm_eq`), courant collectif `= ΣΣ W` (`exactCollectiveCurrent_eq_sum`). Le passage au mode unitaire
   est une ROTATION complexe `1/ρ̄₁`, pas un facteur réel (`exactCross_eq_rotated_unit`).
5. **Correction de l'aveuglement miroir** : pour une paire miroir de même hauteur (`β₁ + β₂ = 1`), `W₁₂ = T e^{t}/‖ρ₁‖²`
   (`exact_mirror_cross_eq`) ; la partie croisée symétrique exacte est STRICTEMENT inférieure à celle du double ON dès `d ≠ 0`
   et `T² > 3/4` (`exact_mirror_cross_lt_double`) : l'énoncé unitaire `mirror_cross_current_blind` (partie croisée `2T` pour
   toute `d`) est vrai pour les modes unitaires, son interprétation « la partie croisée ne lit pas `d` » est fausse pour le
   signal exact. Ce n'est pas une contrainte : la configuration est hypothétique, l'écart est un détecteur d'ordre `d²`.
6. **Contacts** : les contacts absolus d'un vrai zéro rendent `(β, T)` et deux vrais zéros de mêmes contacts consécutifs ont
   même `(β, T)` (`exact_contacts_determine_parameters`) ; les annulations de `Im U` sont aux abscisses `kπ/T`, INDÉPENDANTES de
   `β` (`unitMode_im_zero_at`) : le mode unitaire perd la phase initiale `θ` portée par `1/ρ`.
7. **Régression** : `E_ρ(0) = 1/ρ ≠ 1 = U_ρ(0)` dès `ρ ≠ 1` (`exactSignal_ne_unitMode_at_zero`), donc toute suppression
   accidentelle de `1/ρ` est détectée sur tout vrai zéro (`zeroTerm_ne_unitMode`).

Aucune identité de ce module n'impose `β = 1/2` : identités vraies pour tout `(β, T)`, détecteurs ou caractérisations.
Aucun `sorry`, aucun `admit`, aucun axiome nouveau.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 0. Coefficient et trois types -/

/-- `ρ = β + iT`. -/
noncomputable def zeroCoeff (β T : ℝ) : ℂ := (β : ℂ) + (T : ℂ) * Complex.I

theorem zeroCoeff_re (β T : ℝ) : (zeroCoeff β T).re = β := by simp [zeroCoeff]
theorem zeroCoeff_im (β T : ℝ) : (zeroCoeff β T).im = T := by simp [zeroCoeff]

theorem zeroCoeff_ne_zero {β T : ℝ} (hβ : 0 < β) : zeroCoeff β T ≠ 0 := by
  intro h; have := congrArg Complex.re h; rw [zeroCoeff_re] at this; simp at this; linarith

theorem zeroCoeff_normSq (β T : ℝ) : Complex.normSq (zeroCoeff β T) = β ^ 2 + T ^ 2 := by
  rw [Complex.normSq_apply, zeroCoeff_re, zeroCoeff_im]; ring

theorem zeroCoeff_norm (β T : ℝ) : ‖zeroCoeff β T‖ = Real.sqrt (β ^ 2 + T ^ 2) := by
  rw [← zeroCoeff_normSq, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem zeroCoeff_of_zero (z : TrueZero) :
    zeroPoint z = zeroCoeff (rZeroRadialPosition z.1) (rZeroHeight z.1) := by
  apply Complex.ext <;> simp [zeroCoeff, zeroPoint_re, zeroPoint_im]

/-- Signal exact `E_ρ(t) = e^{ρt}/ρ`. -/
structure ExactZeroSignal where
  β : ℝ
  T : ℝ

/-- Signal ramené à l'échelle `√x` : `R_ρ(t) = e^{(ρ − 1/2)t}/ρ`. -/
structure RescaledZeroSignal where
  β : ℝ
  T : ℝ

/-- Mode à coefficient unité : `U_ρ(t) = e^{(ρ − 1/2)t}`. -/
structure UnitCoefficientMode where
  β : ℝ
  T : ℝ

noncomputable def ExactZeroSignal.ρ (s : ExactZeroSignal) : ℂ := zeroCoeff s.β s.T
noncomputable def RescaledZeroSignal.ρ (s : RescaledZeroSignal) : ℂ := zeroCoeff s.β s.T
noncomputable def UnitCoefficientMode.ρ (s : UnitCoefficientMode) : ℂ := zeroCoeff s.β s.T

noncomputable def ExactZeroSignal.eval (s : ExactZeroSignal) (t : ℝ) : ℂ :=
  Complex.exp (s.ρ * t) / s.ρ

noncomputable def RescaledZeroSignal.eval (s : RescaledZeroSignal) (t : ℝ) : ℂ :=
  Complex.exp ((s.ρ - 1 / 2) * t) / s.ρ

noncomputable def UnitCoefficientMode.eval (s : UnitCoefficientMode) (t : ℝ) : ℂ :=
  Complex.exp ((s.ρ - 1 / 2) * t)

def ExactZeroSignal.toRescaled (s : ExactZeroSignal) : RescaledZeroSignal := ⟨s.β, s.T⟩
def ExactZeroSignal.toUnit (s : ExactZeroSignal) : UnitCoefficientMode := ⟨s.β, s.T⟩
def RescaledZeroSignal.toUnit (s : RescaledZeroSignal) : UnitCoefficientMode := ⟨s.β, s.T⟩

/-- Le signal exact d'un vrai zéro. -/
noncomputable def exactSignalOf (z : TrueZero) : ExactZeroSignal := ⟨rZeroRadialPosition z.1, rZeroHeight z.1⟩

/-! ## 1. Conversions exactes -/

/-- `E_ρ(t) = (e^{t/2}/ρ)·U_ρ(t)`. -/
theorem exact_eq_unit (s : ExactZeroSignal) (t : ℝ) :
    s.eval t = (Real.exp (t / 2) : ℂ) / s.ρ * s.toUnit.eval t := by
  unfold ExactZeroSignal.eval UnitCoefficientMode.eval
  have hρ : s.toUnit.ρ = s.ρ := rfl
  rw [hρ, Complex.ofReal_exp, div_mul_eq_mul_div, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- `R_ρ(t) = U_ρ(t)/ρ`. -/
theorem rescaled_eq_unit (s : RescaledZeroSignal) (t : ℝ) : s.eval t = s.toUnit.eval t / s.ρ := rfl

/-- `U_ρ(t) = ρ·R_ρ(t)`. -/
theorem unit_eq_coeff_mul_rescaled (s : RescaledZeroSignal) (hβ : 0 < s.β) (t : ℝ) :
    s.toUnit.eval t = s.ρ * s.eval t := by
  rw [rescaled_eq_unit]
  have : s.ρ ≠ 0 := zeroCoeff_ne_zero hβ
  field_simp

/-- `R_ρ(t) = e^{−t/2} E_ρ(t)`. -/
theorem rescaled_eq_exact (s : ExactZeroSignal) (t : ℝ) :
    s.toRescaled.eval t = (Real.exp (-(t / 2)) : ℂ) * s.eval t := by
  unfold RescaledZeroSignal.eval ExactZeroSignal.eval
  have hρ : s.toRescaled.ρ = s.ρ := rfl
  rw [hρ, Complex.ofReal_exp, mul_div_assoc', ← Complex.exp_add]
  congr 2; push_cast; ring

/-- Le mode unitaire est le `complexMode` d'E224–E241. -/
theorem unitMode_eval_eq_complexMode (s : UnitCoefficientMode) (t : ℝ) :
    s.eval t = complexMode (s.β - 1 / 2) s.T t := by
  unfold UnitCoefficientMode.eval complexMode UnitCoefficientMode.ρ zeroCoeff
  congr 1; push_cast; ring

/-- Le terme `x^ρ/ρ` de la formule explicite est le signal exact en `t = log x`. -/
theorem zeroTerm_eq_exactSignal (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    zeroTerm z x = (exactSignalOf z).eval (Real.log x) := by
  unfold zeroTerm ExactZeroSignal.eval
  have hρ : (exactSignalOf z).ρ = zeroPoint z := (zeroCoeff_of_zero z).symm
  rw [hρ, Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le, mul_comm]

/-! ## 2. Forme polaire -/

/-- `ρ = ‖ρ‖·e^{iθ}`, `θ = arctan(T/β)`, pour `β > 0`. -/
theorem zeroCoeff_polar {β T : ℝ} (hβ : 0 < β) :
    zeroCoeff β T = (Real.sqrt (β ^ 2 + T ^ 2) : ℂ) *
      Complex.exp ((Real.arctan (T / β) : ℂ) * Complex.I) := by
  set r := Real.sqrt (β ^ 2 + T ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hsq : r ^ 2 = β ^ 2 + T ^ 2 := Real.sq_sqrt (by positivity)
  have hs : Real.sqrt (1 + (T / β) ^ 2) = r / β := by
    rw [show 1 + (T / β) ^ 2 = (r / β) ^ 2 by rw [div_pow (r) β 2, hsq]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have hc : Real.cos (Real.arctan (T / β)) = β / r := by
    rw [Real.cos_arctan, hs]; field_simp
  have hsn : Real.sin (Real.arctan (T / β)) = T / r := by
    rw [Real.sin_arctan, hs]; field_simp
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hsn, zeroCoeff]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  push_cast
  field_simp

/-- **Forme polaire du signal exact** : `E_ρ(t) = (e^{βt}/‖ρ‖)·e^{i(Tt − θ)}`. -/
theorem exactSignal_polar (s : ExactZeroSignal) (hβ : 0 < s.β) (t : ℝ) :
    s.eval t = ((Real.exp (s.β * t) / Real.sqrt (s.β ^ 2 + s.T ^ 2) : ℝ) : ℂ) *
      Complex.exp (((s.T * t - Real.arctan (s.T / s.β) : ℝ) : ℂ) * Complex.I) := by
  have hr0 : 0 < Real.sqrt (s.β ^ 2 + s.T ^ 2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg s.T])
  unfold ExactZeroSignal.eval
  have hρ : s.ρ = zeroCoeff s.β s.T := rfl
  have hnum : Complex.exp (s.ρ * t) =
      (Real.exp (s.β * t) : ℂ) * Complex.exp (((s.T * t : ℝ) : ℂ) * Complex.I) := by
    rw [hρ, Complex.ofReal_exp, ← Complex.exp_add, zeroCoeff]; congr 1; push_cast; ring
  rw [hnum, hρ, zeroCoeff_polar hβ]
  have he : Complex.exp ((((s.T * t - Real.arctan (s.T / s.β)) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((s.T * t : ℝ) : ℂ) * Complex.I) /
        Complex.exp ((Real.arctan (s.T / s.β) : ℂ) * Complex.I) := by
    rw [← Complex.exp_sub]; congr 1; push_cast; ring
  rw [he]
  have hr0' : ((Real.sqrt (s.β ^ 2 + s.T ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hex : Complex.exp ((Real.arctan (s.T / s.β) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  push_cast
  field_simp

theorem exactSignal_norm (s : ExactZeroSignal) (hβ : 0 < s.β) (t : ℝ) :
    ‖s.eval t‖ = Real.exp (s.β * t) / Real.sqrt (s.β ^ 2 + s.T ^ 2) := by
  rw [exactSignal_polar s hβ, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

theorem exactSignal_re (s : ExactZeroSignal) (hβ : 0 < s.β) (t : ℝ) :
    (s.eval t).re = Real.exp (s.β * t) / Real.sqrt (s.β ^ 2 + s.T ^ 2) *
      Real.cos (s.T * t - Real.arctan (s.T / s.β)) := by
  rw [exactSignal_polar s hβ, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem exactSignal_im (s : ExactZeroSignal) (hβ : 0 < s.β) (t : ℝ) :
    (s.eval t).im = Real.exp (s.β * t) / Real.sqrt (s.β ^ 2 + s.T ^ 2) *
      Real.sin (s.T * t - Real.arctan (s.T / s.β)) := by
  rw [exactSignal_polar s hβ, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-! ## 3. Dérivée et courant exact -/

theorem exactSignal_hasDerivAt (s : ExactZeroSignal) (t : ℝ) :
    HasDerivAt s.eval (s.ρ * s.eval t) t := by
  unfold ExactZeroSignal.eval
  have h : HasDerivAt (fun t : ℝ => s.ρ * (t : ℂ)) (s.ρ * 1) t :=
    (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul _
  have := (h.cexp).div_const s.ρ
  rw [show s.ρ * (Complex.exp (s.ρ * t) / s.ρ) = Complex.exp (s.ρ * (t : ℂ)) * (s.ρ * 1) / s.ρ by ring]
  exact this

/-- Courant exact `J = Im(Ē E')`, `E' = ρE`. -/
noncomputable def exactCurrent (s : ExactZeroSignal) (t : ℝ) : ℝ :=
  (starRingEnd ℂ (s.eval t) * (s.ρ * s.eval t)).im

/-- Courant croisé exact `W₁₂ = Im(Ē₁ E₂')`. -/
noncomputable def exactCross (s₁ s₂ : ExactZeroSignal) (t : ℝ) : ℝ :=
  (starRingEnd ℂ (s₁.eval t) * (s₂.ρ * s₂.eval t)).im

theorem exactCurrent_eq_cross (s : ExactZeroSignal) (t : ℝ) : exactCurrent s t = exactCross s s t := rfl

theorem exactSignal_normSq (s : ExactZeroSignal) (hβ : 0 < s.β) (t : ℝ) :
    Complex.normSq (s.eval t) = Real.exp (2 * s.β * t) / (s.β ^ 2 + s.T ^ 2) := by
  rw [Complex.normSq_eq_norm_sq, exactSignal_norm s hβ, div_pow, Real.sq_sqrt (by positivity),
    ← Real.exp_nat_mul]
  congr 2; push_cast; ring

/-- **Courant exact** `J = T e^{2βt}/(β² + T²)`. -/
theorem exactCurrent_eq (s : ExactZeroSignal) (hβ : 0 < s.β) (t : ℝ) :
    exactCurrent s t = s.T * Real.exp (2 * s.β * t) / (s.β ^ 2 + s.T ^ 2) := by
  unfold exactCurrent
  rw [mul_left_comm, mul_comm (starRingEnd ℂ _), Complex.mul_conj, Complex.mul_im, Complex.ofReal_im,
    Complex.ofReal_re, exactSignal_normSq s hβ]
  have : s.ρ.im = s.T := zeroCoeff_im _ _
  rw [this]; ring

/-- Le courant exact est un multiple RÉEL POSITIF du courant réduit unitaire : `J = (T/‖ρ‖²)·e^{t}·K`. -/
theorem exactCurrent_eq_scaled_reduced (s : ExactZeroSignal) (hβ : 0 < s.β) (t : ℝ) :
    exactCurrent s t = s.T / (s.β ^ 2 + s.T ^ 2) * Real.exp t * reducedCurrent (s.β - 1 / 2) t := by
  rw [exactCurrent_eq s hβ, reducedCurrent, mul_assoc (s.T / _), ← Real.exp_add]
  rw [show t + 2 * (s.β - 1 / 2) * t = 2 * s.β * t by ring]; ring

/-- Rapport des courants exacts. -/
noncomputable def exactCurrentRatio (s₁ s₂ : ExactZeroSignal) (t : ℝ) : ℝ := exactCurrent s₂ t / exactCurrent s₁ t

/-- `J₂/J₁ = (T₂‖ρ₁‖²)/(T₁‖ρ₂‖²) · Q(t)` : le coefficient `1/ρ` ne contribue qu'une constante. -/
theorem exactCurrentRatio_eq (s₁ s₂ : ExactZeroSignal) (hβ₁ : 0 < s₁.β) (hβ₂ : 0 < s₂.β) (hT₁ : 0 < s₁.T) (t : ℝ) :
    exactCurrentRatio s₁ s₂ t = s₂.T * (s₁.β ^ 2 + s₁.T ^ 2) / (s₁.T * (s₂.β ^ 2 + s₂.T ^ 2)) *
      currentRatio (s₁.β - 1 / 2) (s₂.β - 1 / 2) t := by
  unfold exactCurrentRatio
  rw [exactCurrent_eq_scaled_reduced s₁ hβ₁, exactCurrent_eq_scaled_reduced s₂ hβ₂, currentRatio]
  have h1 : 0 < s₁.β ^ 2 + s₁.T ^ 2 := by positivity
  have h2 : 0 < s₂.β ^ 2 + s₂.T ^ 2 := by positivity
  have h3 := reducedCurrent_pos (s₁.β - 1 / 2) t
  have h4 := Real.exp_pos t
  field_simp

/-- **Caractérisation inchangée par le signal exact** : rapport des courants exacts égal en deux abscisses distinctes ⟺ même
`β`. La normalisation ne perdait aucune information sur `β` dans ce test (le facteur `1/ρ` est constant en `t`). -/
theorem exactCurrentRatio_two_points_iff (s₁ s₂ : ExactZeroSignal) (hβ₁ : 0 < s₁.β) (hβ₂ : 0 < s₂.β)
    (hT₁ : 0 < s₁.T) (hT₂ : 0 < s₂.T) {t₁ t₂ : ℝ} (ht : t₁ ≠ t₂) :
    exactCurrentRatio s₁ s₂ t₁ = exactCurrentRatio s₁ s₂ t₂ ↔ s₁.β = s₂.β := by
  rw [exactCurrentRatio_eq s₁ s₂ hβ₁ hβ₂ hT₁, exactCurrentRatio_eq s₁ s₂ hβ₁ hβ₂ hT₁]
  have hc : s₂.T * (s₁.β ^ 2 + s₁.T ^ 2) / (s₁.T * (s₂.β ^ 2 + s₂.T ^ 2)) ≠ 0 := by positivity
  rw [mul_right_inj' hc, currentRatio_two_points_iff ht]
  constructor <;> intro h <;> linarith

/-- **Passage authentique, signal exact** : départ ON ; rapport des courants EXACTS arrivée / départ égal en deux abscisses
distinctes ⟺ `radialFactor l = 1`. Même caractérisation qu'E240 (TYPE C), aucune contrainte nouvelle. -/
theorem exact_current_transport_iff_radialFactor (e l : TrueZero) (hOn : rZeroRadialPosition e.1 = 1 / 2)
    {t₁ t₂ : ℝ} (ht : t₁ ≠ t₂) :
    exactCurrentRatio (exactSignalOf e) (exactSignalOf l) t₁ =
        exactCurrentRatio (exactSignalOf e) (exactSignalOf l) t₂ ↔ radialFactor l = 1 := by
  rw [exactCurrentRatio_two_points_iff _ _ (thm_zeroRadialPosition_positive e.1)
    (thm_zeroRadialPosition_positive l.1) e.2 l.2 ht, radialFactor_eq_one_iff]
  show rZeroRadialPosition e.1 = rZeroRadialPosition l.1 ↔ _
  rw [hOn]; exact eq_comm

/-! ## 4. Produit conjugué, interférence et courant croisé exacts -/

/-- `Ē₁E₂ = (e^{(β₁+β₂)t}/(‖ρ₁‖‖ρ₂‖))·e^{iΔΦ}`, `ΔΦ = (T₂ − T₁)t + θ₁ − θ₂`. -/
theorem conj_mul_exactSignal (s₁ s₂ : ExactZeroSignal) (hβ₁ : 0 < s₁.β) (hβ₂ : 0 < s₂.β) (t : ℝ) :
    starRingEnd ℂ (s₁.eval t) * s₂.eval t =
      ((Real.exp ((s₁.β + s₂.β) * t) / (Real.sqrt (s₁.β ^ 2 + s₁.T ^ 2) * Real.sqrt (s₂.β ^ 2 + s₂.T ^ 2)) : ℝ) : ℂ) *
        Complex.exp (((((s₂.T - s₁.T) * t + Real.arctan (s₁.T / s₁.β) - Real.arctan (s₂.T / s₂.β)) : ℝ) : ℂ) *
          Complex.I) := by
  rw [exactSignal_polar s₁ hβ₁, exactSignal_polar s₂ hβ₂, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  have hc : starRingEnd ℂ ((((s₁.T * t - Real.arctan (s₁.T / s₁.β)) : ℝ) : ℂ) * Complex.I) =
      -((((s₁.T * t - Real.arctan (s₁.T / s₁.β)) : ℝ) : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  rw [hc]
  have he : Complex.exp ((((((s₂.T - s₁.T) * t + Real.arctan (s₁.T / s₁.β) - Real.arctan (s₂.T / s₂.β))) : ℝ) : ℂ) *
      Complex.I) = Complex.exp (-((((s₁.T * t - Real.arctan (s₁.T / s₁.β)) : ℝ) : ℂ) * Complex.I)) *
        Complex.exp ((((s₂.T * t - Real.arctan (s₂.T / s₂.β)) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [he]
  have ha : ((Real.exp ((s₁.β + s₂.β) * t) / (Real.sqrt (s₁.β ^ 2 + s₁.T ^ 2) * Real.sqrt (s₂.β ^ 2 + s₂.T ^ 2)) : ℝ) : ℂ) =
      ((Real.exp (s₁.β * t) / Real.sqrt (s₁.β ^ 2 + s₁.T ^ 2) : ℝ) : ℂ) *
        ((Real.exp (s₂.β * t) / Real.sqrt (s₂.β ^ 2 + s₂.T ^ 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]; congr 1
    rw [add_mul, Real.exp_add]; ring
  rw [ha]; ring

/-- **Courant croisé exact** : `W₁₂ = e^{(β₁+β₂)t}/(‖ρ₁‖‖ρ₂‖)·[T₂ cos ΔΦ + β₂ sin ΔΦ]` (coefficient `β₂ + iT₂`, pas `d₂ + iT₂`). -/
theorem exactCross_eq (s₁ s₂ : ExactZeroSignal) (hβ₁ : 0 < s₁.β) (hβ₂ : 0 < s₂.β) (t : ℝ) :
    exactCross s₁ s₂ t =
      Real.exp ((s₁.β + s₂.β) * t) / (Real.sqrt (s₁.β ^ 2 + s₁.T ^ 2) * Real.sqrt (s₂.β ^ 2 + s₂.T ^ 2)) *
        (s₂.T * Real.cos ((s₂.T - s₁.T) * t + Real.arctan (s₁.T / s₁.β) - Real.arctan (s₂.T / s₂.β)) +
          s₂.β * Real.sin ((s₂.T - s₁.T) * t + Real.arctan (s₁.T / s₁.β) - Real.arctan (s₂.T / s₂.β))) := by
  unfold exactCross
  rw [mul_left_comm, conj_mul_exactSignal s₁ s₂ hβ₁ hβ₂, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  have hρ : s₂.ρ = (s₂.β : ℂ) + (s₂.T : ℂ) * Complex.I := rfl
  rw [hρ]
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **Partie symétrique exacte** `W₁₂ + W₂₁ = A·[(T₁ + T₂) cos ΔΦ + (β₂ − β₁) sin ΔΦ]`. -/
theorem exactCross_symm_eq (s₁ s₂ : ExactZeroSignal) (hβ₁ : 0 < s₁.β) (hβ₂ : 0 < s₂.β) (t : ℝ) :
    exactCross s₁ s₂ t + exactCross s₂ s₁ t =
      Real.exp ((s₁.β + s₂.β) * t) / (Real.sqrt (s₁.β ^ 2 + s₁.T ^ 2) * Real.sqrt (s₂.β ^ 2 + s₂.T ^ 2)) *
        ((s₁.T + s₂.T) * Real.cos ((s₂.T - s₁.T) * t + Real.arctan (s₁.T / s₁.β) - Real.arctan (s₂.T / s₂.β)) +
          (s₂.β - s₁.β) *
            Real.sin ((s₂.T - s₁.T) * t + Real.arctan (s₁.T / s₁.β) - Real.arctan (s₂.T / s₂.β))) := by
  rw [exactCross_eq s₁ s₂ hβ₁ hβ₂, exactCross_eq s₂ s₁ hβ₂ hβ₁]
  have h : (s₁.T - s₂.T) * t + Real.arctan (s₂.T / s₂.β) - Real.arctan (s₁.T / s₁.β) =
      -((s₂.T - s₁.T) * t + Real.arctan (s₁.T / s₁.β) - Real.arctan (s₂.T / s₂.β)) := by ring
  rw [h, Real.cos_neg, Real.sin_neg, add_comm s₂.β s₁.β, mul_comm (Real.sqrt (s₂.β ^ 2 + s₂.T ^ 2))]
  ring

/-- **Interférence exacte** de deux Tours : `‖E₁ + E₂‖² = e^{2β₁t}/‖ρ₁‖² + e^{2β₂t}/‖ρ₂‖² + 2A cos ΔΦ`. -/
theorem exact_interference_normSq (s₁ s₂ : ExactZeroSignal) (hβ₁ : 0 < s₁.β) (hβ₂ : 0 < s₂.β) (t : ℝ) :
    ‖s₁.eval t + s₂.eval t‖ ^ 2 =
      Real.exp (2 * s₁.β * t) / (s₁.β ^ 2 + s₁.T ^ 2) + Real.exp (2 * s₂.β * t) / (s₂.β ^ 2 + s₂.T ^ 2) +
        2 * (Real.exp ((s₁.β + s₂.β) * t) /
            (Real.sqrt (s₁.β ^ 2 + s₁.T ^ 2) * Real.sqrt (s₂.β ^ 2 + s₂.T ^ 2)) *
          Real.cos ((s₂.T - s₁.T) * t + Real.arctan (s₁.T / s₁.β) - Real.arctan (s₂.T / s₂.β))) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, exactSignal_normSq s₁ hβ₁, exactSignal_normSq s₂ hβ₂]
  have hre : (s₁.eval t * starRingEnd ℂ (s₂.eval t)).re = (starRingEnd ℂ (s₁.eval t) * s₂.eval t).re := by
    rw [← Complex.conj_re (starRingEnd ℂ (s₁.eval t) * s₂.eval t), map_mul, Complex.conj_conj, mul_comm]
  rw [hre, conj_mul_exactSignal s₁ s₂ hβ₁ hβ₂, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- Courant collectif exact d'une famille finie. -/
noncomputable def exactCollectiveCurrent {ι : Type*} (s : Finset ι) (f : ι → ExactZeroSignal) (t : ℝ) : ℝ :=
  (starRingEnd ℂ (∑ n ∈ s, (f n).eval t) * ∑ m ∈ s, ((f m).ρ * (f m).eval t)).im

/-- **Courant collectif exact** `= Σ_n Σ_m W_{nm}`, diagonale = courants individuels exacts. -/
theorem exactCollectiveCurrent_eq_sum {ι : Type*} (s : Finset ι) (f : ι → ExactZeroSignal) (t : ℝ) :
    exactCollectiveCurrent s f t = ∑ n ∈ s, ∑ m ∈ s, exactCross (f n) (f m) t := by
  unfold exactCollectiveCurrent exactCross
  rw [map_sum, Finset.sum_mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.im_sum]

/-- **Conversion du courant croisé** : `W₁₂^{exact} = Im((e^{t}/ρ̄₁)·Ū₁U₂)` alors que le courant unitaire est
`Im((ρ₂ − 1/2)·Ū₁U₂)` : le passage de l'un à l'autre est une ROTATION complexe par `arg ρ₁`, pas un facteur réel. -/
theorem exactCross_eq_rotated_unit (s₁ s₂ : ExactZeroSignal) (hβ₂ : 0 < s₂.β) (t : ℝ) :
    exactCross s₁ s₂ t =
      ((Real.exp t : ℂ) / starRingEnd ℂ s₁.ρ * (starRingEnd ℂ (s₁.toUnit.eval t) * s₂.toUnit.eval t)).im ∧
    crossCurrent (s₁.β - 1 / 2) s₁.T (s₂.β - 1 / 2) s₂.T t =
      ((s₂.ρ - 1 / 2) * (starRingEnd ℂ (s₁.toUnit.eval t) * s₂.toUnit.eval t)).im := by
  constructor
  · unfold exactCross
    rw [exact_eq_unit s₁, exact_eq_unit s₂]
    have hρ2 : s₂.ρ ≠ 0 := zeroCoeff_ne_zero hβ₂
    have hexp : (Real.exp t : ℂ) = (Real.exp (t / 2) : ℂ) * (Real.exp (t / 2) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
    rw [map_mul, map_div₀, Complex.conj_ofReal, hexp]
    congr 1
    field_simp
  · rw [unitMode_eval_eq_complexMode, unitMode_eval_eq_complexMode]
    unfold crossCurrent
    simp only [ExactZeroSignal.toUnit]
    have : ((s₂.β - 1 / 2 : ℝ) : ℂ) + (s₂.T : ℂ) * Complex.I = s₂.ρ - 1 / 2 := by
      show _ = zeroCoeff s₂.β s₂.T - 1 / 2
      unfold zeroCoeff; push_cast; ring
    rw [this, mul_left_comm]

/-! ## 5. Paire miroir de même hauteur : correction de l'aveuglement -/

/-- Pour `β₁ + β₂ = 1` et même hauteur : `Ē₁·(ρ₂E₂) = e^{t}/ρ̄₁`, donc `W₁₂ = T e^{t}/‖ρ₁‖²`. -/
theorem exact_mirror_cross_eq (β T t : ℝ) (_hβ : 0 < β) (hβ1 : β < 1) :
    exactCross ⟨β, T⟩ ⟨1 - β, T⟩ t = T * Real.exp t / (β ^ 2 + T ^ 2) := by
  unfold exactCross ExactZeroSignal.eval ExactZeroSignal.ρ
  have h2 : zeroCoeff (1 - β) T ≠ 0 := zeroCoeff_ne_zero (by linarith)
  have key : starRingEnd ℂ (Complex.exp (zeroCoeff β T * t) / zeroCoeff β T) *
      (zeroCoeff (1 - β) T * (Complex.exp (zeroCoeff (1 - β) T * t) / zeroCoeff (1 - β) T)) =
        (Real.exp t : ℂ) / starRingEnd ℂ (zeroCoeff β T) := by
    rw [mul_div_cancel₀ _ h2, map_div₀, ← Complex.exp_conj, div_mul_eq_mul_div, ← Complex.exp_add,
      Complex.ofReal_exp]
    congr 2
    rw [map_mul, Complex.conj_ofReal]
    unfold zeroCoeff
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  rw [key, Complex.div_im]
  have hre : (starRingEnd ℂ (zeroCoeff β T)).re = β := by rw [Complex.conj_re, zeroCoeff_re]
  have him : (starRingEnd ℂ (zeroCoeff β T)).im = -T := by rw [Complex.conj_im, zeroCoeff_im]
  rw [hre, him, Complex.normSq_conj, zeroCoeff_normSq, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Partie croisée symétrique exacte d'une paire miroir : `T e^{t}(1/‖ρ₊‖² + 1/‖ρ₋‖²)`. -/
theorem exact_mirror_cross_symm_eq (β T t : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    exactCross ⟨β, T⟩ ⟨1 - β, T⟩ t + exactCross ⟨1 - β, T⟩ ⟨β, T⟩ t =
      T * Real.exp t * (1 / (β ^ 2 + T ^ 2) + 1 / ((1 - β) ^ 2 + T ^ 2)) := by
  have h2 := exact_mirror_cross_eq (1 - β) T t (by linarith) (by linarith)
  rw [show (1 : ℝ) - (1 - β) = β by ring] at h2
  rw [exact_mirror_cross_eq β T t hβ hβ1, h2]; ring

/-- Le courant exact d'un membre ON vaut `T e^{t}/(1/4 + T²)`. -/
theorem exactCurrent_onLine (T t : ℝ) : exactCurrent ⟨1 / 2, T⟩ t = T * Real.exp t / (1 / 4 + T ^ 2) := by
  rw [exactCurrent_eq ⟨1 / 2, T⟩ (by norm_num)]
  show T * Real.exp (2 * (1 / 2) * t) / ((1 / 2) ^ 2 + T ^ 2) = _
  rw [show 2 * (1 / 2 : ℝ) * t = t by ring]; norm_num

/-- **Correction** : la partie croisée symétrique EXACTE de la paire miroir `(1/2 + d, 1/2 − d)` est strictement inférieure à
celle du double ON `2T e^{t}/(1/4 + T²)` dès `d ≠ 0` et `T² > 3/4`. L'aveuglement de `mirror_cross_current_blind` est propre au
mode unitaire. Écart d'ordre `d²` : détecteur, pas contrainte. -/
theorem exact_mirror_cross_lt_double {β T : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hd : β ≠ 1 / 2) (hT : 0 < T)
    (hT2 : 3 / 4 < T ^ 2) (t : ℝ) :
    exactCross ⟨β, T⟩ ⟨1 - β, T⟩ t + exactCross ⟨1 - β, T⟩ ⟨β, T⟩ t < 2 * exactCurrent ⟨1 / 2, T⟩ t := by
  rw [exact_mirror_cross_symm_eq β T t hβ hβ1, exactCurrent_onLine]
  have he := Real.exp_pos t
  have ha : 0 < β ^ 2 + T ^ 2 := by positivity
  have hb : 0 < (1 - β) ^ 2 + T ^ 2 := by positivity
  have hc : 0 < 1 / 4 + T ^ 2 := by positivity
  have hd2 : 0 < (β - 1 / 2) ^ 2 := by
    have : β - 1 / 2 ≠ 0 := sub_ne_zero.mpr hd
    positivity
  have key : 1 / (β ^ 2 + T ^ 2) + 1 / ((1 - β) ^ 2 + T ^ 2) < 2 / (1 / 4 + T ^ 2) := by
    rw [div_add_div _ _ ha.ne' hb.ne', div_lt_div_iff₀ (by positivity) hc]
    nlinarith [mul_pos hd2 (show 0 < 1 / 4 + T ^ 2 + (β - 1 / 2) ^ 2 - 1 by nlinarith)]
  have := mul_lt_mul_of_pos_left key (mul_pos hT he)
  calc T * Real.exp t * (1 / (β ^ 2 + T ^ 2) + 1 / ((1 - β) ^ 2 + T ^ 2))
      < T * Real.exp t * (2 / (1 / 4 + T ^ 2)) := this
    _ = 2 * (T * Real.exp t / (1 / 4 + T ^ 2)) := by ring

/-! ## 6. Contacts absolus et perte de phase du mode unitaire -/

/-- **Contacts absolus** : deux vrais zéros ayant les mêmes contacts aux indices `k`, `k + 1` ont même hauteur et même
position radiale (inversion `T = π/log(C_{k+1}/C_k)`, `β = T/tan(T log C_k)`, `inversion_from_consecutive_contacts`). -/
theorem exact_contacts_determine_parameters (z w : TrueZero) (k : ℤ)
    (h0 : contactMinusAt z k = contactMinusAt w k) (h1 : contactMinusAt z (k + 1) = contactMinusAt w (k + 1)) :
    rZeroHeight z.1 = rZeroHeight w.1 ∧ rZeroRadialPosition z.1 = rZeroRadialPosition w.1 := by
  obtain ⟨hTz, hβz⟩ := inversion_from_consecutive_contacts z k
  obtain ⟨hTw, hβw⟩ := inversion_from_consecutive_contacts w k
  have hT : rZeroHeight z.1 = rZeroHeight w.1 := by rw [← hTz, ← hTw, h0, h1]
  refine ⟨hT, ?_⟩
  rw [← hβz, ← hβw, hT, h0]

/-- **Perte de phase** : les annulations de `Im U` sont aux abscisses `kπ/T` pour TOUTE position radiale ; le mode unitaire
n'a pas la phase initiale `θ = arctan(T/β)` que porte `1/ρ` et que lisent les contacts absolus. -/
theorem unitMode_im_zero_at (d T : ℝ) (hT : T ≠ 0) (k : ℤ) :
    (complexMode d T (k * Real.pi / T)).im = 0 := by
  rw [complexMode_eq, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im,
    show T * (k * Real.pi / T) = k * Real.pi by field_simp, Real.sin_int_mul_pi, mul_zero]

/-! ## 7. Régression : `1/ρ` ne peut pas être supprimé silencieusement -/

theorem exactSignal_eval_zero (s : ExactZeroSignal) : s.eval 0 = 1 / s.ρ := by
  simp [ExactZeroSignal.eval]

theorem unitMode_eval_zero (s : UnitCoefficientMode) : s.eval 0 = 1 := by
  simp [UnitCoefficientMode.eval]

theorem exactSignal_ne_unitMode_at_zero (s : ExactZeroSignal) (h1 : s.ρ ≠ 1) : s.eval 0 ≠ s.toUnit.eval 0 := by
  rw [exactSignal_eval_zero, unitMode_eval_zero]
  intro h
  have hρ : s.ρ ≠ 0 := by intro h0; rw [h0] at h; simp at h
  apply h1
  field_simp at h
  exact h.symm

/-- Sur tout vrai zéro le signal exact diffère du mode unitaire en `t = 0` (`T > 0` donne `ρ ≠ 1`). -/
theorem zeroTerm_ne_unitMode (z : TrueZero) :
    (exactSignalOf z).eval 0 ≠ (exactSignalOf z).toUnit.eval 0 := by
  apply exactSignal_ne_unitMode_at_zero
  intro h
  have := congrArg Complex.im h
  rw [show (exactSignalOf z).ρ = zeroCoeff (rZeroRadialPosition z.1) (rZeroHeight z.1) from rfl, zeroCoeff_im] at this
  simp at this
  exact absurd this z.2.ne'

example : (⟨1 / 2, 14⟩ : ExactZeroSignal).eval 0 = 1 / zeroCoeff (1 / 2) 14 := exactSignal_eval_zero _

end RHV6Fresh
