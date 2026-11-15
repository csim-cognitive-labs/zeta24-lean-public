/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.HarmonicRestoringLaw
import RHV6Fresh.Terminal.ArrivalFiberHypotheses

/-!
# RHV6Fresh — courant harmonique individuel et son transport (mission E239–E241, partie B, 2026-10-13)

Mode normalisé d'un membre `u(t) = e^{dt + iTt}` (`complexMode`, `t = log x`, `d = β − 1/2`). Résultats (axiomes standard) :

1. **Dérivée** `u' = (d + iT) u` (`complexMode_hasDerivAt`).
2. **Courant** `J = Im(ū u') = T e^{2dt}` (`harmonicCurrent_eq`), courant réduit `K = J/T = e^{2dt}` (`reducedCurrent_eq`).
3. **Rapport de deux courants réduits** `Q(t) = K₂/K₁ = e^{2(d₂ − d₁)t}` (`currentRatio_eq`).
4. **Tests B, C, D** (identités vraies pour tout `(d₁, d₂)`) : `Q(t) = 1` en un `t ≠ 0` ⟺ `d₁ = d₂` (`currentRatio_eq_one_iff`) ;
   `Q(t₁) = Q(t₂)` en deux points distincts ⟺ `d₁ = d₂` (`currentRatio_two_points_iff`) ; `Q` constant ⟺ `d₁ = d₂`
   (`currentRatio_const_iff`). Ce sont des CARACTÉRISATIONS : aucune ne fournit l'égalité.
5. **Test A** (enroulement et phase seuls) : pour toute `β ∈ ]0, 1/2]` la grille de contacts admissible d'E200 existe
   (`parameter_grid_admissible`) et le rapport des courants lu aux contacts vaut `C_k^{2(β − 1/2)}`, différent de `1` dès
   `β < 1/2` (`winding_admissible_current_free`) : contre-modèle, les contacts ne fixent pas le courant.
6. **Test E** (passage authentique) : départ ON, rapport des courants à deux abscisses distinctes égal ⟺ `radialFactor = 1`
   (`two_point_current_transport_iff_radialFactor`) ; même chose aux contacts du départ (`contact_current_transport_iff`).
   C'est le but `:399` réécrit, pas sa démonstration.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau ; aucune conservation n'est posée.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Dérivée du mode et courant -/

theorem complexMode_hasDerivAt (d T t : ℝ) :
    HasDerivAt (complexMode d T) (((d : ℂ) + (T : ℂ) * Complex.I) * complexMode d T t) t := by
  unfold complexMode
  have h : HasDerivAt (fun t : ℝ => ((d : ℂ) + (T : ℂ) * Complex.I) * (t : ℂ))
      (((d : ℂ) + (T : ℂ) * Complex.I) * 1) t :=
    (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul _
  have := h.cexp
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

/-- Courant harmonique `J = Im(ū u')`, écrit avec la dérivée exacte `u' = (d + iT) u`. -/
noncomputable def harmonicCurrent (d T t : ℝ) : ℝ :=
  (starRingEnd ℂ (complexMode d T t) * (((d : ℂ) + (T : ℂ) * Complex.I) * complexMode d T t)).im

/-- Courant croisé général `Im(ū₁ u₂')`. -/
noncomputable def crossCurrent (d₁ T₁ d₂ T₂ t : ℝ) : ℝ :=
  (starRingEnd ℂ (complexMode d₁ T₁ t) * (((d₂ : ℂ) + (T₂ : ℂ) * Complex.I) * complexMode d₂ T₂ t)).im

theorem harmonicCurrent_eq_cross (d T t : ℝ) : harmonicCurrent d T t = crossCurrent d T d T t := rfl

/-- `ū₁ u₂ = e^{(d₁ + d₂)t} e^{i(T₂ − T₁)t}`. -/
theorem conj_mul_complexMode (d₁ T₁ d₂ T₂ t : ℝ) :
    starRingEnd ℂ (complexMode d₁ T₁ t) * complexMode d₂ T₂ t =
      (Real.exp ((d₁ + d₂) * t) : ℂ) * Complex.exp ((((T₂ - T₁) * t : ℝ)) * Complex.I) := by
  rw [complexMode_eq, complexMode_eq, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  have : starRingEnd ℂ (((T₁ * t : ℝ) : ℂ) * Complex.I) = -(((T₁ * t : ℝ) : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  rw [this]
  have e1 : (Real.exp ((d₁ + d₂) * t) : ℂ) = (Real.exp (d₁ * t) : ℂ) * (Real.exp (d₂ * t) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
  have e2 : Complex.exp ((((T₂ - T₁) * t : ℝ)) * Complex.I) =
      Complex.exp (-(((T₁ * t : ℝ) : ℂ) * Complex.I)) * Complex.exp (((T₂ * t : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e1, e2]; ring

/-- **Courant croisé** : `Im(ū₁ u₂') = e^{(d₁ + d₂)t}[T₂ cos((T₂ − T₁)t) + d₂ sin((T₂ − T₁)t)]`. -/
theorem crossCurrent_eq (d₁ T₁ d₂ T₂ t : ℝ) :
    crossCurrent d₁ T₁ d₂ T₂ t =
      Real.exp ((d₁ + d₂) * t) * (T₂ * Real.cos ((T₂ - T₁) * t) + d₂ * Real.sin ((T₂ - T₁) * t)) := by
  unfold crossCurrent
  rw [mul_left_comm, conj_mul_complexMode]
  set θ := (T₂ - T₁) * t
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **Courant individuel** : `J = Im(ū u') = T e^{2dt}`. -/
theorem harmonicCurrent_eq (d T t : ℝ) : harmonicCurrent d T t = T * Real.exp (2 * d * t) := by
  rw [harmonicCurrent_eq_cross, crossCurrent_eq, sub_self, zero_mul, Real.cos_zero, Real.sin_zero]
  have h : (d + d) * t = 2 * d * t := by ring
  rw [h]; ring

/-- Courant réduit `K = e^{2dt}`. -/
noncomputable def reducedCurrent (d t : ℝ) : ℝ := Real.exp (2 * d * t)

theorem reducedCurrent_eq {d T t : ℝ} (hT : T ≠ 0) : harmonicCurrent d T t / T = reducedCurrent d t := by
  rw [harmonicCurrent_eq, reducedCurrent, mul_div_cancel_left₀ _ hT]

theorem reducedCurrent_pos (d t : ℝ) : 0 < reducedCurrent d t := Real.exp_pos _

/-- Le courant réduit est le carré du module du mode. -/
theorem reducedCurrent_eq_normSq (d T t : ℝ) : reducedCurrent d t = ‖complexMode d T t‖ ^ 2 := by
  rw [complexMode_norm, reducedCurrent, ← Real.exp_nat_mul]; congr 1; push_cast; ring

/-! ## 2. Rapport de deux courants réduits -/

/-- `Q(t) = K₂(t)/K₁(t)`. -/
noncomputable def currentRatio (d₁ d₂ t : ℝ) : ℝ := reducedCurrent d₂ t / reducedCurrent d₁ t

/-- **`Q(t) = e^{2(d₂ − d₁)t}`**. -/
theorem currentRatio_eq (d₁ d₂ t : ℝ) : currentRatio d₁ d₂ t = Real.exp (2 * (d₂ - d₁) * t) := by
  unfold currentRatio reducedCurrent
  rw [← Real.exp_sub]; congr 1; ring

/-- **Test B** : égalité des courants réduits en un point `t ≠ 0` ⟺ `d₁ = d₂`. -/
theorem currentRatio_eq_one_iff {d₁ d₂ t : ℝ} (ht : t ≠ 0) : currentRatio d₁ d₂ t = 1 ↔ d₁ = d₂ := by
  rw [currentRatio_eq, Real.exp_eq_one_iff]
  constructor
  · intro h
    have : (d₂ - d₁) * t = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact absurd h' ht
  · intro h; rw [h]; ring

/-- **Test C** : égalité du rapport en deux points distincts ⟺ `d₁ = d₂`. -/
theorem currentRatio_two_points_iff {d₁ d₂ t₁ t₂ : ℝ} (ht : t₁ ≠ t₂) :
    currentRatio d₁ d₂ t₁ = currentRatio d₁ d₂ t₂ ↔ d₁ = d₂ := by
  rw [currentRatio_eq, currentRatio_eq, Real.exp_eq_exp]
  constructor
  · intro h
    have : (d₂ - d₁) * (t₁ - t₂) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact absurd (sub_eq_zero.mp h') ht
  · intro h; rw [h]; ring

/-- **Test D** : `Q` constant sur toute la droite ⟺ `d₁ = d₂`. -/
theorem currentRatio_const_iff (d₁ d₂ : ℝ) :
    (∀ t₁ t₂ : ℝ, currentRatio d₁ d₂ t₁ = currentRatio d₁ d₂ t₂) ↔ d₁ = d₂ := by
  constructor
  · intro h; exact (currentRatio_two_points_iff (t₁ := 0) (t₂ := 1) (by norm_num)).mp (h 0 1)
  · intro h t₁ t₂; rw [h, currentRatio_eq, currentRatio_eq]; simp

/-- Le rapport est strictement monotone en `t` dès que `d₁ ≠ d₂` : il n'a aucun point de retour. -/
theorem currentRatio_strictMono {d₁ d₂ : ℝ} (h : d₁ < d₂) : StrictMono (currentRatio d₁ d₂) := by
  intro a b hab
  rw [currentRatio_eq, currentRatio_eq, Real.exp_lt_exp]
  have : 0 < 2 * (d₂ - d₁) := by linarith
  nlinarith

/-! ## 3. Test A : enroulement et phase seuls (contre-modèle) -/

/-- **Contre-modèle A** : pour toute `β ∈ ]0, 1/2[` et `T > 0`, la grille de contacts paramétrée est admissible (fenêtre de
phase, contacts = ligne × facteur, d'après `parameter_grid_admissible`), et le rapport des courants réduits d'un mode de
position `β` à celui d'un mode ON, lu à un contact `C_k > 1`, vaut `C_k^{2(β − 1/2)} ≠ 1`. Les contraintes de phase et
d'enroulement sont satisfaites sans transporter le courant. -/
theorem winding_admissible_current_free {β T : ℝ} (hT : 0 < T) (hβ : 0 < β) (hβ2 : β < 1 / 2) (k : ℤ)
    (hk : 1 < windingContact β T k) :
    (1 ≤ paramFactor β T ∧ paramFactor β T < Real.exp (1 / (2 * T) / T) ∧
      ∀ j : ℤ, windingContact β T j = lineContact T j * paramFactor β T) ∧
    currentRatio 0 (β - 1 / 2) (Real.log (windingContact β T k)) =
      Real.exp (2 * (β - 1 / 2) * Real.log (windingContact β T k)) ∧
    currentRatio 0 (β - 1 / 2) (Real.log (windingContact β T k)) ≠ 1 := by
  refine ⟨parameter_grid_admissible hT hβ hβ2.le, by rw [currentRatio_eq, sub_zero], ?_⟩
  rw [Ne, currentRatio_eq_one_iff (Real.log_pos hk).ne']
  intro h; linarith

/-! ## 4. Test E : lecture sur le passage authentique -/

/-- Mode d'un vrai zéro. -/
noncomputable def zeroDepth (z : TrueZero) : ℝ := rZeroRadialPosition z.1 - 1 / 2

/-- **Test E (caractérisation)** : départ ON ; le rapport des courants réduits arrivée / départ prend la même valeur en deux
abscisses logarithmiques distinctes ⟺ `radialFactor l = 1`. -/
theorem two_point_current_transport_iff_radialFactor (e l : TrueZero) (hOn : rZeroRadialPosition e.1 = 1 / 2)
    {t₁ t₂ : ℝ} (ht : t₁ ≠ t₂) :
    currentRatio (zeroDepth e) (zeroDepth l) t₁ = currentRatio (zeroDepth e) (zeroDepth l) t₂ ↔
      radialFactor l = 1 := by
  rw [currentRatio_two_points_iff ht, radialFactor_eq_one_iff, zeroDepth, zeroDepth, hOn, sub_self, eq_comm, sub_eq_zero]

/-- Deux contacts distincts d'un vrai zéro ont des logarithmes distincts. -/
theorem log_contact_ne (z : TrueZero) {k k' : ℤ} (hk : k ≠ k') :
    Real.log (contactMinusAt z k) ≠ Real.log (contactMinusAt z k') := by
  rw [contactMinusAt_eq_exp, contactMinusAt_eq_exp, Real.log_exp, Real.log_exp]
  have hT : rZeroHeight z.1 ≠ 0 := z.2.ne'
  intro h
  rw [div_left_inj' hT, add_right_inj] at h
  have : (k : ℝ) = k' := mul_right_cancel₀ Real.pi_ne_zero h
  exact hk (by exact_mod_cast this)

/-- **Test E aux contacts du départ** : égalité du rapport des courants aux contacts `k ≠ k'` du membre engagé ⟺ arrivée ON
(facteur radial `1`). Caractérisation ; aucun théorème du dépôt ne fournit le membre de gauche. -/
theorem contact_current_transport_iff (e l : TrueZero) (hOn : rZeroRadialPosition e.1 = 1 / 2) {k k' : ℤ} (hk : k ≠ k') :
    currentRatio (zeroDepth e) (zeroDepth l) (Real.log (contactMinusAt e k)) =
        currentRatio (zeroDepth e) (zeroDepth l) (Real.log (contactMinusAt e k')) ↔
      radialFactor l = 1 :=
  two_point_current_transport_iff_radialFactor e l hOn (log_contact_ne e hk)

/-- Le courant d'un vrai zéro lu en `x` : `T x^{2(β − 1/2)}`, quelle que soit sa position radiale. -/
theorem zero_current_at (z : TrueZero) {x : ℝ} (hx : 0 < x) :
    harmonicCurrent (zeroDepth z) (rZeroHeight z.1) (Real.log x) =
      rZeroHeight z.1 * x ^ (2 * (rZeroRadialPosition z.1 - 1 / 2)) := by
  rw [harmonicCurrent_eq, Real.rpow_def_of_pos hx, zeroDepth]; congr 2; ring

end RHV6Fresh
