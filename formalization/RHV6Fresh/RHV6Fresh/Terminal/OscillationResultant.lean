/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.BackgroundModulation

/-!
# Résultante oscillatoire des zéros et canal de comptage (E330, E331 ; auteur, 2026-10-17)

Pour une famille finie `s` de vrais zéros, la résultante pondérée est
`Q_s(u) = Σ_{z ∈ s} e^{(β_z − 1/2) u} e^{i T_z u}` ; pour des zéros sur la ligne elle est la résultante unité
`Σ e^{i T_z u}` (oscillations d'amplitude un, fréquences propres `T_z`).

Contenu (tout est DÉMONTRÉ ; `Ei` n'existe pas dans Mathlib, la primitive locale de `e^w/w` de chaque zéro est une
hypothèse explicite `hF`, comme dans `BackgroundModulation`) :
* §1 résultante, partie réelle `Σ cos(T_j u)`, forme amplitude-phase `‖Q‖ cos(arg Q) = Re Q`, passage de `s` à
  `insert j s`, bornes `‖Q‖ ≤ card s` (unité) et `‖Q_s‖ ≤ Σ e^{(β−1/2)u}` (pondérée), dérivée de la résultante unité ;
* §2 somme des densités de modulation du canal de comptage `= −2/(√x log x) · Re Q_s(log x)` (toute position radiale,
  avec la résultante pondérée ; sur la ligne, la résultante unité) ;
* §3 égalité centrale d'E330 : la somme des contributions `−2 Re F_z(ρ_z log x)` a pour dérivée
  `−2/(√x log x) · Re Q_s(log x)` et, sur `[a, b] ⊂ ]1, ∞[`,
  `S(b) = S(a) + ∫_a^b −2/(√t log t) · Re Q_s(log t) dt` ; constante initiale = la somme elle-même en `a` ;
* §4 complément : `E_{insert j s} = E_s − b_j` (passage de `N` à `N + 1`), aucune borne ;
* §5 interférences `‖Q‖² = card s + Σ_{i ≠ j} cos((T_i − T_j)u)` (tout ensemble de fréquences) ; module d'un mode seul
  `e^{(β−1/2)u}` ; non-décroissance entre deux fenêtres ⟺ `β ≥ 1/2` (caractérisation).

Niveaux (correction du 2026-10-18, E332–E333, `Terminal/CountingFieldArchitecture.lean`) : la résultante unité est le
niveau 1 (modes de module 1), la résultante pondérée le niveau 2 (module `e^{(β−1/2)u}`), la densité de comptage le niveau 3,
obtenue par le facteur exact `−2/(√x log x)` ; la contribution de comptage elle-même est l'intégrale de cette densité. Aucun de
ces niveaux n'est l'amplitude d'un autre. Les fréquences `T_j` sont intrinsèques en `u = log x` ; en `x` la fréquence locale est
`T/(2πx)`. Les lectures d'E330/E331 qui plaçaient des contacts du canal π par zéro (seuils `2^m` de Möbius) sont retirées :
le canal π n'est exact que par Möbius sur la SOMME ; les contributions individuelles se lisent dans le canal `J`, sur les mêmes
écarts premiers que la somme (E332).

Portée : identités vraies pour toute famille finie et toute position radiale. Aucun énoncé ne relie la somme sur
TOUS les zéros au comptage des premiers (formule explicite du canal `J` démontrée nulle part ; nommée `CountingExplicitFormula`) ni ne borne le complément.
Le poids `e^{(β−1/2)u}` est la seule place où la position radiale entre dans la résultante ; l'égalité à la résultante
unité est une caractérisation de la ligne, jamais une loi.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## §1 La résultante -/

/-- Résultante unité `Q_s(u) = Σ_{j ∈ s} e^{i T_j u}`. -/
noncomputable def unitResultant {ι : Type*} (s : Finset ι) (T : ι → ℝ) (u : ℝ) : ℂ :=
  ∑ j ∈ s, Complex.exp (((T j * u : ℝ) : ℂ) * Complex.I)

/-- Résultante pondérée `Σ_{j ∈ s} e^{(β_j − 1/2) u} e^{i T_j u}`. -/
noncomputable def weightedResultant {ι : Type*} (s : Finset ι) (β T : ι → ℝ) (u : ℝ) : ℂ :=
  ∑ j ∈ s, ((Real.exp ((β j - 1 / 2) * u) : ℝ) : ℂ) * Complex.exp (((T j * u : ℝ) : ℂ) * Complex.I)

theorem unitResultant_re {ι : Type*} (s : Finset ι) (T : ι → ℝ) (u : ℝ) :
    (unitResultant s T u).re = ∑ j ∈ s, Real.cos (T j * u) := by
  unfold unitResultant
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun j _ => Complex.exp_ofReal_mul_I_re _

theorem weightedResultant_re {ι : Type*} (s : Finset ι) (β T : ι → ℝ) (u : ℝ) :
    (weightedResultant s β T u).re = ∑ j ∈ s, Real.exp ((β j - 1 / 2) * u) * Real.cos (T j * u) := by
  unfold weightedResultant
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- Forme amplitude-phase : `Re Q = A cos Φ`, `A = ‖Q‖`, `Φ = arg Q` (vraie aussi en `Q = 0`, où `Φ` est
conventionnel). -/
theorem resultant_amplitude_phase (Q : ℂ) : ‖Q‖ * Real.cos (Complex.arg Q) = Q.re :=
  Complex.norm_mul_cos_arg Q

/-- Passage de `N` à `N + 1` oscillations. -/
theorem unitResultant_insert {ι : Type*} [DecidableEq ι] {s : Finset ι} {j : ι} (hj : j ∉ s) (T : ι → ℝ) (u : ℝ) :
    unitResultant (insert j s) T u = Complex.exp (((T j * u : ℝ) : ℂ) * Complex.I) + unitResultant s T u := by
  unfold unitResultant; rw [Finset.sum_insert hj]

theorem weightedResultant_insert {ι : Type*} [DecidableEq ι] {s : Finset ι} {j : ι} (hj : j ∉ s) (β T : ι → ℝ)
    (u : ℝ) : weightedResultant (insert j s) β T u =
      ((Real.exp ((β j - 1 / 2) * u) : ℝ) : ℂ) * Complex.exp (((T j * u : ℝ) : ℂ) * Complex.I) +
        weightedResultant s β T u := by
  unfold weightedResultant; rw [Finset.sum_insert hj]

/-- Sur la ligne, la résultante pondérée est la résultante unité (caractérisation, aucune loi). -/
theorem weightedResultant_eq_unit {ι : Type*} {s : Finset ι} {β : ι → ℝ} (h : ∀ j ∈ s, β j = 1 / 2)
    (T : ι → ℝ) (u : ℝ) : weightedResultant s β T u = unitResultant s T u := by
  unfold weightedResultant unitResultant
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [h j hj, sub_self, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]

theorem norm_unitResultant_le {ι : Type*} (s : Finset ι) (T : ι → ℝ) (u : ℝ) :
    ‖unitResultant s T u‖ ≤ s.card := by
  unfold unitResultant
  calc ‖∑ j ∈ s, Complex.exp (((T j * u : ℝ) : ℂ) * Complex.I)‖
      ≤ ∑ j ∈ s, ‖Complex.exp (((T j * u : ℝ) : ℂ) * Complex.I)‖ := norm_sum_le _ _
    _ = ∑ j ∈ s, (1 : ℝ) := Finset.sum_congr rfl fun j _ => Complex.norm_exp_ofReal_mul_I _
    _ = s.card := by simp

theorem norm_weightedResultant_le {ι : Type*} (s : Finset ι) (β T : ι → ℝ) (u : ℝ) :
    ‖weightedResultant s β T u‖ ≤ ∑ j ∈ s, Real.exp ((β j - 1 / 2) * u) := by
  unfold weightedResultant
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- Dérivée de la résultante unité : `Q'(u) = Σ i T_j e^{i T_j u}`. -/
theorem unitResultant_hasDerivAt {ι : Type*} (s : Finset ι) (T : ι → ℝ) (u : ℝ) :
    HasDerivAt (unitResultant s T)
      (∑ j ∈ s, ((T j : ℝ) : ℂ) * Complex.I * Complex.exp (((T j * u : ℝ) : ℂ) * Complex.I)) u := by
  have h : ∀ j ∈ s, HasDerivAt (fun v : ℝ => Complex.exp (((T j * v : ℝ) : ℂ) * Complex.I))
      (((T j : ℝ) : ℂ) * Complex.I * Complex.exp (((T j * u : ℝ) : ℂ) * Complex.I)) u := by
    intro j _
    have h1 : HasDerivAt (fun v : ℝ => ((T j * v : ℝ) : ℂ)) ((T j : ℝ) : ℂ) u := by
      simpa using ((hasDerivAt_id u).const_mul (T j)).ofReal_comp
    have h2 := (h1.mul_const Complex.I).cexp
    convert h2 using 1
    ring
  exact HasDerivAt.fun_sum h

/-! ## §2 Somme des densités de comptage = résultante -/

/-- `x^{β − 1} = e^{(β − 1/2) log x}/√x` pour `x > 0`. -/
theorem rpow_sub_one_eq_exp_div_sqrt {x : ℝ} (hx : 0 < x) (β : ℝ) :
    x ^ (β - 1) = Real.exp ((β - 1 / 2) * Real.log x) / Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx, ← Real.exp_sub]
  congr 1; ring

/-- La somme des densités de modulation du canal de comptage est lue sur la résultante pondérée :
`Σ_{z ∈ s} b_z'(x) = −2/(√x log x) · Re Q_s(log x)`, toute position radiale. -/
theorem counting_density_sum_eq (s : Finset TrueZero) {x : ℝ} (hx : 1 < x) :
    ∑ z ∈ s, countingModulationDensity z x =
      -2 / (Real.sqrt x * Real.log x) *
        (weightedResultant s (fun z => rZeroRadialPosition z.1) (fun z => rZeroHeight z.1) (Real.log x)).re := by
  have hx0 : 0 < x := lt_trans one_pos hx
  rw [weightedResultant_re, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold countingModulationDensity
  rw [rpow_sub_one_eq_exp_div_sqrt hx0, mul_comm (rZeroHeight z.1) (Real.log x)]
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [mul_comm (Real.log x) (rZeroHeight z.1)]
  field_simp

/-- Sur la ligne : `Σ b_z'(x) = −2/(√x log x) · Σ cos(T_z log x)`, résultante unité. -/
theorem counting_density_sum_eq_unit (s : Finset TrueZero)
    (hOn : ∀ z ∈ s, rZeroRadialPosition z.1 = 1 / 2) {x : ℝ} (hx : 1 < x) :
    ∑ z ∈ s, countingModulationDensity z x =
      -2 / (Real.sqrt x * Real.log x) * (unitResultant s (fun z => rZeroHeight z.1) (Real.log x)).re := by
  rw [counting_density_sum_eq s hx, weightedResultant_eq_unit hOn]

/-! ## §3 Égalité centrale : intégration de la résultante -/

/-- Somme des contributions `S_s(x) = Σ_{z ∈ s} −2 Re F_z(ρ_z log x)` (primitives locales `F_z` données). -/
noncomputable def countingSum (s : Finset TrueZero) (F : TrueZero → ℂ → ℂ) (x : ℝ) : ℝ :=
  ∑ z ∈ s, -2 * (F z (zeroPoint z * (Real.log x : ℂ))).re

/-- Dérivée de la somme : `S_s'(x) = −2/(√x log x) · Re Q_s(log x)`. -/
theorem countingSum_hasDerivAt (s : Finset TrueZero) {F : TrueZero → ℂ → ℂ} {x : ℝ} (hx : 1 < x)
    (hF : ∀ z ∈ s, HasDerivAt (F z)
      (Complex.exp (zeroPoint z * (Real.log x : ℂ)) / (zeroPoint z * (Real.log x : ℂ)))
      (zeroPoint z * (Real.log x : ℂ))) :
    HasDerivAt (countingSum s F)
      (-2 / (Real.sqrt x * Real.log x) *
        (weightedResultant s (fun z => rZeroRadialPosition z.1) (fun z => rZeroHeight z.1) (Real.log x)).re) x := by
  rw [← counting_density_sum_eq s hx]
  have h : ∀ z ∈ s, HasDerivAt (fun y : ℝ => -2 * (F z (zeroPoint z * (Real.log y : ℂ))).re)
      (countingModulationDensity z x) x := fun z hz => counting_pair_hasDerivAt z hx (hF z hz)
  exact HasDerivAt.fun_sum h

theorem countingModulationDensity_continuousOn (z : TrueZero) {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (countingModulationDensity z) (Set.Icc a b) := by
  intro t ht
  have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
  have ht0 : 0 < t := lt_trans one_pos ht1
  apply ContinuousAt.continuousWithinAt
  unfold countingModulationDensity
  have hlog : ContinuousAt Real.log t := Real.continuousAt_log ht0.ne'
  refine ContinuousAt.div ?_ hlog (Real.log_pos ht1).ne'
  refine ContinuousAt.mul (ContinuousAt.mul continuousAt_const ?_) ?_
  · exact Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')
  · exact Real.continuous_cos.continuousAt.comp (continuousAt_const.mul hlog)

/-- Égalité centrale d'E330 : sur `[a, b] ⊂ ]1, ∞[`,
`S_s(b) = S_s(a) + ∫_a^b −2/(√t log t) · Re Q_s(log t) dt`. La constante `S_s(a)` est la somme des contributions
elle-même en `a`, jamais un ajustement. -/
theorem countingSum_eq_resultant_integral (s : Finset TrueZero) {F : TrueZero → ℂ → ℂ} {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b)
    (hF : ∀ z ∈ s, ∀ t ∈ Set.Icc a b, HasDerivAt (F z)
      (Complex.exp (zeroPoint z * (Real.log t : ℂ)) / (zeroPoint z * (Real.log t : ℂ)))
      (zeroPoint z * (Real.log t : ℂ))) :
    countingSum s F b = countingSum s F a +
      ∫ t in a..b, -2 / (Real.sqrt t * Real.log t) *
        (weightedResultant s (fun z => rZeroRadialPosition z.1) (fun z => rZeroHeight z.1) (Real.log t)).re := by
  have hI : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (countingSum s F)
      (∑ z ∈ s, countingModulationDensity z t) t := by
    intro t ht
    rw [hI] at ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    rw [counting_density_sum_eq s ht1]
    exact countingSum_hasDerivAt s ht1 fun z hz => hF z hz t ht
  have hcont : ContinuousOn (fun t => ∑ z ∈ s, countingModulationDensity z t) (Set.Icc a b) :=
    continuousOn_finsetSum _ fun z _ => countingModulationDensity_continuousOn z ha
  have hint : IntervalIntegrable (fun t => ∑ z ∈ s, countingModulationDensity z t) MeasureTheory.volume a b :=
    (hI ▸ hcont).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hcongr : ∫ t in a..b, ∑ z ∈ s, countingModulationDensity z t =
      ∫ t in a..b, -2 / (Real.sqrt t * Real.log t) *
        (weightedResultant s (fun z => rZeroRadialPosition z.1) (fun z => rZeroHeight z.1) (Real.log t)).re := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [hI] at ht
    exact counting_density_sum_eq s (lt_of_lt_of_le ha ht.1)
  rw [← hcongr, hftc]; ring

/-- Sur la ligne : intégration de la résultante unité `Σ e^{i T_z u}`. -/
theorem countingSum_eq_unit_resultant_integral (s : Finset TrueZero) {F : TrueZero → ℂ → ℂ} {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hOn : ∀ z ∈ s, rZeroRadialPosition z.1 = 1 / 2)
    (hF : ∀ z ∈ s, ∀ t ∈ Set.Icc a b, HasDerivAt (F z)
      (Complex.exp (zeroPoint z * (Real.log t : ℂ)) / (zeroPoint z * (Real.log t : ℂ)))
      (zeroPoint z * (Real.log t : ℂ))) :
    countingSum s F b = countingSum s F a +
      ∫ t in a..b, -2 / (Real.sqrt t * Real.log t) *
        (unitResultant s (fun z => rZeroHeight z.1) (Real.log t)).re := by
  rw [countingSum_eq_resultant_integral s ha hab hF]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [weightedResultant_eq_unit hOn]

/-! ## §4 Complément et passage de `N` à `N + 1` -/

theorem countingSum_insert [DecidableEq TrueZero] {s : Finset TrueZero} {z : TrueZero} (hz : z ∉ s) (F : TrueZero → ℂ → ℂ) (x : ℝ) :
    countingSum (insert z s) F x = -2 * (F z (zeroPoint z * (Real.log x : ℂ))).re + countingSum s F x := by
  unfold countingSum; rw [Finset.sum_insert hz]

/-- Complément `E_s = C − S_s` (`C` correction arithmétique quelconque) : ajouter un zéro retire exactement sa
contribution, `E_{insert z s} = E_s − b_z`. Aucune borne : l'ajout peut augmenter localement le complément. -/
theorem complement_insert [DecidableEq TrueZero] {s : Finset TrueZero} {z : TrueZero} (hz : z ∉ s) (F : TrueZero → ℂ → ℂ)
    (C : ℝ → ℝ) (x : ℝ) :
    C x - countingSum (insert z s) F x =
      (C x - countingSum s F x) - (-2 * (F z (zeroPoint z * (Real.log x : ℂ))).re) := by
  rw [countingSum_insert hz]; ring

/-! ## §5 Interférences : `|Q|² = N + Σ_{i ≠ j} cos((T_i − T_j)u)` et poids d'un mode seul -/

theorem mode_mul_conj (a b : ℝ) :
    Complex.exp ((a : ℂ) * Complex.I) * (starRingEnd ℂ) (Complex.exp ((b : ℂ) * Complex.I)) =
      Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- Identité d'interférence : `‖Q_s(u)‖² = Σ_i Σ_j cos((T_i − T_j)u)`, vraie pour TOUT ensemble de fréquences. -/
theorem normSq_unitResultant {ι : Type*} (s : Finset ι) (T : ι → ℝ) (u : ℝ) :
    ‖unitResultant s T u‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, Real.cos ((T i - T j) * u) := by
  have h1 : ‖unitResultant s T u‖ ^ 2 =
      (unitResultant s T u * (starRingEnd ℂ) (unitResultant s T u)).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h1]
  unfold unitResultant
  rw [map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mode_mul_conj, Complex.exp_ofReal_mul_I_re]
  congr 1; ring

/-- Forme « diagonale + compensation interfréquences » : `‖Q‖² = card s + Σ_i Σ_{j ≠ i} cos((T_i − T_j)u)`. -/
theorem normSq_unitResultant_split {ι : Type*} [DecidableEq ι] (s : Finset ι) (T : ι → ℝ) (u : ℝ) :
    ‖unitResultant s T u‖ ^ 2 =
      s.card + ∑ i ∈ s, ∑ j ∈ s.erase i, Real.cos ((T i - T j) * u) := by
  rw [normSq_unitResultant]
  have h : ∀ i ∈ s, ∑ j ∈ s, Real.cos ((T i - T j) * u) =
      1 + ∑ j ∈ s.erase i, Real.cos ((T i - T j) * u) := by
    intro i hi
    rw [← Finset.add_sum_erase s _ hi, sub_self, zero_mul, Real.cos_zero]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib]
  simp

/-- Un mode seul de la résultante pondérée a pour module son poids `e^{(β − 1/2)u}`. -/
theorem norm_weightedResultant_singleton {ι : Type*} (j : ι) (β T : ι → ℝ) (u : ℝ) :
    ‖weightedResultant {j} β T u‖ = Real.exp ((β j - 1 / 2) * u) := by
  simp only [weightedResultant, Finset.sum_singleton]
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- Le poids d'un mode ne décroît pas entre deux fenêtres `u₁ < u₂` ⟺ `β ≥ 1/2` (CARACTÉRISATION, aucune loi). -/
theorem mode_weight_nondecreasing_iff {β u₁ u₂ : ℝ} (h : u₁ < u₂) :
    Real.exp ((β - 1 / 2) * u₁) ≤ Real.exp ((β - 1 / 2) * u₂) ↔ 1 / 2 ≤ β := by
  rw [Real.exp_le_exp]
  constructor
  · intro hle; by_contra hb; have := not_le.mp hb; nlinarith
  · intro hb; nlinarith

end RHV6Fresh

#print axioms RHV6Fresh.countingSum_eq_resultant_integral
#print axioms RHV6Fresh.countingSum_eq_unit_resultant_integral
#print axioms RHV6Fresh.unitResultant_hasDerivAt
#print axioms RHV6Fresh.normSq_unitResultant_split
#print axioms RHV6Fresh.mode_weight_nondecreasing_iff
