/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RemainderExponent
import RHV6Fresh.Terminal.GrammarWordLoad
import RHV6Fresh.Terminal.StableTowerSignals

/-!
# E350 — projections spectrales sur fenêtres logarithmiques translatées, fenêtres grammaticales (axe D)

Objets (premiers seuls du côté arithmétique, aucun zéro dans les définitions D1–D6) :

* `logWindowProjection f T U L = ∫_U^{U+L} f(u) e^{−iTu} du` (D1) ;
* `isolatedMode A β T u = A e^{(β−1/2)u} e^{iTu}` et l'identité de translation
  `P_T(U+H, L) = e^{(β−1/2)H} P_T(U, L)` (D2, `isolatedMode_projection_translate`), d'où l'inversion
  `β = 1/2 + (1/H) log‖P_T(U+H,L)/P_T(U,L)‖` (`isolatedMode_radial_inversion`) ;
* décomposition de la projection collective en mode cible + complément (D3, `logWindowProjection_target_add_complement`,
  linéarité de l'intégrale sur une famille finie, `logWindowProjection_finset_sum`) ;
* borne de perturbation de l'estimateur radial sous une erreur relative `ε < 1` sur les deux fenêtres (D4,
  `radial_estimator_perturbation_bound` : `|β̂ − β| ≤ (1/H) log((1+ε)/(1−ε))`) : HYPOTHÈSE quantitative explicite, jamais
  dérivée ici ;
* identités arithmétiques des fenêtres grammaticales (D5) : retour d'état ⟺ somme des écarts ≡ 0 mod 6
  (`window_return_iff_gap_sum_mod6`), verrou de canal réutilisé (`ab_ba_channel_lock`), les trois critères de « fenêtre
  complète » (retour d'état, Σ g ≡ 0 (6), #AB = #BA) coïncident (`complete_window_criteria_agree`) ;
* seule inégalité indépendante démontrée reliant fenêtres et projections (D6) : exposant 1, depuis `Λ ≥ 0` et Chebyshev
  (`normalizedSignal_projection_le_exponent_one`) ;
* transport (D7) : la projection stable d'un mode entre deux fenêtres translatées CARACTÉRISE `β = 1/2`
  (`stableProjection_iff_onLine`) : c'est une réécriture du but, pas une loi indépendante.

Tout est à hypothèses explicites ; aucune borne d'exposant `< 1` n'est démontrée ; aucun théorème ne touche le but `:854`.
-/

namespace RHV6Fresh

open Complex intervalIntegral MeasureTheory

/-! ## D1. Projections finies -/

/-- Projection d'un signal `f` sur `e^{−iTu}` le long de la fenêtre logarithmique `[U, U + L]`. -/
noncomputable def logWindowProjection (f : ℝ → ℂ) (T U L : ℝ) : ℂ :=
  ∫ u in U..U + L, f u * Complex.exp (-((T * u : ℝ) : ℂ) * Complex.I)

/-- Signal arithmétique normalisé `g(u) = R(e^u) e^{−u/2}` (normalisation analytique explicite du reste lissé compilé). -/
noncomputable def normalizedSignal (u : ℝ) : ℂ :=
  smoothedRemainder (Real.exp u) * ((Real.exp (-u / 2) : ℝ) : ℂ)

/-- Mode isolé idéal `A e^{(β−1/2)u} e^{iTu}`. -/
noncomputable def isolatedMode (A : ℂ) (β T : ℝ) (u : ℝ) : ℂ :=
  A * ((Real.exp ((β - 1 / 2) * u) : ℝ) : ℂ) * Complex.exp (((T * u : ℝ) : ℂ) * Complex.I)

theorem isolatedMode_mul_conjugate (A : ℂ) (β T u : ℝ) :
    isolatedMode A β T u * Complex.exp (-((T * u : ℝ) : ℂ) * Complex.I) =
      A * ((Real.exp ((β - 1 / 2) * u) : ℝ) : ℂ) := by
  unfold isolatedMode
  rw [mul_assoc, ← Complex.exp_add]
  have : ((T * u : ℝ) : ℂ) * Complex.I + -((T * u : ℝ) : ℂ) * Complex.I = 0 := by ring
  rw [this, Complex.exp_zero, mul_one]

/-- D1 : la projection d'un mode isolé est l'intégrale réelle de son enveloppe, fois `A`. -/
theorem isolatedMode_projection (A : ℂ) (β T U L : ℝ) :
    logWindowProjection (isolatedMode A β T) T U L =
      A * ((∫ u in U..U + L, Real.exp ((β - 1 / 2) * u) : ℝ) : ℂ) := by
  unfold logWindowProjection
  simp_rw [isolatedMode_mul_conjugate]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]

/-! ## D2. Identité de translation et inversion radiale -/

theorem exp_envelope_integral_translate (c U L H : ℝ) :
    (∫ u in U + H..U + H + L, Real.exp (c * u)) = Real.exp (c * H) * ∫ u in U..U + L, Real.exp (c * u) := by
  have h := intervalIntegral.integral_comp_add_right (fun u => Real.exp (c * u)) H (a := U) (b := U + L)
  rw [show U + L + H = U + H + L by ring] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  congr 1; ext u
  rw [← Real.exp_add]; ring_nf

/-- **D2** : `P_T(U + H, L) = e^{(β−1/2)H} P_T(U, L)` pour un mode isolé, toute position radiale. -/
theorem isolatedMode_projection_translate (A : ℂ) (β T U L H : ℝ) :
    logWindowProjection (isolatedMode A β T) T (U + H) L =
      ((Real.exp ((β - 1 / 2) * H) : ℝ) : ℂ) * logWindowProjection (isolatedMode A β T) T U L := by
  rw [isolatedMode_projection, isolatedMode_projection, exp_envelope_integral_translate]
  push_cast; ring

/-- Le rapport des modules des deux projections est l'enveloppe `e^{(β−1/2)H}`. -/
theorem isolatedMode_projection_ratio (A : ℂ) (β T U L H : ℝ)
    (h0 : logWindowProjection (isolatedMode A β T) T U L ≠ 0) :
    ‖logWindowProjection (isolatedMode A β T) T (U + H) L‖ / ‖logWindowProjection (isolatedMode A β T) T U L‖ =
      Real.exp ((β - 1 / 2) * H) := by
  rw [isolatedMode_projection_translate, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_div_assoc, div_self (norm_ne_zero_iff.mpr h0), mul_one]

/-- **Inversion radiale exacte d'un mode isolé** : `β = 1/2 + (1/H) log(‖P(U+H)‖/‖P(U)‖)`, `H ≠ 0`. -/
theorem isolatedMode_radial_inversion (A : ℂ) (β T U L H : ℝ) (hH : H ≠ 0)
    (h0 : logWindowProjection (isolatedMode A β T) T U L ≠ 0) :
    β = 1 / 2 + (1 / H) * Real.log (‖logWindowProjection (isolatedMode A β T) T (U + H) L‖ /
      ‖logWindowProjection (isolatedMode A β T) T U L‖) := by
  rw [isolatedMode_projection_ratio A β T U L H h0, Real.log_exp]
  field_simp
  ring

/-! ## D3. Décomposition de la projection collective -/

/-- Linéarité : la projection d'une somme finie de signaux intégrables est la somme des projections. -/
theorem logWindowProjection_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (T U L : ℝ)
    (hf : ∀ i ∈ s, IntervalIntegrable (fun u => f i u * Complex.exp (-((T * u : ℝ) : ℂ) * Complex.I))
      volume U (U + L)) :
    logWindowProjection (fun u => ∑ i ∈ s, f i u) T U L = ∑ i ∈ s, logWindowProjection (f i) T U L := by
  unfold logWindowProjection
  simp_rw [Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum hf

/-- **D3** : projection collective = projection du mode cible + projection du complément (le complément est, par
définition, la différence ; cette identité ne borne rien). -/
theorem logWindowProjection_target_add_complement (g target : ℝ → ℂ) (T U L : ℝ)
    (hg : IntervalIntegrable (fun u => g u * Complex.exp (-((T * u : ℝ) : ℂ) * Complex.I)) volume U (U + L))
    (ht : IntervalIntegrable (fun u => target u * Complex.exp (-((T * u : ℝ) : ℂ) * Complex.I)) volume U (U + L)) :
    logWindowProjection g T U L =
      logWindowProjection target T U L + logWindowProjection (fun u => g u - target u) T U L := by
  unfold logWindowProjection
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub hg ht]; ring

/-! ## D4. Borne de perturbation de l'estimateur radial -/

/-- Si deux quantités positives sont connues à une erreur relative `ε < 1` près, le logarithme de leur rapport est connu
à `log((1+ε)/(1−ε))` près. -/
theorem log_ratio_perturbation {a b a' b' ε : ℝ} (ha : 0 < a) (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b')
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hA : |a' - a| ≤ ε * a) (hB : |b' - b| ≤ ε * b) :
    |Real.log (b' / a') - Real.log (b / a)| ≤ Real.log ((1 + ε) / (1 - ε)) := by
  have h1ε : 0 < 1 - ε := by linarith
  have ha'lo : (1 - ε) * a ≤ a' := by
    have := (abs_le.mp hA).1; linarith
  have ha'hi : a' ≤ (1 + ε) * a := by
    have := (abs_le.mp hA).2; linarith
  have hb'lo : (1 - ε) * b ≤ b' := by
    have := (abs_le.mp hB).1; linarith
  have hb'hi : b' ≤ (1 + ε) * b := by
    have := (abs_le.mp hB).2; linarith
  rw [Real.log_div hb'.ne' ha'.ne', Real.log_div hb.ne' ha.ne', Real.log_div (by linarith) h1ε.ne']
  have hla' : Real.log ((1 - ε) * a) ≤ Real.log a' := Real.log_le_log (by positivity) ha'lo
  have hla'' : Real.log a' ≤ Real.log ((1 + ε) * a) := Real.log_le_log ha' ha'hi
  have hlb' : Real.log ((1 - ε) * b) ≤ Real.log b' := Real.log_le_log (by positivity) hb'lo
  have hlb'' : Real.log b' ≤ Real.log ((1 + ε) * b) := Real.log_le_log hb' hb'hi
  rw [Real.log_mul h1ε.ne' ha.ne'] at hla'
  rw [Real.log_mul (by linarith) ha.ne'] at hla''
  rw [Real.log_mul h1ε.ne' hb.ne'] at hlb'
  rw [Real.log_mul (by linarith) hb.ne'] at hlb''
  rw [abs_le]; constructor <;> linarith

/-- **D4** : l'estimateur `β̂ = 1/2 + (1/H) log(‖P'(U+H)‖/‖P'(U)‖)` lu sur une projection perturbée `P'` à erreur relative
`ε < 1` sur les deux fenêtres vérifie `|β̂ − β| ≤ (1/H) log((1+ε)/(1−ε))`, `H > 0`. L'hypothèse d'erreur est explicite :
rien ici ne la fournit (la borne démontrée du complément est d'exposant 1, D6). -/
theorem radial_estimator_perturbation_bound (A : ℂ) (β T U L H : ℝ) (hH : 0 < H)
    (h0 : logWindowProjection (isolatedMode A β T) T U L ≠ 0)
    (P0' P1' ε : ℝ) (hP0 : 0 < P0') (hP1 : 0 < P1') (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (e0 : |P0' - ‖logWindowProjection (isolatedMode A β T) T U L‖| ≤ ε * ‖logWindowProjection (isolatedMode A β T) T U L‖)
    (e1 : |P1' - ‖logWindowProjection (isolatedMode A β T) T (U + H) L‖| ≤
      ε * ‖logWindowProjection (isolatedMode A β T) T (U + H) L‖) :
    |(1 / 2 + (1 / H) * Real.log (P1' / P0')) - β| ≤ (1 / H) * Real.log ((1 + ε) / (1 - ε)) := by
  have hP0pos : 0 < ‖logWindowProjection (isolatedMode A β T) T U L‖ := norm_pos_iff.mpr h0
  have h1 : logWindowProjection (isolatedMode A β T) T (U + H) L ≠ 0 := by
    rw [isolatedMode_projection_translate]
    exact mul_ne_zero (by exact_mod_cast (Real.exp_pos _).ne') h0
  have hP1pos : 0 < ‖logWindowProjection (isolatedMode A β T) T (U + H) L‖ := norm_pos_iff.mpr h1
  have hβ := isolatedMode_radial_inversion A β T U L H hH.ne' h0
  have hlog := log_ratio_perturbation hP0pos hP1pos hP0 hP1 hε0 hε1 e0 e1
  have hinv : 0 < 1 / H := by positivity
  have hdiff : (1 / 2 + (1 / H) * Real.log (P1' / P0')) - β =
      (1 / H) * (Real.log (P1' / P0') - Real.log (‖logWindowProjection (isolatedMode A β T) T (U + H) L‖ /
          ‖logWindowProjection (isolatedMode A β T) T U L‖)) := by
    linear_combination (-1 : ℝ) * hβ
  rw [hdiff, abs_mul, abs_of_pos hinv]
  gcongr

/-! ## D5. Identités arithmétiques des fenêtres grammaticales -/

/-- Somme des écarts d'une fenêtre de `m` pas = différence des extrémités (télescopage, entiers). -/
theorem window_gap_sum (p : ℕ → ℕ) (hmono : Monotone p) (n m : ℕ) :
    ∑ i ∈ Finset.range m, (p (n + i + 1) - p (n + i)) = p (n + m) - p n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, show n + m + 1 = n + (m + 1) by ring]
    have h1 : p n ≤ p (n + m) := hmono (Nat.le_add_right n m)
    have h2 : p (n + m) ≤ p (n + (m + 1)) := hmono (by omega)
    omega

/-- **D5** : retour d'état (`p_{n+m} ≡ p_n (mod 6)`) ⟺ la somme des écarts de la fenêtre est divisible par 6. -/
theorem window_return_iff_gap_sum_mod6 (p : ℕ → ℕ) (hmono : Monotone p) (n m : ℕ) :
    p (n + m) % 6 = p n % 6 ↔ 6 ∣ ∑ i ∈ Finset.range m, (p (n + i + 1) - p (n + i)) := by
  rw [window_gap_sum p hmono n m]
  have h : p n ≤ p (n + m) := hmono (Nat.le_add_right n m)
  exact ⟨fun hmod => (Nat.modEq_iff_dvd' h).mp (Nat.ModEq.symm hmod),
     fun hd => ((Nat.modEq_iff_dvd' h).mpr hd).symm⟩

/-- Les trois critères de « fenêtre grammaticalement complète » coïncident : retour d'état `s_{n+m} = s_n`,
`#AB − #BA = 0` (verrou de canal) ; et, pour les premiers `> 3` (états `1`/`5` mod 6), `Σ g ≡ 0 (mod 6)`. -/
theorem complete_window_criteria_agree (s : ℕ → Bool) (m : ℕ) :
    (∑ i ∈ Finset.range m, abMinusBa (s i) (s (i + 1)) = 0) ↔ s m = s 0 := by
  rw [ab_ba_channel_lock]
  unfold stateIndicator
  cases s m <;> cases s 0 <;> simp

/-- Pour deux résidus dans `{1, 5}` mod 6 : même état ⟺ même résidu. -/
theorem state6_eq_iff_mod6 {a b : ℕ} (ha : GoodMod6 a) (hb : GoodMod6 b) :
    state6 a = state6 b ↔ a % 6 = b % 6 := by
  unfold state6; unfold GoodMod6 at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

/-! ## D6. Seule inégalité indépendante démontrée : exposant 1 -/

/-- Borne triviale de toute projection par le maximum du module sur la fenêtre. -/
theorem logWindowProjection_norm_le (f : ℝ → ℂ) (T U L C : ℝ) (hL : 0 ≤ L)
    (hf : ∀ u ∈ Set.Ioc U (U + L), ‖f u‖ ≤ C) :
    ‖logWindowProjection f T U L‖ ≤ C * L := by
  unfold logWindowProjection
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := U) (b := U + L) (C := C)
    (f := fun u => f u * Complex.exp (-((T * u : ℝ) : ℂ) * Complex.I)) (by
      intro u hu
      rw [Set.uIoc_of_le (by linarith)] at hu
      rw [norm_mul]
      have : ‖Complex.exp (-((T * u : ℝ) : ℂ) * Complex.I)‖ = 1 := by
        rw [show -((T * u : ℝ) : ℂ) * Complex.I = ((-(T * u) : ℝ) : ℂ) * Complex.I by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [this, mul_one]; exact hf u hu)
  simpa [abs_of_nonneg hL] using h

/-- Enveloppe du signal normalisé depuis `Λ ≥ 0` et Chebyshev : `‖g(u)‖ ≤ C e^{u/2}` (exposant 1 du reste). -/
theorem normalizedSignal_envelope :
    ∃ C : ℝ, ∀ u : ℝ, 0 < u → ‖normalizedSignal u‖ ≤ C * Real.exp (u / 2) := by
  obtain ⟨C, hC⟩ := smoothedRemainder_linear_growth
  refine ⟨C, fun u hu => ?_⟩
  unfold normalizedSignal
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h := hC (Real.exp u) (Real.one_lt_exp_iff.mpr hu)
  rw [Real.rpow_one] at h
  calc ‖smoothedRemainder (Real.exp u)‖ * Real.exp (-u / 2)
      ≤ C * Real.exp u * Real.exp (-u / 2) := by gcongr
    _ = C * Real.exp (u / 2) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- **D6** : la seule borne indépendante démontrée de la projection du signal des premiers sur une fenêtre est
d'exposant 1 : `‖P_T(U, L)‖ ≤ C e^{(U+L)/2} L`. Aucun exposant `< 1` n'est démontré dans le dépôt. -/
theorem normalizedSignal_projection_le_exponent_one :
    ∃ C : ℝ, ∀ T U L : ℝ, 0 < U → 0 ≤ L →
      ‖logWindowProjection normalizedSignal T U L‖ ≤ C * Real.exp ((U + L) / 2) * L := by
  obtain ⟨C, hC⟩ := normalizedSignal_envelope
  refine ⟨C, fun T U L hU hL => ?_⟩
  apply logWindowProjection_norm_le _ _ _ _ _ hL
  intro u hu
  have hu0 : 0 < u := by linarith [hu.1]
  calc ‖normalizedSignal u‖ ≤ C * Real.exp (u / 2) := hC u hu0
    _ ≤ C * Real.exp ((U + L) / 2) := by
      by_cases hC0 : 0 ≤ C
      · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hu.2])) hC0
      · exfalso
        have := hC 1 one_pos
        have hpos : 0 < ‖normalizedSignal 1‖ ∨ 0 = ‖normalizedSignal 1‖ := by
          rcases (norm_nonneg (normalizedSignal 1)).lt_or_eq with h | h
          · exact Or.inl h
          · exact Or.inr h
        have : C * Real.exp (1 / 2) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hC0) (Real.exp_pos _)
        linarith [norm_nonneg (normalizedSignal 1)]

/-! ## D7. Transport de stabilité = caractérisation -/

/-- Projection stable d'un mode isolé : même module sur toute fenêtre translatée. -/
def StableProjection (A : ℂ) (β T : ℝ) : Prop :=
  ∀ U L H : ℝ, ‖logWindowProjection (isolatedMode A β T) T (U + H) L‖ = ‖logWindowProjection (isolatedMode A β T) T U L‖

/-- **D7** : la projection stable d'un mode isolé CARACTÉRISE la position radiale un demi (`A ≠ 0`). Ce n'est pas un
transport démontré entre deux passages : c'est la réécriture, en termes de projections, du but ouvert. -/
theorem stableProjection_iff_onLine (A : ℂ) (hA : A ≠ 0) (β T : ℝ) :
    StableProjection A β T ↔ β = 1 / 2 := by
  constructor
  · intro h
    have h1 := h 0 1 1
    have h0 : logWindowProjection (isolatedMode A β T) T 0 1 ≠ 0 := by
      rw [isolatedMode_projection]
      refine mul_ne_zero hA ?_
      have hpos : 0 < ∫ u in (0:ℝ)..0 + 1, Real.exp ((β - 1 / 2) * u) :=
        intervalIntegral.intervalIntegral_pos_of_pos_on
          ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)
          (fun _ _ => Real.exp_pos _) (by norm_num)
      exact_mod_cast hpos.ne'
    have := isolatedMode_projection_ratio A β T 0 1 1 h0
    rw [h1, div_self (norm_ne_zero_iff.mpr h0)] at this
    have := Real.exp_eq_one_iff ((β - 1 / 2) * 1) |>.mp this.symm
    linarith
  · intro hβ U L H
    rw [isolatedMode_projection_translate, hβ]
    simp

end RHV6Fresh

namespace RHV6Fresh

/-! ## D6 bis. Identité analytique de battement : l'interférence d'un mode voisin à enveloppe plate s'annule exactement
sur une fenêtre rectangulaire dont la longueur est un nombre entier de périodes de battement -/

/-- Projection d'un mode voisin plat (`β' = 1/2`) de fréquence `T'` sur `e^{−iTu}` : `A ∫_U^{U+L} e^{i(T'−T)u} du`. -/
theorem neighbour_mode_projection (A : ℂ) (T' T U L : ℝ) :
    logWindowProjection (isolatedMode A (1 / 2) T') T U L =
      A * ∫ u in U..U + L, Complex.exp ((((T' - T) * u : ℝ) : ℂ) * Complex.I) := by
  unfold logWindowProjection isolatedMode
  rw [← intervalIntegral.integral_const_mul]
  congr 1; ext u
  simp only [sub_self, zero_mul, Real.exp_zero, Complex.ofReal_one, mul_one]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- Primitive de `e^{icu}` : `(e^{icu})/(ic)`, `c ≠ 0`. -/
theorem integral_exp_mul_I (c U L : ℝ) (hc : c ≠ 0) :
    (∫ u in U..U + L, Complex.exp (((c * u : ℝ) : ℂ) * Complex.I)) =
      (Complex.exp (((c * (U + L) : ℝ) : ℂ) * Complex.I) - Complex.exp (((c * U : ℝ) : ℂ) * Complex.I)) /
        ((c : ℂ) * Complex.I) := by
  have hcI : ((c : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by exact_mod_cast hc) Complex.I_ne_zero
  have hfun : ∀ u : ℝ, (((c * u : ℝ) : ℂ) * Complex.I) = ((c : ℂ) * Complex.I) * (u : ℂ) := by
    intro u; push_cast; ring
  simp_rw [hfun]
  rw [integral_exp_mul_complex hcI]

/-- **Annulation exacte de l'interférence au battement** : si `(T' − T) L = 2πk`, `k ∈ ℤ`, la projection d'un mode voisin
plat sur la fenêtre rectangulaire `[U, U + L]` est nulle (toute phase, toute position `U`). Identité analytique de la
fenêtre : elle ne lit aucun premier et ne fixe aucune position radiale. -/
theorem beat_window_interference_vanishes (A : ℂ) (T' T U L : ℝ) (hne : T' ≠ T) (k : ℤ)
    (hL : (T' - T) * L = 2 * Real.pi * k) :
    logWindowProjection (isolatedMode A (1 / 2) T') T U L = 0 := by
  rw [neighbour_mode_projection, integral_exp_mul_I _ _ _ (sub_ne_zero.mpr hne)]
  have h : Complex.exp ((((T' - T) * (U + L) : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((((T' - T) * U : ℝ) : ℂ) * Complex.I) := by
    have hLc : ((T' : ℂ) - T) * L = 2 * Real.pi * k := by exact_mod_cast hL
    rw [show (((T' - T) * (U + L) : ℝ) : ℂ) * Complex.I =
        (((T' - T) * U : ℝ) : ℂ) * Complex.I + (k : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast; linear_combination Complex.I * hLc]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h, sub_self, zero_div, mul_zero]

end RHV6Fresh
