/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.ExactSignalArchitecture
import RHV6Fresh.Terminal.RemainderRepresentation

/-!
# RHV6Fresh — synchronisation des Tours sur chaque écart premier (E243, 2026-10-13)

Objet (auteur, 2026-10-13) : des oscillations d'amplitude commune, de fréquences distinctes et de phases distinctes, qui
produisent COLLECTIVEMENT, pour chaque écart premier `[p_n, p_{n+1}]`, la correction arithmétique requise. Rien n'est normalisé.

Variable `t = log x`, écart `[a, b]` en logarithmes, centre `m = (a + b)/2`, demi-largeur `h = (b − a)/2`.

1. **Contribution exacte d'une Tour à un écart** `gapTerm ρ a b = ∫_a^b e^{ρt} dt = ∫_{e^a}^{e^b} x^{ρ−1} dx`
   (`gapTerm_eq`, `gapTerm_eq_cpow`) ; forme fermée `2h e^{ρm} sinh(ρh)/(ρh)` (`gapTerm_sinh`) ; oscillateur unitaire :
   `∫_a^b e^{iTt} dt = 2h·sinc(Th)·e^{iTm}` (`unitGapTerm_sinc`) ; membre ON (`gapTerm_onLine`).
2. **Amplitude commune sans normalisation** : la densité `x^{ρ−1}` a pour module `x^{β−1}` (`density_norm`) ; deux densités
   ont même amplitude en une abscisse `x ≠ 1` ⟺ même partie réelle (`common_amplitude_iff`) ; un membre et son miroir ont
   même amplitude ⟺ `β = 1/2` (`common_amplitude_mirror_iff`). L'amplitude commune de la structure imposée est donc, pour
   les densités exactes, la CONCLUSION (même partie réelle), pas une donnée.
3. **Loi de synchronisation par écart, démontrée (canal lissé)** : pour `1 < a`, `1 < b`,
   `R(b) − R(a) = Σ_ρ (−m_ρ/(ρ + 1))·gapTerm ρ (log a) (log b)` (`smoothed_gap_synchronization`), somme sur TOUS les vrais
   zéros, absolument convergente ; instance sur l'écart de deux premiers consécutifs (`prime_gap_synchronization`).
   Chaque Tour contribue à CHAQUE écart, par son intégrale exacte sur l'écart (filtre de largeur `2h`), pondérée par le
   facteur de lissage ; la somme infinie complète l'écart.
4. **La loi est linéaire** : la contribution d'une famille finie à un écart est l'intégrale de sa superposition
   (`gap_sum_linear`) ; les battements (termes croisés) n'apparaissent que dans l'intensité, jamais dans la correction.
5. **Portée** : un déplacement radial `δ` est une repondération `e^{δt}` de la densité (`gapTerm_shift`) ; la forme de la loi
   vaut pour toute partie réelle (`gapTerm_sinh` sans hypothèse sur `β`). La loi par écart est la formule explicite intégrée
   sur l'écart : elle ne fixe pas, à elle seule, la partie réelle d'un membre (E243, T6, T7).
-/

namespace RHV6Fresh

open RHV3Lean Complex

/-! ## 1. Contribution exacte d'une Tour à un écart -/

/-- Contribution exacte de la densité `e^{ρt}` (soit `x^{ρ−1} dx`) à l'écart logarithmique `[a, b]`. -/
noncomputable def gapTerm (ρ : ℂ) (a b : ℝ) : ℂ := ∫ t in a..b, Complex.exp (ρ * t)

/-- Centre logarithmique de l'écart. -/
noncomputable def gapCenter (a b : ℝ) : ℝ := (a + b) / 2

/-- Demi-largeur logarithmique de l'écart. -/
noncomputable def gapHalfWidth (a b : ℝ) : ℝ := (b - a) / 2

theorem gapTerm_eq {ρ : ℂ} (hρ : ρ ≠ 0) (a b : ℝ) :
    gapTerm ρ a b = (Complex.exp (ρ * b) - Complex.exp (ρ * a)) / ρ :=
  integral_exp_mul_complex hρ

/-- **Forme fermée** : `∫_a^b e^{ρt} dt = 2h·e^{ρm}·sinh(ρh)/(ρh)`, toute partie réelle. -/
theorem gapTerm_sinh {ρ : ℂ} (hρ : ρ ≠ 0) {a b : ℝ} (hab : a ≠ b) :
    gapTerm ρ a b = 2 * (gapHalfWidth a b : ℂ) * Complex.exp (ρ * gapCenter a b) *
      (Complex.sinh (ρ * gapHalfWidth a b) / (ρ * gapHalfWidth a b)) := by
  have hh : (gapHalfWidth a b : ℂ) ≠ 0 := by
    unfold gapHalfWidth
    exact_mod_cast div_ne_zero (sub_ne_zero.mpr (Ne.symm hab)) two_ne_zero
  have hb : Complex.exp (ρ * b) = Complex.exp (ρ * gapCenter a b) * Complex.exp (ρ * gapHalfWidth a b) := by
    rw [← Complex.exp_add]; congr 1; unfold gapCenter gapHalfWidth; push_cast; ring
  have ha : Complex.exp (ρ * a) = Complex.exp (ρ * gapCenter a b) * Complex.exp (-(ρ * gapHalfWidth a b)) := by
    rw [← Complex.exp_add]; congr 1; unfold gapCenter gapHalfWidth; push_cast; ring
  have hs : Complex.sinh (ρ * gapHalfWidth a b) =
      (Complex.exp (ρ * gapHalfWidth a b) - Complex.exp (-(ρ * gapHalfWidth a b))) / 2 := by
    rw [← Complex.two_sinh]; ring
  rw [gapTerm_eq hρ, hb, ha, hs]
  field_simp

/-- **Oscillateur d'amplitude unitaire** : `∫_a^b e^{iTt} dt = 2h·sinc(Th)·e^{iTm}`, `sinc z = sin z / z`. -/
theorem unitGapTerm_sinc {T : ℝ} (hT : T ≠ 0) {a b : ℝ} (hab : a ≠ b) :
    gapTerm (T * I) a b = 2 * (gapHalfWidth a b : ℂ) *
      ((Real.sin (T * gapHalfWidth a b) / (T * gapHalfWidth a b) : ℝ) : ℂ) *
      Complex.exp (T * gapCenter a b * I) := by
  have hTI : (T : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hT) I_ne_zero
  have hh : gapHalfWidth a b ≠ 0 := by
    unfold gapHalfWidth; exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hab)) two_ne_zero
  rw [gapTerm_sinh hTI hab]
  have h1 : (T : ℂ) * I * (gapHalfWidth a b : ℂ) = ((T * gapHalfWidth a b : ℝ) : ℂ) * I := by push_cast; ring
  rw [h1, Complex.sinh_mul_I, ← Complex.ofReal_sin]
  have h2 : (T : ℂ) * I * (gapCenter a b : ℂ) = (T : ℂ) * gapCenter a b * I := by ring
  rw [h2]
  have hTh : (T : ℂ) * gapHalfWidth a b ≠ 0 := mul_ne_zero (by exact_mod_cast hT) (by exact_mod_cast hh)
  push_cast
  field_simp

/-- **Membre ON** : `∫_a^b e^{(1/2+iT)t} dt = 2h·e^{m/2}·e^{iTm}·sinh((1/2+iT)h)/((1/2+iT)h)`. -/
theorem gapTerm_onLine (T : ℝ) {a b : ℝ} (hab : a ≠ b) :
    gapTerm (1 / 2 + T * I) a b = 2 * (gapHalfWidth a b : ℂ) * Complex.exp (gapCenter a b / 2) *
      Complex.exp (T * gapCenter a b * I) *
      (Complex.sinh ((1 / 2 + T * I) * gapHalfWidth a b) / ((1 / 2 + T * I) * gapHalfWidth a b)) := by
  have hρ : (1 / 2 + T * I : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [gapTerm_sinh hρ hab]
  have : Complex.exp ((1 / 2 + T * I) * gapCenter a b) =
      Complex.exp (gapCenter a b / 2) * Complex.exp (T * gapCenter a b * I) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [this]; ring

/-- Lien avec l'écart des abscisses : pour `0 < a < b` réels, `gapTerm ρ (log a) (log b) = (b^ρ − a^ρ)/ρ`,
c'est-à-dire `∫_a^b x^{ρ−1} dx`. -/
theorem gapTerm_eq_cpow {ρ : ℂ} (hρ : ρ ≠ 0) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    gapTerm ρ (Real.log a) (Real.log b) = ((b : ℂ) ^ ρ - (a : ℂ) ^ ρ) / ρ := by
  rw [gapTerm_eq hρ, Complex.cpow_def_of_ne_zero (by exact_mod_cast hb.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast ha.ne'), ← Complex.ofReal_log ha.le,
    ← Complex.ofReal_log hb.le, mul_comm ρ, mul_comm ρ]

/-! ## 2. Amplitude commune des densités exactes -/

/-- La densité exacte `x^{ρ−1}` a pour module `x^{β−1}`, sans normalisation. -/
theorem density_norm (ρ : ℂ) {x : ℝ} (hx : 0 < x) : ‖(x : ℂ) ^ (ρ - 1)‖ = x ^ (ρ.re - 1) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp

/-- **Amplitude commune ⟺ même partie réelle** (en une abscisse `x ≠ 1`). -/
theorem common_amplitude_iff (ρ₁ ρ₂ : ℂ) {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    ‖(x : ℂ) ^ (ρ₁ - 1)‖ = ‖(x : ℂ) ^ (ρ₂ - 1)‖ ↔ ρ₁.re = ρ₂.re := by
  rw [density_norm ρ₁ hx, density_norm ρ₂ hx]
  constructor
  · intro h
    have hl : Real.log x ≠ 0 := by
      intro h0
      rcases Real.log_eq_zero.mp h0 with h0 | h0 | h0
      · exact hx.ne' h0
      · exact hx1 h0
      · linarith
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx] at h
    have := Real.exp_injective h
    have h2 : (ρ₁.re - 1) = (ρ₂.re - 1) := by
      have := mul_right_cancel₀ hl (by linarith [this] : (ρ₁.re - 1) * Real.log x = (ρ₂.re - 1) * Real.log x)
      exact this
    linarith
  · intro h; rw [h]

/-- **Un membre et son miroir ont même amplitude ⟺ `β = 1/2`.** -/
theorem common_amplitude_mirror_iff (ρ : ℂ) {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    ‖(x : ℂ) ^ (ρ - 1)‖ = ‖(x : ℂ) ^ ((1 - (starRingEnd ℂ) ρ) - 1)‖ ↔ ρ.re = 1 / 2 := by
  rw [common_amplitude_iff ρ _ hx hx1]
  simp only [sub_re, one_re, conj_re]
  constructor <;> intro h <;> linarith

/-! ## 3. La loi de synchronisation par écart (canal lissé, démontrée) -/

/-- **Incrément d'un terme lissé sur un écart** : `term(b) − term(a) = (−m/(ρ + 1))·∫_a^b x^{ρ−1} dx`. -/
theorem residueTerm_gap_eq (ρ : ExplicitIndex) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    nontrivialZeroResidueTerm b ρ - nontrivialZeroResidueTerm a ρ =
      (-(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) + 1)) * gapTerm ρ (Real.log a) (Real.log b) := by
  obtain ⟨h0, h1⟩ := explicitIndex_ne_zero ρ
  rw [gapTerm_eq_cpow h0 ha hb]
  unfold nontrivialZeroResidueTerm Perron.f
  field_simp
  ring

/-- **Loi de synchronisation par écart** (canal lissé, sans normalisation) : pour `1 < a`, `1 < b`, l'incrément du reste
lissé des premiers sur `[a, b]` est la somme, sur TOUS les vrais zéros, de leurs contributions exactes à l'écart, pondérées
par `−m/(ρ + 1)`. -/
theorem smoothed_gap_synchronization {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    smoothedRemainder b - smoothedRemainder a =
      ∑' ρ : ExplicitIndex, (-(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) + 1)) *
        gapTerm ρ (Real.log a) (Real.log b) := by
  rw [smoothedRemainder_eq_tsum_residueTerm hb, smoothedRemainder_eq_tsum_residueTerm ha,
    ← (nontrivial_zero_residue_series_summable hb).tsum_sub (nontrivial_zero_residue_series_summable ha)]
  exact tsum_congr fun ρ => residueTerm_gap_eq ρ (by linarith) (by linarith)

/-- **Instance sur l'écart de deux premiers consécutifs** `[p_n, p_{n+1}]`. -/
theorem prime_gap_synchronization (n : ℕ) :
    smoothedRemainder (fnPrimeAtRank (n + 1)) - smoothedRemainder (fnPrimeAtRank n) =
      ∑' ρ : ExplicitIndex, (-(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) + 1)) *
        gapTerm ρ (Real.log (fnPrimeAtRank n)) (Real.log (fnPrimeAtRank (n + 1))) := by
  have h : ∀ k, (1 : ℝ) < fnPrimeAtRank k := fun k => by
    exact_mod_cast (thm_primeAtRank_isPrime k).one_lt
  exact smoothed_gap_synchronization (h n) (h (n + 1))

/-! ## 4. Linéarité : la correction est lue sur la superposition, non sur l'intensité -/

/-- La contribution d'une famille finie à un écart est l'intégrale de sa superposition linéaire. -/
theorem gap_sum_linear {ι : Type*} (s : Finset ι) (c ρ : ι → ℂ) (a b : ℝ) :
    ∑ j ∈ s, c j * gapTerm (ρ j) a b = ∫ t in a..b, ∑ j ∈ s, c j * Complex.exp (ρ j * t) := by
  unfold gapTerm
  rw [intervalIntegral.integral_finsetSum]
  · exact Finset.sum_congr rfl fun j _ => (intervalIntegral.integral_const_mul _ _).symm
  · intro j _
    exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-! ## 5. Portée radiale -/

/-- Un déplacement radial `δ` est une repondération `e^{δt}` de la densité sur l'écart. -/
theorem gapTerm_shift (ρ δ : ℂ) (a b : ℝ) :
    gapTerm (ρ + δ) a b = ∫ t in a..b, Complex.exp (δ * t) * Complex.exp (ρ * t) := by
  unfold gapTerm
  congr 1; funext t; rw [← Complex.exp_add]; congr 1; ring

end RHV6Fresh
