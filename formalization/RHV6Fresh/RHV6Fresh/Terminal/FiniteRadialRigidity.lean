/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import Mathlib

/-!
# Rigidité radiale finie (théorème Z1 d'Astra) : somme finie d'exponentielles bornée ⟹ exposants `≤ 0`

Classement : OUTIL ANALYTIQUE INDÉPENDANT (famille finie, aucun zéro de zêta). Il est CONDITIONNEL à une BORNE
du signal fini, qui n'est PAS acquise pour la somme infinie des zéros : il n'exclut aucun zéro hors ligne.

* B1 `trig_poly_mean_square` : `(1/L) ∫₀ᴸ ‖Σ c_j e^{i T_j u}‖² du → Σ ‖c_j‖²` (fréquences distinctes) ;
* B2 `mean_square_tendsto_zero_of_tendsto_zero`, `trig_poly_not_tendsto_zero` ;
* B3 `finite_exponential_sum_bounded_imp_nonpos`.
-/
namespace RHV6Fresh.FiniteRadialRigidity

open Finset Filter Topology MeasureTheory intervalIntegral
open scoped ComplexConjugate

/-! ## B1. Moyenne quadratique d'un polynôme trigonométrique -/

/-- Polynôme trigonométrique `Σ c_j e^{i T_j u}`. -/
noncomputable def trigPoly {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℂ) (T : ι → ℝ) (u : ℝ) : ℂ :=
  ∑ j, c j * Complex.exp (Complex.I * ((T j : ℂ) * u))

theorem trigPoly_continuous {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℂ) (T : ι → ℝ) :
    Continuous (trigPoly c T) := by
  unfold trigPoly
  fun_prop

/-- Terme croisé `c_j conj(c_k) e^{i(T_j − T_k)u}`. -/
noncomputable def crossTerm {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℂ) (T : ι → ℝ) (j k : ι) (u : ℝ) : ℂ :=
  c j * conj (c k) * Complex.exp ((Complex.I * ((T j - T k : ℝ) : ℂ)) * (u : ℂ))

theorem trigPoly_mul_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℂ) (T : ι → ℝ) (u : ℝ) :
    trigPoly c T u * conj (trigPoly c T u) = ∑ j, ∑ k, crossTerm c T j k u := by
  unfold trigPoly crossTerm
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  have : conj (Complex.I * ((T k : ℂ) * (u:ℂ))) = -(Complex.I * ((T k : ℂ) * u)) := by
    simp [map_mul, Complex.conj_ofReal]
  rw [this]
  have h2 : (Complex.I * ((T j - T k : ℝ) : ℂ)) * (u : ℂ) =
      Complex.I * ((T j : ℂ) * u) + -(Complex.I * ((T k : ℂ) * u)) := by
    push_cast; ring
  rw [h2, Complex.exp_add]
  ring

/-- Terme hors diagonale de l'intégrale du terme croisé. -/
noncomputable def offTerm {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℂ) (T : ι → ℝ) (L : ℝ) (j k : ι) : ℂ :=
  if j = k then 0 else
    c j * conj (c k) * ((Complex.exp ((Complex.I * ((T j - T k : ℝ) : ℂ)) * (L : ℂ)) - 1) /
      (Complex.I * ((T j - T k : ℝ) : ℂ)))

/-- Constante de borne des termes croisés (indépendante de `L`). -/
noncomputable def offBound {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℂ) (T : ι → ℝ) : ℝ :=
  ∑ j, ∑ k, if j = k then 0 else ‖c j‖ * ‖c k‖ * (2 / |T j - T k|)

theorem integral_crossTerm {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℂ) {T : ι → ℝ} (hT : Function.Injective T)
    (L : ℝ) (j k : ι) :
    (∫ u in (0:ℝ)..L, crossTerm c T j k u) =
      (if j = k then ((‖c j‖ ^ 2 : ℝ) : ℂ) * (L : ℂ) else 0) + offTerm c T L j k := by
  unfold crossTerm offTerm
  rw [intervalIntegral.integral_const_mul]
  by_cases h : j = k
  · subst h
    simp only [sub_self, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, if_true, add_zero]
    rw [Complex.mul_conj']
    simp [mul_comm]
  · have hne : T j - T k ≠ 0 := sub_ne_zero.mpr (fun e => h (hT e))
    have hc : (Complex.I * ((T j - T k : ℝ) : ℂ)) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hne)
    rw [integral_exp_mul_complex hc]
    simp [h]

theorem offTerm_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℂ) {T : ι → ℝ} (L : ℝ) (j k : ι) :
    ‖offTerm c T L j k‖ ≤ if j = k then 0 else ‖c j‖ * ‖c k‖ * (2 / |T j - T k|) := by
  unfold offTerm
  by_cases h : j = k
  · simp [h]
  · simp only [h, if_false]
    rw [norm_mul, norm_mul, Complex.norm_conj, norm_div]
    have hden : ‖Complex.I * ((T j - T k : ℝ) : ℂ)‖ = |T j - T k| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hden]
    have hnum : ‖Complex.exp ((Complex.I * ((T j - T k : ℝ) : ℂ)) * (L : ℂ)) - 1‖ ≤ 2 := by
      have h1 : ‖Complex.exp ((Complex.I * ((T j - T k : ℝ) : ℂ)) * (L : ℂ))‖ = 1 := by
        have : (Complex.I * ((T j - T k : ℝ) : ℂ)) * (L : ℂ) = ((T j - T k) * L : ℝ) * Complex.I := by
          push_cast; ring
        rw [this]; exact Complex.norm_exp_ofReal_mul_I _
      calc _ ≤ ‖Complex.exp ((Complex.I * ((T j - T k : ℝ) : ℂ)) * (L : ℂ))‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [h1]; simp; norm_num
    have : ‖Complex.exp ((Complex.I * ((T j - T k : ℝ) : ℂ)) * (L : ℂ)) - 1‖ / |T j - T k| ≤ 2 / |T j - T k| :=
      div_le_div_of_nonneg_right hnum (abs_nonneg _)
    calc _ = ‖c j‖ * ‖c k‖ * (‖Complex.exp ((Complex.I * ((T j - T k : ℝ) : ℂ)) * (L : ℂ)) - 1‖ / |T j - T k|) := by
          ring
      _ ≤ _ := by gcongr

/-- Écart exact : `|∫₀ᴸ ‖P‖² − (Σ‖c_j‖²) L| ≤ K`, `K` indépendant de `L`. -/
theorem trig_poly_integral_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℂ) {T : ι → ℝ}
    (hT : Function.Injective T) (L : ℝ) :
    |(∫ u in (0:ℝ)..L, ‖trigPoly c T u‖ ^ 2) - (∑ j, ‖c j‖ ^ 2) * L| ≤ offBound c T := by
  have hcpl : (((∫ u in (0:ℝ)..L, ‖trigPoly c T u‖ ^ 2 : ℝ)) : ℂ) =
      ∑ j, ∑ k, ∫ u in (0:ℝ)..L, crossTerm c T j k u := by
    rw [← intervalIntegral.integral_ofReal]
    have hint : ∀ j k, IntervalIntegrable (crossTerm c T j k) volume 0 L := by
      intro j k
      apply Continuous.intervalIntegrable
      unfold crossTerm; fun_prop
    have : (fun u : ℝ => (((‖trigPoly c T u‖ ^ 2 : ℝ)) : ℂ)) =
        fun u => ∑ j, ∑ k, crossTerm c T j k u := by
      funext u
      rw [← trigPoly_mul_conj, Complex.mul_conj']
      push_cast; ring
    rw [this, intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [intervalIntegral.integral_finsetSum]
      intro k _; exact hint j k
    · intro j _
      apply Continuous.intervalIntegrable
      unfold crossTerm; fun_prop
  have hsplit : (((∫ u in (0:ℝ)..L, ‖trigPoly c T u‖ ^ 2 : ℝ)) : ℂ) =
      (((∑ j, ‖c j‖ ^ 2) * L : ℝ) : ℂ) + ∑ j, ∑ k, offTerm c T L j k := by
    rw [hcpl]
    simp only [integral_crossTerm c hT L, Finset.sum_add_distrib]
    congr 1
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    push_cast
    rw [Finset.sum_mul]
  have : |(∫ u in (0:ℝ)..L, ‖trigPoly c T u‖ ^ 2) - (∑ j, ‖c j‖ ^ 2) * L| =
      ‖∑ j, ∑ k, offTerm c T L j k‖ := by
    have h2 : (((∫ u in (0:ℝ)..L, ‖trigPoly c T u‖ ^ 2) - (∑ j, ‖c j‖ ^ 2) * L : ℝ) : ℂ) =
        ∑ j, ∑ k, offTerm c T L j k := by
      push_cast
      push_cast at hsplit
      rw [hsplit]; ring
    rw [← h2, Complex.norm_real, Real.norm_eq_abs]
  rw [this]
  calc ‖∑ j, ∑ k, offTerm c T L j k‖ ≤ ∑ j, ‖∑ k, offTerm c T L j k‖ := norm_sum_le _ _
    _ ≤ ∑ j, ∑ k, ‖offTerm c T L j k‖ :=
        Finset.sum_le_sum fun j _ => norm_sum_le _ _
    _ ≤ offBound c T :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => offTerm_norm_le c L j k

/-- **B1** : moyenne quadratique d'un polynôme trigonométrique à fréquences distinctes. -/
theorem trig_poly_mean_square {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℂ) {T : ι → ℝ}
    (hT : Function.Injective T) :
    Tendsto (fun L : ℝ => (1 / L) * ∫ u in (0:ℝ)..L, ‖trigPoly c T u‖ ^ 2) atTop
      (𝓝 (∑ j, ‖c j‖ ^ 2)) := by
  set S := ∑ j, ‖c j‖ ^ 2
  have hK : Tendsto (fun L : ℝ => offBound c T / L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlt : Tendsto (fun L : ℝ => |(1 / L) * (∫ u in (0:ℝ)..L, ‖trigPoly c T u‖ ^ 2) - S|) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hK
    filter_upwards [eventually_gt_atTop 0] with L hL
    have h := trig_poly_integral_sub_le c hT L
    have : (1 / L) * (∫ u in (0:ℝ)..L, ‖trigPoly c T u‖ ^ 2) - S =
        ((∫ u in (0:ℝ)..L, ‖trigPoly c T u‖ ^ 2) - S * L) / L := by
      field_simp
    rw [this, abs_div, abs_of_pos hL, mul_comm S L]
    exact div_le_div_of_nonneg_right (by simpa [mul_comm] using h) hL.le
  have := (tendsto_zero_iff_abs_tendsto_zero _).mpr hlt
  simpa using this.add_const S

#print axioms trig_poly_mean_square

/-! ## B2. Une fonction tendant vers `0` a une moyenne quadratique tendant vers `0` -/

/-- Pour `f` continue tendant vers `0` : `(1/L) ∫₀ᴸ ‖f‖² → 0`. -/
theorem mean_square_tendsto_zero_of_tendsto_zero {f : ℝ → ℂ} (hf : Continuous f)
    (h0 : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun L : ℝ => (1 / L) * ∫ u in (0:ℝ)..L, ‖f u‖ ^ 2) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall : ∀ᶠ u in atTop, ‖f u‖ ^ 2 ≤ ε / 2 := by
    have h0' : Tendsto (fun u => ‖f u‖) atTop (𝓝 0) := by simpa using h0.norm
    have := h0'.eventually (gt_mem_nhds (show (0:ℝ) < Real.sqrt (ε / 2) from
      Real.sqrt_pos.mpr (by linarith)))
    filter_upwards [this] with u hu
    have hu' : ‖f u‖ ≤ Real.sqrt (ε / 2) := hu.le
    calc ‖f u‖ ^ 2 ≤ (Real.sqrt (ε / 2)) ^ 2 := by gcongr
      _ = ε / 2 := Real.sq_sqrt (by linarith)
  obtain ⟨U, hU⟩ := eventually_atTop.mp hsmall
  set U' := max U 0 with hU'
  set C := ∫ u in (0:ℝ)..U', ‖f u‖ ^ 2 with hC
  have hcont : Continuous fun u => ‖f u‖ ^ 2 := by fun_prop
  have hC0 : 0 ≤ C := intervalIntegral.integral_nonneg (le_max_right _ _) (fun u _ => by positivity)
  have hev : ∀ᶠ L : ℝ in atTop, C / L < ε / 2 ∧ U' ≤ L ∧ 0 < L := by
    have h1 : Tendsto (fun L : ℝ => C / L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have := (h1.eventually (gt_mem_nhds (show (0:ℝ) < ε / 2 by linarith)))
    filter_upwards [this, eventually_ge_atTop U', eventually_gt_atTop 0] with L a b c
    exact ⟨a, b, c⟩
  filter_upwards [hev] with L ⟨hL1, hL2, hL3⟩
  have hsplit : (∫ u in (0:ℝ)..L, ‖f u‖ ^ 2) =
      C + ∫ u in U'..L, ‖f u‖ ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have htail : (∫ u in U'..L, ‖f u‖ ^ 2) ≤ ∫ u in U'..L, ε / 2 :=
    intervalIntegral.integral_mono_on hL2 (hcont.intervalIntegrable _ _)
      (by simp) (fun u hu => hU u (le_trans (le_max_left _ _) hu.1))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at htail
  have hI0 : 0 ≤ ∫ u in (0:ℝ)..L, ‖f u‖ ^ 2 :=
    intervalIntegral.integral_nonneg hL3.le (fun u _ => by positivity)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have : (1 / L) * (∫ u in (0:ℝ)..L, ‖f u‖ ^ 2) ≤ C / L + ε / 2 := by
    rw [hsplit]
    have : (1 / L) * (C + ∫ u in U'..L, ‖f u‖ ^ 2) ≤ (1 / L) * (C + (L - U') * (ε / 2)) := by
      gcongr
    refine le_trans this ?_
    have hU0 : 0 ≤ U' := le_max_right _ _
    have : (1 / L) * (C + (L - U') * (ε / 2)) = C / L + (L - U') / L * (ε / 2) := by
      field_simp
    rw [this]
    have : (L - U') / L ≤ 1 := by
      rw [div_le_one hL3]; linarith
    nlinarith [this]
  linarith

/-- **B2** : un polynôme trigonométrique à fréquences distinctes et à un coefficient non nul
ne tend pas vers `0`. -/
theorem trig_poly_not_tendsto_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℂ) {T : ι → ℝ}
    (hT : Function.Injective T) (hc : ∃ j, c j ≠ 0) :
    ¬ Tendsto (trigPoly c T) atTop (𝓝 0) := by
  intro h
  have h1 := mean_square_tendsto_zero_of_tendsto_zero (trigPoly_continuous c T) h
  have h2 := trig_poly_mean_square c hT
  have h3 := tendsto_nhds_unique h2 h1
  obtain ⟨j, hj⟩ := hc
  have hpos : 0 < ∑ j, ‖c j‖ ^ 2 :=
    lt_of_lt_of_le (by positivity : 0 < ‖c j‖ ^ 2)
      (Finset.single_le_sum (f := fun j => ‖c j‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j))
  linarith

/-! ## B3. Énoncé cible -/

/-- Somme finie d'exponentielles-polynômes `Σ c_j e^{(α_j + i T_j)u}`. -/
noncomputable def expSum {m : ℕ} (c : Fin m → ℂ) (α T : Fin m → ℝ) (u : ℝ) : ℂ :=
  ∑ j, c j * Complex.exp (((α j : ℂ) + (T j : ℂ) * Complex.I) * u)

/-- **B3 (Z1 d'Astra)** : famille finie à couples `(α_j, T_j)` deux à deux distincts et coefficients
non nuls ; si la somme est bornée sur `u ≥ 0`, alors tous les `α_j ≤ 0`.
Conditionnel à une BORNE du signal fini (non acquise pour la somme infinie des zéros). -/
theorem finite_exponential_sum_bounded_imp_nonpos {m : ℕ} (c : Fin m → ℂ) (α T : Fin m → ℝ)
    (hdist : ∀ j k, α j = α k → T j = T k → j = k) (hc : ∀ j, c j ≠ 0)
    (hB : ∃ B, ∀ u : ℝ, 0 ≤ u → ‖expSum c α T u‖ ≤ B) :
    ∀ j, α j ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j0, hj0⟩ := hcon
  obtain ⟨js, -, hjs⟩ := Finset.exists_max_image Finset.univ α ⟨j0, Finset.mem_univ _⟩
  set a := α js with ha
  have hapos : 0 < a := lt_of_lt_of_le hj0 (hjs j0 (Finset.mem_univ _))
  obtain ⟨B, hB⟩ := hB
  set A : Finset (Fin m) := Finset.univ.filter (fun j => α j = a) with hA
  -- terme normalisé
  let g : Fin m → ℝ → ℂ := fun j u =>
    c j * Complex.exp ((((α j - a : ℝ) : ℂ) + (T j : ℂ) * Complex.I) * u)
  let G : ℝ → ℂ := fun u => ∑ j, g j u
  have hGeq : ∀ u : ℝ, G u = expSum c α T u * Complex.exp (-(a : ℂ) * u) := by
    intro u
    simp only [G, g, expSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  have hGnorm : ∀ u : ℝ, ‖G u‖ = ‖expSum c α T u‖ * Real.exp (-a * u) := by
    intro u
    rw [hGeq, norm_mul, Complex.norm_exp]
    congr 1
    simp
  have hG0 : Tendsto G atTop (𝓝 0) := by
    have hexp : Tendsto (fun u : ℝ => B * Real.exp (-a * u)) atTop (𝓝 0) := by
      have : Tendsto (fun u : ℝ => -a * u) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      simpa using (Real.tendsto_exp_atBot.comp this).const_mul B
    refine squeeze_zero_norm' ?_ hexp
    filter_upwards [eventually_ge_atTop (0:ℝ)] with u hu
    rw [hGnorm]
    exact mul_le_mul_of_nonneg_right (hB u hu) (Real.exp_pos _).le
  -- partie hors du maximum : tend vers 0
  let R : ℝ → ℂ := fun u => ∑ j ∈ Finset.univ.filter (fun j => ¬ α j = a), g j u
  have hR0 : Tendsto R atTop (𝓝 0) := by
    have : Tendsto R atTop (𝓝 (∑ j ∈ Finset.univ.filter (fun j => ¬ α j = a), (0:ℂ))) := by
      refine tendsto_finsetSum _ fun j hj => ?_
      have hlt : α j - a < 0 := by
        have hne : ¬ α j = a := (Finset.mem_filter.mp hj).2
        exact sub_neg.mpr (lt_of_le_of_ne (hjs j (Finset.mem_univ _)) hne)
      have hn : Tendsto (fun u : ℝ => ‖g j u‖) atTop (𝓝 0) := by
        have h1 : ∀ u : ℝ, ‖g j u‖ = ‖c j‖ * Real.exp ((α j - a) * u) := by
          intro u
          simp only [g]
          rw [norm_mul, Complex.norm_exp]
          congr 2
          simp
        simp only [h1]
        have : Tendsto (fun u : ℝ => (α j - a) * u) atTop atBot :=
          tendsto_id.const_mul_atTop_of_neg hlt
        simpa using (Real.tendsto_exp_atBot.comp this).const_mul ‖c j‖
      exact tendsto_zero_iff_norm_tendsto_zero.mpr hn
    simpa using this
  -- le polynôme trigonométrique
  let As : Type := ↥A
  let cA : As → ℂ := fun j => c j
  let TA : As → ℝ := fun j => T j
  have hTA : Function.Injective TA := by
    intro j k hjk
    apply Subtype.ext
    apply hdist
    · have hj := (Finset.mem_filter.mp j.2).2
      have hk := (Finset.mem_filter.mp k.2).2
      rw [hj, hk]
    · exact hjk
  have hP : ∀ u : ℝ, trigPoly cA TA u = G u - R u := by
    intro u
    have hsplit : G u = (∑ j ∈ A, g j u) + R u := by
      simp only [G, R]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => α j = a)]
    rw [hsplit, add_sub_cancel_right]
    unfold trigPoly
    rw [← Finset.sum_coe_sort A (fun j => g j u)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : α j = a := (Finset.mem_filter.mp j.2).2
    simp only [g, cA, TA, hj, sub_self, Complex.ofReal_zero, zero_add]
    congr 2
    ring
  have hPlim : Tendsto (trigPoly cA TA) atTop (𝓝 0) := by
    have : trigPoly cA TA = fun u => G u - R u := funext hP
    rw [this]
    simpa using hG0.sub hR0
  exact trig_poly_not_tendsto_zero cA hTA ⟨(⟨js, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩ : As), hc js⟩ hPlim

#print axioms mean_square_tendsto_zero_of_tendsto_zero
#print axioms trig_poly_not_tendsto_zero
#print axioms finite_exponential_sum_bounded_imp_nonpos

end RHV6Fresh.FiniteRadialRigidity
