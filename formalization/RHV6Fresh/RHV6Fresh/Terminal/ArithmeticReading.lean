/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.EngagedPersistence
import Mathlib.Analysis.MellinTransform

/-!
# RHV6Fresh — la lecture du reste arithmétique lui-même, sans passer par les zéros (2026-09-30)

Accord de l'auteur : « la pièce manquante est la lecture du reste arithmétique lui-même : montrer,
sans passer par les zéros, qu'il ne porte que des composantes sur la ligne ».

Le reste arithmétique est ici un objet écrit avec les seuls premiers :

    A(x) = Σ_{n < x} Λ(n) (1 − n/x)  −  fond(x)

(`smoothedVonMangoldtSum x - smoothedZeroBackground x`, le fond ne contient aucun zéro non
trivial). Ce fichier compile la lecture de `A` par sa seule taille :

* **Lecture par la croissance** (`cpow_series_growth_fibre_zero`) : pour une série de profils
  `Σ a_i x^{s_i}` (exposants `Re ≤ 1`, localement finie, coefficients absolument sommables), si la
  somme est bornée par `C · x^θ` pour tout `x > 1`, alors aucun exposant de partie réelle `> θ` ne
  porte de coefficient. Preuve : transformée de Mellin de la somme, analytique sur `Re z > θ` par
  la borne ; égale à `Σ a_i / (z − s_i)` sur `Re z > 1` ; prolongement le long d'une bande
  horizontale sans exposant ; lecture du pôle.
* **Application au reste arithmétique** (`smoothedRemainder_growth_bounds_zero`,
  `radial_le_of_remainder_growth`) : si `‖A(x)‖ ≤ C · x^θ` pour tout `x > 1`, tout zéro a une
  position radiale `≤ θ`.
* **La cible, écrite sans aucun zéro** (`riemannHypothesis_iff_remainder_sqrt_growth`) :
  l'hypothèse de Riemann équivaut à `∃ C, ∀ x > 1, ‖A(x)‖ ≤ C · √x`.

Borne : la dernière ligne est une équivalence. Elle écrit la cible sur les premiers seuls ; la
borne en `√x` elle-même n'est pas dérivée.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean MeasureTheory Set Filter Topology

section Growth

variable {ι : Type*}

/-- La série de profils lue en `t = 1/x`. -/
noncomputable def invSeries (s a : ι → ℂ) (t : ℝ) : ℂ := ∑' i, a i * (t : ℂ) ^ (-(s i))

/-- La série lue en `t = 1/x`, portée par `0 < t ≤ 1`. -/
noncomputable def invProfile (s a : ι → ℂ) : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator (invSeries s a)

theorem invSeries_term_bound (s a : ι → ℂ) (hre : ∀ i, (s i).re ≤ 1) (i : ι) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) : ‖a i * (t : ℂ) ^ (-(s i))‖ ≤ ‖a i‖ * t⁻¹ := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.neg_re]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h := Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2
    (show (-1 : ℝ) ≤ -(s i).re by linarith [hre i])
  rwa [Real.rpow_neg_one] at h

theorem invSeries_continuousOn (s a : ι → ℂ) (hre : ∀ i, (s i).re ≤ 1)
    (ha : Summable fun i => ‖a i‖) : ContinuousOn (invSeries s a) (Ioc (0 : ℝ) 1) := by
  refine continuousOn_of_locally_continuousOn fun t₀ ht₀ =>
    ⟨Ioi (t₀ / 2), isOpen_Ioi, by simp only [mem_Ioi]; linarith [ht₀.1], ?_⟩
  refine continuousOn_tsum (u := fun i => ‖a i‖ * (2 / t₀)) (fun i => ?_) (ha.mul_right _)
    (fun i t ht => ?_)
  · refine ContinuousOn.mul continuousOn_const (fun t ht => ?_)
    exact (Complex.continuousAt_ofReal_cpow_const t (-(s i))
      (Or.inr ht.1.1.ne')).continuousWithinAt
  · refine (invSeries_term_bound s a hre i ht.1).trans
      (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have h0 : (0 : ℝ) < t₀ / 2 := by linarith [ht₀.1]
    have h1 : t₀ / 2 ≤ t := le_of_lt ht.2
    have h2 := inv_anti₀ h0 h1
    rwa [inv_div] at h2

theorem invProfile_locallyIntegrableOn (s a : ι → ℂ) (hre : ∀ i, (s i).re ≤ 1)
    (ha : Summable fun i => ‖a i‖) : LocallyIntegrableOn (invProfile s a) (Ioi 0) := by
  refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).mpr fun k hk hkc => ?_
  unfold invProfile
  rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
    Measure.restrict_restrict measurableSet_Ioc]
  have hcomp : IsCompact (k ∩ Iic (1 : ℝ)) := hkc.inter_right isClosed_Iic
  have hsub : k ∩ Iic (1 : ℝ) ⊆ Ioc 0 1 := fun t ht => ⟨hk ht.1, ht.2⟩
  have hI : IntegrableOn (invSeries s a) (k ∩ Iic 1) :=
    ((invSeries_continuousOn s a hre ha).mono hsub).integrableOn_compact hcomp
  exact hI.mono_set (fun t ht => ⟨ht.2, ht.1.2⟩)

/-- En `t = 1/x`, la série est la série de profils en `x`. -/
theorem invSeries_eq (s a : ι → ℂ) {t : ℝ} (ht : 0 < t) :
    invSeries s a t = ∑' i, a i * ((t⁻¹ : ℝ) : ℂ) ^ s i := by
  unfold invSeries
  refine tsum_congr fun i => ?_
  have harg : ((t : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht.le]
    exact Real.pi_pos.ne
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg]

theorem invProfile_bound (s a : ι → ℂ) {θ C : ℝ}
    (hgrowth : ∀ x : ℝ, 1 < x → ‖∑' i, a i * (x : ℂ) ^ s i‖ ≤ C * x ^ θ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : ‖invProfile s a t‖ ≤ C * t ^ (-θ) := by
  unfold invProfile
  rw [indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.le⟩), invSeries_eq s a ht.1]
  have h := hgrowth t⁻¹ ((one_lt_inv₀ ht.1).mpr ht.2)
  rwa [Real.inv_rpow ht.1.le, ← Real.rpow_neg ht.1.le] at h

/-- La transformée de Mellin du profil est analytique sur `Re z > θ`. -/
theorem invProfile_mellin_differentiableAt (s a : ι → ℂ) (hre : ∀ i, (s i).re ≤ 1)
    (ha : Summable fun i => ‖a i‖) {θ C : ℝ}
    (hgrowth : ∀ x : ℝ, 1 < x → ‖∑' i, a i * (x : ℂ) ^ s i‖ ≤ C * x ^ θ) {z : ℂ}
    (hz : θ < z.re) : DifferentiableAt ℂ (mellin (invProfile s a)) z := by
  refine mellin_differentiableAt_of_isBigO_rpow (a := z.re + 1) (b := θ)
    (invProfile_locallyIntegrableOn s a hre ha) ?_ (by linarith) ?_ hz
  · have h0 : invProfile s a =ᶠ[atTop] fun _ => (0 : ℂ) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      exact indicator_of_notMem (fun h => absurd h.2 (not_le.mpr ht)) _
    exact h0.trans_isBigO (Asymptotics.isBigO_zero _ _)
  · refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    exact invProfile_bound s a hgrowth ht

/-- Sur `Re z > 1`, la transformée de Mellin du profil est la série de fractions simples. -/
theorem invProfile_mellin_eq [Countable ι] (s a : ι → ℂ) (hre : ∀ i, (s i).re ≤ 1)
    (ha : Summable fun i => ‖a i‖) {z : ℂ} (hz : 1 < z.re) :
    mellin (invProfile s a) z = ∑' i, a i / (z - s i) := by
  have hexp : ∀ i, -1 < (z - 1 - s i).re := fun i => by
    simp only [Complex.sub_re, Complex.one_re]; linarith [hre i]
  have hint : ∀ i, Integrable (fun t : ℝ => a i * (t : ℂ) ^ (z - 1 - s i))
      (volume.restrict (Ioc 0 1)) := fun i =>
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_cpow' (hexp i))).const_mul (a i)
  have hval : ∀ i, ∫ t in Ioc (0 : ℝ) 1, a i * (t : ℂ) ^ (z - 1 - s i) = a i / (z - s i) := by
    intro i
    have hne : z - 1 - s i + 1 ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.zero_re] at h1
      linarith [hre i]
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
      integral_cpow (Or.inl (hexp i)), Complex.ofReal_one, Complex.one_cpow,
      Complex.ofReal_zero, Complex.zero_cpow hne, sub_zero,
      show z - 1 - s i + 1 = z - s i by ring, mul_one_div]
  have hnorm : ∀ i, ∫ t in Ioc (0 : ℝ) 1, ‖a i * (t : ℂ) ^ (z - 1 - s i)‖ =
      ‖a i‖ / (z.re - (s i).re) := by
    intro i
    have hEq : EqOn (fun t : ℝ => ‖a i * (t : ℂ) ^ (z - 1 - s i)‖)
        (fun t : ℝ => ‖a i‖ * t ^ (z - 1 - s i).re) (Ioc 0 1) := by
      intro t ht
      change ‖a i * (t : ℂ) ^ (z - 1 - s i)‖ = ‖a i‖ * t ^ (z - 1 - s i).re
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
    have hne : (z - 1 - s i).re + 1 ≠ 0 := by linarith [hexp i]
    rw [setIntegral_congr_fun measurableSet_Ioc hEq, integral_const_mul,
      ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (hexp i)),
      Real.one_rpow, Real.zero_rpow hne, sub_zero,
      show (z - 1 - s i).re + 1 = z.re - (s i).re by
        simp only [Complex.sub_re, Complex.one_re]; ring, mul_one_div]
  have hsum : Summable fun i => ∫ t in Ioc (0 : ℝ) 1, ‖a i * (t : ℂ) ^ (z - 1 - s i)‖ := by
    rw [show (fun i => ∫ t in Ioc (0 : ℝ) 1, ‖a i * (t : ℂ) ^ (z - 1 - s i)‖) =
      fun i => ‖a i‖ / (z.re - (s i).re) from funext hnorm]
    refine Summable.of_nonneg_of_le
      (fun i => div_nonneg (norm_nonneg _) (by linarith [hre i])) (fun i => ?_)
      (ha.div_const (z.re - 1))
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) (by linarith [hre i])
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hEq1 : EqOn (fun t : ℝ => (t : ℂ) ^ (z - 1) • invSeries s a t)
      (fun t : ℝ => ∑' i, a i * (t : ℂ) ^ (z - 1 - s i)) (Ioc 0 1) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    change (t : ℂ) ^ (z - 1) • invSeries s a t = ∑' i, a i * (t : ℂ) ^ (z - 1 - s i)
    unfold invSeries
    rw [smul_eq_mul, ← tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [show z - 1 - s i = z - 1 + -(s i) by ring, Complex.cpow_add _ _ ht0]
    ring
  have hmel : mellin (invProfile s a) z =
      ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (z - 1) • invSeries s a t := by
    unfold mellin invProfile
    have hind : (fun t : ℝ => (t : ℂ) ^ (z - 1) • (Ioc (0 : ℝ) 1).indicator (invSeries s a) t) =
        (Ioc (0 : ℝ) 1).indicator (fun t : ℝ => (t : ℂ) ^ (z - 1) • invSeries s a t) := by
      funext t
      by_cases ht : t ∈ Ioc (0 : ℝ) 1
      · rw [indicator_of_mem ht, indicator_of_mem ht]
      · rw [indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
    rw [hind, setIntegral_indicator measurableSet_Ioc,
      show Ioi (0 : ℝ) ∩ Ioc 0 1 = Ioc 0 1 from
        inter_eq_right.mpr fun t ht => ht.1]
  rw [hmel, setIntegral_congr_fun measurableSet_Ioc hEq1, ← hswap]
  exact tsum_congr hval

/-- La série de fractions simples est analytique hors des exposants. -/
theorem partialFractions_differentiableOn (s a : ι → ℂ)
    (hfin : ∀ R : ℝ, {i | ‖s i‖ ≤ R}.Finite) (ha : Summable fun i => ‖a i‖)
    (hne : (Set.range s).Nonempty) :
    DifferentiableOn ℂ (fun z => ∑' i, a i / (z - s i)) (Set.range s)ᶜ := by
  have hclosed := isClosed_range_of_locallyFinite s hfin
  intro z0 hz0
  have hδ : 0 < Metric.infDist z0 (Set.range s) :=
    (hclosed.notMem_iff_infDist_pos hne).mp hz0
  set δ := Metric.infDist z0 (Set.range s) with hδdef
  set V : Set ℂ := {z | δ / 2 < Metric.infDist z (Set.range s)} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const (Metric.continuous_infDist_pt _)
  have hz0V : z0 ∈ V := by
    change δ / 2 < δ
    linarith
  have hdist : ∀ i, ∀ z ∈ V, δ / 2 < ‖z - s i‖ := fun i z hz => by
    rw [← dist_eq_norm]
    exact lt_of_lt_of_le hz (Metric.infDist_le_dist_of_mem ⟨i, rfl⟩)
  have hDV : DifferentiableOn ℂ (fun z => ∑' i, a i / (z - s i)) V := by
    refine Complex.differentiableOn_tsum_of_summable_norm (u := fun i => ‖a i‖ * (2 / δ))
      (ha.mul_right _) (fun i => ?_) hVo (fun i z hz => ?_)
    · refine DifferentiableOn.div (differentiableOn_const _)
        (differentiableOn_id.sub (differentiableOn_const _)) (fun z hz h0 => ?_)
      have h1 := hdist i z hz
      rw [h0, norm_zero] at h1
      linarith
    · rw [norm_div]
      have h1 := hdist i z hz
      rw [div_le_iff₀ (by linarith)]
      have h2 : 1 ≤ 2 / δ * ‖z - s i‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ]; linarith
      nlinarith [norm_nonneg (a i)]
  exact ((hDV z0 hz0V).differentiableAt (hVo.mem_nhds hz0V)).differentiableWithinAt

open Classical in
/-- **Lecture par la croissance.** Famille d'exposants localement finie, `Re ≤ 1`, coefficients
absolument sommables. Si `‖Σ' a i · x^{s i}‖ ≤ C · x^θ` pour tout `x > 1`, alors en tout point `p`
de partie réelle `> θ` la somme des coefficients portés par `p` est nulle. -/
theorem cpow_series_growth_fibre_zero (s a : ι → ℂ) (hre : ∀ i, (s i).re ≤ 1)
    (hfin : ∀ R : ℝ, {i | ‖s i‖ ≤ R}.Finite) (ha : Summable fun i => ‖a i‖)
    {θ C : ℝ} (hgrowth : ∀ x : ℝ, 1 < x → ‖∑' i, a i * (x : ℂ) ^ s i‖ ≤ C * x ^ θ)
    (p : ℂ) (hp : θ < p.re) :
    ∑' i, (if s i = p then a i else 0) = 0 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact tsum_empty
  obtain ⟨i0⟩ := hι
  have hne : (Set.range s).Nonempty := ⟨s i0, i0, rfl⟩
  have : Countable ι := by
    have huniv : (Set.univ : Set ι) = ⋃ n : ℕ, {i | ‖s i‖ ≤ n} := by
      ext i
      simp only [mem_univ, mem_iUnion, Set.mem_ofPred_eq, true_iff]
      exact ⟨⌈‖s i‖⌉₊, Nat.le_ceil _⟩
    rw [← Set.countable_univ_iff, huniv]
    exact Set.countable_iUnion fun n => (hfin n).countable
  set H : ℂ → ℂ := fun z => ∑' i, a i / (z - s i) with hH
  set G : ℂ → ℂ := mellin (invProfile s a) with hG
  have hHd : DifferentiableOn ℂ H (Set.range s)ᶜ :=
    partialFractions_differentiableOn s a hfin ha hne
  have hGd : ∀ z : ℂ, θ < z.re → DifferentiableAt ℂ G z := fun z hz =>
    invProfile_mellin_differentiableAt s a hre ha hgrowth hz
  have hGH : ∀ z : ℂ, 1 < z.re → G z = H z := fun z hz => invProfile_mellin_eq s a hre ha hz
  -- isolement de `p`
  obtain ⟨r, hr, hsep⟩ : ∃ r : ℝ, 0 < r ∧ ∀ i, s i ≠ p → r ≤ ‖s i - p‖ := by
    have hQ : IsClosed (s '' ({i | ‖s i‖ ≤ ‖p‖ + 1} ∩ {i | s i ≠ p})) :=
      (((hfin (‖p‖ + 1)).subset inter_subset_left).image s).isClosed
    have hpQ : p ∈ (s '' ({i | ‖s i‖ ≤ ‖p‖ + 1} ∩ {i | s i ≠ p}))ᶜ := by
      rintro ⟨i, ⟨_, hip⟩, hi⟩
      exact hip hi
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hQ.isOpen_compl p hpQ
    refine ⟨min ε 1, lt_min hε one_pos, fun i hip => ?_⟩
    by_contra hlt
    push Not at hlt
    have h1 : ‖s i‖ ≤ ‖p‖ + 1 := by
      calc ‖s i‖ = ‖p + (s i - p)‖ := by congr 1; ring
        _ ≤ ‖p‖ + ‖s i - p‖ := norm_add_le _ _
        _ ≤ ‖p‖ + 1 := by linarith [min_le_right ε 1]
    exact hball (Metric.mem_ball.mpr (by
      rw [dist_eq_norm]; exact lt_of_lt_of_le hlt (min_le_left _ _))) ⟨i, ⟨h1, hip⟩, rfl⟩
  -- séparation des hauteurs voisines de celle de `p`
  set R₀ : ℝ := |θ| + 1 + (|p.im| + 1) with hR₀
  obtain ⟨d, hd, hdsep⟩ : ∃ d : ℝ, 0 < d ∧
      ∀ i, ‖s i‖ ≤ R₀ → (s i).im ≠ p.im → d ≤ |(s i).im - p.im| := by
    have hQ : IsClosed ((fun i => (s i).im) '' ({i | ‖s i‖ ≤ R₀} ∩ {i | (s i).im ≠ p.im})) :=
      (((hfin R₀).subset inter_subset_left).image _).isClosed
    have hpQ : p.im ∈
        ((fun i => (s i).im) '' ({i | ‖s i‖ ≤ R₀} ∩ {i | (s i).im ≠ p.im}))ᶜ := by
      rintro ⟨i, ⟨_, hip⟩, hi⟩
      exact hip hi
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hQ.isOpen_compl p.im hpQ
    refine ⟨ε, hε, fun i hi hip => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hball (Metric.mem_ball.mpr (by rw [Real.dist_eq]; exact hlt)) ⟨i, ⟨hi, hip⟩, rfl⟩
  set S : ℂ := ∑' i, (if s i = p then a i else 0) with hS
  set A : ℝ := ∑' i, ‖a i‖ with hA
  have hfibre_bound : ∀ i, ‖(if s i = p then a i else 0)‖ ≤ ‖a i‖ := fun i => by
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  have hfibre_norm : Summable fun i => ‖(if s i = p then a i else 0)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hfibre_bound ha
  have hfibre : Summable fun i => (if s i = p then a i else 0) := hfibre_norm.of_norm
  by_contra hSne
  have hSpos : 0 < ‖S‖ := norm_pos_iff.mpr hSne
  have hApos : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  -- `G` est bornée près de `p`
  obtain ⟨ρ, hρ, hGb⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ z, dist z p < ρ → ‖G z‖ ≤ ‖G p‖ + 1 := by
    obtain ⟨ρ, hρ, h⟩ := Metric.continuousAt_iff.mp (hGd p hp).continuousAt 1 one_pos
    refine ⟨ρ, hρ, fun z hz => ?_⟩
    have h1 := h hz
    rw [dist_eq_norm] at h1
    calc ‖G z‖ = ‖G p + (G z - G p)‖ := by congr 1; ring
      _ ≤ ‖G p‖ + ‖G z - G p‖ := norm_add_le _ _
      _ ≤ ‖G p‖ + 1 := by linarith
  set K : ℝ := ‖G p‖ + 1 + A * (2 / r) with hK
  have hKpos : 0 < K := by
    have : 0 ≤ A * (2 / r) := mul_nonneg hApos (by positivity)
    have := norm_nonneg (G p)
    linarith
  set τ : ℝ := min (min (r / 4) (ρ / 2)) (min (min (d / 2) (1 / 2)) (‖S‖ / (2 * K))) with hτ
  have hτpos : 0 < τ := by
    refine lt_min (lt_min (by linarith) (by linarith))
      (lt_min (lt_min (by linarith) (by norm_num)) ?_)
    positivity
  have hτr : τ ≤ r / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hτρ : τ ≤ ρ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hτd : τ ≤ d / 2 := ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hτ1 : τ ≤ 1 / 2 := ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hτS : τ ≤ ‖S‖ / (2 * K) := (min_le_right _ _).trans (min_le_right _ _)
  set z : ℂ := p + (τ : ℂ) * Complex.I with hz
  have hzp : z - p = (τ : ℂ) * Complex.I := by rw [hz]; ring
  have hτn : ‖(τ : ℂ) * Complex.I‖ = τ := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτpos]
  have hzre : z.re = p.re := by simp [hz]
  have hzim : z.im = p.im + τ := by simp [hz]
  -- la bande horizontale sans exposant
  set W : Set ℂ := ({w : ℂ | θ < w.re} ∩ {w : ℂ | p.im < w.im}) ∩ {w : ℂ | w.im < p.im + 2 * τ}
    with hW
  have hWo : IsOpen W :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hWc : Convex ℝ W :=
    ((convex_halfSpace_re_gt θ).inter (convex_halfSpace_im_gt p.im)).inter
      (convex_halfSpace_im_lt (p.im + 2 * τ))
  have hWU : W ⊆ (Set.range s)ᶜ := by
    rintro w ⟨⟨hw1, hw2⟩, hw3⟩ ⟨i, rfl⟩
    have hw1' : θ < (s i).re := hw1
    have hw2' : p.im < (s i).im := hw2
    have hw3' : (s i).im < p.im + 2 * τ := hw3
    have hnorm : ‖s i‖ ≤ R₀ := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have h1 : |(s i).re| ≤ |θ| + 1 := by
        rw [abs_le]
        constructor
        · linarith [neg_abs_le θ]
        · linarith [hre i, abs_nonneg θ]
      have h2 : |(s i).im| ≤ |p.im| + 1 := by
        rw [abs_le]
        constructor
        · linarith [neg_abs_le p.im]
        · linarith [le_abs_self p.im]
      rw [hR₀]
      linarith
    have h3 := hdsep i hnorm (ne_of_gt hw2')
    rw [abs_of_pos (by linarith)] at h3
    linarith
  have hzW : z ∈ W := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change θ < z.re
      rw [hzre]; exact hp
    · change p.im < z.im
      rw [hzim]; linarith
    · change z.im < p.im + 2 * τ
      rw [hzim]; linarith
  set z₁ : ℂ := ((|θ| + 2 : ℝ) : ℂ) + ((p.im + τ : ℝ) : ℂ) * Complex.I with hz₁
  have hz₁re : z₁.re = |θ| + 2 := by simp [hz₁]
  have hz₁im : z₁.im = p.im + τ := by simp [hz₁]
  have hz₁W : z₁ ∈ W := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change θ < z₁.re
      rw [hz₁re]; linarith [le_abs_self θ]
    · change p.im < z₁.im
      rw [hz₁im]; linarith
    · change z₁.im < p.im + 2 * τ
      rw [hz₁im]; linarith
  set D : ℂ → ℂ := fun w => H w - G w with hD
  have hDd : DifferentiableOn ℂ D W := fun w hw =>
    ((hHd w (hWU hw)).mono hWU).sub (hGd w hw.1.1).differentiableWithinAt
  have hDa : AnalyticOnNhd ℂ D W := hDd.analyticOnNhd hWo
  have hev : D =ᶠ[nhds z₁] 0 := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : z₁ ∈ {w : ℂ | 1 < w.re} := by
      change 1 < z₁.re
      rw [hz₁re]; linarith [abs_nonneg θ]
    filter_upwards [hopen.mem_nhds hmem] with w hw
    change H w - G w = 0
    rw [hGH w hw, sub_self]
  have hzero : EqOn D 0 W :=
    hDa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hWc.isPreconnected hz₁W hev
  have hHz : H z = G z := by
    have h := hzero hzW
    change H z - G z = 0 at h
    exact sub_eq_zero.mp h
  have hGz : ‖G z‖ ≤ ‖G p‖ + 1 := by
    refine hGb z ?_
    rw [dist_eq_norm, hzp, hτn]
    linarith
  -- découpage : la fibre de `p`, et le reste
  have hzi : ∀ i, s i ≠ p → r / 2 ≤ ‖z - s i‖ := fun i hip => by
    have h1 := hsep i hip
    have h2 : ‖s i - p‖ ≤ ‖z - s i‖ + ‖(τ : ℂ) * Complex.I‖ := by
      calc ‖s i - p‖ = ‖-(z - s i) + (τ : ℂ) * Complex.I‖ := by congr 1; rw [hz]; ring
        _ ≤ ‖-(z - s i)‖ + ‖(τ : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = ‖z - s i‖ + ‖(τ : ℂ) * Complex.I‖ := by rw [norm_neg]
    rw [hτn] at h2
    linarith
  have hrest_bound : ∀ i, ‖(if s i = p then 0 else a i / (z - s i))‖ ≤ ‖a i‖ * (2 / r) :=
    fun i => by
      split_ifs with hip
      · rw [norm_zero]; positivity
      · rw [norm_div, div_eq_mul_one_div]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [show (2 : ℝ) / r = 1 / (r / 2) by field_simp]
        exact one_div_le_one_div_of_le (by linarith) (hzi i hip)
  have hrest_norm : Summable fun i => ‖(if s i = p then 0 else a i / (z - s i))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hrest_bound (ha.mul_right _)
  have hterm : ∀ i, a i / (z - s i) =
      (if s i = p then a i else 0) / ((τ : ℂ) * Complex.I) +
        (if s i = p then 0 else a i / (z - s i)) :=
    fun i => by
      split_ifs with hip
      · rw [hip, hzp, add_zero]
      · rw [zero_div, zero_add]
  have hsplit : H z = S / ((τ : ℂ) * Complex.I) +
      ∑' i, (if s i = p then 0 else a i / (z - s i)) := by
    change ∑' i, a i / (z - s i) = _
    rw [tsum_congr hterm, (hfibre.div_const _).tsum_add hrest_norm.of_norm, tsum_div_const]
  have hrest : ‖∑' i, (if s i = p then 0 else a i / (z - s i))‖ ≤ A * (2 / r) :=
    calc ‖∑' i, (if s i = p then 0 else a i / (z - s i))‖
        ≤ ∑' i, ‖(if s i = p then 0 else a i / (z - s i))‖ := norm_tsum_le_tsum_norm hrest_norm
      _ ≤ ∑' i, ‖a i‖ * (2 / r) := hrest_norm.tsum_le_tsum hrest_bound (ha.mul_right _)
      _ = A * (2 / r) := tsum_mul_right
  have hk : S / ((τ : ℂ) * Complex.I) =
      G z - ∑' i, (if s i = p then 0 else a i / (z - s i)) := by
    rw [← hHz, hsplit]; ring
  have hnk : ‖S‖ / τ ≤ K := by
    have h1 := congrArg norm hk
    rw [norm_div, hτn] at h1
    rw [h1, hK]
    calc ‖G z - ∑' i, (if s i = p then 0 else a i / (z - s i))‖
        ≤ ‖G z‖ + ‖∑' i, (if s i = p then 0 else a i / (z - s i))‖ := norm_sub_le _ _
      _ ≤ ‖G p‖ + 1 + A * (2 / r) := by linarith
  rw [div_le_iff₀ hτpos] at hnk
  have hfin2 : K * τ ≤ ‖S‖ / 2 := by
    calc K * τ ≤ K * (‖S‖ / (2 * K)) := mul_le_mul_of_nonneg_left hτS hKpos.le
      _ = ‖S‖ / 2 := by field_simp
  linarith

end Growth

/-! ## Application au reste arithmétique -/

/-- **Le reste arithmétique**, écrit avec les seuls premiers : la somme lissée de von Mangoldt
moins le fond. Aucun zéro non trivial n'entre dans sa définition. -/
noncomputable def smoothedRemainder (x : ℝ) : ℂ :=
  smoothedVonMangoldtSum x - smoothedZeroBackground x

/-- Le poids que la somme de von Mangoldt donne au premier de rang `n` est le poids de son
événement dans la grammaire première. -/
theorem vonMangoldt_prime_eq_event_weight (n : ℕ) :
    ArithmeticFunction.vonMangoldt (fnPrimeAtRank n) = (primalEventAt n).weight :=
  ArithmeticFunction.vonMangoldt_apply_prime (thm_primeAtRank_isPrime n)

/-- **Une borne de croissance du reste arithmétique borne la position radiale de tout zéro.** -/
theorem smoothedRemainder_growth_bounds_zero {θ C : ℝ}
    (h : ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ θ) (ρ : ExplicitIndex) :
    (ρ : ℂ).re ≤ θ := by
  classical
  by_contra hlt
  push Not at hlt
  have hsum : Summable fun σ : ExplicitIndex =>
      ‖-(zetaZeroMultiplicity (σ : ℂ) : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1))‖ :=
    multiplicity_weight_summable.congr fun σ => by rw [neg_div, norm_neg]
  have key := cpow_series_growth_fibre_zero (fun σ : ExplicitIndex => (σ : ℂ))
    (fun σ => -(zetaZeroMultiplicity (σ : ℂ) : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1)))
    explicitIndex_re_le_one explicitIndex_locallyFinite hsum (θ := θ) (C := C)
    (fun x hx => by
      have heq : ∑' σ : ExplicitIndex,
          -(zetaZeroMultiplicity (σ : ℂ) : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1)) * (x : ℂ) ^ (σ : ℂ) =
          ∑' σ : ExplicitIndex, nontrivialZeroResidueTerm x σ := by
        refine tsum_congr fun σ => ?_
        change -(zetaZeroMultiplicity (σ : ℂ) : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1)) *
            (x : ℂ) ^ (σ : ℂ) =
          -(zetaZeroMultiplicity (σ : ℂ) : ℂ) * ((x : ℂ) ^ (σ : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1)))
        ring
      rw [heq, channel_eq_arithmetic hx]
      exact h x hx) (ρ : ℂ) hlt
  rw [tsum_eq_single ρ (fun σ hσ => if_neg (fun h => hσ (Subtype.ext h))), if_pos rfl] at key
  obtain ⟨h0, h1⟩ := explicitIndex_ne_zero ρ
  have hm : (zetaZeroMultiplicity (ρ : ℂ) : ℂ) = 0 := by
    have := (div_eq_zero_iff.mp key).resolve_right (mul_ne_zero h0 h1)
    exact neg_eq_zero.mp this
  exact (zetaZeroMultiplicity_pos ρ.property.1).ne' (by exact_mod_cast hm)

/-- La même borne, lue sur un membre : sa position radiale ne dépasse pas l'exposant de
croissance du reste arithmétique. -/
theorem radial_le_of_remainder_growth {θ C : ℝ}
    (h : ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ θ) (z : TrueZero) :
    rZeroRadialPosition z.1 ≤ θ := by
  have := smoothedRemainder_growth_bounds_zero h (memberIndex z)
  rwa [show ((memberIndex z : ExplicitIndex) : ℂ) = zeroPoint z from rfl, zeroPoint_re] at this

/-- **Une borne en `√x` du reste arithmétique donne l'hypothèse de Riemann.** -/
theorem riemannHypothesis_of_remainder_sqrt_growth
    (h : ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 / 2 : ℝ)) :
    RiemannHypothesis := by
  obtain ⟨C, hC⟩ := h
  refine riemannHypothesis_of_noLowerSide fun z hβ => ?_
  have hm := radial_le_of_remainder_growth hC (mirrorMember z)
  rw [mirrorMember_radial] at hm
  linarith

/-- **Sous l'hypothèse de Riemann, le reste arithmétique est borné par `C · √x`.** -/
theorem remainder_sqrt_growth_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 / 2 : ℝ) := by
  refine ⟨∑' ρ : ExplicitIndex,
    ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_trans one_pos hx
  have hterm : ∀ ρ : ExplicitIndex, ‖nontrivialZeroResidueTerm x ρ‖ =
      ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖ * x ^ (1 / 2 : ℝ) := by
    intro ρ
    have hre : (ρ : ℂ).re = 1 / 2 := hRH (ρ : ℂ) ρ.property.1 ρ.property.2.1 ρ.property.2.2
    change ‖-(zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
      ((x : ℂ) ^ (ρ : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1)))‖ = _
    rw [norm_mul, norm_neg, norm_div, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre]
    ring
  have hsumm : Summable fun ρ : ExplicitIndex => ‖nontrivialZeroResidueTerm x ρ‖ :=
    (nontrivial_zero_residue_series_summable hx).norm
  unfold smoothedRemainder
  rw [← channel_eq_arithmetic hx]
  calc ‖∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm x ρ‖
      ≤ ∑' ρ : ExplicitIndex, ‖nontrivialZeroResidueTerm x ρ‖ := norm_tsum_le_tsum_norm hsumm
    _ = ∑' ρ : ExplicitIndex,
          ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖ * x ^ (1 / 2 : ℝ) :=
        tsum_congr hterm
    _ = (∑' ρ : ExplicitIndex,
          ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖) * x ^ (1 / 2 : ℝ) :=
        tsum_mul_right

/-- **La cible écrite sans aucun zéro.** L'hypothèse de Riemann équivaut à une borne en `√x` du
reste arithmétique, objet défini par les seuls premiers. -/
theorem riemannHypothesis_iff_remainder_sqrt_growth :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ x : ℝ, 1 < x → ‖smoothedRemainder x‖ ≤ C * x ^ (1 / 2 : ℝ) :=
  ⟨remainder_sqrt_growth_of_riemannHypothesis, riemannHypothesis_of_remainder_sqrt_growth⟩

#print axioms cpow_series_growth_fibre_zero
#print axioms vonMangoldt_prime_eq_event_weight
#print axioms smoothedRemainder_growth_bounds_zero
#print axioms radial_le_of_remainder_growth
#print axioms riemannHypothesis_of_remainder_sqrt_growth
#print axioms remainder_sqrt_growth_of_riemannHypothesis
#print axioms riemannHypothesis_iff_remainder_sqrt_growth

end RHV6Fresh
