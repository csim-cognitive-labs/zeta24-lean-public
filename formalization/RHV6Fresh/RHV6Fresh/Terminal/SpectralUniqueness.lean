/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.RegimeCell

/-!
# RHV6Fresh — unicité de la décomposition spectrale du reste (auteur, 2026-09-30)

Question de l'auteur : la représentation exacte de `R_arith(x)` permet-elle de récupérer
individuellement les fréquences `T` et les exposants `β` ?

Réponse compilée ici, sans prémisse : **oui**. La somme infinie elle-même détermine chaque
composante.

* `cpow_series_fibre_sum_zero` : pour une famille quelconque d'exposants complexes `s i`
  (localement finie, `Re ≤ 1`) et de coefficients `a i` absolument sommables, si
  `Σ' a i · x^{s i} = 0` pour tout `x > 1`, alors en chaque point `p` du plan la somme des
  coefficients portés par `p` est nulle. Preuve : transformée de Mellin terme à terme
  (`mellin_vanish`), prolongement analytique de `Σ' a i / (z − s i)` hors des exposants, puis
  lecture du pôle en `p`.
* `cpow_series_unique` : si les exposants sont distincts, tous les coefficients sont nuls.
* `spectral_weights_unique` : des poids sur les zéros non triviaux, de contribution nulle pour tout
  `x > 1`, sont nuls — aucune modification, finie ou infinie, des multiplicités ne conserve la
  somme.
* `SpectralRepresentation` : toute représentation du canal compilé par une famille localement
  finie de points distincts et de poids. La vraie existe (`trueRepresentation`). Dans toute
  représentation : chaque zéro figure avec sa multiplicité (`contains_member`, aucun membre
  retiré) ; tout point qui n'est pas un zéro porte le poids `0` (`no_intruder`, aucun intrus) ;
  l'exposant `β`, la fréquence `T` et la multiplicité de chaque membre sont retrouvés
  (`recovers_member`) ; l'identité d'un hors-ligne n'est pas effacée
  (`off_identity_not_erased`).
* `channel_eq_arithmetic` : le canal est une fonction du seul côté arithmétique.
* `riemannHypothesis_iff_onLine_representation` : RH équivaut à l'existence d'une représentation
  du canal dont tous les exposants sont sur la ligne. C'est une caractérisation, pas une prémisse.

Borne : l'unicité retrouve les zéros tels qu'ils sont. Elle vaut pour toute famille d'exposants,
quelles que soient leurs parties réelles ; elle ne dit pas que ces parties réelles valent `1/2`.

Aucun `sorry`, aucun `admit`, aucun axiome nouveau, aucune prémisse.
-/

namespace RHV6Fresh

open RHV3Lean MeasureTheory Set

section Uniqueness

variable {ι : Type*}

/-- Une famille localement finie de points du plan a une image fermée. -/
theorem isClosed_range_of_locallyFinite (s : ι → ℂ)
    (hfin : ∀ R : ℝ, {i | ‖s i‖ ≤ R}.Finite) : IsClosed (Set.range s) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro z hz
  have hP : IsClosed (s '' {i | ‖s i‖ ≤ ‖z‖ + 1}) := ((hfin (‖z‖ + 1)).image s).isClosed
  have hzP : z ∈ (s '' {i | ‖s i‖ ≤ ‖z‖ + 1})ᶜ := fun ⟨i, _, hi⟩ => hz ⟨i, hi⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hP.isOpen_compl z hzP
  refine ⟨min ε 1, lt_min hε one_pos, ?_⟩
  rintro w hw ⟨i, rfl⟩
  have hw' : dist (s i) z < min ε 1 := hw
  have h1 : ‖s i‖ ≤ ‖z‖ + 1 := by
    have h2 : ‖s i - z‖ < 1 := by
      rw [← dist_eq_norm]; exact lt_of_lt_of_le hw' (min_le_right _ _)
    calc ‖s i‖ = ‖z + (s i - z)‖ := by congr 1; ring
      _ ≤ ‖z‖ + ‖s i - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + 1 := by linarith
  exact hball (Metric.mem_ball.mpr (lt_of_lt_of_le hw' (min_le_left _ _))) ⟨i, h1, rfl⟩

/-- **Transformée de Mellin terme à terme** : si `Σ' a i · x^{s i} = 0` pour tout `x > 1`, alors
`Σ' a i / (z − s i) = 0` pour tout `z` de partie réelle `> 1`. -/
theorem mellin_vanish [Countable ι] (s a : ι → ℂ) (hre : ∀ i, (s i).re ≤ 1)
    (ha : Summable fun i => ‖a i‖)
    (h : ∀ x : ℝ, 1 < x → ∑' i, a i * (x : ℂ) ^ s i = 0) {z : ℂ} (hz : 1 < z.re) :
    ∑' i, a i / (z - s i) = 0 := by
  have hexp : ∀ i, (s i - z - 1).re < -1 := fun i => by
    simp only [Complex.sub_re, Complex.one_re]; linarith [hre i]
  have hint : ∀ i, Integrable (fun x : ℝ => a i * (x : ℂ) ^ (s i - z - 1))
      (volume.restrict (Ioi 1)) :=
    fun i => (integrableOn_Ioi_cpow_of_lt (hexp i) one_pos).const_mul (a i)
  have hval : ∀ i, ∫ x in Ioi (1 : ℝ), a i * (x : ℂ) ^ (s i - z - 1) = a i / (z - s i) := by
    intro i
    rw [integral_const_mul, integral_Ioi_cpow_of_lt (hexp i) one_pos, Complex.ofReal_one,
      Complex.one_cpow]
    have hne : z - s i ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.re h0
      simp only [Complex.sub_re, Complex.zero_re] at h1
      linarith [hre i]
    have hne' : s i - z - 1 + 1 ≠ 0 := by
      intro h0; apply hne; linear_combination -h0
    rw [show s i - z - 1 + 1 = -(z - s i) by ring, neg_div_neg_eq, mul_one_div]
  have hnorm : ∀ i, ∫ x in Ioi (1 : ℝ), ‖a i * (x : ℂ) ^ (s i - z - 1)‖ =
      ‖a i‖ / (z.re - (s i).re) := by
    intro i
    have hEq : EqOn (fun x : ℝ => ‖a i * (x : ℂ) ^ (s i - z - 1)‖)
        (fun x : ℝ => ‖a i‖ * x ^ (s i - z - 1).re) (Ioi 1) := by
      intro x hx
      change ‖a i * (x : ℂ) ^ (s i - z - 1)‖ = ‖a i‖ * x ^ (s i - z - 1).re
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans one_pos hx)]
    rw [setIntegral_congr_fun measurableSet_Ioi hEq, integral_const_mul,
      integral_Ioi_rpow_of_lt (hexp i) one_pos, Real.one_rpow]
    have h1 : z.re - (s i).re ≠ 0 := by linarith [hre i]
    have h2 : (s i - z - 1).re + 1 = -(z.re - (s i).re) := by
      simp only [Complex.sub_re, Complex.one_re]; ring
    rw [h2]
    field_simp
  have hsum : Summable fun i => ∫ x in Ioi (1 : ℝ), ‖a i * (x : ℂ) ^ (s i - z - 1)‖ := by
    rw [show (fun i => ∫ x in Ioi (1 : ℝ), ‖a i * (x : ℂ) ^ (s i - z - 1)‖) =
      fun i => ‖a i‖ / (z.re - (s i).re) from funext hnorm]
    refine Summable.of_nonneg_of_le
      (fun i => div_nonneg (norm_nonneg _) (by linarith [hre i])) (fun i => ?_)
      (ha.div_const (z.re - 1))
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) (by linarith [hre i])
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hEq0 : EqOn (fun x : ℝ => ∑' i, a i * (x : ℂ) ^ (s i - z - 1)) (fun _ => (0 : ℂ))
      (Ioi 1) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_trans one_pos hx).ne'
    change ∑' i, a i * (x : ℂ) ^ (s i - z - 1) = 0
    have hterm : ∀ i, a i * (x : ℂ) ^ (s i - z - 1) =
        a i * (x : ℂ) ^ s i * (x : ℂ) ^ (-z - 1) := fun i => by
      rw [show s i - z - 1 = s i + (-z - 1) by ring, Complex.cpow_add _ _ hx0, mul_assoc]
    rw [tsum_congr hterm, tsum_mul_right, h x hx, zero_mul]
  have hzero : ∫ x in Ioi (1 : ℝ), ∑' i, a i * (x : ℂ) ^ (s i - z - 1) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hEq0, integral_zero]
  rw [← hzero, ← hswap]
  exact tsum_congr fun i => (hval i).symm

open Classical in
/-- **Unicité de la décomposition en profils, somme infinie.** Famille quelconque d'exposants
(localement finie, `Re ≤ 1`), coefficients absolument sommables. Si `Σ' a i · x^{s i} = 0` pour
tout `x > 1`, alors en chaque point `p` la somme des coefficients portés par `p` est nulle. -/
theorem cpow_series_fibre_sum_zero (s a : ι → ℂ) (hre : ∀ i, (s i).re ≤ 1)
    (hfin : ∀ R : ℝ, {i | ‖s i‖ ≤ R}.Finite) (ha : Summable fun i => ‖a i‖)
    (h : ∀ x : ℝ, 1 < x → ∑' i, a i * (x : ℂ) ^ s i = 0) (p : ℂ) :
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
  have hclosed := isClosed_range_of_locallyFinite s hfin
  set H : ℂ → ℂ := fun z => ∑' i, a i / (z - s i) with hH
  set U : Set ℂ := (Set.range s)ᶜ with hU
  have hUo : IsOpen U := hclosed.isOpen_compl
  -- `H` est analytique hors des exposants
  have hdiff : DifferentiableOn ℂ H U := by
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
    have hDV : DifferentiableOn ℂ H V := by
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
  have hana : AnalyticOnNhd ℂ H U := hdiff.analyticOnNhd hUo
  have hconn : IsPreconnected U :=
    ((Set.countable_range s).isConnected_compl_of_one_lt_rank
      (by simp only [Complex.rank_real_complex, Nat.one_lt_ofNat])).isPreconnected
  have h2U : (2 : ℂ) ∈ U := by
    rintro ⟨i, hi⟩
    have h1 := hre i
    rw [hi] at h1
    norm_num at h1
  have hev : H =ᶠ[nhds (2 : ℂ)] 0 := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact mellin_vanish s a hre ha h hz
  have hzero : EqOn H 0 U := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn h2U hev
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
  have hSA : ‖S‖ ≤ A :=
    (norm_tsum_le_tsum_norm hfibre_norm).trans (hfibre_norm.tsum_le_tsum hfibre_bound ha)
  have hApos : 0 < A := lt_of_lt_of_le hSpos hSA
  set t : ℝ := min (r / 4) (‖S‖ * r / (4 * A)) with ht
  have htpos : 0 < t := lt_min (by linarith) (by positivity)
  have ht1 : t ≤ r / 4 := min_le_left _ _
  have ht2 : t ≤ ‖S‖ * r / (4 * A) := min_le_right _ _
  set z : ℂ := p + (t : ℂ) with hz
  have hzp : z - p = (t : ℂ) := by rw [hz]; ring
  have htn : ‖(t : ℂ)‖ = t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
  have hzi : ∀ i, s i ≠ p → r / 2 ≤ ‖z - s i‖ := fun i hip => by
    have h1 := hsep i hip
    have h2 : ‖s i - p‖ ≤ ‖z - s i‖ + ‖(t : ℂ)‖ := by
      calc ‖s i - p‖ = ‖-(z - s i) + (t : ℂ)‖ := by congr 1; rw [hz]; ring
        _ ≤ ‖-(z - s i)‖ + ‖(t : ℂ)‖ := norm_add_le _ _
        _ = ‖z - s i‖ + ‖(t : ℂ)‖ := by rw [norm_neg]
    rw [htn] at h2
    linarith
  have hzU : z ∈ U := by
    rintro ⟨i, hi⟩
    by_cases hip : s i = p
    · have h0 : (t : ℂ) = 0 := by rw [← hzp, ← hi, hip]; ring
      exact htpos.ne' (by exact_mod_cast h0)
    · have h1 := hzi i hip
      rw [← hi, sub_self, norm_zero] at h1
      linarith
  have hHz : H z = 0 := hzero hzU
  -- découpage : la fibre de `p`, et le reste
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
      (if s i = p then a i else 0) / (t : ℂ) + (if s i = p then 0 else a i / (z - s i)) :=
    fun i => by
      split_ifs with hip
      · rw [hip, hzp, add_zero]
      · rw [zero_div, zero_add]
  have hsplit : H z = S / (t : ℂ) + ∑' i, (if s i = p then 0 else a i / (z - s i)) := by
    change ∑' i, a i / (z - s i) = _
    rw [tsum_congr hterm, (hfibre.div_const _).tsum_add hrest_norm.of_norm, tsum_div_const]
  have hrest : ‖∑' i, (if s i = p then 0 else a i / (z - s i))‖ ≤ A * (2 / r) :=
    calc ‖∑' i, (if s i = p then 0 else a i / (z - s i))‖
        ≤ ∑' i, ‖(if s i = p then 0 else a i / (z - s i))‖ := norm_tsum_le_tsum_norm hrest_norm
      _ ≤ ∑' i, ‖a i‖ * (2 / r) := hrest_norm.tsum_le_tsum hrest_bound (ha.mul_right _)
      _ = A * (2 / r) := tsum_mul_right
  have hk : S / (t : ℂ) = -∑' i, (if s i = p then 0 else a i / (z - s i)) := by
    rw [hHz] at hsplit
    linear_combination -hsplit
  have hnk : ‖S‖ / t ≤ A * (2 / r) := by
    have h1 := congrArg norm hk
    rw [norm_div, htn, norm_neg] at h1
    rw [h1]
    exact hrest
  rw [div_le_iff₀ htpos] at hnk
  have hfin2 : A * (2 / r) * t ≤ ‖S‖ / 2 := by
    calc A * (2 / r) * t ≤ A * (2 / r) * (‖S‖ * r / (4 * A)) :=
          mul_le_mul_of_nonneg_left ht2 (by positivity)
      _ = ‖S‖ / 2 := by field_simp; ring
  linarith

/-- **Exposants distincts : tous les coefficients sont nuls.** -/
theorem cpow_series_unique (s a : ι → ℂ) (hinj : Function.Injective s)
    (hre : ∀ i, (s i).re ≤ 1) (hfin : ∀ R : ℝ, {i | ‖s i‖ ≤ R}.Finite)
    (ha : Summable fun i => ‖a i‖)
    (h : ∀ x : ℝ, 1 < x → ∑' i, a i * (x : ℂ) ^ s i = 0) : ∀ i, a i = 0 := by
  classical
  intro k
  have hk := cpow_series_fibre_sum_zero s a hre hfin ha h (s k)
  rw [tsum_eq_single k (fun j hj => if_neg (fun hjk => hj (hinj hjk))), if_pos rfl] at hk
  exact hk

end Uniqueness

/-! ## Application aux zéros non triviaux -/

/-- Les zéros non triviaux forment une famille localement finie. -/
theorem explicitIndex_locallyFinite (R : ℝ) : {ρ : ExplicitIndex | ‖(ρ : ℂ)‖ ≤ R}.Finite := by
  have hfin := nontrivialZetaZerosByHeight_finite (R + 1)
  refine Set.Finite.of_finite_image (hfin.subset ?_)
    (Set.injOn_of_injective Subtype.coe_injective)
  rintro _ ⟨ρ, hρ, rfl⟩
  exact ⟨ρ.property, lt_of_le_of_lt ((Complex.abs_im_le_norm _).trans hρ) (by linarith)⟩

theorem explicitIndex_re_le_one (ρ : ExplicitIndex) : (ρ : ℂ).re ≤ 1 :=
  (isNontrivialZetaZero_re_mem_Ioo ρ.property).2.le

/-- **Unicité des poids sur les zéros** : des poids de contribution nulle pour tout `x > 1` sont
nuls. Aucune modification des multiplicités, finie ou infinie, ne conserve la somme. -/
theorem spectral_weights_unique (w : ExplicitIndex → ℂ)
    (hw : Summable fun ρ : ExplicitIndex => ‖w ρ / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖)
    (h : ∀ x : ℝ, 1 < x → ∑' ρ : ExplicitIndex, w ρ * Perron.f x (ρ : ℂ) = 0) :
    ∀ ρ, w ρ = 0 := by
  have key := cpow_series_unique (fun ρ : ExplicitIndex => (ρ : ℂ))
    (fun ρ => w ρ / ((ρ : ℂ) * ((ρ : ℂ) + 1))) Subtype.coe_injective explicitIndex_re_le_one
    explicitIndex_locallyFinite hw (fun x hx => by
      rw [← h x hx]
      refine tsum_congr fun ρ => ?_
      change w ρ / ((ρ : ℂ) * ((ρ : ℂ) + 1)) * (x : ℂ) ^ (ρ : ℂ) =
        w ρ * ((x : ℂ) ^ (ρ : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1)))
      ring)
  intro ρ
  obtain ⟨h0, h1⟩ := explicitIndex_ne_zero ρ
  exact (div_eq_zero_iff.mp (key ρ)).resolve_right (mul_ne_zero h0 h1)

/-- Les poids vrais `m(ρ) / (ρ (ρ + 1))` sont absolument sommables. -/
theorem multiplicity_weight_summable :
    Summable fun ρ : ExplicitIndex =>
      ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖ := by
  have h2 := (nontrivial_zero_residue_series_summable (x := 2) (by norm_num)).norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ρ => ?_) h2
  change ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))‖ ≤
    ‖-(zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
      ((((2 : ℝ) : ℂ)) ^ (ρ : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1)))‖
  rw [norm_mul, norm_neg, norm_div, norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h1 : (1 : ℝ) ≤ 2 ^ (ρ : ℂ).re :=
    Real.one_le_rpow (by norm_num) (isNontrivialZetaZero_re_mem_Ioo ρ.property).1.le
  calc ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖
      = ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ * (1 / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) := by ring
    _ ≤ ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ *
        (2 ^ (ρ : ℂ).re / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 (norm_nonneg _))
        (norm_nonneg _)

/-- Le canal compilé est une fonction du seul côté arithmétique : la somme lissée de von Mangoldt
moins le fond. -/
theorem channel_eq_arithmetic {x : ℝ} (hx : 1 < x) :
    ∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm x ρ =
      smoothedVonMangoldtSum x - smoothedZeroBackground x := by
  rw [← smoothedZeroFormula_eq_smoothedVonMangoldtSum hx, smoothedZeroFormula_sub_background hx]

/-- Une série de profils de coefficients absolument sommables et d'exposants `Re ≤ 1` est
sommable en tout `x > 1`. -/
theorem summable_profiles {ι : Type*} (s a : ι → ℂ) (hre : ∀ i, (s i).re ≤ 1)
    (ha : Summable fun i => ‖a i‖) {x : ℝ} (hx : 1 < x) :
    Summable fun i => a i * (x : ℂ) ^ s i := by
  refine Summable.of_norm_bounded (ha.mul_right x) (fun i => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans one_pos hx)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc x ^ (s i).re ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le (hre i)
    _ = x := Real.rpow_one x

/-- **Une représentation spectrale du canal compilé** : une famille de points distincts du plan,
localement finie, et des poids, dont la série de noyaux redonne le canal pour tout `x > 1`. -/
structure SpectralRepresentation (ι : Type*) where
  point : ι → ℂ
  weight : ι → ℂ
  injective : Function.Injective point
  re_le_one : ∀ i, (point i).re ≤ 1
  ne_zero : ∀ i, point i ≠ 0 ∧ point i + 1 ≠ 0
  locallyFinite : ∀ R : ℝ, {i | ‖point i‖ ≤ R}.Finite
  summable : Summable fun i => ‖weight i / (point i * (point i + 1))‖
  represents : ∀ x : ℝ, 1 < x →
    ∑' i, weight i * Perron.f x (point i) = ∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm x ρ

/-- **La représentation vraie** : les zéros non triviaux, avec les poids `−m(ρ)`. -/
noncomputable def trueRepresentation : SpectralRepresentation ExplicitIndex where
  point ρ := (ρ : ℂ)
  weight ρ := -(zetaZeroMultiplicity (ρ : ℂ) : ℂ)
  injective := Subtype.coe_injective
  re_le_one := explicitIndex_re_le_one
  ne_zero := explicitIndex_ne_zero
  locallyFinite := explicitIndex_locallyFinite
  summable := by
    refine multiplicity_weight_summable.congr fun ρ => ?_
    rw [neg_div, norm_neg]
  represents := fun _ _ => rfl

namespace SpectralRepresentation

variable {ι : Type*} (Rep : SpectralRepresentation ι)

open Classical in
/-- En chaque point `p` du plan, le poids que la représentation porte en `p` (divisé par
`p (p + 1)`) plus le poids vrai en `p` est nul. -/
theorem fibre_balance (p : ℂ) :
    (∑' i, (if Rep.point i = p then Rep.weight i / (Rep.point i * (Rep.point i + 1)) else 0)) +
      ∑' ρ : ExplicitIndex, (if (ρ : ℂ) = p then
        (zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1)) else 0) = 0 := by
  set S : ι ⊕ ExplicitIndex → ℂ := Sum.elim Rep.point (fun ρ => (ρ : ℂ)) with hS
  set a : ι ⊕ ExplicitIndex → ℂ := Sum.elim
    (fun i => Rep.weight i / (Rep.point i * (Rep.point i + 1)))
    (fun ρ => (zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))) with ha
  have hre : ∀ u, (S u).re ≤ 1 := by
    rintro (i | ρ)
    · exact Rep.re_le_one i
    · exact explicitIndex_re_le_one ρ
  have hfin : ∀ R : ℝ, {u | ‖S u‖ ≤ R}.Finite := by
    intro R
    refine (((Rep.locallyFinite R).image Sum.inl).union
      ((explicitIndex_locallyFinite R).image Sum.inr)).subset ?_
    rintro (i | ρ) hu
    · exact Or.inl ⟨i, hu, rfl⟩
    · exact Or.inr ⟨ρ, hu, rfl⟩
  have hsum : Summable fun u => ‖a u‖ :=
    Summable.sum (fun u => ‖a u‖) Rep.summable multiplicity_weight_summable
  have hzero : ∀ x : ℝ, 1 < x → ∑' u, a u * (x : ℂ) ^ S u = 0 := by
    intro x hx
    have h1 : Summable ((fun u => a u * (x : ℂ) ^ S u) ∘ Sum.inl) :=
      summable_profiles Rep.point _ Rep.re_le_one Rep.summable hx
    have h2 : Summable ((fun u => a u * (x : ℂ) ^ S u) ∘ Sum.inr) :=
      summable_profiles (fun ρ : ExplicitIndex => (ρ : ℂ)) _ explicitIndex_re_le_one
        multiplicity_weight_summable hx
    rw [Summable.tsum_sum h1 h2]
    have e1 : ∑' i, a (Sum.inl i) * (x : ℂ) ^ S (Sum.inl i) =
        ∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm x ρ := by
      rw [← Rep.represents x hx]
      refine tsum_congr fun i => ?_
      change Rep.weight i / (Rep.point i * (Rep.point i + 1)) * (x : ℂ) ^ Rep.point i =
        Rep.weight i * ((x : ℂ) ^ Rep.point i / (Rep.point i * (Rep.point i + 1)))
      ring
    have e2 : ∑' ρ : ExplicitIndex, a (Sum.inr ρ) * (x : ℂ) ^ S (Sum.inr ρ) =
        -∑' ρ : ExplicitIndex, nontrivialZeroResidueTerm x ρ := by
      rw [← tsum_neg]
      refine tsum_congr fun ρ => ?_
      change (zetaZeroMultiplicity (ρ : ℂ) : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1)) * (x : ℂ) ^ (ρ : ℂ) =
        -(-(zetaZeroMultiplicity (ρ : ℂ) : ℂ) * ((x : ℂ) ^ (ρ : ℂ) / ((ρ : ℂ) * ((ρ : ℂ) + 1))))
      ring
    rw [e1, e2, add_neg_cancel]
  have key := cpow_series_fibre_sum_zero S a hre hfin hsum hzero p
  have hb : ∀ u, ‖(if S u = p then a u else 0)‖ ≤ ‖a u‖ := fun u => by
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  have hs1 : Summable ((fun u => if S u = p then a u else 0) ∘ Sum.inl) :=
    Summable.of_norm_bounded Rep.summable (fun i => hb (Sum.inl i))
  have hs2 : Summable ((fun u => if S u = p then a u else 0) ∘ Sum.inr) :=
    Summable.of_norm_bounded multiplicity_weight_summable (fun ρ => hb (Sum.inr ρ))
  rw [Summable.tsum_sum hs1 hs2] at key
  exact key

/-- **Aucun membre retiré** : tout zéro non trivial figure dans la représentation, avec
exactement sa multiplicité. -/
theorem contains_member (ρ : ExplicitIndex) :
    ∃ i, Rep.point i = (ρ : ℂ) ∧ Rep.weight i = -(zetaZeroMultiplicity (ρ : ℂ) : ℂ) := by
  classical
  have key := Rep.fibre_balance (ρ : ℂ)
  obtain ⟨h0, h1⟩ := explicitIndex_ne_zero ρ
  have hD : (ρ : ℂ) * ((ρ : ℂ) + 1) ≠ 0 := mul_ne_zero h0 h1
  rw [tsum_eq_single ρ (fun σ hσ => if_neg (fun h => hσ (Subtype.ext h))), if_pos rfl] at key
  by_cases hex : ∃ i, Rep.point i = (ρ : ℂ)
  · obtain ⟨i, hi⟩ := hex
    refine ⟨i, hi, ?_⟩
    rw [tsum_eq_single i (fun j hj => if_neg (fun h => hj (Rep.injective (h.trans hi.symm)))),
      if_pos hi, hi, ← add_div] at key
    have := (div_eq_zero_iff.mp key).resolve_right hD
    linear_combination this
  · exfalso
    push Not at hex
    rw [tsum_congr (fun i => if_neg (hex i)), tsum_zero, zero_add] at key
    have hm : (zetaZeroMultiplicity (ρ : ℂ) : ℂ) = 0 := (div_eq_zero_iff.mp key).resolve_right hD
    exact (zetaZeroMultiplicity_pos ρ.property.1).ne' (by exact_mod_cast hm)

/-- **Aucun intrus** : un point de la représentation qui n'est pas un zéro non trivial porte le
poids `0`. -/
theorem no_intruder (i : ι) (hi : ¬ IsNontrivialZetaZero (Rep.point i)) : Rep.weight i = 0 := by
  classical
  have key := Rep.fibre_balance (Rep.point i)
  rw [tsum_eq_single i (fun j hj => if_neg (fun h => hj (Rep.injective h))), if_pos rfl,
    tsum_congr (fun ρ : ExplicitIndex => if_neg (fun h : (ρ : ℂ) = Rep.point i =>
      hi (h ▸ ρ.property))), tsum_zero, add_zero] at key
  obtain ⟨h0, h1⟩ := Rep.ne_zero i
  exact (div_eq_zero_iff.mp key).resolve_right (mul_ne_zero h0 h1)

/-- **L'identité de chaque membre est retrouvée dans toute représentation** : son exposant `β`,
sa fréquence `T` et sa multiplicité. -/
theorem recovers_member (z : TrueZero) :
    ∃ i, (Rep.point i).re = rZeroRadialPosition z.1 ∧ (Rep.point i).im = rZeroHeight z.1 ∧
      Rep.weight i = -(zetaZeroMultiplicity (zeroPoint z) : ℂ) ∧ Rep.weight i ≠ 0 := by
  obtain ⟨i, hi, hw⟩ := Rep.contains_member (memberIndex z)
  have hi' : Rep.point i = zeroPoint z := hi
  have hw' : Rep.weight i = -(zetaZeroMultiplicity (zeroPoint z) : ℂ) := hw
  refine ⟨i, by rw [hi', zeroPoint_re], by rw [hi', zeroPoint_im], hw', ?_⟩
  rw [hw', neg_ne_zero]
  exact_mod_cast (zetaZeroMultiplicity_pos (zeroPoint_isNontrivial z).1).ne'

/-- **L'identité d'un hors-ligne n'est pas effacée** : s'il existe un zéro hors ligne, toute
représentation du canal porte un poids non nul en un exposant de partie réelle `≠ 1/2`. -/
theorem off_identity_not_erased {z : TrueZero} (hOff : PIsOffCriticalLine z.1) :
    ∃ i, Rep.weight i ≠ 0 ∧ (Rep.point i).re ≠ 1 / 2 := by
  obtain ⟨i, hre, _, _, hne⟩ := Rep.recovers_member z
  exact ⟨i, hne, by rw [hre]; exact hOff⟩

/-- Une représentation dont tous les exposants de poids non nul sont sur la ligne force RH. -/
theorem riemannHypothesis_of_onLine
    (h : ∀ i, Rep.weight i ≠ 0 → (Rep.point i).re = 1 / 2) : RiemannHypothesis :=
  riemannHypothesis_of_noOff fun _ hOff => by
    obtain ⟨i, hne, hre⟩ := Rep.off_identity_not_erased hOff
    exact hre (h i hne)

end SpectralRepresentation

/-- **Caractérisation** : RH équivaut à « le canal compilé (donc le reste arithmétique lissé)
admet une représentation dont tous les exposants sont sur la ligne ». -/
theorem riemannHypothesis_iff_onLine_representation :
    RiemannHypothesis ↔
      ∃ Rep : SpectralRepresentation ExplicitIndex,
        ∀ i, Rep.weight i ≠ 0 → (Rep.point i).re = 1 / 2 :=
  ⟨fun hRH => ⟨trueRepresentation, fun ρ _ =>
      hRH (ρ : ℂ) ρ.property.1 ρ.property.2.1 ρ.property.2.2⟩,
    fun ⟨Rep, h⟩ => Rep.riemannHypothesis_of_onLine h⟩

#print axioms isClosed_range_of_locallyFinite
#print axioms mellin_vanish
#print axioms cpow_series_fibre_sum_zero
#print axioms cpow_series_unique
#print axioms spectral_weights_unique
#print axioms multiplicity_weight_summable
#print axioms channel_eq_arithmetic
#print axioms trueRepresentation
#print axioms SpectralRepresentation.fibre_balance
#print axioms SpectralRepresentation.contains_member
#print axioms SpectralRepresentation.no_intruder
#print axioms SpectralRepresentation.recovers_member
#print axioms SpectralRepresentation.off_identity_not_erased
#print axioms SpectralRepresentation.riemannHypothesis_of_onLine
#print axioms riemannHypothesis_iff_onLine_representation

end RHV6Fresh
