/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.LogGapsTheorem

/-!
# La verticale infinie au sommet : sous-cas (a) du §18.3, compilé (module isolé)

Validé par l'auteur le 2026-10-29 (« je confirme, compile le sous-cas »). Objet : lever la restriction de
FINITUDE dans « sommet atteint » (`SummitAttained.lean`). Là, la famille du sommet devait être finie,
parce que le polynôme de fréquences d'une famille finie ne tend pas vers zéro (`trig_poly_not_tendsto_zero`)
et est lipschitzien. Ici, la famille du sommet est une verticale QUELCONQUE, finie ou infinie : la somme de
ses contributions, rapportée à la puissance du sommet, est une série trigonométrique en `log x` dont les
coefficients ont pour modules les poids des indices, qui sont absolument sommables (`indexWeight_summable`).

**L'argument de valeur moyenne, sans intégrale nouvelle.** Une série trigonométrique à coefficients
absolument sommables, à fréquences distinctes et à un coefficient non nul ne tend pas vers zéro
(`trigSeries_not_tendsto_zero`) : on la tronque à une partie finie contenant l'indice du coefficient non
nul, de queue plus petite que le quart du module de ce coefficient ; si la série tendait vers zéro, le
polynôme tronqué serait, à partir d'un certain point, de module au plus la moitié de ce coefficient ; sa
moyenne quadratique (compilée, `trig_poly_mean_square`) serait au plus le quart du carré du coefficient
plus une marge, alors qu'elle vaut au moins le carré du coefficient. La série est uniformément continue
(`trigSeries_uniformly_continuous`) : troncature finie lipschitzienne plus queue petite. Avec les écarts
logarithmiques vers zéro (théorème, `logGapsVanish_holds`), elle est échantillonnée aux rencontres
(`trigSeries_sampled_at_meetings`). Le reste strictement sous le sommet, rapporté au sommet, tend vers zéro
par convergence dominée (`restRatioLine_tendsto_zero`), comme au §17 mais sur le complément d'une verticale.

**Résultat.** Sous l'hypothèse de clôture seule : si le supremum des positions radiales est atteint — par
une verticale finie ou infinie —, aucun indice n'est à droite de un demi (`no_right_of_supremumAttained`),
donc RH (`riemannHypothesis_of_closure_supremum`). La dichotomie devient : RH, ou bien toute position
atteinte est strictement dépassée, c'est-à-dire le supremum n'est pas atteint
(`riemannHypothesis_or_supremum_not_attained`). C'est exactement le sous-cas (b) du §18.3, l'obstruction de
Landau, désormais SEUL monde restant sous l'hypothèse de clôture.

Hypothèses nommées, jamais posées : `SupremumAttained` (plus faible que `SummitAttained`), `DemandBoundedAtMeetings`
(hypothèse de clôture). Aucun axiome au-delà des axiomes standard, aucun `sorry`. La chaîne est intacte.
-/

namespace RHV6Fresh

open Complex RHV3Lean Filter Topology FiniteRadialRigidity

/-! ## 1. Séries trigonométriques à coefficients absolument sommables -/

/-- La série trigonométrique de coefficients `c` et de fréquences `T`, en la variable `u`. -/
noncomputable def trigSeries {ι : Type*} (c : ι → ℂ) (T : ι → ℝ) (u : ℝ) : ℂ :=
  ∑' j, c j * Complex.exp (I * ((T j : ℂ) * u))

theorem norm_trigTerm {ι : Type*} (c : ι → ℂ) (T : ι → ℝ) (u : ℝ) (j : ι) :
    ‖c j * Complex.exp (I * ((T j : ℂ) * u))‖ = ‖c j‖ := by
  rw [norm_mul]
  have h : I * ((T j : ℂ) * u) = I * ((T j * u : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_exp_I_mul_ofReal, mul_one]

theorem trigTerm_summable {ι : Type*} {c : ι → ℂ} (hc : Summable fun j => ‖c j‖) (T : ι → ℝ)
    (u : ℝ) : Summable fun j => c j * Complex.exp (I * ((T j : ℂ) * u)) :=
  Summable.of_norm ((summable_congr fun j => norm_trigTerm c T u j).mpr hc)

/-- Une partie finie dont la queue des modules est au plus `τ`. -/
theorem exists_finset_tail_le {ι : Type*} (c : ι → ℂ) {τ : ℝ} (hτ : 0 < τ) :
    ∃ N : Finset ι, ∑' j : ((N : Set ι)ᶜ : Set ι), ‖c j‖ ≤ τ := by
  have h := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero fun j => ‖c j‖)).2 τ hτ
  obtain ⟨N, hN⟩ := h.exists
  exact ⟨N, hN.le⟩

/-- Une partie finie contenant un indice donné, dont la queue des modules est au plus `τ`. -/
theorem exists_finset_tail_le_mem {ι : Type*} (c : ι → ℂ) (k : ι) {τ : ℝ} (hτ : 0 < τ) :
    ∃ N : Finset ι, k ∈ N ∧ ∑' j : ((N : Set ι)ᶜ : Set ι), ‖c j‖ ≤ τ := by
  have h := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero fun j => ‖c j‖)).2 τ hτ
  obtain ⟨N, hN, hkN⟩ := (h.and (eventually_ge_atTop ({k} : Finset ι))).exists
  exact ⟨N, Finset.singleton_subset_iff.mp hkN, hN.le⟩

open Classical in
/-- La série moins sa troncature à `N` est la somme sur le complément de `N`. -/
theorem trigSeries_sub_trigPoly {ι : Type*} {c : ι → ℂ} (hc : Summable fun j => ‖c j‖)
    (T : ι → ℝ) (N : Finset ι) (u : ℝ) :
    trigSeries c T u - trigPoly (fun j : N => c j) (fun j : N => T j) u =
      ∑' j : ((N : Set ι)ᶜ : Set ι), c j * Complex.exp (I * ((T j : ℂ) * u)) := by
  have h1 : trigPoly (fun j : N => c j) (fun j : N => T j) u =
      ∑ j ∈ N, c j * Complex.exp (I * ((T j : ℂ) * u)) := by
    unfold trigPoly
    exact Finset.sum_coe_sort N (fun j => c j * Complex.exp (I * ((T j : ℂ) * u)))
  rw [h1]
  unfold trigSeries
  rw [← (trigTerm_summable hc T u).sum_add_tsum_compl (s := N)]
  ring

open Classical in
/-- La troncature approche la série à la queue près, uniformément en `u`. -/
theorem norm_trigSeries_sub_trigPoly_le {ι : Type*} {c : ι → ℂ} (hc : Summable fun j => ‖c j‖)
    (T : ι → ℝ) (N : Finset ι) (u : ℝ) :
    ‖trigSeries c T u - trigPoly (fun j : N => c j) (fun j : N => T j) u‖ ≤
      ∑' j : ((N : Set ι)ᶜ : Set ι), ‖c j‖ := by
  rw [trigSeries_sub_trigPoly hc T N u]
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · exact ((summable_congr fun j => norm_trigTerm c T u j).mpr hc).subtype _
  · exact tsum_congr fun j => norm_trigTerm c T u j

/-- Si `‖f‖²` est au plus `δ` à partir d'un certain point, la moyenne quadratique est au plus `δ + ε` à
partir d'un certain point. Variante de `mean_square_tendsto_zero_of_tendsto_zero`. -/
theorem mean_square_eventually_le {f : ℝ → ℂ} (hf : Continuous f) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : ∀ᶠ u in atTop, ‖f u‖ ^ 2 ≤ δ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, (1 / L) * ∫ u in (0:ℝ)..L, ‖f u‖ ^ 2 ≤ δ + ε := by
  obtain ⟨U, hU⟩ := eventually_atTop.mp hsmall
  obtain ⟨U', hU'⟩ : ∃ U' : ℝ, U' = max U 0 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∫ u in (0:ℝ)..U', ‖f u‖ ^ 2 := ⟨_, rfl⟩
  have hcont : Continuous fun u => ‖f u‖ ^ 2 := by fun_prop
  have hU0 : 0 ≤ U' := by rw [hU']; exact le_max_right _ _
  have hUU : U ≤ U' := by rw [hU']; exact le_max_left _ _
  have hC0 : 0 ≤ C := by
    rw [hC]; exact intervalIntegral.integral_nonneg hU0 (fun u _ => by positivity)
  have hev : ∀ᶠ L : ℝ in atTop, C / L < ε ∧ U' ≤ L ∧ 0 < L := by
    have h1 : Tendsto (fun L : ℝ => C / L) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    filter_upwards [h1.eventually (gt_mem_nhds hε), eventually_ge_atTop U', eventually_gt_atTop 0]
      with L a b c
    exact ⟨a, b, c⟩
  filter_upwards [hev] with L ⟨hL1, hL2, hL3⟩
  have hsplit : (∫ u in (0:ℝ)..L, ‖f u‖ ^ 2) = C + ∫ u in U'..L, ‖f u‖ ^ 2 := by
    rw [hC]
    exact (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)).symm
  have htail : (∫ u in U'..L, ‖f u‖ ^ 2) ≤ ∫ u in U'..L, δ :=
    intervalIntegral.integral_mono_on hL2 (hcont.intervalIntegrable _ _) (by simp)
      (fun u hu => hU u (le_trans hUU hu.1))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at htail
  rw [hsplit]
  have h1 : (1 / L) * (C + ∫ u in U'..L, ‖f u‖ ^ 2) ≤ (1 / L) * (C + (L - U') * δ) := by
    gcongr
  have h2 : (1 / L) * (C + (L - U') * δ) = C / L + (L - U') / L * δ := by
    field_simp
  have h3 : (L - U') / L ≤ 1 := by rw [div_le_one hL3]; linarith
  have h4 : (L - U') / L * δ ≤ δ := by
    calc (L - U') / L * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right h3 hδ
      _ = δ := one_mul δ
  linarith

/-- **Une série trigonométrique à coefficients absolument sommables, à fréquences distinctes et à un
coefficient non nul ne tend pas vers zéro.** Argument de valeur moyenne par troncature finie. -/
theorem trigSeries_not_tendsto_zero {ι : Type*} {c : ι → ℂ} (hc : Summable fun j => ‖c j‖)
    {T : ι → ℝ} (hT : Function.Injective T) {k : ι} (hk : c k ≠ 0) :
    ¬ Tendsto (trigSeries c T) atTop (𝓝 0) := by
  classical
  intro h0
  have hck : 0 < ‖c k‖ := norm_pos_iff.mpr hk
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = ‖c k‖ / 4 := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτ]; positivity
  obtain ⟨N, hkN, hN⟩ := exists_finset_tail_le_mem c k hτ0
  obtain ⟨P, hP⟩ : ∃ P : ℝ → ℂ, P = trigPoly (fun j : N => c j) (fun j : N => T j) := ⟨_, rfl⟩
  have hPc : Continuous P := by rw [hP]; exact trigPoly_continuous _ _
  have hinj : Function.Injective (fun j : N => T j) := fun a b hab => Subtype.ext (hT hab)
  have hmean := trig_poly_mean_square (fun j : N => c j) hinj
  rw [← hP] at hmean
  -- à partir d'un certain point, la troncature est de module au plus `2τ`
  have hev : ∀ᶠ u in atTop, ‖P u‖ ^ 2 ≤ (2 * τ) ^ 2 := by
    have h1 : ∀ᶠ u in atTop, ‖trigSeries c T u‖ < τ :=
      (tendsto_zero_iff_norm_tendsto_zero.mp h0).eventually (gt_mem_nhds hτ0)
    filter_upwards [h1] with u hu
    have h2 := norm_trigSeries_sub_trigPoly_le hc T N u
    rw [← hP] at h2
    have h3 : ‖P u‖ ≤ 2 * τ := by
      have := norm_sub_norm_le (P u) (trigSeries c T u)
      rw [norm_sub_rev] at this
      linarith
    have h4 : 0 ≤ ‖P u‖ := norm_nonneg _
    nlinarith
  -- la moyenne quadratique est au moins le carré du coefficient `k`
  have hS : ‖c k‖ ^ 2 ≤ ∑ j : N, ‖(fun j : N => c j) j‖ ^ 2 := by
    have := Finset.single_le_sum (f := fun j : N => ‖(fun j : N => c j) j‖ ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ (⟨k, hkN⟩ : N))
    simpa using this
  -- et au plus `(2τ)² + (2τ)²`
  have hle : ∑ j : N, ‖(fun j : N => c j) j‖ ^ 2 ≤ (2 * τ) ^ 2 + (2 * τ) ^ 2 :=
    le_of_tendsto hmean (mean_square_eventually_le hPc (by positivity) hev (by positivity))
  have hsq : (2 * τ) ^ 2 + (2 * τ) ^ 2 = ‖c k‖ ^ 2 / 2 := by rw [hτ]; ring
  have hpos : 0 < ‖c k‖ ^ 2 := by positivity
  linarith

/-- **La série est uniformément continue** : troncature lipschitzienne plus queue petite. -/
theorem trigSeries_uniformly_continuous {ι : Type*} {c : ι → ℂ} (hc : Summable fun j => ‖c j‖)
    (T : ι → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u v : ℝ, |u - v| ≤ δ → ‖trigSeries c T u - trigSeries c T v‖ ≤ ε := by
  classical
  obtain ⟨N, hN⟩ := exists_finset_tail_le c (by positivity : (0 : ℝ) < ε / 4)
  obtain ⟨P, hP⟩ : ∃ P : ℝ → ℂ, P = trigPoly (fun j : N => c j) (fun j : N => T j) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = lipschitzConstant (fun j : N => c j) (fun j : N => T j) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by
    rw [hL]; unfold lipschitzConstant
    exact Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)
  refine ⟨ε / (2 * (L + 1)), by positivity, fun u v huv => ?_⟩
  have h1 := norm_trigSeries_sub_trigPoly_le hc T N u
  have h2 := norm_trigSeries_sub_trigPoly_le hc T N v
  have h3 := trigPoly_lipschitz (fun j : N => c j) (fun j : N => T j) u v
  rw [← hP] at h1 h2 h3
  rw [← hL] at h3
  have h4 : L * |u - v| ≤ ε / 2 := by
    calc L * |u - v| ≤ L * (ε / (2 * (L + 1))) := mul_le_mul_of_nonneg_left huv hL0
      _ ≤ ε / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  have htri : ‖trigSeries c T u - trigSeries c T v‖ ≤
      ‖trigSeries c T u - P u‖ + ‖P u - P v‖ + ‖P v - trigSeries c T v‖ := by
    calc ‖trigSeries c T u - trigSeries c T v‖
        = ‖(trigSeries c T u - P u) + (P u - P v) + (P v - trigSeries c T v)‖ := by
          congr 1; ring
      _ ≤ _ := norm_add₃_le
  rw [norm_sub_rev (P v)] at htri
  linarith

/-- **Échantillonnage aux rencontres** (théorème, par les écarts logarithmiques vers zéro) : une
série trigonométrique à coefficients absolument sommables, à fréquences distinctes et à un
coefficient non nul dépasse un seuil fixe en des rencontres de rang arbitrairement grand. -/
theorem trigSeries_sampled_at_meetings {ι : Type*} {c : ι → ℂ} (hc : Summable fun j => ‖c j‖)
    {T : ι → ℝ} (hT : Function.Injective T) {k : ι} (hk : c k ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧
      ε ≤ ‖trigSeries c T (Real.log (meetingPoint ⟨n⟩))‖ := by
  have hnot := trigSeries_not_tendsto_zero hc hT hk
  rw [Metric.tendsto_atTop] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hbig⟩ := hnot
  obtain ⟨δ, hδ, hunif⟩ := trigSeries_uniformly_continuous hc T (half_pos hε)
  refine ⟨ε / 2, half_pos hε, fun n₀ => ?_⟩
  obtain ⟨U, hU⟩ := exists_meeting_in_window logGapsVanish_holds hδ n₀
  obtain ⟨u, hu, hd⟩ := hbig U
  rw [dist_zero_right] at hd
  obtain ⟨n, hn, h1, h2⟩ := hU u hu
  refine ⟨n, hn, ?_⟩
  have h3 := hunif (Real.log (meetingPoint ⟨n⟩)) u (by rw [abs_of_pos (by linarith)]; linarith)
  have h4 := norm_sub_norm_le (trigSeries c T u) (trigSeries c T (Real.log (meetingPoint ⟨n⟩)))
  rw [norm_sub_rev] at h4
  linarith

/-! ## 2. La verticale du sommet -/

/-- La verticale de position radiale `b` : tous les indices à cette position. -/
def topLine (b : ℝ) : Set ExplicitIndex := {ρ | (ρ : ℂ).re = b}

/-- Le module du coefficient d'un indice est son poids. -/
theorem norm_memberCoefficient (σ : ExplicitIndex) : ‖memberCoefficient σ‖ = indexWeight σ := by
  unfold memberCoefficient indexWeight
  have h1 : ‖Complex.exp (-(smoothingPhase σ : ℂ) * I)‖ = 1 := by
    rw [show -(smoothingPhase σ : ℂ) * I = ((-(smoothingPhase σ) : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [norm_mul, h1, mul_one, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (indexDenominator_pos σ)]
  congr 1
  simp

/-- Les coefficients de la verticale sont absolument sommables : ce sont les poids. -/
theorem topLine_coefficients_summable (b : ℝ) :
    Summable fun ρ : topLine b => ‖memberCoefficient ρ‖ :=
  (summable_congr fun ρ : topLine b => norm_memberCoefficient ρ).mpr
    (indexWeight_summable.subtype _)

/-- Sur la verticale, les fréquences sont distinctes. -/
theorem topLine_frequencies_injective (b : ℝ) :
    Function.Injective fun ρ : topLine b => ((ρ : ExplicitIndex) : ℂ).im := by
  intro σ τ h
  have hσ : ((σ : ExplicitIndex) : ℂ).re = b := σ.2
  have hτ : ((τ : ExplicitIndex) : ℂ).re = b := τ.2
  apply Subtype.ext
  apply Subtype.ext
  apply Complex.ext
  · rw [hσ, hτ]
  · exact h

/-- La série de la verticale, en la variable `u = log x`. -/
noncomputable def topSeries (b : ℝ) (u : ℝ) : ℂ :=
  trigSeries (fun ρ : topLine b => memberCoefficient ρ)
    (fun ρ : topLine b => ((ρ : ExplicitIndex) : ℂ).im) u

/-- La contribution de la verticale est la puissance du sommet fois la série. -/
theorem channelOn_topLine_eq (b : ℝ) {x : ℝ} (hx : 0 < x) :
    channelOn (topLine b) x = ((x ^ b : ℝ) : ℂ) * topSeries b (Real.log x) := by
  unfold channelOn topSeries trigSeries
  rw [← tsum_mul_left]
  refine tsum_congr fun ρ => ?_
  have hre : ((ρ : ExplicitIndex) : ℂ).re = b := ρ.2
  rw [residueTerm_decomp (ρ : ExplicitIndex) hx, hre, mul_assoc]
  congr 3
  ring

/-- Rapport du reste de la verticale au sommet : somme, hors de la verticale, des poids
affaiblis. -/
noncomputable def restRatioLine (b : ℝ) (x : ℝ) : ℝ :=
  ∑' ρ : ((topLine b)ᶜ : Set ExplicitIndex), indexWeight ρ * x ^ ((ρ : ℂ).re - b)

/-- Le reste de la verticale est au plus la puissance du sommet fois le rapport. -/
theorem norm_channelOn_compl_le (b : ℝ) {x : ℝ} (hx : 1 < x) :
    ‖channelOn (topLine b)ᶜ x‖ ≤ x ^ b * restRatioLine b x := by
  have hx0 : 0 < x := by linarith
  unfold channelOn restRatioLine
  have hs := (summable_norm_iff.mpr (nontrivial_zero_residue_series_summable hx)).subtype
    ((topLine b)ᶜ)
  refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq ?_)
  rw [← tsum_mul_left]
  refine tsum_congr fun ρ => ?_
  rw [norm_residueTerm_eq ρ hx0, mul_left_comm, ← Real.rpow_add hx0]
  congr 2
  ring

/-- **Convergence dominée** : si le sommet `b` majore toutes les positions, le rapport du reste de
la verticale tend vers zéro. -/
theorem restRatioLine_tendsto_zero (b : ℝ) (hle : ∀ ρ : ExplicitIndex, (ρ : ℂ).re ≤ b) :
    Tendsto (fun x : ℝ => restRatioLine b x) atTop (𝓝 0) := by
  have hrest : ∀ ρ : ((topLine b)ᶜ : Set ExplicitIndex), ((ρ : ExplicitIndex) : ℂ).re < b :=
    fun ρ => lt_of_le_of_ne (hle ρ) (fun h => ρ.2 h)
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (x : ℝ) (ρ : ((topLine b)ᶜ : Set ExplicitIndex)) =>
      indexWeight ρ * x ^ ((ρ : ℂ).re - b))
    (g := fun _ => (0 : ℝ))
    (bound := fun ρ : ((topLine b)ᶜ : Set ExplicitIndex) => indexWeight ρ)
    (indexWeight_summable.subtype _)
    (fun ρ => by
      have h := (tendsto_rpow_neg_atTop (y := b - (ρ : ℂ).re)
        (by linarith [hrest ρ])).const_mul (indexWeight ρ)
      rw [mul_zero] at h
      refine h.congr (fun x => ?_)
      congr 2
      ring)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx ρ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (indexWeight_nonneg ρ)
        (Real.rpow_nonneg (by linarith) _))]
      exact mul_le_of_le_one_right (indexWeight_nonneg ρ)
        (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith [hrest ρ])))
  simpa [restRatioLine] using h

/-! ## 3. Sous un supremum atteint, la demande n'est pas bornée aux rencontres -/

/-- **Théorème** : si le supremum `b > 1/2` des positions est atteint — par une verticale finie ou
infinie —, le niveau de la demande n'est pas borné aux rencontres. -/
theorem demand_unbounded_of_supremum (b : ℝ) (hb : 1 / 2 < b)
    (hex : ∃ ρ : ExplicitIndex, (ρ : ℂ).re = b) (hle : ∀ ρ : ExplicitIndex, (ρ : ℂ).re ≤ b)
    (c : ℝ) : ∃ I : PrimeGapInterval, c < demandRelativeLevel (meetingPoint I) := by
  obtain ⟨ρ₀, hρ₀⟩ := hex
  have hk : (fun ρ : topLine b => memberCoefficient ρ) ⟨ρ₀, hρ₀⟩ ≠ 0 :=
    memberCoefficient_ne_zero ρ₀
  obtain ⟨ε, hε, hinf⟩ := trigSeries_sampled_at_meetings (topLine_coefficients_summable b)
    (topLine_frequencies_injective b) hk
  have hev1 : ∀ᶠ n : ℕ in atTop, restRatioLine b (meetingPoint ⟨n⟩) ≤ ε / 2 :=
    ((restRatioLine_tendsto_zero b hle).comp meetingPoint_tendsto_atTop).eventually
      (Iic_mem_nhds (half_pos hε))
  have hpow : Tendsto (fun x : ℝ => x ^ (b - 1 / 2)) atTop atTop := tendsto_rpow_atTop (by linarith)
  have hev2 : ∀ᶠ n : ℕ in atTop, c < (meetingPoint ⟨n⟩) ^ (b - 1 / 2) * (ε / 2) :=
    ((hpow.comp meetingPoint_tendsto_atTop).atTop_mul_const (half_pos hε)).eventually_gt_atTop c
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hev1.and hev2)
  obtain ⟨n, hn, hFn⟩ := hinf n₀
  obtain ⟨h1, h2⟩ := hn₀ n hn
  refine ⟨⟨n⟩, ?_⟩
  have hFn' : ε ≤ ‖topSeries b (Real.log (meetingPoint ⟨n⟩))‖ := hFn
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = meetingPoint ⟨n⟩ := ⟨_, rfl⟩
  rw [← hxdef] at h1 h2 hFn' ⊢
  have hx1 : 1 < x := by rw [hxdef]; exact one_lt_meetingPoint ⟨n⟩
  have hx0 : 0 < x := by linarith
  have hsplit : smoothedRemainder x = channelOn (topLine b) x + channelOn (topLine b)ᶜ x := by
    rw [smoothedRemainder_eq_tsum_residueTerm hx1]
    exact channel_eq_packet_add_complement (topLine b) hx1
  have hA : ‖channelOn (topLine b) x‖ = x ^ b * ‖topSeries b (Real.log x)‖ := by
    rw [channelOn_topLine_eq b hx0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
  have hB := norm_channelOn_compl_le b hx1
  have hlow : x ^ b * (ε / 2) ≤ ‖smoothedRemainder x‖ := by
    rw [hsplit]
    have htri := norm_sub_le (channelOn (topLine b) x + channelOn (topLine b)ᶜ x)
      (channelOn (topLine b)ᶜ x)
    rw [add_sub_cancel_right] at htri
    have hpb : 0 ≤ x ^ b := (Real.rpow_pos_of_pos hx0 b).le
    have h3 : x ^ b * (ε / 2) ≤ x ^ b * (‖topSeries b (Real.log x)‖ - restRatioLine b x) :=
      mul_le_mul_of_nonneg_left (by linarith) hpb
    rw [mul_sub] at h3
    linarith
  unfold demandRelativeLevel
  rw [lt_div_iff₀ (Real.rpow_pos_of_pos hx0 _)]
  have e1 : x ^ (b - 1 / 2) * x ^ (1 / 2 : ℝ) = x ^ b := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  calc c * x ^ (1 / 2 : ℝ) < x ^ (b - 1 / 2) * (ε / 2) * x ^ (1 / 2 : ℝ) :=
        mul_lt_mul_of_pos_right h2 (Real.rpow_pos_of_pos hx0 _)
    _ = x ^ b * (ε / 2) := by rw [mul_right_comm, e1]
    _ ≤ ‖smoothedRemainder x‖ := hlow

/-! ## 4. L'hypothèse nommée affaiblie, et la dichotomie resserrée -/

/-- **Supremum atteint (hypothèse nommée, jamais posée)** : s'il existe un indice strictement à
droite de un demi, le supremum des positions radiales est atteint — par une verticale finie ou
infinie. Plus faible que `SummitAttained`. -/
def SupremumAttained : Prop :=
  (∃ ρ : ExplicitIndex, 1 / 2 < (ρ : ℂ).re) →
    ∃ b : ℝ, (∃ ρ : ExplicitIndex, (ρ : ℂ).re = b) ∧ ∀ ρ : ExplicitIndex, (ρ : ℂ).re ≤ b

theorem supremumAttained_of_summitAttained (h : SummitAttained) : SupremumAttained := by
  intro hex
  obtain ⟨b, hb, hle, _⟩ := summitAttained_iff.mp h hex
  exact ⟨b, hb, hle⟩

/-- Sous RH, vraie par vacuité : pas plus forte que la cible. -/
theorem supremumAttained_of_riemannHypothesis (h : RiemannHypothesis) : SupremumAttained :=
  supremumAttained_of_summitAttained (summitAttained_of_riemannHypothesis h)

/-- **Aucun indice à droite** : sous l'hypothèse de clôture et le supremum atteint. -/
theorem no_right_of_supremumAttained (hdem : DemandBoundedAtMeetings) (hsup : SupremumAttained) :
    ∀ ρ : ExplicitIndex, (ρ : ℂ).re ≤ 1 / 2 := by
  intro ρ
  by_contra hlt
  push Not at hlt
  obtain ⟨b, hex, hle⟩ := hsup ⟨ρ, hlt⟩
  have hb : 1 / 2 < b := lt_of_lt_of_le hlt (hle ρ)
  obtain ⟨C, hC⟩ := hdem
  obtain ⟨I, hI⟩ := demand_unbounded_of_supremum b hb hex hle C
  linarith [hC I]

/-- **Chemin des zéros, élargi** : hypothèse de clôture et supremum atteint donnent RH. -/
theorem riemannHypothesis_of_closure_supremum (hdem : DemandBoundedAtMeetings)
    (hsup : SupremumAttained) : RiemannHypothesis := by
  refine riemannHypothesis_of_noLowerSide fun l hlow => ?_
  have h := no_right_of_supremumAttained hdem hsup (memberIndex (mirrorMember l))
  change (zeroPoint (mirrorMember l)).re ≤ 1 / 2 at h
  rw [zeroPoint_re, mirrorMember_radial] at h
  linarith

/-- Sous l'hypothèse de clôture, RH équivaut au supremum atteint. -/
theorem riemannHypothesis_iff_supremumAttained_of_closure (hdem : DemandBoundedAtMeetings) :
    RiemannHypothesis ↔ SupremumAttained :=
  ⟨supremumAttained_of_riemannHypothesis, riemannHypothesis_of_closure_supremum hdem⟩

/-- Sous l'hypothèse de clôture, le sommet atteint (verticale finie) découle du supremum atteint. -/
theorem summitAttained_of_supremumAttained (hdem : DemandBoundedAtMeetings)
    (hsup : SupremumAttained) : SummitAttained :=
  summitAttained_of_riemannHypothesis (riemannHypothesis_of_closure_supremum hdem hsup)

/-- **Dichotomie resserrée** : sous l'hypothèse de clôture seule, RH, ou bien l'ensemble droit est
infini et toute position atteinte est strictement dépassée — le supremum n'est pas atteint. C'est le
sous-cas (b) du §18.3, seul monde restant. -/
theorem riemannHypothesis_or_supremum_not_attained (hdem : DemandBoundedAtMeetings) :
    RiemannHypothesis ∨
      (Set.Infinite {ρ : ExplicitIndex | 1 / 2 < (ρ : ℂ).re} ∧
        ∀ b : ℝ, (∃ ρ : ExplicitIndex, (ρ : ℂ).re = b) → ∃ ρ : ExplicitIndex, b < (ρ : ℂ).re) := by
  by_cases hex : ∃ ρ : ExplicitIndex, 1 / 2 < (ρ : ℂ).re
  · right
    refine ⟨infinite_right_of_sampling meetingsSampleFrequencies_holds hdem hex, fun b hbex => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨ρ, hρ⟩ := hex
    have hb : 1 / 2 < b := lt_of_lt_of_le hρ (hcon ρ)
    obtain ⟨C, hC⟩ := hdem
    obtain ⟨I, hI⟩ := demand_unbounded_of_supremum b hb hbex hcon C
    linarith [hC I]
  · left
    refine riemannHypothesis_of_noLowerSide fun l hlow => ?_
    push Not at hex
    have h := hex (memberIndex (mirrorMember l))
    change (zeroPoint (mirrorMember l)).re ≤ 1 / 2 at h
    rw [zeroPoint_re, mirrorMember_radial] at h
    linarith

/-- Les deux chemins vers RH, sous l'hypothèse de clôture, avec le chemin des zéros élargi. -/
theorem riemannHypothesis_of_closure' (hdem : DemandBoundedAtMeetings)
    (hroute : SupremumAttained ∨ UniformVariationAtGaps) : RiemannHypothesis := by
  rcases hroute with hs | hv
  · exact riemannHypothesis_of_closure_supremum hdem hs
  · exact riemannHypothesis_of_meetings_of_variation hdem hv

end RHV6Fresh
