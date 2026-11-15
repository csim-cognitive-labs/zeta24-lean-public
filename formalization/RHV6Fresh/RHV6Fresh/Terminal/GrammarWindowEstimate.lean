/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GrammarWindowSeparation
import RHV6Fresh.Terminal.FirstGainPremise
import RHV6Fresh.Terminal.WindowProgression
import RHV6Fresh.Terminal.MirrorPairExactSum
import RHV6Fresh.Terminal.CountingDeficit
import RHV6Fresh.Direct.PairTowers

/-!
# Fenêtre grammaticale : composition généralisée et estimations tentées (ordre correctif de l'auteur, 2026-10-11)

La séparation `‖L(Y)‖ + marge + ‖moitié conjuguée‖ < minoration` est une CONDITION SUFFISANTE NON DÉMONTRÉE ; elle ne
constitue pas une solution acquise. Ce module :

* §1 bornes de SÉRIE FILTRÉE, phases propres conservées : `‖Σ_r λ_r Σ'_σ w_σ x_r^σ‖ ≤ Σ'_σ ‖w_σ‖·‖Σ_r λ_r x_r^σ‖`
  (`filtered_series_norm_le`) ; l'inégalité triangulaire n'est appliquée qu'en `σ`, l'oscillation sur la fenêtre est gardée ;
  la borne est démontrée au plus égale à la marge triangulaire (`filteredSeriesBound_le`). Instances : complément
  (`complement_filtered_le`, `complement_filtered_le_margin`), historique fini (`history_filtered_le`), retrait réduit à
  sa part première exacte (`historyRemoved_le_primeSide`).
* §2 TROIS OBJETS DISTINCTS, aucun passage de l'un à l'autre sans preuve : partie réelle de la moitié supérieure ; groupe
  complet (`group_re_ge` : minoration du groupe = minoration supérieure − contrôle de la moitié conjuguée) ; retrait moins
  groupe = complément filtré (`removal_sub_group_le`). Composition GÉNÉRALE avec une majoration explicite `B_Q` du
  complément filtré (`window_closes_of_bounds`) ; la marge triangulaire en est un cas particulier
  (`window_closes_triangular`), non imposé.
* §3 minoration instanciée sur l'arrivée ET son miroir : appartenance à la fibre, hauteur, coefficient propre,
  multiplicité vérifiés (`arrival_mirror_fiber`) ; minoration par tout ensemble fini de membres supérieurs
  (`upper_fiber_finset_minoration`) et par la paire (`arrival_mirror_minoration`).
* §4 fenêtre RATTACHÉE AU PASSAGE : départ au premier partagé `p_{n₀}`, écarts = magnitude × 6 + classe, planchers de
  classe, alternance, télescopage `Σ g_r = p_{n₀+m} − p_{n₀}`, plancher `3m` ; composés avec la minoration
  (`passage_pair_minoration_floor`).
* §5 complément filtré développé avec ses phases propres (`complement_phase_development`), résidu au-delà d'une coupure
  conservé (`complement_window_residual_split`) ; moitié conjuguée majorée terme à terme, oscillation `2T` gardée
  (`lower_half_le`, `lower_half_term_norm`).
* §6 RÉDUCTION du passage (`passage_window_reduction`) : sous le filtre accordé sur la fenêtre du passage, l'inégalité
  exacte `‖part première filtrée‖ + B_P + B_Q + B_L < minoration de la paire` sur UNE fenêtre ⟹ `False`. Démontrée ; son
  antécédent n'est PAS démontré : c'est l'estimation que cette tentative exige encore.
-/

namespace RHV6Fresh

open RHV3Lean Complex

/-! ## 1. Bornes de série filtrée (phases conservées) -/

/-- Borne d'une série filtrée : `Σ'_σ ‖w_σ‖·‖Σ_r λ_r x_r^σ‖` (triangulaire en `σ` seulement). -/
noncomputable def filteredSeriesBound (w : ExplicitIndex → ℂ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) : ℝ :=
  ∑' σ, ‖w σ‖ * ‖∑ r, lam r * (x r : ℂ) ^ (σ : ℂ)‖

theorem filteredSeries_term_summable (w : ExplicitIndex → ℂ) (hw : Summable fun σ => ‖w σ‖) {x : ℝ} (hx : 1 < x) :
    Summable fun σ : ExplicitIndex => w σ * (x : ℂ) ^ (σ : ℂ) := by
  have hx0 : 0 < x := lt_trans one_pos hx
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun σ => ?_) (hw.mul_right x))
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc x ^ (σ : ℂ).re ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le (explicitIndex_re_le_one σ)
    _ = x := Real.rpow_one x

theorem filteredSeriesBound_summable (w : ExplicitIndex → ℂ) (hw : Summable fun σ => ‖w σ‖) {m : ℕ}
    (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    Summable fun σ : ExplicitIndex => ‖w σ‖ * ‖∑ r, lam r * (x r : ℂ) ^ (σ : ℂ)‖ :=
  Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun σ => mul_le_mul_of_nonneg_left (window_profile_le x lam hx σ) (norm_nonneg _)) (hw.mul_right _)

/-- **Échange fini / série** : `Σ_r λ_r Σ'_σ w_σ x_r^σ = Σ'_σ w_σ Σ_r λ_r x_r^σ`. -/
theorem filtered_series_eq (w : ExplicitIndex → ℂ) (hw : Summable fun σ => ‖w σ‖) {m : ℕ}
    (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    ∑ r, lam r * ∑' σ, w σ * (x r : ℂ) ^ (σ : ℂ) = ∑' σ, w σ * ∑ r, lam r * (x r : ℂ) ^ (σ : ℂ) := by
  have h : ∀ r, lam r * ∑' σ, w σ * (x r : ℂ) ^ (σ : ℂ) = ∑' σ, lam r * (w σ * (x r : ℂ) ^ (σ : ℂ)) :=
    fun r => tsum_mul_left.symm
  rw [Finset.sum_congr rfl fun r _ => h r,
    ← Summable.tsum_finsetSum fun r _ => (filteredSeries_term_summable w hw (hx r)).mul_left (lam r)]
  refine tsum_congr fun σ => ?_
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring

/-- **Borne de série filtrée** : l'oscillation de chaque profil sur la fenêtre est conservée. -/
theorem filtered_series_norm_le (w : ExplicitIndex → ℂ) (hw : Summable fun σ => ‖w σ‖) {m : ℕ}
    (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    ‖∑ r, lam r * ∑' σ, w σ * (x r : ℂ) ^ (σ : ℂ)‖ ≤ filteredSeriesBound w x lam := by
  rw [filtered_series_eq w hw x lam hx]
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · exact (filteredSeriesBound_summable w hw x lam hx).congr fun σ => (norm_mul _ _).symm
  · unfold filteredSeriesBound; exact tsum_congr fun σ => norm_mul _ _

/-- La borne filtrée est au plus la borne triangulaire `(Σ'‖w‖)·Σ_r |λ_r| x_r`. -/
theorem filteredSeriesBound_le (w : ExplicitIndex → ℂ) (hw : Summable fun σ => ‖w σ‖) {m : ℕ}
    (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    filteredSeriesBound w x lam ≤ (∑' σ, ‖w σ‖) * ∑ r, ‖lam r‖ * x r := by
  unfold filteredSeriesBound
  rw [← tsum_mul_right]
  exact Summable.tsum_le_tsum (fun σ => mul_le_mul_of_nonneg_left (window_profile_le x lam hx σ) (norm_nonneg _))
    (filteredSeriesBound_summable w hw x lam hx) (hw.mul_right _)

theorem precedingSum_eq_series (H x : ℝ) :
    precedingSum H x = ∑' σ, precedingWeight H σ * (x : ℂ) ^ (σ : ℂ) := by
  unfold precedingSum; exact tsum_congr fun σ => precedingSum_term_eq H x σ

/-- **Complément filtré, phases conservées** : `‖Σ_r λ_r Q_{H'}(x_r)‖ ≤ B_Q`. -/
theorem complement_filtered_le (H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    ‖∑ r, lam r * followingSum H' (x r)‖ ≤ filteredSeriesBound (followingWeight H') x lam :=
  filtered_series_norm_le _ (followingWeight_norm_summable H') x lam hx

/-- `B_Q` est au plus la marge triangulaire. -/
theorem complement_filtered_le_margin (H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    filteredSeriesBound (followingWeight H') x lam ≤ windowMargin H' x lam :=
  filteredSeriesBound_le _ (followingWeight_norm_summable H') x lam hx

/-- **Historique fini filtré** : `‖Σ_r λ_r P_H(x_r)‖ ≤ B_P`. -/
theorem history_filtered_le (H : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    ‖∑ r, lam r * precedingSum H (x r)‖ ≤ filteredSeriesBound (precedingWeight H) x lam := by
  have h : ∑ r, lam r * precedingSum H (x r) = ∑ r, lam r * ∑' σ, precedingWeight H σ * (x r : ℂ) ^ (σ : ℂ) :=
    Finset.sum_congr rfl fun r _ => by rw [precedingSum_eq_series]
  rw [h]; exact filtered_series_norm_le _ (precedingWeight_norm_summable H) x lam hx

/-- Part première filtrée du retrait : `Σ_{n<N} Λ(n)Φ_λ(n) − Σ_r λ_r·fond(x_r)` (poids premiers exacts). -/
noncomputable def primeSideFiltered (N : ℕ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt n : ℂ) * primeFilter x lam n
    - ∑ r, lam r * smoothedZeroBackground (x r)

theorem historyRemoved_eq_primeSide (H : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (N : ℕ)
    (hN : ∀ r, ⌈x r⌉₊ ≤ N) :
    historyRemoved H x lam = primeSideFiltered N x lam - ∑ r, lam r * precedingSum H (x r) := by
  rw [historyRemoved_filtered_primes H x lam N hN]; rfl

/-- **Retrait majoré par sa part première exacte et l'historique filtré.** -/
theorem historyRemoved_le_primeSide (H : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r)
    (N : ℕ) (hN : ∀ r, ⌈x r⌉₊ ≤ N) :
    ‖historyRemoved H x lam‖ ≤ ‖primeSideFiltered N x lam‖ + filteredSeriesBound (precedingWeight H) x lam := by
  rw [historyRemoved_eq_primeSide H x lam N hN]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (history_filtered_le H x lam hx))

/-! ## 2. Trois objets distincts et composition générale -/

/-- **Groupe complet** : une minoration `U` de la partie réelle supérieure et un contrôle `B_L` de la moitié conjuguée
minorent la partie réelle du groupe par `U − B_L`. -/
theorem group_re_ge {H H' : ℝ} {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) {U BL : ℝ}
    (hU : U ≤ (∑' σ, upperFiltered H H' x lam σ).re) (hL : ‖∑' σ, lowerFiltered H H' x lam σ‖ ≤ BL) :
    U - BL ≤ (groupSignal H H' x lam).re := by
  have hsplit := congrArg Complex.re (groupSignal_split H H' x lam hx)
  rw [Complex.add_re] at hsplit
  have b := neg_le_of_abs_le (Complex.abs_re_le_norm (∑' σ, lowerFiltered H H' x lam σ))
  linarith

/-- **Retrait moins groupe** : c'est le complément filtré, majoré par toute borne démontrée de celui-ci. -/
theorem removal_sub_group_le {H H' : ℝ} {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) {BQ : ℝ}
    (hQ : ‖∑ r, lam r * followingSum H' (x r)‖ ≤ BQ) :
    ‖historyRemoved H x lam - groupSignal H H' x lam‖ ≤ BQ := by
  rw [window_same_quantity H H' x lam hx]; exact hQ

/-- **Composition générale** : majoration explicite `B_Q` du complément filtré (démontrée par ailleurs), contrôle `B_L`
de la moitié conjuguée, minoration `U` de la partie réelle supérieure, majoration `B_Y` du retrait. -/
theorem window_closes_of_bounds {H H' : ℝ} {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r)
    {U BY BQ BL : ℝ} (hU : U ≤ (∑' σ, upperFiltered H H' x lam σ).re)
    (hL : ‖∑' σ, lowerFiltered H H' x lam σ‖ ≤ BL) (hQ : ‖∑ r, lam r * followingSum H' (x r)‖ ≤ BQ)
    (hY : ‖historyRemoved H x lam‖ ≤ BY) (hsep : BY + BQ + BL < U) : False := by
  have hG := group_re_ge x lam hx hU hL
  have hD := removal_sub_group_le (H := H) x lam hx hQ
  have a := Complex.re_le_norm (groupSignal H H' x lam)
  have b : ‖groupSignal H H' x lam‖ ≤ ‖historyRemoved H x lam‖ +
      ‖historyRemoved H x lam - groupSignal H H' x lam‖ := by
    have := norm_sub_le (historyRemoved H x lam) (historyRemoved H x lam - groupSignal H H' x lam)
    simpa using this
  linarith

/-- Cas particulier : la marge triangulaire comme majoration du complément (non imposée). -/
theorem window_closes_triangular {H H' : ℝ} {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r)
    {U BY BL : ℝ} (hU : U ≤ (∑' σ, upperFiltered H H' x lam σ).re)
    (hL : ‖∑' σ, lowerFiltered H H' x lam σ‖ ≤ BL) (hY : ‖historyRemoved H x lam‖ ≤ BY)
    (hsep : BY + windowMargin H' x lam + BL < U) : False :=
  window_closes_of_bounds x lam hx hU hL (window_complement_margin H' x lam hx) hY hsep

/-! ## 3. Minoration sur l'arrivée et son miroir -/

/-- Partie réelle d'un membre supérieur de la fibre sous le filtre accordé : `Re w_σ · Σ_r c_r x_r^{β_σ}`. -/
theorem upper_filtered_re_eq {H H' : ℝ} (hHH' : H ≤ H')
    (hFib : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' → |(σ : ℂ).im| = H')
    {m : ℕ} (c x : Fin m → ℝ) (hx : ∀ r, 1 < x r) (σ : ExplicitIndex) (h0 : 0 < (σ : ℂ).im)
    (h1 : H < |(σ : ℂ).im|) (h2 : |(σ : ℂ).im| ≤ H') :
    (upperFiltered H H' x (phaseMatched H' c x) σ).re =
      (-(zetaZeroMultiplicity (σ : ℂ) : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1))).re * ∑ r, c r * x r ^ (σ : ℂ).re := by
  rw [upper_term_eq hHH' hFib c x hx σ h0, fiberWeight_of_mem h1 h2, Complex.re_mul_ofReal]

theorem upper_filtered_re_nonneg {H H' : ℝ} (hHH' : H ≤ H')
    (hFib : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' → |(σ : ℂ).im| = H')
    (hT : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' →
      (σ : ℂ).re * ((σ : ℂ).re + 1) < (σ : ℂ).im ^ 2)
    {m : ℕ} (c x : Fin m → ℝ) (hc : ∀ r, 0 ≤ c r) (hx : ∀ r, 1 < x r) (σ : ExplicitIndex) :
    0 ≤ (upperFiltered H H' x (phaseMatched H' c x) σ).re := by
  by_cases hσ : 0 < (σ : ℂ).im
  · rw [upper_term_eq hHH' hFib c x hx σ hσ, Complex.re_mul_ofReal]
    by_cases h0' : fiberWeight H H' σ = 0
    · rw [h0', Complex.zero_re, zero_mul]
    obtain ⟨a1, a2⟩ := fiberWeight_ne_zero_mem hHH' h0'
    rw [fiberWeight_of_mem a1 a2]
    exact mul_nonneg (upper_weight_re_nonneg (hT σ a1 a2) _)
      (Finset.sum_nonneg fun r _ => mul_nonneg (hc r) (Real.rpow_nonneg (by linarith [hx r]) _))
  · unfold upperFiltered; rw [if_neg hσ, Complex.zero_re]

/-- **Minoration par tout ensemble fini de membres supérieurs de la fibre** (les autres membres, `≥ 0`, restent dans la
série). -/
theorem upper_fiber_finset_minoration {H H' : ℝ} (hHH' : H ≤ H')
    (hFib : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' → |(σ : ℂ).im| = H')
    (hT : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' →
      (σ : ℂ).re * ((σ : ℂ).re + 1) < (σ : ℂ).im ^ 2)
    {m : ℕ} (c x : Fin m → ℝ) (hc : ∀ r, 0 ≤ c r) (hx : ∀ r, 1 < x r) (S : Finset ExplicitIndex)
    (hS : ∀ σ ∈ S, 0 < (σ : ℂ).im ∧ H < |(σ : ℂ).im| ∧ |(σ : ℂ).im| ≤ H') :
    ∑ σ ∈ S, (-(zetaZeroMultiplicity (σ : ℂ) : ℂ) / ((σ : ℂ) * ((σ : ℂ) + 1))).re * ∑ r, c r * x r ^ (σ : ℂ).re ≤
      (∑' σ, upperFiltered H H' x (phaseMatched H' c x) σ).re := by
  have hs := upperFiltered_summable H H' x (phaseMatched H' c x) hx
  rw [Complex.re_tsum hs]
  have hsr : Summable fun σ => (upperFiltered H H' x (phaseMatched H' c x) σ).re := Complex.reCLM.summable hs
  have key := hsr.sum_le_tsum S (fun σ _ => upper_filtered_re_nonneg hHH' hFib hT c x hc hx σ)
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun σ hσ => ?_)) key
  obtain ⟨a0, a1, a2⟩ := hS σ hσ
  exact (upper_filtered_re_eq hHH' hFib c x hx σ a0 a1 a2).symm

/-- **Le miroir de l'arrivée dans la fibre** : distinct de l'arrivée sous `β_l < 1/2`, point `1 − ρ̄_l`, même hauteur,
partie réelle `1 − β_l`, dans la fibre, même multiplicité, coefficient propre. -/
theorem arrival_mirror_fiber {H H' : ℝ} (l : TrueZero) (hH : H < rZeroHeight l.1) (hH' : rZeroHeight l.1 ≤ H')
    (hβ : rZeroRadialPosition l.1 < 1 / 2) :
    memberIndex l ≠ memberIndex (mirrorMember l) ∧
    ((memberIndex (mirrorMember l) : ExplicitIndex) : ℂ) = 1 - (starRingEnd ℂ) (zeroPoint l) ∧
    ((memberIndex (mirrorMember l) : ExplicitIndex) : ℂ).im = rZeroHeight l.1 ∧
    ((memberIndex (mirrorMember l) : ExplicitIndex) : ℂ).re = 1 - rZeroRadialPosition l.1 ∧
    0 < ((memberIndex (mirrorMember l) : ExplicitIndex) : ℂ).im ∧
    H < |((memberIndex (mirrorMember l) : ExplicitIndex) : ℂ).im| ∧
    |((memberIndex (mirrorMember l) : ExplicitIndex) : ℂ).im| ≤ H' ∧
    zetaZeroMultiplicity ((memberIndex (mirrorMember l) : ExplicitIndex) : ℂ) = zetaZeroMultiplicity (zeroPoint l) ∧
    fiberWeight H H' (memberIndex (mirrorMember l)) =
      -(zetaZeroMultiplicity (zeroPoint l) : ℂ) / (zeroPoint (mirrorMember l) * (zeroPoint (mirrorMember l) + 1)) := by
  have hIm : ((memberIndex (mirrorMember l) : ExplicitIndex) : ℂ).im = rZeroHeight l.1 := mirrorMember_ordinate l
  have hpos : 0 < ((memberIndex (mirrorMember l) : ExplicitIndex) : ℂ).im := by rw [hIm]; exact l.2
  have h1 : H < |((memberIndex (mirrorMember l) : ExplicitIndex) : ℂ).im| := by rw [abs_of_pos hpos, hIm]; exact hH
  have h2 : |((memberIndex (mirrorMember l) : ExplicitIndex) : ℂ).im| ≤ H' := by rw [abs_of_pos hpos, hIm]; exact hH'
  have hmult : zetaZeroMultiplicity ((memberIndex (mirrorMember l) : ExplicitIndex) : ℂ) =
      zetaZeroMultiplicity (zeroPoint l) := by
    show zetaZeroMultiplicity (zeroPoint (mirrorMember l)) = _
    rw [zeroPoint_mirrorMember]; exact zetaZeroMultiplicity_mirrorPoint l.1.2
  refine ⟨fun h => mirrorMember_ne hβ (memberIndex_injective h).symm, zeroPoint_mirrorMember l, hIm,
    mirrorMember_radial l, hpos, h1, h2, hmult, ?_⟩
  rw [fiberWeight_of_mem h1 h2, hmult]; rfl

/-- **Minoration par la paire arrivée + miroir** (coefficients propres, multiplicité commune, exposants `β_l`, `1 − β_l`). -/
theorem arrival_mirror_minoration {H H' : ℝ} (hHH' : H ≤ H')
    (hFib : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' → |(σ : ℂ).im| = H')
    (hT : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' →
      (σ : ℂ).re * ((σ : ℂ).re + 1) < (σ : ℂ).im ^ 2)
    {m : ℕ} (c x : Fin m → ℝ) (hc : ∀ r, 0 ≤ c r) (hx : ∀ r, 1 < x r)
    (l : TrueZero) (hH : H < rZeroHeight l.1) (hH' : rZeroHeight l.1 ≤ H') (hβ : rZeroRadialPosition l.1 < 1 / 2) :
    (-(zetaZeroMultiplicity (zeroPoint l) : ℂ) / (zeroPoint l * (zeroPoint l + 1))).re *
        ∑ r, c r * x r ^ rZeroRadialPosition l.1 +
      (-(zetaZeroMultiplicity (zeroPoint l) : ℂ) /
          (zeroPoint (mirrorMember l) * (zeroPoint (mirrorMember l) + 1))).re *
        ∑ r, c r * x r ^ (1 - rZeroRadialPosition l.1) ≤
      (∑' σ, upperFiltered H H' x (phaseMatched H' c x) σ).re := by
  obtain ⟨hne, -, -, hre, hpos, h1, h2, hmult, -⟩ := arrival_mirror_fiber l hH hH' hβ
  have hlpos : 0 < ((memberIndex l : ExplicitIndex) : ℂ).im := l.2
  have hl1 : H < |((memberIndex l : ExplicitIndex) : ℂ).im| := by
    rw [abs_of_pos hlpos]; exact hH
  have hl2 : |((memberIndex l : ExplicitIndex) : ℂ).im| ≤ H' := by rw [abs_of_pos hlpos]; exact hH'
  have key := upper_fiber_finset_minoration hHH' hFib hT c x hc hx {memberIndex l, memberIndex (mirrorMember l)}
    (by
      intro σ hσ
      rcases Finset.mem_insert.mp hσ with rfl | hσ
      · exact ⟨hlpos, hl1, hl2⟩
      · rw [Finset.mem_singleton.mp hσ]; exact ⟨hpos, h1, h2⟩)
  rw [Finset.sum_pair hne, hmult, hre] at key
  exact key

/-! ## 4. Fenêtre rattachée au passage : écarts, classes, alternance, planchers -/

/-- `p_k ≥ k + 2` (départ `p_0 = 2`, croissance stricte). -/
theorem fnPrimeAtRank_ge_add_two (k : ℕ) : k + 2 ≤ fnPrimeAtRank k := by
  induction k with
  | zero => rw [thm_primeAtRank_zero_eq_two]
  | succ k ih =>
    have : fnPrimeAtRank k < fnPrimeAtRank (k + 1) := thm_primeAtRank_strictMono (by omega)
    omega

theorem gapWeights_eq_gap (n₀ m : ℕ) (r : Fin m) : gapWeights n₀ m r = (nPrimeGap (n₀ + r) : ℝ) := by
  unfold gapWeights nPrimeGap fnPrimeSuccessor
  rw [Nat.cast_sub (thm_primeAtRank_strictMono (Nat.lt_succ_self _)).le]

/-- **Écart = 6 × magnitude + classe**, à chaque événement de la fenêtre. -/
theorem gapWeights_magnitude_class (n₀ m : ℕ) (r : Fin m) :
    gapWeights n₀ m r = 6 * (gapMagnitude (n₀ + r) : ℝ) + (eventClass (n₀ + r) : ℝ) := by
  rw [gapWeights_eq_gap, primeGap_eq_magnitude_class]; push_cast; ring

/-- **Plancher de classe** à chaque événement (`p_{n₀} > 3`). -/
theorem gapWeights_ge_classFloor (n₀ m : ℕ) (h3 : 3 < fnPrimeAtRank n₀) (r : Fin m) :
    (classFloor (eventClass (n₀ + r)) : ℝ) ≤ gapWeights n₀ m r := by
  rw [gapWeights_eq_gap]
  have h3' : 3 < fnPrimeAtRank (n₀ + r) := lt_of_lt_of_le h3 (thm_primeAtRank_strictMono.monotone (by omega))
  exact_mod_cast primeGap_ge_classFloor (n₀ + r) h3'

/-- **Alternance** des classes non nulles consécutives dans la fenêtre. -/
theorem passage_window_alternation (n₀ : ℕ) (h3 : 3 < fnPrimeAtRank n₀) (r : ℕ)
    (h1 : eventClass (n₀ + r) ≠ 0) (h2 : eventClass (n₀ + r + 1) ≠ 0) :
    eventClass (n₀ + r) ≠ eventClass (n₀ + r + 1) :=
  eventClass_alternates (n₀ + r) (lt_of_lt_of_le h3 (thm_primeAtRank_strictMono.monotone (by omega))) h1 h2

/-- **Télescopage** : `Σ_r g_r = p_{n₀+m} − p_{n₀}`. -/
theorem gapWeights_sum (n₀ m : ℕ) :
    ∑ r, gapWeights n₀ m r = (fnPrimeAtRank (n₀ + m) : ℝ) - fnPrimeAtRank n₀ := by
  unfold gapWeights
  rw [Fin.sum_univ_eq_sum_range (fun r => (fnPrimeAtRank (n₀ + r + 1) : ℝ) - fnPrimeAtRank (n₀ + r)) m]
  have := Finset.sum_range_sub (fun r => (fnPrimeAtRank (n₀ + r) : ℝ)) m
  simpa [add_assoc] using this

/-- **Plancher de fenêtre** : `m` pair, `p_{n₀} > 3` ⟹ `Σ_r g_r ≥ 3m`. -/
theorem gapWeights_sum_ge_three_mul (n₀ m : ℕ) (hm : Even m) (h3 : 3 < fnPrimeAtRank n₀) :
    3 * (m : ℝ) ≤ ∑ r, gapWeights n₀ m r := by
  rw [gapWeights_sum]
  have := primeAtRank_window_ge_three_mul n₀ m hm h3
  have h' : ((fnPrimeAtRank n₀ + 3 * m : ℕ) : ℝ) ≤ fnPrimeAtRank (n₀ + m) := by exact_mod_cast this
  push_cast at h'; linarith

/-- **Plancher par classes** : `Σ_r plancher(a_r) ≤ Σ_r g_r`. -/
theorem gapWeights_sum_ge_classFloor (n₀ m : ℕ) (h3 : 3 < fnPrimeAtRank n₀) :
    ∑ r : Fin m, (classFloor (eventClass (n₀ + r)) : ℝ) ≤ ∑ r, gapWeights n₀ m r :=
  Finset.sum_le_sum fun r _ => gapWeights_ge_classFloor n₀ m h3 r

/-- **Plancher pondéré** : `Σ_r g_r p_r^β ≥ p_{n₀}^β (p_{n₀+m} − p_{n₀})` pour `β ≥ 0`. -/
theorem weighted_window_floor (n₀ m : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    (fnPrimeAtRank n₀ : ℝ) ^ β * ((fnPrimeAtRank (n₀ + m) : ℝ) - fnPrimeAtRank n₀) ≤
      ∑ r, gapWeights n₀ m r * primeWindow n₀ m r ^ β := by
  rw [← gapWeights_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (gapWeights_pos n₀ m r).le
  unfold primeWindow
  exact Real.rpow_le_rpow (Nat.cast_nonneg _)
    (by exact_mod_cast thm_primeAtRank_strictMono.monotone (by omega : n₀ ≤ n₀ + (r : ℕ))) hβ

/-- **Composé : minoration de la paire × plancher grammatical de la fenêtre.** -/
theorem passage_pair_minoration_floor {H H' : ℝ} (hHH' : H ≤ H')
    (hFib : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' → |(σ : ℂ).im| = H')
    (hT : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' →
      (σ : ℂ).re * ((σ : ℂ).re + 1) < (σ : ℂ).im ^ 2)
    (n₀ m : ℕ) (l : TrueZero) (hH : H < rZeroHeight l.1) (hH' : rZeroHeight l.1 ≤ H')
    (hβ : rZeroRadialPosition l.1 < 1 / 2) :
    ((-(zetaZeroMultiplicity (zeroPoint l) : ℂ) / (zeroPoint l * (zeroPoint l + 1))).re *
        (fnPrimeAtRank n₀ : ℝ) ^ rZeroRadialPosition l.1 +
      (-(zetaZeroMultiplicity (zeroPoint l) : ℂ) /
          (zeroPoint (mirrorMember l) * (zeroPoint (mirrorMember l) + 1))).re *
        (fnPrimeAtRank n₀ : ℝ) ^ (1 - rZeroRadialPosition l.1)) *
        ((fnPrimeAtRank (n₀ + m) : ℝ) - fnPrimeAtRank n₀) ≤
      (∑' σ, upperFiltered H H' (primeWindow n₀ m)
        (phaseMatched H' (gapWeights n₀ m) (primeWindow n₀ m)) σ).re := by
  obtain ⟨-, -, -, -, hpos, h1, h2, -, -⟩ := arrival_mirror_fiber l hH hH' hβ
  have hlpos : 0 < ((memberIndex l : ExplicitIndex) : ℂ).im := l.2
  have hl1 : H < |((memberIndex l : ExplicitIndex) : ℂ).im| := by rw [abs_of_pos hlpos]; exact hH
  have hl2 : |((memberIndex l : ExplicitIndex) : ℂ).im| ≤ H' := by rw [abs_of_pos hlpos]; exact hH'
  have hw1 := upper_weight_re_nonneg (hT _ hl1 hl2) (zetaZeroMultiplicity (zeroPoint l))
  have hw2 := upper_weight_re_nonneg (hT _ h1 h2) (zetaZeroMultiplicity (zeroPoint l))
  have hb0 : 0 ≤ rZeroRadialPosition l.1 := (zeroPoint_re_pos l).le
  have hb1 : 0 ≤ 1 - rZeroRadialPosition l.1 := by linarith
  have f1 := weighted_window_floor n₀ m hb0
  have f2 := weighted_window_floor n₀ m hb1
  have key := arrival_mirror_minoration hHH' hFib hT (gapWeights n₀ m) (primeWindow n₀ m)
    (fun r => (gapWeights_pos n₀ m r).le) (primeWindow_gt_one n₀ m) l hH hH' hβ
  have hw1' : 0 ≤ (-(zetaZeroMultiplicity (zeroPoint l) : ℂ) / (zeroPoint l * (zeroPoint l + 1))).re := hw1
  have hw2' : 0 ≤ (-(zetaZeroMultiplicity (zeroPoint l) : ℂ) /
      (zeroPoint (mirrorMember l) * (zeroPoint (mirrorMember l) + 1))).re := hw2
  nlinarith [mul_le_mul_of_nonneg_left f1 hw1', mul_le_mul_of_nonneg_left f2 hw2']

/-! ## 5. Complément filtré développé avec ses phases propres, résidu conservé ; moitié conjuguée -/

/-- **Complément filtré, phases propres** : sous le filtre accordé sur `T`, chaque membre au-dessus de `T` contribue
`w_σ·Σ_r c_r x_r^{σ − iT}` (rotation relative `T_σ − T` conservée). -/
theorem complement_phase_development (T : ℝ) {m : ℕ} (c x : Fin m → ℝ) (hx : ∀ r, 1 < x r) :
    ∑ r, phaseMatched T c x r * followingSum T (x r) =
      ∑' σ, followingWeight T σ * ∑ r, (c r : ℂ) * (x r : ℂ) ^ ((σ : ℂ) - (T : ℂ) * I) := by
  rw [show (∑ r, phaseMatched T c x r * followingSum T (x r)) =
      ∑ r, phaseMatched T c x r * ∑' σ, followingWeight T σ * (x r : ℂ) ^ (σ : ℂ) from rfl,
    filtered_series_eq _ (followingWeight_norm_summable T) x _ hx]
  refine tsum_congr fun σ => ?_
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold phaseMatched
  exact phaseMatched_cpow (lt_trans one_pos (hx r)) T (c r) σ

/-- **Complément = fibre suivante finie + résidu au-delà de `H''`** (toutes les compensations conservées). -/
theorem complement_residual_split (H' H'' : ℝ) {x : ℝ} (hx : 1 < x) :
    followingSum H' x = nextFiberSum H' H'' x + followingSum H'' x := by
  rw [expected_next_fiber H' H'' hx, remainder_eq_preceding_add_following H' hx]; ring

theorem complement_window_residual_split (H' H'' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ)
    (hx : ∀ r, 1 < x r) :
    ∑ r, lam r * followingSum H' (x r) =
      ∑ r, lam r * nextFiberSum H' H'' (x r) + ∑ r, lam r * followingSum H'' (x r) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ => by rw [complement_residual_split H' H'' (hx r)]; ring

/-- **Contrôle de la moitié conjuguée**, terme à terme (oscillation sur la fenêtre conservée). -/
theorem lower_half_le {H H' : ℝ} {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    ‖∑' σ, lowerFiltered H H' x lam σ‖ ≤ ∑' σ, ‖lowerFiltered H H' x lam σ‖ :=
  norm_tsum_le_tsum_norm (lowerFiltered_summable H H' x lam hx).norm

/-- Terme conjugué sous le filtre accordé : `‖w_σ‖·‖Σ_r c_r x_r^{β_σ} x_r^{−2iT}‖`. -/
theorem lower_half_term_norm {H H' : ℝ} (hHH' : H ≤ H')
    (hFib : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' → |(σ : ℂ).im| = H')
    {m : ℕ} (c x : Fin m → ℝ) (hx : ∀ r, 1 < x r) (σ : ExplicitIndex) (hσ : (σ : ℂ).im ≤ 0) :
    ‖lowerFiltered H H' x (phaseMatched H' c x) σ‖ =
      ‖fiberWeight H H' σ‖ * ‖∑ r, ((c r * x r ^ (σ : ℂ).re : ℝ) : ℂ) * (x r : ℂ) ^ (-(2 * H' : ℂ) * I)‖ := by
  rw [lower_term_eq hHH' hFib c x hx σ hσ, norm_mul]

/-! ## 6. Réduction du passage -/

/-- **Réduction du passage à une inégalité exacte sur une fenêtre** : fenêtre `p_{n₀}, …, p_{n₀+m−1}`, filtre accordé
`λ_r = g_r p_r^{−iH'}`. Si, sur une longueur `m`, la part première filtrée du retrait, l'historique filtré `B_P`, le
complément filtré `B_Q` (phases conservées) et le contrôle de la moitié conjuguée `B_L` restent sous la minoration de
la paire arrivée + miroir, contradiction. Démontrée ; l'antécédent ne l'est pas. -/
theorem passage_window_reduction {H H' : ℝ} (hHH' : H ≤ H')
    (hFib : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' → |(σ : ℂ).im| = H')
    (hT : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → |(σ : ℂ).im| ≤ H' →
      (σ : ℂ).re * ((σ : ℂ).re + 1) < (σ : ℂ).im ^ 2)
    (n₀ : ℕ) (l : TrueZero) (hH : H < rZeroHeight l.1) (hH' : rZeroHeight l.1 ≤ H')
    (hβ : rZeroRadialPosition l.1 < 1 / 2)
    (hsep : ∃ m : ℕ,
      ‖primeSideFiltered (fnPrimeAtRank (n₀ + m)) (primeWindow n₀ m)
          (phaseMatched H' (gapWeights n₀ m) (primeWindow n₀ m))‖
        + filteredSeriesBound (precedingWeight H) (primeWindow n₀ m)
          (phaseMatched H' (gapWeights n₀ m) (primeWindow n₀ m))
        + filteredSeriesBound (followingWeight H') (primeWindow n₀ m)
          (phaseMatched H' (gapWeights n₀ m) (primeWindow n₀ m))
        + ∑' σ, ‖lowerFiltered H H' (primeWindow n₀ m)
          (phaseMatched H' (gapWeights n₀ m) (primeWindow n₀ m)) σ‖ <
      (-(zetaZeroMultiplicity (zeroPoint l) : ℂ) / (zeroPoint l * (zeroPoint l + 1))).re *
          ∑ r, gapWeights n₀ m r * primeWindow n₀ m r ^ rZeroRadialPosition l.1 +
        (-(zetaZeroMultiplicity (zeroPoint l) : ℂ) /
            (zeroPoint (mirrorMember l) * (zeroPoint (mirrorMember l) + 1))).re *
          ∑ r, gapWeights n₀ m r * primeWindow n₀ m r ^ (1 - rZeroRadialPosition l.1)) : False := by
  obtain ⟨m, hm⟩ := hsep
  have hx := primeWindow_gt_one n₀ m
  exact window_closes_of_bounds (H := H) (H' := H') (primeWindow n₀ m) _ hx
    (arrival_mirror_minoration hHH' hFib hT (gapWeights n₀ m) (primeWindow n₀ m)
      (fun r => (gapWeights_pos n₀ m r).le) hx l hH hH' hβ)
    (lower_half_le _ _ hx) (complement_filtered_le H' _ _ hx)
    (historyRemoved_le_primeSide H _ _ hx _ (primeWindow_ceil_le n₀ m)) (by linarith)

#print axioms filtered_series_norm_le
#print axioms complement_filtered_le_margin
#print axioms window_closes_of_bounds
#print axioms arrival_mirror_fiber
#print axioms arrival_mirror_minoration
#print axioms passage_pair_minoration_floor
#print axioms gapWeights_sum_ge_three_mul
#print axioms complement_phase_development
#print axioms passage_window_reduction

end RHV6Fresh
