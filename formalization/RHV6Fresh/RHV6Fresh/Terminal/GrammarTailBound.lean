/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.GrammarOperator
import RHV6Fresh.Terminal.StageCell

/-!
# La borne du complément infini sous l'opérateur grammatical (auteur, 2026-10-19 : « chercher une borne démontrée du
complément infini (zéros au-dessus de l'arrivée) »)

Inventaire du dépôt : aucune borne UNIFORME en la translation du signal des zéros au-dessus d'une hauteur `H` n'est
démontrée ; ce qui existe est (i) la borne d'exposant `1` de la queue (`followingSum_norm_le_budget_linear`, toute
position radiale, par `Re ρ ≤ 1`) et (ii) la caractérisation « queue sous `√x` ⟺ tout zéro au-dessus de `H` est en
ligne » (`followingSum_sqrt_iff_following_le_half`). Ce module transporte ces deux faits, tels quels, dans le cadre de
l'opérateur `𝓛_G` (signal normalisé en `u = log x`, projection fenêtrée, différence seconde pondérée par classes) :

* découpage EXACT du signal normalisé des premiers en tête (hauteurs `≤ H`, somme finie) et queue (hauteurs `> H`,
  somme infinie) : `signal_eq_head_add_tail` ;
* queue : borne d'exposant `1` (`tailSignal_norm_le_linear`), borne uniforme ⟺ tout zéro au-dessus de `H` en ligne
  (`tailSignal_bounded_iff`, aucun côté dérivé ici) ;
* tête : bornée uniformément dès que tout zéro de hauteur `≤ H` est en ligne (`headSignal_norm_le_of_onLine`) ;
* projection fenêtrée et `𝓛_G` de la queue : borne d'exposant `1` en la translation (`grammarTail_norm_le_linear`,
  croissance `e^{a/2}`), borne uniforme sous la seule hypothèse « tout zéro au-dessus de `H` en ligne »
  (`grammarTail_uniform_of_following_onLine`) ;
* l'enveloppe d'exposant `1` n'est bornée par aucune constante (`grammarTail_linear_envelope_unbounded`).

Portée : la borne démontrée du complément infini a l'exposant `1`, c'est-à-dire exactement la croissance maximale que
la paire de l'arrivée elle-même peut avoir (`e^{(1/2 − β)a} ≤ e^{a/2}`) ; elle ne sépare rien. La borne uniforme qui
fermerait le schéma `grammar_operator_two_lemma_closes` équivaut, au niveau du signal, à « tout zéro au-dessus de la
hauteur de coupure est en ligne » : elle n'est pas dérivée.
-/


namespace RHV6Fresh

open scoped BigOperators
open RHV3Lean MeasureTheory

/-! ## §1 Tête et queue du signal normalisé des premiers -/

/-- Queue normalisée : somme à l'infini des contributions lissées des zéros de hauteur `> H`, en `u = log x`,
divisée par `√x = e^{u/2}`. -/
noncomputable def tailSignal (H u : ℝ) : ℂ := followingSum H (Real.exp u) / (Real.exp (u / 2) : ℂ)

/-- Tête normalisée : somme (finie) des contributions lissées des zéros de hauteur `≤ H`, divisée par `√x`. -/
noncomputable def headSignal (H u : ℝ) : ℂ := precedingSum H (Real.exp u) / (Real.exp (u / 2) : ℂ)

/-- **Découpage exact** du signal normalisé des premiers : tête + queue, pour tout `u > 0` et toute coupure `H`
(identité, aucune borne, aucune position radiale). -/
theorem signal_eq_head_add_tail (H : ℝ) {u : ℝ} (hu : 0 < u) :
    (smoothedRemainder (Real.exp u) / (Real.exp (u / 2) : ℂ)) = headSignal H u + tailSignal H u := by
  unfold headSignal tailSignal
  rw [remainder_eq_preceding_add_following H (Real.one_lt_exp_iff.mpr hu), add_div]

/-- `(e^u)^{1/2} = e^{u/2}`. -/
theorem exp_rpow_half (u : ℝ) : Real.exp u ^ (1 / 2 : ℝ) = Real.exp (u / 2) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp]; ring_nf

/-- Le budget de la queue est positif ou nul. -/
theorem followingBudget_nonneg (H : ℝ) : 0 ≤ followingBudget H :=
  tsum_nonneg fun _ => norm_nonneg _

/-! ## §2 La queue : exposant `1` démontré, borne uniforme caractérisée -/

/-- **Borne démontrée de la queue normalisée** : `‖queue(u)‖ ≤ budget(H)·e^{u/2}` pour `u > 0`, toute position
radiale (exposant `1` du reste, `Re ρ ≤ 1`). Elle croît avec `u`. -/
theorem tailSignal_norm_le_linear (H : ℝ) {u : ℝ} (hu : 0 < u) :
    ‖tailSignal H u‖ ≤ followingBudget H * Real.exp (u / 2) := by
  unfold tailSignal
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    div_le_iff₀ (Real.exp_pos _)]
  calc ‖followingSum H (Real.exp u)‖ ≤ followingBudget H * Real.exp u :=
        followingSum_norm_le_budget_linear H (Real.one_lt_exp_iff.mpr hu)
    _ = followingBudget H * Real.exp (u / 2) * Real.exp (u / 2) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- **Queue bornée uniformément dès que tout zéro au-dessus de `H` est en ligne** : `‖queue(u)‖ ≤ budget(H)`. -/
theorem tailSignal_norm_le_of_following_onLine {H : ℝ}
    (hOn : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → (σ : ℂ).re ≤ 1 / 2) {u : ℝ} (hu : 0 < u) :
    ‖tailSignal H u‖ ≤ followingBudget H := by
  unfold tailSignal
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    div_le_iff₀ (Real.exp_pos _)]
  have := followingSum_le_budget_of_le_half hOn (Real.one_lt_exp_iff.mpr hu)
  rwa [exp_rpow_half] at this

/-- **Caractérisation** : la queue normalisée est bornée uniformément en `u > 0` ⟺ tout zéro au-dessus de `H` est en
ligne. Aucun des deux côtés n'est dérivé ici : c'est la lecture du pôle (`followingSum_sqrt_iff_following_le_half`)
transportée au signal normalisé. -/
theorem tailSignal_bounded_iff (H : ℝ) :
    (∃ C : ℝ, ∀ u : ℝ, 0 < u → ‖tailSignal H u‖ ≤ C) ↔
      ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → (σ : ℂ).re ≤ 1 / 2 := by
  constructor
  · rintro ⟨C, hC⟩
    refine (followingSum_sqrt_iff_following_le_half H).mp ⟨C, fun x hx => ?_⟩
    have hx0 : 0 < x := lt_trans one_pos hx
    have hu : 0 < Real.log x := Real.log_pos hx
    have h := hC (Real.log x) hu
    unfold tailSignal at h
    rw [Real.exp_log hx0, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      div_le_iff₀ (Real.exp_pos _)] at h
    rw [Real.rpow_def_of_pos hx0]
    calc ‖followingSum H x‖ ≤ C * Real.exp (Real.log x / 2) := h
      _ = C * Real.exp (Real.log x * (1 / 2)) := by ring_nf
  · intro hOn
    exact ⟨followingBudget H, fun u hu => tailSignal_norm_le_of_following_onLine hOn hu⟩

/-! ## §3 La tête : bornée dès que son historique est en ligne -/

/-- **Tête bornée uniformément** dès que tout zéro de hauteur `≤ H` est en ligne (`precedingSum_le_budget_of_onLine`). -/
theorem headSignal_norm_le_of_onLine {H : ℝ}
    (hOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ H → rZeroRadialPosition w.1 = 1 / 2) {u : ℝ} (hu : 0 < u) :
    ‖headSignal H u‖ ≤ precedingBudget H := by
  unfold headSignal
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    div_le_iff₀ (Real.exp_pos _)]
  have := precedingSum_le_budget_of_onLine hOn (Real.one_lt_exp_iff.mpr hu)
  rwa [exp_rpow_half] at this

/-! ## §4 Projection fenêtrée d'un signal majoré sur la fenêtre -/

/-- Le filtre est de module `1`. -/
theorem filter_norm_eq_one (T u : ℝ) : ‖Complex.exp (-((T : ℂ) * Complex.I * (u : ℂ)))‖ = 1 := by
  have : -((T : ℂ) * Complex.I * (u : ℂ)) = ((-(T * u) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- La projection fenêtrée d'un signal majoré par `M` sur la fenêtre `[a, a + L]` est majorée par `M·L`, à toute
fréquence. -/
theorem windowProjection_norm_le_of_bound (f : ℝ → ℂ) (a : ℝ) {L M : ℝ} (hL : 0 ≤ L)
    (hf : ∀ u, a < u → u ≤ a + L → ‖f u‖ ≤ M) (T : ℝ) : ‖windowProjection f a L T‖ ≤ M * L := by
  unfold windowProjection
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + L) (C := M)
    (f := fun u => f u * Complex.exp (-((T : ℂ) * Complex.I * (u : ℂ)))) (by
      intro u hu
      rw [Set.uIoc_of_le (by linarith)] at hu
      rw [norm_mul, filter_norm_eq_one, mul_one]
      exact hf u hu.1 hu.2)
  rwa [add_sub_cancel_left, abs_of_nonneg hL] at h

/-- Projection de la queue : borne d'exposant `1`, `‖P(queue)(a)‖ ≤ budget(H)·e^{(a+L)/2}·L` pour `a > 0`. -/
theorem tail_projection_norm_le (H a : ℝ) {L : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (T : ℝ) :
    ‖windowProjection (tailSignal H) a L T‖ ≤ followingBudget H * Real.exp ((a + L) / 2) * L := by
  refine windowProjection_norm_le_of_bound _ a hL (fun u hu hu' => ?_) T
  calc ‖tailSignal H u‖ ≤ followingBudget H * Real.exp (u / 2) := tailSignal_norm_le_linear H (by linarith)
    _ ≤ followingBudget H * Real.exp ((a + L) / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (followingBudget_nonneg H)

/-- Projection de la queue, borne uniforme sous « tout zéro au-dessus de `H` en ligne » : `≤ budget(H)·L`. -/
theorem tail_projection_uniform_of_following_onLine {H : ℝ}
    (hOn : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → (σ : ℂ).re ≤ 1 / 2) (a : ℝ) {L : ℝ} (ha : 0 < a)
    (hL : 0 ≤ L) (T : ℝ) : ‖windowProjection (tailSignal H) a L T‖ ≤ followingBudget H * L :=
  windowProjection_norm_le_of_bound _ a hL
    (fun u hu _ => tailSignal_norm_le_of_following_onLine hOn (by linarith)) T

/-! ## §5 `𝓛_G` de la queue -/

/-- `𝓛_G` d'une fonction majorée aux trois translatés de chaque écart : `≤ 4M Σ_r |w(a_r)|` (version ponctuelle de
`classWeightedCurvatureC_norm_le`, aucune borne globale exigée). -/
theorem classWeightedCurvatureC_norm_le_of_translates (w : ℕ → ℝ) (r₀ m : ℕ) (F : ℝ → ℂ) {M : ℝ} (a : ℝ)
    (hF : ∀ j : Fin m, ‖F (a + rPrimeGapLogRatio (r₀ + j))‖ ≤ M ∧ ‖F a‖ ≤ M ∧
      ‖F (a - rPrimeGapLogRatio (r₀ + j))‖ ≤ M) :
    ‖classWeightedCurvatureC w r₀ m F a‖ ≤ (∑ j : Fin m, |w (eventClass (r₀ + j))|) * (4 * M) := by
  unfold classWeightedCurvatureC
  rw [Finset.sum_mul]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  obtain ⟨h1, h2, h3⟩ := hF j
  calc ‖F (a + rPrimeGapLogRatio (r₀ + j)) - 2 * F a + F (a - rPrimeGapLogRatio (r₀ + j))‖
      ≤ ‖F (a + rPrimeGapLogRatio (r₀ + j)) - 2 * F a‖ + ‖F (a - rPrimeGapLogRatio (r₀ + j))‖ := norm_add_le _ _
    _ ≤ (‖F (a + rPrimeGapLogRatio (r₀ + j))‖ + ‖2 * F a‖) + ‖F (a - rPrimeGapLogRatio (r₀ + j))‖ :=
        by have := norm_sub_le (F (a + rPrimeGapLogRatio (r₀ + j))) (2 * F a); linarith
    _ ≤ (M + 2 * M) + M := by
        have h2' : ‖(2 : ℂ) * F a‖ = 2 * ‖F a‖ := by rw [norm_mul, Complex.norm_ofNat]
        rw [h2']; linarith
    _ = 4 * M := by ring

/-- **`𝓛_G` de la queue** : l'opérateur grammatical appliqué à la projection fenêtrée de la queue au-dessus de `H`. -/
noncomputable def grammarTail (w : ℕ → ℝ) (r₀ m : ℕ) (L T H a : ℝ) : ℂ :=
  classWeightedCurvatureC w r₀ m (fun a => windowProjection (tailSignal H) a L T) a

/-- **Borne démontrée de `𝓛_G(queue)`, exposant `1`** : si tous les écarts de la fenêtre sont `≤ Lmax < a`,
`‖𝓛_G(queue)(a)‖ ≤ 4 Σ|w| · budget(H) · e^{(a + Lmax + L)/2} · L`. Elle croît en `e^{a/2}` avec la translation. -/
theorem grammarTail_norm_le_linear (w : ℕ → ℝ) (r₀ m : ℕ) {L T H a Lmax : ℝ} (hL : 0 ≤ L)
    (hgap : ∀ j : Fin m, rPrimeGapLogRatio (r₀ + j) ≤ Lmax) (hLmax : 0 ≤ Lmax) (ha : Lmax < a) :
    ‖grammarTail w r₀ m L T H a‖ ≤
      (∑ j : Fin m, |w (eventClass (r₀ + j))|) * (4 * (followingBudget H * Real.exp ((a + Lmax + L) / 2) * L)) := by
  unfold grammarTail
  refine classWeightedCurvatureC_norm_le_of_translates w r₀ m _ a fun j => ?_
  have hj := hgap j
  have hj0 : 0 ≤ rPrimeGapLogRatio (r₀ + j) := (thm_primeGapLogRatio_pos _).le
  have key : ∀ b : ℝ, 0 < b → b ≤ a + Lmax →
      ‖windowProjection (tailSignal H) b L T‖ ≤ followingBudget H * Real.exp ((a + Lmax + L) / 2) * L := by
    intro b hb hb'
    calc ‖windowProjection (tailSignal H) b L T‖ ≤ followingBudget H * Real.exp ((b + L) / 2) * L :=
          tail_projection_norm_le H b hb hL T
      _ ≤ followingBudget H * Real.exp ((a + Lmax + L) / 2) * L :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
            (followingBudget_nonneg H)) hL
  exact ⟨key _ (by linarith) (by linarith), key a (by linarith) (by linarith),
    key _ (by linarith) (by linarith)⟩

/-- **`𝓛_G(queue)` bornée uniformément** sous la seule hypothèse « tout zéro au-dessus de `H` est en ligne » :
`≤ 4 Σ|w| · budget(H) · L`, pour toute translation `a` au-delà des écarts de la fenêtre. -/
theorem grammarTail_uniform_of_following_onLine (w : ℕ → ℝ) (r₀ m : ℕ) {L T H a : ℝ} (hL : 0 ≤ L)
    (hOn : ∀ σ : ExplicitIndex, H < |(σ : ℂ).im| → (σ : ℂ).re ≤ 1 / 2)
    (ha : ∀ j : Fin m, rPrimeGapLogRatio (r₀ + j) < a) :
    ‖grammarTail w r₀ m L T H a‖ ≤ (∑ j : Fin m, |w (eventClass (r₀ + j))|) * (4 * (followingBudget H * L)) := by
  unfold grammarTail
  refine classWeightedCurvatureC_norm_le_of_translates w r₀ m _ a fun j => ?_
  have hj := ha j
  have hj0 : 0 ≤ rPrimeGapLogRatio (r₀ + j) := (thm_primeGapLogRatio_pos _).le
  exact ⟨tail_projection_uniform_of_following_onLine hOn _ (by linarith) hL T,
    tail_projection_uniform_of_following_onLine hOn _ (by linarith) hL T,
    tail_projection_uniform_of_following_onLine hOn _ (by linarith) hL T⟩

/-- **L'enveloppe d'exposant `1` n'est pas une borne uniforme** : dès que le budget et la largeur sont strictement
positifs, `budget·e^{(a + Lmax + L)/2}·L` dépasse toute constante le long des translations. -/
theorem grammarTail_linear_envelope_unbounded {H L Lmax : ℝ} (hB : 0 < followingBudget H) (hL : 0 < L) (K : ℝ) :
    ∃ a : ℝ, Lmax < a ∧ K < followingBudget H * Real.exp ((a + Lmax + L) / 2) * L := by
  set c : ℝ := 2 * Real.log (K / (followingBudget H * L) + 1) - Lmax - L + 1 with hc
  refine ⟨max (Lmax + 1) c, by linarith [le_max_left (Lmax + 1) c], ?_⟩
  have hBL : 0 < followingBudget H * L := mul_pos hB hL
  have hc' : c ≤ max (Lmax + 1) c := le_max_right _ _
  have h1 : K / (followingBudget H * L) < Real.exp ((max (Lmax + 1) c + Lmax + L) / 2) := by
    calc K / (followingBudget H * L) < K / (followingBudget H * L) + 1 := by linarith
      _ ≤ Real.exp (Real.log (K / (followingBudget H * L) + 1)) := Real.le_exp_log _
      _ ≤ Real.exp ((max (Lmax + 1) c + Lmax + L) / 2) := Real.exp_le_exp.mpr (by rw [hc] at hc'; linarith)
  rw [div_lt_iff₀ hBL] at h1
  linarith

#print axioms grammarTail_norm_le_linear
#print axioms tailSignal_bounded_iff
#print axioms grammarTail_uniform_of_following_onLine

end RHV6Fresh
