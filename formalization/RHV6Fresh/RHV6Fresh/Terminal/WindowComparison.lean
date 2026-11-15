/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import RHV6Fresh.Terminal.CertifiedRemoval
import RHV6Fresh.Terminal.JointComparison

/-!
# Comparaison de fenêtres de zéros : identités de chaîne et borne de groupe (auteur, 2026-10-11 ; E197)

Étude comparative début / milieu / fin (E197, `experiments/e197_window_comparison.py`, hors Lean) : sur toutes les
fenêtres, la même identité exacte relie le reste, l'historique retiré, les groupes successifs et le complément ; seule la
taille relative des termes varie avec la hauteur. Ce module formalise les identités vérifiables, sans prémisse.

* §1 chaîne de fibres : `P_{h_K} − P_{h_0} = Σ_{i<K} fibre]h_i, h_{i+1}]` (`fiber_chain_telescope`) ; reste
  `R − P_{h_0} = Σ fibres + Q_{h_K}` (`remainder_window_chain`) ; version fenêtre (`historyRemoved_chain`) ; relation
  entre deux positions `retrait(H) = groupe]H, H'] + retrait(H')` (`historyRemoved_shift`, sans condition).
* §2 borne de groupe démontrée sous ON des membres du groupe : `‖fibre]H, H'](x)‖ ≤ fiberBudget·√x`
  (`nextFiberSum_le_sqrt_of_onLine`), conjointe (`groupSignal_le_sqrt_of_onLine`).
* §3 changement de position de l'estimation : sous l'historique ON jusqu'à `H ≥ 28`, une estimation du retrait de
  l'historique `‖Σλ(R − P_H)(x_r)‖ ≤ C Σ|λ| x_r^θ` donne celle du retrait certifié d'exposant `max θ (1/2)`
  (`certified_estimate_of_history_estimate`) : on peut lire l'estimation à la position de la fenêtre.
-/

namespace RHV6Fresh

open RHV3Lean

/-! ## 1. Chaîne de fibres -/

/-- **Télescopage des fibres** entre hauteurs successives `h 0, …, h K`. -/
theorem fiber_chain_telescope (h : ℕ → ℝ) (K : ℕ) (x : ℝ) :
    precedingSum (h K) x - precedingSum (h 0) x = ∑ i ∈ Finset.range K, nextFiberSum (h i) (h (i + 1)) x := by
  unfold nextFiberSum
  exact (Finset.sum_range_sub (fun i => precedingSum (h i) x) K).symm

/-- **Reste depuis une position** : `R − P_{h_0} = Σ_{i<K} fibre]h_i, h_{i+1}] + Q_{h_K}` (identité exacte). -/
theorem remainder_window_chain (h : ℕ → ℝ) (K : ℕ) {x : ℝ} (hx : 1 < x) :
    smoothedRemainder x - precedingSum (h 0) x =
      (∑ i ∈ Finset.range K, nextFiberSum (h i) (h (i + 1)) x) + followingSum (h K) x := by
  rw [← fiber_chain_telescope, remainder_eq_preceding_add_following (h K) hx]; ring

/-- **Relation entre deux positions** : le retrait de l'historique jusqu'à `H` est le signal du groupe `]H, H']` plus le
retrait jusqu'à `H'` (aucune condition, aucun module). -/
theorem historyRemoved_shift (H H' : ℝ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) :
    historyRemoved H x lam = groupSignal H H' x lam + historyRemoved H' x lam := by
  unfold historyRemoved groupSignal nextFiberSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- **Chaîne de fenêtres** : retrait depuis `h 0` = somme des signaux des groupes successifs + complément entier. -/
theorem historyRemoved_chain (h : ℕ → ℝ) (K : ℕ) {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    historyRemoved (h 0) x lam =
      (∑ i ∈ Finset.range K, groupSignal (h i) (h (i + 1)) x lam) + ∑ r, lam r * followingSum (h K) (x r) := by
  have key : ∀ r, smoothedRemainder (x r) - precedingSum (h 0) (x r) =
      (∑ i ∈ Finset.range K, nextFiberSum (h i) (h (i + 1)) (x r)) + followingSum (h K) (x r) :=
    fun r => remainder_window_chain h K (hx r)
  unfold historyRemoved groupSignal
  simp_rw [key, mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_comm]

/-! ## 2. Borne de groupe sous ON des membres du groupe -/

theorem fiberWeight_eq_zero_of_le {H H' : ℝ} (hHH : H ≤ H') (σ : ExplicitIndex)
    (hσ : ¬ (H < |(σ : ℂ).im| ∧ |(σ : ℂ).im| ≤ H')) : fiberWeight H H' σ = 0 := by
  unfold fiberWeight precedingWeight
  by_cases h1 : H < |(σ : ℂ).im|
  · have h2 : H' < |(σ : ℂ).im| := lt_of_not_ge fun h => hσ ⟨h1, h⟩
    rw [if_pos h2, if_pos h1, sub_zero]
  · have h2 : ¬ H' < |(σ : ℂ).im| := fun h => h1 (lt_of_le_of_lt hHH h)
    rw [if_neg h2, if_neg h1, sub_self]

/-- **Borne démontrée du groupe** : si tous les membres de hauteur dans `]H, H']` sont ON, la fibre est bornée par
`fiberBudget·√x`. -/
theorem nextFiberSum_le_sqrt_of_onLine {H H' : ℝ} (hHH : H ≤ H')
    (hOn : ∀ w : TrueZero, H < rZeroHeight w.1 → rZeroHeight w.1 ≤ H' → rZeroRadialPosition w.1 = 1 / 2)
    {x : ℝ} (hx : 1 < x) : ‖nextFiberSum H H' x‖ ≤ fiberBudget H H' * x ^ (1 / 2 : ℝ) := by
  have hx0 : 0 < x := lt_trans one_pos hx
  have hterm : ∀ σ : ExplicitIndex,
      ‖fiberWeight H H' σ * (x : ℂ) ^ (σ : ℂ)‖ ≤ ‖fiberWeight H H' σ‖ * x ^ (1 / 2 : ℝ) := by
    intro σ
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    by_cases h : H < |(σ : ℂ).im| ∧ |(σ : ℂ).im| ≤ H'
    · obtain ⟨hh, hr⟩ := explicitIndex_upper_readings σ
      have hre : (σ : ℂ).re ≤ 1 / 2 := by
        rw [← hr]; exact (hOn _ (by rw [hh]; exact h.1) (by rw [hh]; exact h.2)).le
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx.le hre) (norm_nonneg _)
    · rw [fiberWeight_eq_zero_of_le hHH σ h, norm_zero, zero_mul, zero_mul]
  have hdom : Summable fun σ : ExplicitIndex => ‖fiberWeight H H' σ‖ * x ^ (1 / 2 : ℝ) :=
    (fiberWeight_norm_summable H H').mul_right _
  have hs : Summable fun σ : ExplicitIndex => ‖fiberWeight H H' σ * (x : ℂ) ^ (σ : ℂ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hdom
  rw [nextFiberSum_eq_tsum H H' hx]
  calc ‖∑' σ : ExplicitIndex, fiberWeight H H' σ * (x : ℂ) ^ (σ : ℂ)‖
      ≤ ∑' σ : ExplicitIndex, ‖fiberWeight H H' σ * (x : ℂ) ^ (σ : ℂ)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' σ : ExplicitIndex, ‖fiberWeight H H' σ‖ * x ^ (1 / 2 : ℝ) := Summable.tsum_le_tsum hterm hs hdom
    _ = fiberBudget H H' * x ^ (1 / 2 : ℝ) := by unfold fiberBudget; exact tsum_mul_right

/-- **Borne conjointe du groupe** sous ON : `‖Σλ_r fibre(x_r)‖ ≤ fiberBudget·Σ|λ_r| √x_r`. -/
theorem groupSignal_le_sqrt_of_onLine {H H' : ℝ} (hHH : H ≤ H')
    (hOn : ∀ w : TrueZero, H < rZeroHeight w.1 → rZeroHeight w.1 ≤ H' → rZeroRadialPosition w.1 = 1 / 2)
    {m : ℕ} (x : Fin m → ℝ) (lam : Fin m → ℂ) (hx : ∀ r, 1 < x r) :
    ‖groupSignal H H' x lam‖ ≤ fiberBudget H H' * ∑ r, ‖lam r‖ * x r ^ (1 / 2 : ℝ) := by
  unfold groupSignal
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul]
  have h := nextFiberSum_le_sqrt_of_onLine hHH hOn (hx r)
  calc ‖lam r‖ * ‖nextFiberSum H H' (x r)‖ ≤ ‖lam r‖ * (fiberBudget H H' * x r ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = fiberBudget H H' * (‖lam r‖ * x r ^ (1 / 2 : ℝ)) := by ring

/-! ## 3. Lecture de l'estimation à la position de la fenêtre -/

/-- **Changement de position** : sous l'historique ON jusqu'à `H ≥ 28`, une estimation du retrait de l'historique d'exposant
`θ` donne l'estimation du retrait des trois contributions certifiées d'exposant `max θ (1/2)`. -/
theorem certified_estimate_of_history_estimate {H : ℝ} (h28 : 28 ≤ H)
    (hOn : ∀ w : TrueZero, rZeroHeight w.1 ≤ H → rZeroRadialPosition w.1 = 1 / 2) {θ C : ℝ}
    (hEst : ∀ (m : ℕ) (x : Fin m → ℝ) (lam : Fin m → ℂ), (∀ r, 1 < x r) →
      ‖historyRemoved H x lam‖ ≤ C * ∑ r, ‖lam r‖ * x r ^ θ) :
    ∀ (m : ℕ) (x : Fin m → ℝ) (lam : Fin m → ℂ), (∀ r, 1 < x r) →
      ‖∑ r, lam r * (smoothedRemainder (x r) - certifiedPart (x r))‖ ≤
        (|C| + fiberBudget 28 H) * ∑ r, ‖lam r‖ * x r ^ max θ (1 / 2) := by
  intro m x lam hx
  have hsplit : ∑ r, lam r * (smoothedRemainder (x r) - certifiedPart (x r)) =
      groupSignal 28 H x lam + historyRemoved H x lam := by
    rw [← historyRemoved_shift]; rfl
  have hG := groupSignal_le_sqrt_of_onLine h28 (fun w _ hw => hOn w hw) x lam hx
  have hH := hEst m x lam hx
  have hB := fiberBudget_nonneg 28 H
  have hmono : ∀ r, ‖lam r‖ * x r ^ θ ≤ ‖lam r‖ * x r ^ max θ (1 / 2) := fun r =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hx r).le (le_max_left _ _)) (norm_nonneg _)
  have hmono' : ∀ r, ‖lam r‖ * x r ^ (1 / 2 : ℝ) ≤ ‖lam r‖ * x r ^ max θ (1 / 2) := fun r =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hx r).le (le_max_right _ _)) (norm_nonneg _)
  have hnn : 0 ≤ ∑ r, ‖lam r‖ * x r ^ θ :=
    Finset.sum_nonneg fun r _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by linarith [hx r]) _)
  rw [hsplit]
  calc ‖groupSignal 28 H x lam + historyRemoved H x lam‖
      ≤ ‖groupSignal 28 H x lam‖ + ‖historyRemoved H x lam‖ := norm_add_le _ _
    _ ≤ fiberBudget 28 H * ∑ r, ‖lam r‖ * x r ^ (1 / 2 : ℝ) + |C| * ∑ r, ‖lam r‖ * x r ^ θ :=
        add_le_add hG (hH.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hnn))
    _ ≤ fiberBudget 28 H * ∑ r, ‖lam r‖ * x r ^ max θ (1 / 2) +
          |C| * ∑ r, ‖lam r‖ * x r ^ max θ (1 / 2) :=
        add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => hmono' r) hB)
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => hmono r) (abs_nonneg C))
    _ = (|C| + fiberBudget 28 H) * ∑ r, ‖lam r‖ * x r ^ max θ (1 / 2) := by ring

#print axioms fiber_chain_telescope
#print axioms remainder_window_chain
#print axioms historyRemoved_shift
#print axioms historyRemoved_chain
#print axioms nextFiberSum_le_sqrt_of_onLine
#print axioms groupSignal_le_sqrt_of_onLine
#print axioms certified_estimate_of_history_estimate

end RHV6Fresh
